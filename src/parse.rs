use crate::cmd::{
    Cmd, CmdAxiom, CmdConst, CmdDef, CmdInductive, CmdInfix, CmdInfixl, CmdInfixr, CmdInstance,
    CmdLemma, CmdLocalTypeConst, CmdNofix, CmdPrefix, CmdStructure, CmdTypeConst, CmdTypeInductive,
    Constructor, DataConstructor, Fixity, InstanceDef, InstanceField, InstanceLemma, Operator,
    StructureAxiom, StructureConst, StructureField,
};
use crate::expr::{
    mk_expr_app, mk_expr_assume, mk_expr_assump, mk_expr_const, mk_expr_inst, mk_expr_take, Expr,
};
use crate::proof::mk_type_prop;
use crate::tt::{
    mk_app, mk_const, mk_fresh_hole, mk_fresh_type_hole, mk_local, mk_type_arrow, mk_type_const,
    mk_type_local, Kind, Name, Term, Type,
};

use crate::lex::{Lex, LexError, SourceInfo, Token, TokenKind};
use anyhow::bail;
use std::collections::{HashMap, HashSet};
use std::mem;
use thiserror::Error;

#[derive(Default, Debug, Clone)]
pub struct TokenTable {
    led: HashMap<String, Operator>,
    nud: HashMap<String, Operator>,
}

impl TokenTable {
    pub fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        match op.fixity {
            Fixity::Infix | Fixity::Infixl | Fixity::Infixr => {
                let sym = op.symbol.clone();
                if self.led.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
            Fixity::Nofix | Fixity::Prefix => {
                let sym = op.symbol.clone();
                if self.nud.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
        };
        Ok(())
    }
}

enum Led {
    App,
    User(Operator),
}

impl Led {
    fn prec(&self) -> usize {
        match self {
            Self::App => 1024,
            Self::User(op) => op.prec,
        }
    }
}

enum Nud {
    Var,
    Abs,
    Forall,
    Exists,
    Uexists,
    Paren,
    Bracket,
    Hole,
    Brace,
    User(Operator),
    NumLit,
}

impl TokenTable {
    fn get_led(&self, token: &Token) -> Option<Led> {
        match token.kind {
            TokenKind::Ident => Some(Led::App),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match self.led.get(lit) {
                    Some(op) => Some(Led::User(op.clone())),
                    None => {
                        if self.get_nud(token).is_some() {
                            Some(Led::App)
                        } else {
                            None
                        }
                    }
                }
            }
            TokenKind::NumLit => Some(Led::App),
            TokenKind::Keyword => None,
        }
    }

    fn get_nud(&self, token: &Token) -> Option<Nud> {
        match token.kind {
            TokenKind::Ident => Some(Nud::Var),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match lit {
                    "(" => Some(Nud::Paren),
                    "⟨" => Some(Nud::Bracket),
                    "λ" => Some(Nud::Abs),
                    "∀" => Some(Nud::Forall),
                    "∃" => Some(Nud::Exists),
                    "∃!" => Some(Nud::Uexists),
                    "_" => Some(Nud::Hole),
                    "{" => Some(Nud::Brace),
                    _ => self.nud.get(token.as_str()).map(|op| Nud::User(op.clone())),
                }
            }
            TokenKind::NumLit => Some(Nud::NumLit),
            TokenKind::Keyword => None,
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("tokenize error")]
    Lex {
        #[from]
        lex_error: LexError,
    },
    #[error("parse error: {message} at {source_info}")]
    Parse {
        message: String,
        source_info: String,
    },
    #[error("unexpected end of input at {source_info}")]
    Eof { source_info: String },
}

#[derive(Debug, Default, Clone)]
pub struct AxiomInfo {
    pub type_arity: usize,
    pub num_params: usize,
}

#[derive(Debug, Default, Clone)]
pub struct Nasmespace {
    pub type_consts: HashSet<Name>,
    // mapping name to type arity
    pub consts: HashMap<Name, usize>,
    pub type_locals: Vec<Name>,
    // mapping name to type arity
    pub locals: Vec<Name>,
    // mapping name to type arity
    pub axioms: HashMap<Name, AxiomInfo>,
}

pub struct Parser<'a, 'b> {
    lex: &'b mut Lex<'a>,
    tt: &'b TokenTable,
    ns: &'b Nasmespace,
    type_locals: Vec<Name>,
    locals: Vec<Name>,
    holes: Vec<(Name, Type)>,
}

impl<'a, 'b> Parser<'a, 'b> {
    pub fn new(
        lex: &'b mut Lex<'a>,
        tt: &'b TokenTable,
        ns: &'b Nasmespace,
        type_variables: Vec<Name>,
    ) -> Self {
        Self {
            lex,
            tt,
            ns,
            type_locals: type_variables,
            locals: vec![],
            holes: vec![],
        }
    }

    fn fail<R>(token: Token<'a>, message: impl Into<String>) -> Result<R, ParseError> {
        Err(ParseError::Parse {
            message: message.into(),
            source_info: token.source_info.to_string(),
        })
    }

    fn eof_error(&self) -> ParseError {
        ParseError::Eof {
            source_info: SourceInfo::eof(self.lex.input()).to_string(),
        }
    }

    fn optional<F, R>(&mut self, f: F) -> Option<R>
    where
        F: FnOnce(&mut Self) -> Result<R, ParseError>,
    {
        let state = self.lex.save();
        match f(self) {
            Ok(m) => Some(m),
            Err(_err) => {
                self.lex.restore(state);
                None
            }
        }
    }

    fn peek_opt(&mut self) -> Option<Token<'a>> {
        self.optional(|this| this.peek())
    }

    fn peek(&mut self) -> Result<Token<'a>, ParseError> {
        self.lex
            .clone()
            .next()
            .transpose()?
            .ok_or_else(|| self.eof_error())
    }

    fn advance(&mut self) {
        self.lex
            .next()
            .expect("unchecked advance")
            .expect("impossible lex error! probably due to unchecked advance");
    }

    pub fn eof(&mut self) -> Result<(), ParseError> {
        if let Some(token) = self.peek_opt() {
            Self::fail(token, "expected EOF but tokens remain")?;
        }
        Ok(())
    }

    fn any_token(&mut self) -> Result<Token<'a>, ParseError> {
        self.lex
            .next()
            .transpose()
            .expect("lex error")
            .ok_or_else(|| self.eof_error())
    }

    fn ident(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_ident() {
            return Self::fail(token, "expected identifier");
        }
        Ok(token)
    }

    fn ident_opt(&mut self) -> Option<Token<'a>> {
        if let Some(token) = self.peek_opt() {
            if token.is_ident() {
                self.advance();
                return Some(token);
            }
        }
        None
    }

    fn expect_ident(&mut self, name: &str) -> Result<(), ParseError> {
        let token = self.any_token()?;
        if token.kind == TokenKind::Ident && token.as_str() == name {
            return Ok(());
        }
        Self::fail(token, format!("expected identifier '{}'", name))
    }

    fn symbol(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_symbol() {
            return Self::fail(token, "expected symbol");
        }
        Ok(token)
    }

    fn expect_symbol(&mut self, sym: &str) -> Result<(), ParseError> {
        let token = self.any_token()?;
        if token.kind == TokenKind::Symbol && token.as_str() == sym {
            return Ok(());
        }
        Self::fail(token, format!("expected symbol '{}'", sym))
    }

    fn expect_symbol_opt(&mut self, sym: &str) -> Option<Token<'a>> {
        if let Some(token) = self.peek_opt() {
            if token.kind == TokenKind::Symbol && token.as_str() == sym {
                self.advance();
                return Some(token);
            }
        }
        None
    }

    fn num_lit(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_num_lit() {
            return Self::fail(token, "expected numeral literal");
        }
        Ok(token)
    }

    fn keyword(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_keyword() {
            return Self::fail(token, "expected keyword");
        }
        Ok(token)
    }

    fn expect_keyword(&mut self, kw: &str) -> Result<(), ParseError> {
        let token = self.any_token()?;
        if token.kind == TokenKind::Keyword && token.as_str() == kw {
            return Ok(());
        }
        Self::fail(token, format!("expected keyword '{}'", kw))
    }

    fn name(&mut self) -> Result<Name, ParseError> {
        Ok(Name::try_from(self.ident()?.as_str()).expect("logic flaw"))
    }

    fn name_opt(&mut self) -> Option<Name> {
        self.ident_opt()
            .map(|token| Name::try_from(token.as_str()).expect("logic flaw"))
    }

    fn kind(&mut self) -> Result<Kind, ParseError> {
        let mut kind = 0;
        self.expect_ident("Type")?;
        while self.expect_symbol_opt("→").is_some() {
            self.expect_ident("Type")?;
            kind += 1;
        }
        Ok(Kind(kind))
    }

    fn type_primary(&mut self) -> Result<Type, ParseError> {
        let token = self.any_token()?;
        if token.is_ident() {
            let name: Name = token.as_str().try_into().expect("logic flaw");
            if self.type_locals.iter().any(|x| x == &name) || self.ns.type_locals.contains(&name) {
                Ok(mk_type_local(name))
            } else if self.ns.type_consts.contains(&name) {
                Ok(mk_type_const(name))
            } else if token.as_str() == "set" {
                let t = self.subty(1024)?;
                Ok(mk_type_arrow(t, mk_type_prop()))
            } else if token.as_str() == "ℕ" {
                Ok(mk_type_const(Name::intern("nat").unwrap()))
            } else {
                Self::fail(token, "unknown type variable")
            }
        } else if token.is_symbol() && token.as_str() == "(" {
            let t = self.ty()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else {
            Self::fail(token, "expected a primary type expression")
        }
    }

    pub fn ty(&mut self) -> Result<Type, ParseError> {
        self.subty(0)
    }

    fn subty(&mut self, rbp: usize) -> Result<Type, ParseError> {
        let mut t = self.type_primary()?;
        while let Some(token) = self.peek_opt() {
            if token.is_symbol() && token.as_str() == "→" {
                // type infixr → : 25
                if rbp >= 25 {
                    break;
                }
                self.advance();
                t = mk_type_arrow(t, self.subty(24)?);
            } else if token.is_symbol() && token.as_str() == "×" {
                // type infixr × : 35
                if rbp >= 35 {
                    break;
                }
                self.advance();
                let s = self.subty(34)?;
                let mut prod = mk_type_const(Name::intern("prod").unwrap());
                prod.apply([t, s]);
                t = prod;
            } else if token.is_ident()
                || (token.is_symbol() && token.as_str() == "(")
                || (token.is_symbol() && token.as_str() == "${")
            {
                if rbp >= 1024 {
                    break;
                }
                t.apply([self.subty(1024)?]);
            } else {
                break;
            }
        }
        Ok(t)
    }

    /// e.g. `"(x y : T)"`
    fn typed_parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError> {
        let mut idents = vec![];
        // needs at least one parameter
        idents.push(self.name()?);
        while let Some(name) = self.name_opt() {
            idents.push(name);
        }
        self.expect_symbol(":")?;
        let t = self.ty()?;
        self.expect_symbol(")")?;
        Ok((idents, t))
    }

    /// e.g. `"(x y : T) (z : U)"`
    fn typed_parameters(&mut self) -> Result<Vec<(Name, Type)>, ParseError> {
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (names, t) = self.typed_parameter(token)?;
            for name in names {
                params.push((name, t.clone()));
            }
        }
        Ok(params)
    }

    fn parameters(&mut self) -> Result<Vec<(Name, Option<Type>)>, ParseError> {
        let mut params = vec![];
        loop {
            if let Some(token) = self.expect_symbol_opt("(") {
                let (names, t) = self.typed_parameter(token)?;
                for name in names {
                    params.push((name, Some(t.clone())));
                }
            } else if let Some(name) = self.name_opt() {
                params.push((name, None));
            } else {
                break;
            }
        }
        Ok(params)
    }

    pub fn term(&mut self) -> Result<Term, ParseError> {
        self.subterm(0)
    }

    fn term_opt(&mut self) -> Option<Term> {
        self.optional(|this| this.term())
    }

    fn term_abs(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_hole(),
            };
            binders.push((name, ty));
        }
        for (name, _) in &binders {
            self.locals.push(*name);
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.abs(&[(name, name, t)], true);
        }
        Ok(m)
    }

    fn mk_const_unchecked(&self, name: &str) -> Term {
        let ty_arity = self
            .ns
            .consts
            .get(&name.try_into().unwrap())
            .copied()
            .unwrap_or_else(|| panic!("unknown constant: {name}"));
        let mut ty_args = vec![];
        for _ in 0..ty_arity {
            ty_args.push(mk_fresh_type_hole());
        }
        mk_const(Name::try_from(name).expect("invalid name"), ty_args)
    }

    fn term_binder(&mut self, token: Token<'a>, binder: &str) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_hole(),
            };
            binders.push((name, ty));
        }
        for (name, _) in &binders {
            self.locals.push(*name);
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.abs(&[(name, name, t.clone())], true);
            let f = mem::take(&mut m);
            m = mk_const(Name::try_from(binder).unwrap(), vec![t]);
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_sep(&mut self, _token: Token<'a>) -> Result<Term, ParseError> {
        let name = self.name()?;
        let t;
        if let Some(_token) = self.expect_symbol_opt(":") {
            t = self.ty()?;
        } else {
            t = mk_fresh_type_hole();
        }
        self.expect_symbol("|")?;
        self.locals.push(name);
        let mut m = self.subterm(0)?;
        self.locals.pop();
        m.abs(&[(name, name, t)], true);
        self.expect_symbol("}")?;
        Ok(m)
    }

    fn term_var(&mut self, token: Token<'a>, entity: Option<Name>) -> Result<Term, ParseError> {
        let name = match entity {
            None => Name::try_from(token.as_str()).expect("logic flaw"),
            Some(s) => s,
        };
        for x in self.locals.iter().rev() {
            if x == &name {
                return Ok(mk_local(name));
            }
        }
        for x in self.ns.locals.iter() {
            if x == &name {
                return Ok(mk_local(name));
            }
        }
        let Some(ty_arity) = self.ns.consts.get(&name).copied() else {
            return Self::fail(token, "unknown variable");
        };
        let mut ty_args = vec![];
        if let Some(_token) = self.expect_symbol_opt(".{") {
            if self.expect_symbol_opt("}").is_none() {
                loop {
                    ty_args.push(self.ty()?);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("}")?;
            }
        } else {
            for _ in 0..ty_arity {
                ty_args.push(mk_fresh_type_hole());
            }
        }
        Ok(mk_const(name, ty_args))
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError> {
        let token = self.any_token()?;
        // nud
        let nud = match self.tt.get_nud(&token) {
            None => todo!("nud unknown: {}", token),
            Some(nud) => nud,
        };
        let mut left = match nud {
            Nud::Var => self.term_var(token, None)?,
            Nud::Abs => self.term_abs(token)?,
            Nud::Paren => {
                let m = self.subterm(0)?;
                self.expect_symbol(")")?;
                m
            }
            Nud::Bracket => {
                let mut terms = vec![];
                while let Some(m) = self.term_opt() {
                    terms.push(m);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("⟩")?;
                // right associative encoding:
                // ⟨⟩ ⇒ star
                // ⟨m⟩ ⇒ m
                // ⟨m,n,l⟩ ⇒ ⟨m, ⟨n, l⟩⟩
                match terms.len() {
                    0 => self.mk_const_unchecked("star"),
                    1 => terms.pop().unwrap(),
                    _ => {
                        let mut m = terms.pop().unwrap();
                        for n in terms.into_iter().rev() {
                            let mut x = self.mk_const_unchecked("pair");
                            x.apply(vec![n, m]);
                            m = x;
                        }
                        m
                    }
                }
            }
            Nud::Forall => self.term_binder(token, "forall")?,
            Nud::Exists => self.term_binder(token, "exists")?,
            Nud::Uexists => self.term_binder(token, "uexists")?,
            Nud::User(op) => match op.fixity {
                Fixity::Nofix => self.term_var(token, Some(op.entity))?,
                Fixity::Prefix => {
                    let mut fun = self.term_var(token, Some(op.entity))?;
                    let arg = self.subterm(op.prec)?;
                    fun.apply(vec![arg]);
                    fun
                }
                Fixity::Infix | Fixity::Infixl | Fixity::Infixr => unreachable!(),
            },
            Nud::NumLit => Self::fail(token, "numeric literal is unsupported")?,
            Nud::Hole => self.mk_term_hole(),
            Nud::Brace => self.term_sep(token)?,
        };
        while let Some(token) = self.peek_opt() {
            let led = match self.tt.get_led(&token) {
                None => break,
                Some(led) => led,
            };
            let prec = led.prec();
            if rbp >= prec {
                break;
            }
            match led {
                Led::App => {
                    let right = self.subterm(led.prec())?;
                    left.apply(vec![right]);
                }
                Led::User(op) => {
                    let prec = match op.fixity {
                        Fixity::Infix | Fixity::Infixl => prec,
                        Fixity::Infixr => prec - 1,
                        Fixity::Nofix | Fixity::Prefix => unreachable!("op = {op:?}"),
                    };
                    self.advance();
                    let mut fun = self.term_var(token, Some(op.entity))?;
                    let right = self.subterm(prec)?;
                    fun.apply(vec![left, right]);
                    left = fun;
                }
            }
        }
        Ok(left)
    }

    // Returns (?M l₁ ⋯ lₙ) where ?M is fresh and l₁ ⋯ lₙ are the context in place.
    fn mk_term_hole(&mut self) -> Term {
        let mut hole = mk_fresh_hole();
        let Term::Hole(name) = &hole else {
            unreachable!()
        };
        self.holes.push((*name, mk_fresh_type_hole()));
        hole.apply(self.locals.iter().map(|name| mk_local(*name)));

        hole
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.subexpr(0)
    }

    fn expr_const(&mut self, token: Token<'a>, auto_inst: bool) -> Result<Expr, ParseError> {
        let name = Name::try_from(token.as_str()).unwrap();
        let Some(axiom_info) = self.ns.axioms.get(&name).cloned() else {
            return Self::fail(token, "unknown variable");
        };
        let mut ty_args = vec![];
        if let Some(_token) = self.expect_symbol_opt(".{") {
            if self.expect_symbol_opt("}").is_none() {
                loop {
                    ty_args.push(self.ty()?);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("}")?;
            }
        } else {
            for _ in 0..axiom_info.type_arity {
                ty_args.push(mk_fresh_type_hole());
            }
        }
        let mut expr = mk_expr_const(name, ty_args);
        if auto_inst {
            for _ in 0..axiom_info.num_params {
                expr = mk_expr_inst(expr, self.mk_term_hole(), self.mk_term_hole());
            }
        }
        Ok(expr)
    }

    fn subexpr(&mut self, rbp: usize) -> Result<Expr, ParseError> {
        // nud
        let mut left = 'left: {
            if let Some(_token) = self.expect_symbol_opt("(") {
                let e = self.subexpr(0)?;
                self.expect_symbol(")")?;
                break 'left e;
            }
            if let Some(_token) = self.expect_symbol_opt("⟪") {
                let prop = self.term()?;
                self.expect_symbol("⟫")?;
                break 'left mk_expr_assump(prop);
            }
            if let Some(_token) = self.expect_symbol_opt("@") {
                let token = self.ident()?;
                let expr = self.expr_const(token, false)?;
                break 'left expr;
            }
            let token = self.ident()?;
            match token.as_str() {
                "assume" => {
                    let m = self.term()?;
                    self.expect_symbol(",")?;
                    let e = self.expr()?;
                    mk_expr_assume(m, e)
                }
                "take" => {
                    self.expect_symbol("(")?;
                    let name = self.name()?;
                    self.expect_symbol(":")?;
                    let ty = self.ty()?;
                    self.expect_symbol(")")?;
                    self.expect_symbol(",")?;
                    self.locals.push(name);
                    let e = self.expr()?;
                    self.locals.pop();
                    mk_expr_take(name, ty, e)
                }
                "change" => {
                    let m = self.term()?;
                    self.expect_symbol(",")?;
                    let e = self.expr()?;
                    mk_expr_app(mk_expr_assume(m.clone(), mk_expr_assump(m.clone())), e, m)
                }
                "have" => {
                    let m = self.term()?;
                    self.expect_symbol(":=")?;
                    let e1 = self.expr()?;
                    self.expect_symbol(",")?;
                    let e2 = self.expr()?;
                    mk_expr_app(mk_expr_assume(m.clone(), e2), e1, self.mk_term_hole())
                }
                "obtain" => {
                    self.expect_symbol("(")?;
                    let name = self.name()?;
                    self.expect_symbol(":")?;
                    let ty = self.ty()?;
                    self.expect_symbol(")")?;
                    self.expect_symbol(",")?;
                    self.locals.push(name);
                    let p = self.term()?;
                    self.locals.pop();
                    self.expect_symbol(":=")?;
                    let e1 = self.expr()?;
                    self.expect_symbol(",")?;
                    self.locals.push(name);
                    let e2 = self.expr()?;
                    self.locals.pop();

                    // Expand[obtain (x : τ), p := e1, e2] := exists.ind.{τ}[_, _] e1 (take (x : τ), assume p, e2)
                    let e = mk_expr_const(Name::intern("exists.ind").unwrap(), vec![ty.clone()]);
                    let e = mk_expr_inst(e, self.mk_term_hole(), self.mk_term_hole());
                    let e = mk_expr_inst(e, self.mk_term_hole(), self.mk_term_hole());
                    let e = mk_expr_app(e, e1, self.mk_term_hole());
                    let e_body = mk_expr_assume(p, e2);
                    let e_body = mk_expr_take(name, ty, e_body);
                    mk_expr_app(e, e_body, self.mk_term_hole())
                }
                _ => self.expr_const(token, true)?,
            }
        };
        while let Some(token) = self.peek_opt() {
            enum ExprLed {
                App,
                Inst,
            }
            let (led, prec) = {
                if token.as_str() == "[" {
                    (ExprLed::Inst, 1025)
                } else if token.as_str() == "("
                    || token.as_str() == "⟪"
                    || token.as_str() == "@"
                    || token.is_ident()
                {
                    (ExprLed::App, 1024)
                } else {
                    break;
                }
            };
            if rbp >= prec {
                break;
            }
            match led {
                ExprLed::App => {
                    let right = self.subexpr(1024)?;
                    left = mk_expr_app(left, right, self.mk_term_hole());
                }
                ExprLed::Inst => {
                    self.advance();
                    let mut args = vec![];
                    while let Some(m) = self.term_opt() {
                        args.push(m);
                        if self.expect_symbol_opt(",").is_none() {
                            break;
                        }
                    }
                    self.expect_symbol("]")?;
                    let mut e = left;
                    for arg in args {
                        e = mk_expr_inst(e, arg, self.mk_term_hole());
                    }
                    left = e;
                }
            }
        }
        Ok(left)
    }

    // pub fn meta_expr(&mut self) -> Result<MetaExpr, ParseError> {
    //     self.meta_subexpr(0)
    // }

    // fn meta_subexpr(&mut self, rbp: usize) -> Result<MetaExpr, ParseError> {
    //     let token = self.any_token()?;
    //     let mut left = if token.is_ident() {
    //         MetaExpr::Var(Name::intern(token.as_str()).unwrap())
    //     } else if token.is_symbol() {
    //         match token.as_str() {
    //             "(" => {
    //                 let e = self.meta_subexpr(0)?;
    //                 self.expect_symbol(")")?;
    //                 e
    //             }
    //             "{" => self.meta_expr_block(token)?,
    //             "λ" => self.meta_expr_fun(token)?,
    //             _ => {}
    //         }
    //     } else {
    //         return Self::fail(token, "unexpected token")?;
    //     };
    //     while let Some(token) = self.peek_opt() {
    //         let led = match self.tt.get_led(&token) {
    //             None => break,
    //             Some(led) => led,
    //         };
    //         let prec = led.prec();
    //         if rbp >= prec {
    //             break;
    //         }
    //         match led {
    //             Led::App => {
    //                 let right = self.subterm(led.prec())?;
    //                 left.apply(vec![right]);
    //             }
    //             Led::User(op) => {
    //                 let prec = match op.fixity {
    //                     Fixity::Infix | Fixity::Infixl => prec,
    //                     Fixity::Infixr => prec - 1,
    //                     Fixity::Nofix | Fixity::Prefix => unreachable!("op = {op:?}"),
    //                 };
    //                 self.advance();
    //                 let mut fun = self.term_var(token, Some(op.entity))?;
    //                 let right = self.subterm(prec)?;
    //                 fun.apply(vec![left, right]);
    //                 left = fun;
    //             }
    //         }
    //     }
    //     Ok(left)
    // }

    fn local_type_binder(&mut self) -> Result<Vec<Name>, ParseError> {
        if let Some(_token) = self.expect_symbol_opt(".{") {
            let mut local_types = vec![];
            if self.expect_symbol_opt("}").is_none() {
                loop {
                    let token = self.ident()?;
                    let tv = Name::intern(token.as_str()).unwrap();
                    for v in &local_types {
                        if &tv == v {
                            return Self::fail(token, "duplicate type variable")?;
                        }
                    }
                    local_types.push(tv);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("}")?;
            }
            Ok(local_types)
        } else {
            Ok(vec![])
        }
    }

    pub fn cmd(&mut self) -> Result<Cmd, ParseError> {
        let keyword = self.keyword()?;
        let cmd = match keyword.as_str() {
            "infixr" => {
                let infixr_cmd = self.infixr_cmd(keyword)?;
                Cmd::Infixr(infixr_cmd)
            }
            "infixl" => {
                let infixl_cmd = self.infixl_cmd(keyword)?;
                Cmd::Infixl(infixl_cmd)
            }
            "infix" => {
                let infix_cmd = self.infix_cmd(keyword)?;
                Cmd::Infix(infix_cmd)
            }
            "prefix" => {
                let prefix_cmd = self.prefix_cmd(keyword)?;
                Cmd::Prefix(prefix_cmd)
            }
            "nofix" => {
                let nofix_cmd = self.nofix_cmd(keyword)?;
                Cmd::Nofix(nofix_cmd)
            }
            "def" => {
                let def_cmd = self.def_cmd(keyword)?;
                Cmd::Def(def_cmd)
            }
            "axiom" => {
                let axiom_cmd = self.axiom_cmd(keyword)?;
                Cmd::Axiom(axiom_cmd)
            }
            "lemma" => {
                let lemma_cmd = self.lemma_cmd(keyword)?;
                Cmd::Lemma(lemma_cmd)
            }
            "const" => {
                let const_cmd = self.const_cmd(keyword)?;
                Cmd::Const(const_cmd)
            }
            "type" => {
                let keyword2 = self.keyword()?;
                match keyword2.as_str() {
                    "const" => {
                        let type_const_cmd = self.type_const_cmd(keyword)?;
                        Cmd::TypeConst(type_const_cmd)
                    }
                    "variable" => {
                        let local_type_const_cmd = self.local_type_const_cmd(keyword)?;
                        Cmd::LocalTypeConst(local_type_const_cmd)
                    }
                    "inductive" => {
                        let type_inductive_cmd = self.type_inductive_cmd(keyword)?;
                        Cmd::TypeInductive(type_inductive_cmd)
                    }
                    _ => {
                        return Self::fail(keyword, "unknown command");
                    }
                }
            }
            "inductive" => {
                let inductive_cmd = self.inductive_cmd(keyword)?;
                Cmd::Inductive(inductive_cmd)
            }
            "structure" => {
                let structure_cmd = self.structure_cmd(keyword)?;
                Cmd::Structure(structure_cmd)
            }
            "instance" => {
                let instance_cmd = self.instance_cmd(keyword)?;
                Cmd::Instance(instance_cmd)
            }
            "local" => {
                let keyword2 = self.keyword()?;
                match keyword2.as_str() {
                    "type" => {
                        let keyword3 = self.keyword()?;
                        match keyword3.as_str() {
                            "const" => {
                                let local_type_const_cmd = self.local_type_const_cmd(keyword)?;
                                Cmd::LocalTypeConst(local_type_const_cmd)
                            }
                            _ => {
                                return Self::fail(keyword, "unknown command");
                            }
                        }
                    }
                    _ => {
                        return Self::fail(keyword, "unknown command");
                    }
                }
            }
            _ => {
                return Self::fail(keyword, "expected command");
            }
        };
        Ok(cmd)
    }

    fn infixr_cmd(&mut self, _token: Token) -> Result<CmdInfixr, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdInfixr {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn infixl_cmd(&mut self, _token: Token) -> Result<CmdInfixl, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdInfixl {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn infix_cmd(&mut self, _token: Token) -> Result<CmdInfix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdInfix {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn prefix_cmd(&mut self, _token: Token) -> Result<CmdPrefix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdPrefix {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn nofix_cmd(&mut self, _token: Token) -> Result<CmdNofix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":=")?;
        let entity = self.name()?;
        Ok(CmdNofix {
            op: op.as_str().to_owned(),
            entity,
        })
    }

    fn def_cmd(&mut self, _token: Token) -> Result<CmdDef, ParseError> {
        let name = self.name()?;
        let local_types = self.local_type_binder()?;
        for ty in &local_types {
            self.type_locals.push(*ty);
        }
        let params = self.typed_parameters()?;
        for (x, _) in &params {
            self.locals.push(*x);
        }
        self.expect_symbol(":")?;
        let mut t = self.ty()?;
        self.expect_symbol(":=")?;
        let mut m = self.term()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.type_locals
            .truncate(self.type_locals.len() - local_types.len());
        for (x, ty) in params.into_iter().rev() {
            t.arrow([ty.clone()]);
            m.abs(&[(x, x, ty)], true);
        }
        Ok(CmdDef {
            name,
            local_types,
            ty: t,
            target: m,
        })
    }

    fn axiom_cmd(&mut self, _token: Token) -> Result<CmdAxiom, ParseError> {
        let name = self.name()?;
        let local_types = self.local_type_binder()?;
        for ty in &local_types {
            self.type_locals.push(*ty);
        }
        let params = self.typed_parameters()?;
        for (x, _) in &params {
            self.locals.push(*x);
        }
        self.expect_symbol(":")?;
        let mut target = self.term()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.type_locals
            .truncate(self.type_locals.len() - local_types.len());
        for (x, ty) in params.into_iter().rev() {
            target.abs(&[(x, x, ty.clone())], true);
            target = mk_app(
                mk_const(Name::try_from("forall").unwrap(), vec![ty]),
                target,
            );
        }
        Ok(CmdAxiom {
            name,
            local_types,
            target,
        })
    }

    fn lemma_cmd(&mut self, _token: Token) -> Result<CmdLemma, ParseError> {
        let name = self.name()?;
        let local_types = self.local_type_binder()?;
        for ty in &local_types {
            self.type_locals.push(*ty);
        }
        let params = self.typed_parameters()?;
        for (x, _) in &params {
            self.locals.push(*x);
        }
        self.expect_symbol(":")?;
        let mut p = self.term()?;
        self.expect_symbol(":=")?;
        let mut e = self.expr()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.type_locals
            .truncate(self.type_locals.len() - local_types.len());
        for (x, ty) in params.into_iter().rev() {
            p.abs(&[(x, x, ty.clone())], true);
            p = mk_app(
                mk_const(Name::try_from("forall").unwrap(), vec![ty.clone()]),
                p,
            );
            e = mk_expr_take(x, ty, e);
        }
        let holes = self.holes.drain(..).collect();
        Ok(CmdLemma {
            name,
            local_types,
            target: p,
            holes,
            expr: e,
        })
    }

    fn const_cmd(&mut self, _token: Token) -> Result<CmdConst, ParseError> {
        let name = self.name()?;
        let local_types = self.local_type_binder()?;
        for ty in &local_types {
            self.type_locals.push(*ty);
        }
        self.expect_symbol(":")?;
        let t = self.ty()?;
        // Parsing finished.
        self.type_locals
            .truncate(self.type_locals.len() - local_types.len());
        Ok(CmdConst {
            name,
            local_types,
            ty: t,
        })
    }

    fn type_const_cmd(&mut self, _token: Token) -> Result<CmdTypeConst, ParseError> {
        let name = self.name()?;
        self.expect_symbol(":")?;
        let kind = self.kind()?;
        Ok(CmdTypeConst { name, kind })
    }

    fn local_type_const_cmd(&mut self, _token: Token) -> Result<CmdLocalTypeConst, ParseError> {
        let mut variables = vec![];
        while let Some(name) = self.name_opt() {
            variables.push(name);
        }
        Ok(CmdLocalTypeConst { variables })
    }

    fn type_inductive_cmd(&mut self, _token: Token<'a>) -> Result<CmdTypeInductive, ParseError> {
        let name = self.name()?;
        self.type_locals.push(name);

        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let tv = Name::intern(token.as_str()).unwrap();
            for v in &local_types {
                if &tv == v {
                    return Self::fail(token, "duplicate type variable")?;
                }
            }
            local_types.push(tv);
            self.type_locals.push(tv);
        }
        let mut ctors: Vec<DataConstructor> = vec![];
        while let Some(_token) = self.expect_symbol_opt("|") {
            let token = self.ident()?;
            let ctor_name = Name::intern(token.as_str()).unwrap();
            for ctor in &ctors {
                if ctor_name == ctor.name {
                    return Self::fail(token, "duplicate constructor")?;
                }
            }
            self.expect_symbol(":")?;
            let ty = self.ty()?;
            ctors.push(DataConstructor {
                name: ctor_name,
                ty,
            })
        }
        // Parsing finished. We can now safaly tear off.
        self.type_locals
            .truncate(self.type_locals.len() - local_types.len());
        self.type_locals.pop();
        Ok(CmdTypeInductive {
            name,
            local_types,
            ctors,
        })
    }

    fn inductive_cmd(&mut self, _token: Token<'a>) -> Result<CmdInductive, ParseError> {
        let name = self.name()?;
        self.locals.push(name);
        let local_types = self.local_type_binder()?;
        for ty in &local_types {
            self.type_locals.push(*ty);
        }
        let params = self.typed_parameters()?;
        for (x, _) in &params {
            self.locals.push(*x);
        }
        self.expect_symbol(":")?;
        let target_ty = self.ty()?;
        let mut ctors: Vec<Constructor> = vec![];
        while let Some(_token) = self.expect_symbol_opt("|") {
            let token = self.ident()?;
            let ctor_name = Name::intern(token.as_str()).unwrap();
            for ctor in &ctors {
                if ctor_name == ctor.name {
                    return Self::fail(token, "duplicate constructor")?;
                }
            }
            let ctor_params = self.typed_parameters()?;
            for (x, _) in &ctor_params {
                self.locals.push(*x);
            }
            self.expect_symbol(":")?;
            let mut target = self.term()?;
            self.locals.truncate(self.locals.len() - ctor_params.len());
            for (x, ty) in ctor_params.into_iter().rev() {
                target.abs(&[(x, x, ty.clone())], true);
                target = mk_app(
                    mk_const(Name::try_from("forall").unwrap(), vec![ty]),
                    target,
                );
            }
            ctors.push(Constructor {
                name: ctor_name,
                target,
            })
        }
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.locals.pop();
        self.type_locals
            .truncate(self.type_locals.len() - local_types.len());
        Ok(CmdInductive {
            name,
            local_types,
            ctors,
            params,
            target_ty,
        })
    }

    fn structure_cmd(&mut self, _token: Token<'a>) -> Result<CmdStructure, ParseError> {
        let name = self.name()?;
        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let tv = Name::intern(token.as_str()).unwrap();
            for v in &local_types {
                if &tv == v {
                    return Self::fail(token, "duplicate type variable")?;
                }
            }
            local_types.push(tv);
            self.type_locals.push(tv);
        }
        self.expect_symbol(":=")?;
        self.expect_symbol("{")?;
        let mut fields: Vec<StructureField> = vec![];
        let mut num_consts = 0;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "const" => {
                    let field_name = self.name()?;
                    self.expect_symbol(":")?;
                    let field_ty = self.ty()?;
                    fields.push(StructureField::Const(StructureConst {
                        name: field_name,
                        ty: field_ty,
                    }));

                    self.locals.push(field_name);
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    let params = self.typed_parameters()?;
                    for (x, _) in &params {
                        self.locals.push(*x);
                    }
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(self.locals.len() - params.len());
                    for (x, ty) in params.into_iter().rev() {
                        target.abs(&[(x, x, ty.clone())], true);
                        target = mk_app(
                            mk_const(Name::try_from("forall").unwrap(), vec![ty]),
                            target,
                        );
                    }
                    fields.push(StructureField::Axiom(StructureAxiom {
                        name: field_name,
                        target,
                    }))
                }
                _ => {
                    return Self::fail(keyword, "expected const or axiom");
                }
            }
        }
        self.locals.truncate(self.locals.len() - num_consts);
        self.type_locals
            .truncate(self.type_locals.len() - local_types.len());
        Ok(CmdStructure {
            name,
            local_types,
            fields,
        })
    }

    fn instance_cmd(&mut self, _token: Token<'a>) -> Result<CmdInstance, ParseError> {
        let name = self.name()?;
        let local_types = self.local_type_binder()?;
        for ty in &local_types {
            self.type_locals.push(*ty);
        }
        let params = self.typed_parameters()?;
        for (x, _) in &params {
            self.locals.push(*x);
        }
        self.expect_symbol(":")?;
        let target_ty = self.ty()?;
        let mut fields = vec![];
        self.expect_symbol(":=")?;
        self.expect_symbol("{")?;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "def" => {
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    for (x, _) in &field_params {
                        self.locals.push(*x);
                    }
                    self.expect_symbol(":")?;
                    let mut field_ty = self.ty()?;
                    self.expect_symbol(":=")?;
                    let mut field_target = self.term()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    for (x, t) in field_params.into_iter().rev() {
                        field_ty.arrow([t.clone()]);
                        field_target.abs(&[(x, x, t.clone())], true);
                    }
                    fields.push(InstanceField::Def(InstanceDef {
                        name: field_name,
                        ty: field_ty,
                        target: field_target,
                    }));
                }
                "lemma" => {
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    for (x, _) in &field_params {
                        self.locals.push(*x);
                    }
                    self.expect_symbol(":")?;
                    let mut field_target = self.term()?;
                    self.expect_symbol(":=")?;
                    let mut expr = self.expr()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    for (x, ty) in field_params.into_iter().rev() {
                        field_target.abs(&[(x, x, ty.clone())], true);
                        field_target = mk_app(
                            mk_const(Name::try_from("forall").unwrap(), vec![ty.clone()]),
                            field_target,
                        );
                        expr = mk_expr_take(x, ty, expr);
                    }
                    let holes = self.holes.drain(..).collect();
                    fields.push(InstanceField::Lemma(InstanceLemma {
                        name: field_name,
                        target: field_target,
                        holes,
                        expr,
                    }))
                }
                _ => Self::fail(keyword, "unknown command in instance")?,
            }
        }
        // parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.type_locals
            .truncate(self.type_locals.len() - local_types.len());
        Ok(CmdInstance {
            name,
            local_types,
            params,
            target_ty,
            fields,
        })
    }
}

#[test]
fn parse_term() {
    let mut tt = TokenTable::default();

    let ops = [
        Operator {
            symbol: "=".to_owned(),
            fixity: Fixity::Infix,
            prec: 50,
            entity: "eq".try_into().unwrap(),
        },
        Operator {
            symbol: "⊤".to_owned(),
            fixity: Fixity::Nofix,
            prec: usize::MAX,
            entity: "top".try_into().unwrap(),
        },
        Operator {
            symbol: "∧".to_owned(),
            fixity: Fixity::Infixr,
            prec: 35,
            entity: "and".try_into().unwrap(),
        },
        Operator {
            symbol: "¬".to_owned(),
            fixity: Fixity::Prefix,
            prec: 40,
            entity: "not".try_into().unwrap(),
        },
    ];
    for op in ops {
        tt.add(op).unwrap();
    }

    let mut ns = Nasmespace::default();
    ns.type_consts.insert("Prop".try_into().unwrap());
    ns.consts.insert("eq".try_into().unwrap(), 1);
    ns.consts.insert("top".try_into().unwrap(), 0);
    ns.consts.insert("and".try_into().unwrap(), 0);
    ns.consts.insert("not".try_into().unwrap(), 0);
    ns.type_locals.push("α".try_into().unwrap());
    ns.type_locals.push("u".try_into().unwrap());
    ns.type_locals.push("v".try_into().unwrap());

    let parse = |input: &str| -> Term {
        let mut lex = Lex::new(input);
        let mut parser = Parser::new(&mut lex, &tt, &ns, vec![]);
        let m = parser.term().unwrap();
        parser.eof().unwrap();
        m
    };

    insta::assert_snapshot!(parse("λ (x : α), x"), @"(lam (local α) (var 0))");
    insta::assert_snapshot!(parse("λ (p q r : Prop), p q r"), @"(lam Prop (lam Prop (lam Prop (((var 2) (var 1)) (var 0)))))");
    insta::assert_snapshot!(parse("λ (φ ψ : Prop), eq.{α} (λ (f : Prop → Prop → Prop), f φ ψ) (λ (f : Prop → Prop → Prop), f ⊤ ⊤)"), @"(lam Prop (lam Prop ((eq.{(local α)} (lam (Prop → (Prop → Prop)) (((var 0) (var 2)) (var 1)))) (lam (Prop → (Prop → Prop)) (((var 0) top) top)))))");
    insta::assert_snapshot!(parse("λ (p q : Prop), p =.{Prop} (p ∧ q)"), @"(lam Prop (lam Prop ((eq.{Prop} (var 1)) ((and (var 1)) (var 0)))))");
    insta::assert_snapshot!(parse("λ (a b : Prop), (¬a) =.{Prop} b"), @"(lam Prop (lam Prop ((eq.{Prop} (not (var 1))) (var 0))))");
    insta::assert_snapshot!(parse("λ (a b : Prop), ¬a =.{Prop} b"), @"(lam Prop (lam Prop (not ((eq.{Prop} (var 1)) (var 0)))))");
    insta::assert_snapshot!(parse("λ (x : α), eq.{u → v} x"), @"(lam (local α) (eq.{((local u) → (local v))} (var 0)))");
}
