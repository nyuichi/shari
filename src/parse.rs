use crate::cmd::{
    mk_expr_fun, Cmd, CmdAxiom, CmdDef, CmdInfix, CmdInfixl, CmdInfixr, CmdMetaDef, CmdNofix,
    CmdPrefix, Expr, Fixity, MetaExpr, Operator,
};
use crate::kernel::proof::Prop;
use crate::kernel::tt::{
    mk_app, mk_const, mk_fresh_type_mvar, mk_local, mk_type_arrow, mk_type_const, mk_type_local,
    Name, Term, Type,
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
                    "${" => Some(Nud::Hole),
                    _ => self.nud.get(token.as_str()).map(|op| Nud::User(op.clone())),
                }
            }
            TokenKind::NumLit => Some(Nud::NumLit),
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
pub struct Context {
    pub type_consts: HashSet<Name>,
    // mapping name to type arity
    pub consts: HashMap<Name, usize>,
}

pub struct Parser<'a, 'b> {
    lex: &'b mut Lex<'a>,
    tt: &'b TokenTable,
    ctx: &'b Context,
    locals: Vec<Name>,
    pub holes: Vec<Name>,
    pub type_holes: Vec<Name>,
}

impl<'a, 'b> Parser<'a, 'b> {
    pub fn new(lex: &'b mut Lex<'a>, tt: &'b TokenTable, ctx: &'b Context) -> Self {
        Self {
            lex,
            tt,
            ctx,
            locals: vec![],
            holes: vec![],
            type_holes: vec![],
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

    fn name(&mut self) -> Result<Name, ParseError> {
        Ok(Name::try_from(self.ident()?.as_str()).expect("logic flaw"))
    }

    fn name_opt(&mut self) -> Option<Name> {
        self.ident_opt()
            .map(|token| Name::try_from(token.as_str()).expect("logic flaw"))
    }

    fn type_hole(&mut self, token: Token<'a>) -> Result<Type, ParseError> {
        self.expect_symbol("}")?;
        let name = Name::fresh();
        self.type_holes.push(name);
        Ok(mk_type_local(name))
    }

    fn type_primary(&mut self) -> Result<Type, ParseError> {
        let token = self.any_token()?;
        if token.is_ident() {
            let name: Name = token.as_str().try_into().expect("logic flaw");
            match self.ctx.type_consts.get(&name) {
                Some(_) => Ok(mk_type_const(name)),
                None => Ok(mk_type_local(name)),
            }
        } else if token.is_symbol() && token.as_str() == "(" {
            let t = self.ty()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else if token.is_symbol() && token.as_str() == "${" {
            self.type_hole(token)
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
                if rbp >= 25 {
                    break;
                }
                self.advance();
                t = mk_type_arrow(t, self.subty(24)?);
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

    /// typed parameters e.g. `"(x y : T)"`
    fn parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError> {
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

    fn parameters(&mut self) -> Result<Vec<(Name, Option<Type>)>, ParseError> {
        let mut params = vec![];
        loop {
            if let Some(token) = self.expect_symbol_opt("(") {
                let (names, t) = self.parameter(token)?;
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
                None => mk_fresh_type_mvar(),
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
            m.abs(name, t, name);
        }
        Ok(m)
    }

    fn mk_const_unchecked(&self, name: &str) -> Term {
        let ty_arity = self
            .ctx
            .consts
            .get(&name.try_into().unwrap())
            .copied()
            .unwrap_or_else(|| panic!("unknown constant: {name}"));
        let mut ty_args = vec![];
        for _ in 0..ty_arity {
            ty_args.push(mk_fresh_type_mvar());
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
                None => mk_fresh_type_mvar(),
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
            m.abs(name, t, name);
            let f = mem::take(&mut m);
            m = self.mk_const_unchecked(binder);
            m.apply(vec![f]);
        }
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
        let Some(ty_arity) = self.ctx.consts.get(&name).copied() else {
            return Ok(mk_local(name));
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
                ty_args.push(mk_fresh_type_mvar());
            }
        }
        Ok(mk_const(name, ty_args))
    }

    fn term_hole(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        self.expect_symbol("}")?;
        let name = Name::fresh();
        self.holes.push(name);
        Ok(mk_local(name))
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
            Nud::Hole => self.term_hole(token)?,
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

    fn prop(&mut self) -> Result<Prop, ParseError> {
        Ok(Prop {
            target: self.term()?,
        })
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.subexpr(0)
    }

    fn expr_opt(&mut self) -> Option<Expr> {
        self.optional(|this| this.expr())
    }

    fn expr_abs(&mut self, token: Token<'a>) -> Result<Expr, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut e = self.subexpr(0)?;
        for (name, t) in params.into_iter().rev() {
            e = mk_expr_fun(name, t, e);
        }
        Ok(e)
    }

    fn expr_var(&mut self, token: Token<'a>) -> Result<Expr, ParseError> {
        Ok(Expr::Var(Name::intern(token.as_str()).unwrap()))
    }

    fn expr_unq(&mut self, token: Token<'a>) -> Result<MetaExpr, ParseError> {
        let expr = self.meta_expr()?;
        self.expect_symbol("}")?;
        Ok(expr)
    }

    fn subexpr(&mut self, rbp: usize) -> Result<Term, ParseError> {
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
                let m = self.subexpr(0)?;
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
            Nud::Hole => self.term_hole(token)?,
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

    pub fn meta_expr(&mut self) -> Result<MetaExpr, ParseError> {
        self.meta_subexpr(0)
    }

    fn meta_subexpr(&mut self, rbp: usize) -> Result<MetaExpr, ParseError> {
        let token = self.any_token()?;
        let mut left = if token.is_ident() {
            MetaExpr::Var(Name::intern(token.as_str()).unwrap())
        } else if token.is_symbol() {
            match token.as_str() {
                "(" => {
                    let e = self.meta_subexpr(0)?;
                    self.expect_symbol(")")?;
                    e
                }
                "{" => self.meta_expr_block(token)?,
                "λ" => self.meta_expr_fun(token)?,
                _ => {}
            }
        } else {
            return Self::fail(token, "unexpected token")?;
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

    pub fn cmd(&mut self) -> Result<Cmd, ParseError> {
        let keyword = self.ident()?;
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
            "meta" => {
                let keyword = self.ident()?;
                let cmd = match keyword.as_str() {
                    "def" => {
                        let meta_def_cmd = self.meta_def_cmd(keyword)?;
                        Cmd::MetaDef(meta_def_cmd)
                    }
                    _ => {
                        return Self::fail(keyword, "expected meta command");
                    }
                };
                cmd
            }
            // "lemma" => {
            //     let lemma_cmd = self.lemma_cmd(keyword)?;
            //     Cmd::Lemma(lemma_cmd)
            // }
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
        let mut local_types = vec![];
        if let Some(_token) = self.expect_symbol_opt(".{") {
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
        }
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (names, t) = self.parameter(token)?;
            for name in names {
                params.push((name, t.clone()));
            }
        }
        self.expect_symbol(":")?;
        let mut t = self.ty()?;
        self.expect_symbol(":=")?;
        let mut m = self.term()?;
        for (var, ty) in params.into_iter().rev() {
            m.abs(var, ty.clone(), var);
            t = mk_type_arrow(ty, t);
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
        let mut local_types = vec![];
        if let Some(_token) = self.expect_symbol_opt(".{") {
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
        }
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (names, t) = self.parameter(token)?;
            for name in names {
                params.push((name, t.clone()));
            }
        }
        self.expect_symbol(":")?;
        let mut m = self.term()?;
        for (var, ty) in params.into_iter().rev() {
            m.abs(var, ty.clone(), var);
            m = mk_app(self.mk_const_unchecked("forall"), m);
        }
        Ok(CmdAxiom {
            name,
            local_types,
            target: Prop { target: m },
        })
    }

    // fn lemma_cmd(&mut self, _token: Token) -> Result<CmdLemma, ParseError> {
    //     let name = self.name()?;
    //     let mut local_types = vec![];
    //     if let Some(_token) = self.expect_symbol_opt(".{") {
    //         if self.expect_symbol_opt("}").is_none() {
    //             loop {
    //                 let token = self.ident()?;
    //                 let tv = Name::intern(token.as_str()).unwrap();
    //                 for v in &local_types {
    //                     if &tv == v {
    //                         return Self::fail(token, "duplicate type variable")?;
    //                     }
    //                 }
    //                 local_types.push(tv);
    //                 if self.expect_symbol_opt(",").is_none() {
    //                     break;
    //                 }
    //             }
    //             self.expect_symbol("}")?;
    //         }
    //     }
    //     let mut params = vec![];
    //     while let Some(token) = self.expect_symbol_opt("(") {
    //         let (names, t) = self.parameter(token)?;
    //         for name in names {
    //             params.push((name, t.clone()));
    //         }
    //     }
    //     self.expect_symbol(":")?;
    //     let mut m = self.term()?;
    //     self.expect_symbol(":=")?;
    //     let mut proof = self.proof()?;
    //     for (var, ty) in params.into_iter().rev() {
    //         m.abs(var, ty.clone(), var);
    //         m = mk_app(self.mk_const_unchecked("forall"), m);
    //         proof = mk_proof_forall_intro(var, ty, proof);
    //     }
    //     let target = Prop { target: m };
    //     Ok(CmdLemma {
    //         name,
    //         local_types,
    //         target,
    //         proof,
    //     })
    // }

    fn meta_def_cmd(&mut self, _token: Token) -> Result<CmdMetaDef, ParseError> {
        let name = self.name()?;
        self.expect_symbol(":=")?;
        let meta_expr = self.meta_expr()?;
        Ok(CmdMetaDef { name, meta_expr })
    }
}

// #[test]
// fn test_parse() {
//     use crate::env::{DeclConst, TermDecl};
//     use crate::kernel::proof::mk_type_prop;

//     let ops = [
//         Operator {
//             symbol: "⊤".to_owned(),
//             fixity: Fixity::Nofix,
//             prec: usize::MAX,
//             entity: "top".try_into().unwrap(),
//         },
//         Operator {
//             symbol: "∧".to_owned(),
//             fixity: Fixity::Infixr,
//             prec: 35,
//             entity: "and".try_into().unwrap(),
//         },
//         Operator {
//             symbol: "¬".to_owned(),
//             fixity: Fixity::Prefix,
//             prec: 40,
//             entity: "not".try_into().unwrap(),
//         },
//     ];

//     let mut env = Env::new_kernel();
//     for op in ops {
//         env.add_notation(op).unwrap();
//     }

//     env.add_term_decl(
//         "top".try_into().unwrap(),
//         TermDecl::Const(DeclConst {
//             local_types: vec![],
//             ty: mk_type_prop(),
//         }),
//     )
//     .unwrap();

//     env.add_term_decl(
//         "not".try_into().unwrap(),
//         TermDecl::Const(DeclConst {
//             local_types: vec![],
//             ty: mk_type_arrow(mk_type_prop(), mk_type_prop()),
//         }),
//     )
//     .unwrap();

//     env.add_term_decl(
//         "and".try_into().unwrap(),
//         TermDecl::Const(DeclConst {
//             local_types: vec![],
//             ty: mk_type_arrow(
//                 mk_type_prop(),
//                 mk_type_arrow(mk_type_prop(), mk_type_prop()),
//             ),
//         }),
//     )
//     .unwrap();

//     struct Display<'a> {
//         env: &'a Env,
//         m: Term,
//     }

//     impl<'a> std::fmt::Display for Display<'a> {
//         fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//             Printer::new(self.env).fmt_term(&self.m, f)
//         }
//     }

//     let roundtrip = |s: &str| -> String {
//         let mut lex = Lex::new(s);
//         let mut parser = Parser::new(&mut lex, &env, false);
//         let m = parser.term().unwrap();
//         parser.eof().unwrap();
//         Display { env: &env, m }.to_string()
//     };

//     insta::assert_snapshot!(roundtrip("λ (x : α), x"), @"λ (x : α), x");
//     insta::assert_snapshot!(roundtrip("λ (p q r : Prop), p q r"), @"λ (p : Prop), λ (q : Prop), λ (r : Prop), p q r");
//     insta::assert_snapshot!(roundtrip("λ (φ ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = (λ (f : Prop → Prop → Prop), f ⊤ ⊤)"), @"λ (φ : Prop), λ (ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = λ (f : Prop → Prop → Prop), f ⊤ ⊤");
//     insta::assert_snapshot!(roundtrip("λ (p q : Prop), p = (p ∧ q)"), @"λ (p : Prop), λ (q : Prop), p = (p ∧ q)");
//     insta::assert_snapshot!(roundtrip("λ (a b : Prop), (¬a) = b"), @"λ (a : Prop), λ (b : Prop), (¬a) = b");
//     insta::assert_snapshot!(roundtrip("λ (a b : Prop), ¬a = b"), @"λ (a : Prop), λ (b : Prop), ¬a = b");
//     insta::assert_snapshot!(roundtrip("λ (x : w), eq.{u → v} x"), @"λ (x : w), eq.{u → v} x");
// }

// impl FromStr for Type {
//     type Err = ParseError;

//     fn from_str(s: &str) -> Result<Self, Self::Err> {
//         let mut lex = Lex::new(s);
//         let env = Env::get();
//         let mut parser = Parser::new(&mut lex, &env, false);
//         let ty = parser.ty()?;
//         parser.eof()?;
//         Ok(ty)
//     }
// }

// impl FromStr for Term {
//     type Err = ParseError;

//     fn from_str(s: &str) -> Result<Self, Self::Err> {
//         let mut lex = Lex::new(s);
//         let env = Env::get();
//         let mut parser = Parser::new(&mut lex, &env, false);
//         let m = parser.term()?;
//         parser.eof()?;
//         Ok(m)
//     }
// }
