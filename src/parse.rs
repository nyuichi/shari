use crate::cmd::{
    ClassInstanceDef, ClassInstanceField, ClassInstanceLemma, ClassStructureAxiom,
    ClassStructureConst, ClassStructureField, Cmd, CmdAxiom, CmdClassInstance, CmdClassStructure,
    CmdConst, CmdDef, CmdInductive, CmdInfix, CmdInfixl, CmdInfixr, CmdInstance, CmdLemma,
    CmdNofix, CmdPrefix, CmdStructure, CmdTypeConst, CmdTypeInductive, Constructor,
    DataConstructor, Fixity, InstanceDef, InstanceField, InstanceLemma, Operator, StructureAxiom,
    StructureConst, StructureField,
};
use crate::proof::{
    Axiom, Expr, count_forall, generalize, mk_expr_app, mk_expr_assume, mk_expr_assump,
    mk_expr_assump_by_name, mk_expr_change, mk_expr_const, mk_expr_inst, mk_expr_take,
    mk_type_prop,
};
use crate::tt::{
    Class, ClassType, Const, Id, Kind, Local, Name, QualifiedName, Term, Type, mk_const,
    mk_fresh_hole, mk_fresh_type_hole, mk_instance_hole, mk_local, mk_type_arrow, mk_type_const,
    mk_type_local,
};

use crate::lex::{Lex, LexError, LexState, Span, Token, TokenKind};
use anyhow::bail;
use std::collections::HashMap;
use std::sync::{Arc, LazyLock};
use std::{mem, slice};
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
    Proj(Proj),
}

impl Led {
    fn prec(&self) -> usize {
        match self {
            Self::App => 1024,
            Self::User(op) => op.prec,
            Self::Proj(_) => 1025,
        }
    }
}

#[derive(Clone, Copy)]
enum Proj {
    Fst,
    Snd,
}

impl Proj {
    fn name(self) -> QualifiedName {
        static FST: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("fst"));
        static SND: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("snd"));

        match self {
            Self::Fst => FST.clone(),
            Self::Snd => SND.clone(),
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
    Hole,
    Brace,
    Pair,
    User(Operator),
    NumLit,
}

impl TokenTable {
    fn get_led(&self, token: &Token) -> Option<Led> {
        match token.kind {
            TokenKind::Ident => Some(Led::App),
            TokenKind::Field => None,
            TokenKind::Symbol => {
                let lit = token.as_str();
                match self.led.get(lit) {
                    Some(op) => Some(Led::User(op.clone())),
                    None => {
                        if lit == ".0" {
                            Some(Led::Proj(Proj::Fst))
                        } else if lit == ".1" {
                            Some(Led::Proj(Proj::Snd))
                        } else if self.get_nud(token).is_some() {
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
            TokenKind::Field => None,
            TokenKind::Symbol => {
                let lit = token.as_str();
                match lit {
                    "(" => Some(Nud::Paren),
                    "λ" => Some(Nud::Abs),
                    "∀" => Some(Nud::Forall),
                    "∃" => Some(Nud::Exists),
                    "∃!" => Some(Nud::Uexists),
                    "_" => Some(Nud::Hole),
                    "{" => Some(Nud::Brace),
                    "⟨" => Some(Nud::Pair),
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
    #[error("parse error: {message} at {span}")]
    Parse { message: String, span: Span },
    #[error("unexpected end of input at {span}")]
    Eof { span: Span },
}

// TODO: instance lemma の中で hole を作ると引数にそれまでの instance def が入っちゃって後々 elab で const に置き換えられるので無駄。あと instance 自体の引数が2回ぐらい hole の引数に入ってしまうバグがありそう。
pub struct Parser<'a> {
    lex: &'a mut Lex,
    tt: &'a TokenTable,
    type_const_table: &'a HashMap<QualifiedName, Kind>,
    const_table: &'a HashMap<QualifiedName, Const>,
    axiom_table: &'a HashMap<QualifiedName, Axiom>,
    class_predicate_table: &'a HashMap<QualifiedName, ClassType>,
    local_types: Vec<Name>,
    // TODO: Vec<Name>にする
    locals: Vec<Id>,
    local_axioms: Vec<Name>,
    self_ref: Option<(QualifiedName, Id)>,
    type_self_ref: Option<(QualifiedName, Id)>,
    holes: Vec<(Id, Type)>,
}

impl<'a> Parser<'a> {
    pub fn new(
        lex: &'a mut Lex,
        tt: &'a TokenTable,
        type_const_table: &'a HashMap<QualifiedName, Kind>,
        const_table: &'a HashMap<QualifiedName, Const>,
        axiom_table: &'a HashMap<QualifiedName, Axiom>,
        class_predicate_table: &'a HashMap<QualifiedName, ClassType>,
    ) -> Self {
        Self {
            lex,
            tt,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
            local_types: vec![],
            locals: vec![],
            local_axioms: vec![],
            self_ref: None,
            type_self_ref: None,
            holes: vec![],
        }
    }

    fn span_since(&self, start: LexState) -> Span {
        self.lex.span_since(start)
    }

    fn term_with_span(&mut self, start: LexState, term: Term) -> Term {
        term.with_span(Some(self.span_since(start)))
    }

    fn type_with_span(&mut self, start: LexState, ty: Type) -> Type {
        ty.with_span(Some(self.span_since(start)))
    }

    fn expr_with_span(&mut self, start: LexState, expr: Expr) -> Expr {
        expr.with_span(Some(self.span_since(start)))
    }

    fn fail<R>(token: Token, message: impl Into<String>) -> Result<R, ParseError> {
        Err(ParseError::Parse {
            message: message.into(),
            span: token.span,
        })
    }

    fn eof_error(&self) -> ParseError {
        ParseError::Eof {
            span: Span::eof(Arc::clone(self.lex.input())),
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

    fn peek_opt(&mut self) -> Option<Token> {
        self.optional(|this| this.peek())
    }

    fn peek(&mut self) -> Result<Token, ParseError> {
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

    fn any_token(&mut self) -> Result<Token, ParseError> {
        self.lex
            .next()
            .transpose()
            .expect("lex error")
            .ok_or_else(|| self.eof_error())
    }

    fn ident(&mut self) -> Result<Token, ParseError> {
        let token = self.any_token()?;
        if !token.is_ident() {
            return Self::fail(token, "expected identifier");
        }
        Ok(token)
    }

    fn ident_opt(&mut self) -> Option<Token> {
        if let Some(token) = self.peek_opt()
            && token.is_ident()
        {
            self.advance();
            return Some(token);
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

    fn symbol(&mut self) -> Result<Token, ParseError> {
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

    fn expect_symbol_opt(&mut self, sym: &str) -> Option<Token> {
        if let Some(token) = self.peek_opt()
            && token.kind == TokenKind::Symbol
            && token.as_str() == sym
        {
            self.advance();
            return Some(token);
        }
        None
    }

    fn num_lit(&mut self) -> Result<Token, ParseError> {
        let token = self.any_token()?;
        if !token.is_num_lit() {
            return Self::fail(token, "expected numeral literal");
        }
        Ok(token)
    }

    fn keyword(&mut self) -> Result<Token, ParseError> {
        let token = self.any_token()?;
        if !token.is_keyword() {
            return Self::fail(token, "expected keyword");
        }
        Ok(token)
    }

    fn name(&mut self) -> Result<Name, ParseError> {
        Ok(Name::from_str(self.ident()?.as_str()))
    }

    fn name_opt(&mut self) -> Option<Name> {
        self.ident_opt().map(|token| Name::from_str(token.as_str()))
    }

    fn qualified_name(&mut self, token: &Token) -> QualifiedName {
        let mut name = QualifiedName::from_str(token.as_str());
        while let Some(field) = self.peek_opt() {
            if field.kind != TokenKind::Field {
                break;
            }
            let field = self
                .any_token()
                .expect("peeked field token should be available");
            let suffix = field
                .as_str()
                .strip_prefix('.')
                .expect("field token must start with '.'");
            name = name.extend(suffix);
        }
        name
    }

    fn alias_opt(&mut self) -> Result<Option<Name>, ParseError> {
        if let Some(token) = self.peek_opt()
            && token.kind == TokenKind::Keyword
            && token.as_str() == "as"
        {
            self.advance();
            let name = self.name()?;
            return Ok(Some(name));
        }
        Ok(None)
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
        static SUB_NAME: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("sub"));
        static NAT_NAME: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("ℕ"));

        let token = self.any_token()?;
        if token.is_ident() {
            let name = self.qualified_name(&token);
            if name.prefix().is_none() && self.local_types.iter().any(|x| x == &name.name()) {
                Ok(mk_type_local(Id::from_name(name.name())))
            } else if let Some(stash) =
                self.type_self_ref.as_ref().and_then(|(self_name, stash)| {
                    if self_name == &name {
                        Some(stash)
                    } else {
                        None
                    }
                })
            {
                Ok(mk_type_local(stash.clone()))
            } else if self.type_const_table.contains_key(&name) {
                Ok(mk_type_const(name))
            } else if name == *SUB_NAME {
                let t = self.subty(1024)?;
                Ok(mk_type_arrow(t, mk_type_prop()))
            } else if name == *NAT_NAME {
                Ok(mk_type_const(QualifiedName::from_str("nat")))
            } else {
                Self::fail(token, "unknown type constant")
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
        let start = self.lex.save();
        let mut t = self.type_primary()?;
        t = self.type_with_span(start, t);
        while let Some(token) = self.peek_opt() {
            if token.is_symbol() && token.as_str() == "→" {
                // type infixr → : 25
                if rbp >= 25 {
                    break;
                }
                self.advance();
                let rhs = self.subty(24)?;
                t = mk_type_arrow(t, rhs);
                t = self.type_with_span(start, t);
            } else if token.is_symbol() && token.as_str() == "×" {
                // type infixr × : 35
                if rbp >= 35 {
                    break;
                }
                self.advance();
                let s = self.subty(34)?;
                t = mk_type_const(QualifiedName::from_str("prod")).apply([t, s]);
                t = self.type_with_span(start, t);
            } else if token.is_ident()
                || (token.is_symbol() && token.as_str() == "(")
                || (token.is_symbol() && token.as_str() == "${")
            {
                if rbp >= 1024 {
                    break;
                }
                let arg = self.subty(1024)?;
                t = t.apply([arg]);
                t = self.type_with_span(start, t);
            } else {
                break;
            }
        }
        Ok(t)
    }

    /// e.g. `"(x y : T)"`
    fn typed_parameter(&mut self, _token: Token) -> Result<(Vec<Id>, Type), ParseError> {
        let mut idents = vec![];
        // needs at least one parameter
        idents.push(Id::from_name(self.name()?));
        while let Some(name) = self.name_opt() {
            idents.push(Id::from_name(name));
        }
        self.expect_symbol(":")?;
        let t = self.ty()?;
        self.expect_symbol(")")?;
        Ok((idents, t))
    }

    /// e.g. `"(x y : T) (z : U)"`
    fn typed_parameters(&mut self) -> Result<Vec<Local>, ParseError> {
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (ids, ty) = self.typed_parameter(token)?;
            for id in ids {
                params.push(Local { id, ty: ty.clone() });
            }
        }
        Ok(params)
    }

    fn parameters(&mut self) -> Result<Vec<(Id, Option<Type>)>, ParseError> {
        let mut params = vec![];
        loop {
            if let Some(token) = self.expect_symbol_opt("(") {
                let (ids, t) = self.typed_parameter(token)?;
                for id in ids {
                    params.push((id, Some(t.clone())));
                }
            } else if let Some(name) = self.name_opt() {
                params.push((Id::from_name(name), None));
            } else {
                break;
            }
        }
        Ok(params)
    }

    fn class(&mut self) -> Result<Class, ParseError> {
        let token = self.any_token()?;
        if !token.is_ident() {
            return Self::fail(token, "expected class name");
        }
        let name = self.qualified_name(&token);
        if !self.class_predicate_table.contains_key(&name) {
            return Self::fail(token, "unknown class");
        }
        let mut args = vec![];
        while let Some(t) = self.optional(|this| this.subty(1024)) {
            args.push(t);
        }
        Ok(Class { name, args })
    }

    /// e.g. `"[C] [D]"`
    fn local_class_parameters(&mut self) -> Result<Vec<Class>, ParseError> {
        let mut class_params = vec![];
        while let Some(_token) = self.expect_symbol_opt("[") {
            let class = self.class()?;
            self.expect_symbol("]")?;
            class_params.push(class);
        }
        Ok(class_params)
    }

    pub fn term(&mut self) -> Result<Term, ParseError> {
        self.subterm(0)
    }

    fn term_opt(&mut self) -> Option<Term> {
        self.optional(|this| this.term())
    }

    fn term_abs(&mut self, token: Token) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (id, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_hole(),
            };
            binders.push(Local { id, ty });
        }
        for x in &binders {
            self.locals.push(x.id);
        }
        let mut m = self.subterm(0)?;
        self.locals.truncate(self.locals.len() - binders.len());
        m = m.abs(&binders);
        Ok(m)
    }

    fn term_binder(&mut self, token: Token, binder: &QualifiedName) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (id, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_hole(),
            };
            binders.push(Local { id, ty });
        }
        for x in &binders {
            self.locals.push(x.id);
        }
        let mut m = self.subterm(0)?;
        self.locals.truncate(self.locals.len() - binders.len());
        for x in binders.into_iter().rev() {
            m = m.abs(slice::from_ref(&x));
            let f = mem::take(&mut m);
            m = mk_const(binder.clone(), vec![x.ty], vec![]);
            m = m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_sep(&mut self, _token: Token) -> Result<Term, ParseError> {
        let binder_id = Id::from_name(self.name()?);
        let ty;
        if let Some(_token) = self.expect_symbol_opt(":") {
            ty = self.ty()?;
        } else {
            ty = mk_fresh_type_hole();
        }
        let x = Local { id: binder_id, ty };
        self.expect_symbol("|")?;
        self.locals.push(x.id);
        let mut m = self.subterm(0)?;
        self.locals.pop();
        m = m.abs(&[x]);
        self.expect_symbol("}")?;
        Ok(m)
    }

    fn term_pair(&mut self, _token: Token) -> Result<Term, ParseError> {
        let fst = self.subterm(0)?;
        self.expect_symbol(",")?;
        let snd = self.subterm(0)?;
        self.expect_symbol("⟩")?;
        let pair = mk_const(
            QualifiedName::from_str("pair"),
            vec![mk_fresh_type_hole(), mk_fresh_type_hole()],
            vec![],
        );
        Ok(pair.apply(vec![fst, snd]))
    }

    fn term_proj(&mut self, term: Term, proj: Proj) -> Term {
        let proj = mk_const(
            proj.name(),
            vec![mk_fresh_type_hole(), mk_fresh_type_hole()],
            vec![],
        );
        proj.apply(vec![term])
    }

    fn term_var(
        &mut self,
        token: Token,
        entity: Option<QualifiedName>,
    ) -> Result<Term, ParseError> {
        let name = match entity {
            Some(entity) => entity,
            None => {
                let name = self.qualified_name(&token);
                if name.prefix().is_none()
                    && self.locals.iter().rev().any(|x| {
                        x.name().expect("locals are all internalized names") == name.name()
                    })
                {
                    return Ok(mk_local(Id::from_name(name.name())));
                }
                name
            }
        };
        if let Some(stash) = self.self_ref.as_ref().and_then(|(self_name, stash)| {
            if self_name == &name {
                Some(stash)
            } else {
                None
            }
        }) {
            return Ok(mk_local(*stash));
        }
        let Some(const_info) = self.const_table.get(&name) else {
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
            for _ in 0..const_info.local_types.len() {
                ty_args.push(mk_fresh_type_hole());
            }
        }
        let mut instances = vec![];
        for _ in 0..const_info.local_classes.len() {
            instances.push(mk_instance_hole(Id::fresh()));
        }
        Ok(mk_const(name, ty_args, instances))
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError> {
        let start = self.lex.save();
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
            Nud::Forall => self.term_binder(token, &QualifiedName::from_str("forall"))?,
            Nud::Exists => self.term_binder(token, &QualifiedName::from_str("exists"))?,
            Nud::Uexists => self.term_binder(token, &QualifiedName::from_str("uexists"))?,
            Nud::User(op) => match op.fixity {
                Fixity::Nofix => self.term_var(token, Some(op.entity.clone()))?,
                Fixity::Prefix => {
                    let mut fun = self.term_var(token, Some(op.entity.clone()))?;
                    let arg = self.subterm(op.prec)?;
                    fun = fun.apply(vec![arg]);
                    fun
                }
                Fixity::Infix | Fixity::Infixl | Fixity::Infixr => unreachable!(),
            },
            Nud::NumLit => Self::fail(token, "numeric literal is unsupported")?,
            Nud::Hole => self.mk_term_hole(),
            Nud::Brace => self.term_sep(token)?,
            Nud::Pair => self.term_pair(token)?,
        };
        left = self.term_with_span(start, left);
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
                    left = left.apply(vec![right]);
                    left = self.term_with_span(start, left);
                }
                Led::User(op) => {
                    let prec = match op.fixity {
                        Fixity::Infix | Fixity::Infixl => prec,
                        Fixity::Infixr => prec - 1,
                        Fixity::Nofix | Fixity::Prefix => unreachable!("op = {op:?}"),
                    };
                    self.advance();
                    let mut fun = self.term_var(token, Some(op.entity.clone()))?;
                    let right = self.subterm(prec)?;
                    fun = fun.apply(vec![left, right]);
                    left = self.term_with_span(start, fun);
                }
                Led::Proj(projection) => {
                    self.advance();
                    left = self.term_proj(left, projection);
                    left = self.term_with_span(start, left);
                }
            }
        }
        Ok(left)
    }

    // Returns (?M l₁ ⋯ lₙ) where ?M is fresh and l₁ ⋯ lₙ are the context in place.
    fn mk_term_hole(&mut self) -> Term {
        let mut hole = mk_fresh_hole();
        let Term::Hole(inner) = &hole else {
            unreachable!()
        };
        self.holes.push((inner.id, mk_fresh_type_hole()));
        hole = hole.apply(self.locals.iter().map(|name| mk_local(*name)));

        hole
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.subexpr(0)
    }

    fn expr_const(&mut self, token: Token, auto_inst: bool) -> Result<Expr, ParseError> {
        let name = self.qualified_name(&token);
        let Some(axiom_info) = self.axiom_table.get(&name) else {
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
            for _ in 0..axiom_info.local_types.len() {
                ty_args.push(mk_fresh_type_hole());
            }
        }
        let mut instances = vec![];
        for _ in 0..axiom_info.local_classes.len() {
            instances.push(mk_instance_hole(Id::fresh()));
        }
        let mut expr = mk_expr_const(name.clone(), ty_args, instances);
        if auto_inst {
            for _ in 0..count_forall(&axiom_info.target) {
                expr = mk_expr_inst(expr, self.mk_term_hole());
            }
        }
        Ok(expr)
    }

    fn mk_have(m: Term, alias: Option<Id>, e: Expr, body: Expr) -> Expr {
        mk_expr_app(mk_expr_assume(m, alias, body), e)
    }

    fn mk_eq(lhs: Term, rhs: Term) -> Term {
        let mut eq = mk_const(
            QualifiedName::from_str("eq"),
            vec![mk_fresh_type_hole()],
            vec![],
        );
        eq = eq.apply([lhs, rhs]);
        eq
    }

    fn mk_eq_trans(&mut self, e1: Expr, e2: Expr) -> Expr {
        let name = QualifiedName::from_str("eq").extend("trans");
        let ty_args = vec![mk_fresh_type_hole()];
        let instances = vec![];
        let mut eq_trans = mk_expr_const(name, ty_args, instances);
        for _ in 0..3 {
            eq_trans = mk_expr_inst(eq_trans, self.mk_term_hole());
        }
        mk_expr_app(mk_expr_app(eq_trans, e1), e2)
    }

    fn subexpr(&mut self, rbp: usize) -> Result<Expr, ParseError> {
        let start = self.lex.save();
        // nud
        let mut left = 'left: {
            if let Some(_token) = self.expect_symbol_opt("(") {
                let e = self.subexpr(0)?;
                self.expect_symbol(")")?;
                break 'left e;
            }
            if let Some(_token) = self.expect_symbol_opt("{") {
                let e = self.subexpr(0)?;
                self.expect_symbol("}")?;
                break 'left e;
            }
            if let Some(_token) = self.expect_symbol_opt("«") {
                let prop = self.term()?;
                self.expect_symbol("»")?;
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
                    let alias = self.alias_opt()?;
                    self.expect_symbol(",")?;
                    if let Some(alias_name) = &alias {
                        self.local_axioms.push(alias_name.clone());
                    }
                    let expr = match self.expr() {
                        Ok(expr) => expr,
                        Err(err) => {
                            if alias.is_some() {
                                self.local_axioms.pop();
                            }
                            return Err(err);
                        }
                    };
                    if alias.is_some() {
                        self.local_axioms.pop();
                    }
                    mk_expr_assume(m, alias.map(Id::from_name), expr)
                }
                "take" => {
                    self.expect_symbol("(")?;
                    let local_id = Id::from_name(self.name()?);
                    self.expect_symbol(":")?;
                    let ty = self.ty()?;
                    self.expect_symbol(")")?;
                    self.expect_symbol(",")?;
                    self.locals.push(local_id);
                    let e = self.expr()?;
                    self.locals.pop();
                    mk_expr_take(local_id, ty, e)
                }
                "change" => {
                    let m = self.term()?;
                    self.expect_symbol(",")?;
                    let e = self.expr()?;
                    mk_expr_change(m, e)
                }
                "have" => {
                    let m = self.term()?;
                    let alias = self.alias_opt()?;
                    self.expect_symbol(":=")?;
                    let e1 = self.expr()?;
                    self.expect_symbol(",")?;
                    if let Some(alias_name) = &alias {
                        self.local_axioms.push(alias_name.clone());
                    }
                    let e2 = match self.expr() {
                        Ok(expr) => expr,
                        Err(err) => {
                            if alias.is_some() {
                                self.local_axioms.pop();
                            }
                            return Err(err);
                        }
                    };
                    if alias.is_some() {
                        self.local_axioms.pop();
                    }
                    Self::mk_have(m, alias.map(Id::from_name), e1, e2)
                }
                "obtain" => {
                    self.expect_symbol("(")?;
                    let local_id = Id::from_name(self.name()?);
                    self.expect_symbol(":")?;
                    let ty = self.ty()?;
                    self.expect_symbol(")")?;
                    self.expect_symbol(",")?;
                    self.locals.push(local_id);
                    let p = self.term()?;
                    self.locals.pop();
                    let alias = self.alias_opt()?;
                    self.expect_symbol(":=")?;
                    let e1 = self.expr()?;
                    self.expect_symbol(",")?;
                    self.locals.push(local_id);
                    if let Some(alias_name) = &alias {
                        self.local_axioms.push(alias_name.clone());
                    }
                    let e2 = match self.expr() {
                        Ok(expr) => expr,
                        Err(err) => {
                            if alias.is_some() {
                                self.local_axioms.pop();
                            }
                            self.locals.pop();
                            return Err(err);
                        }
                    };
                    if alias.is_some() {
                        self.local_axioms.pop();
                    }
                    self.locals.pop();

                    // Expand[obtain (x : τ), p := e1, e2] := exists.ind.{τ}[_, _] e1 (take (x : τ), assume p, e2)
                    let e = mk_expr_const(
                        QualifiedName::from_str("exists").extend("ind"),
                        vec![ty.clone()],
                        vec![],
                    );
                    let e = mk_expr_inst(e, self.mk_term_hole());
                    let e = mk_expr_inst(e, self.mk_term_hole());
                    let e = mk_expr_app(e, e1);
                    let e_body = mk_expr_assume(p, alias.map(Id::from_name), e2);
                    let e_body = mk_expr_take(local_id, ty, e_body);
                    mk_expr_app(e, e_body)
                }
                "calc" => {
                    // calc m₁ = m₂ := e₁
                    //     ... = m₃ := e₂
                    //     ... = m₄ := e₃
                    //
                    // is equivalent to
                    //
                    // have m₁ = m₂ := e₁,
                    // have m₁ = m₃ :=
                    //   have m₂ = m₃ := e₂,
                    //   eq.trans «m₁ = m₂» «m₂ = m₃»,
                    // have m₁ = m₄ :=
                    //   have m₃ = m₄ := e₃,
                    //   eq.trans «m₁ = m₃» «m₃ = m₄»,
                    // «m₁ = m₄»
                    let eq_prec = self
                        .tt
                        .led
                        .get("=")
                        .expect("\"=\" operator is not registered in token table")
                        .prec;
                    let lhs = self.subterm(eq_prec)?;
                    let mut rhs_list = vec![];
                    loop {
                        self.expect_symbol("=")?;
                        let rhs = self.subterm(50)?;
                        self.expect_symbol(":=")?;
                        let e = self.expr()?;
                        rhs_list.push((rhs, e));
                        if self.expect_symbol_opt("...").is_none() {
                            break;
                        }
                    }
                    let mut lemma_list = vec![];
                    let mut last_rhs: Option<Term> = None;
                    for (rhs, e) in rhs_list {
                        let e = match last_rhs {
                            Some(last) => Self::mk_have(
                                Self::mk_eq(last.clone(), rhs.clone()),
                                None,
                                e,
                                self.mk_eq_trans(
                                    mk_expr_assump(Self::mk_eq(lhs.clone(), last.clone())),
                                    mk_expr_assump(Self::mk_eq(last, rhs.clone())),
                                ),
                            ),
                            None => e,
                        };
                        lemma_list.push((Self::mk_eq(lhs.clone(), rhs.clone()), e));
                        last_rhs = Some(rhs);
                    }

                    let last_rhs = last_rhs.expect("calc requires at least one equality");
                    let mut body = mk_expr_assump(Self::mk_eq(lhs.clone(), last_rhs));
                    for (lhs, e) in lemma_list.into_iter().rev() {
                        body = Self::mk_have(lhs, None, e, body);
                    }
                    body
                }
                _ => {
                    let name = Name::from_str(token.as_str());
                    if self.local_axioms.iter().rev().any(|n| n == &name) {
                        mk_expr_assump_by_name(Id::from_name(name))
                    } else {
                        self.expr_const(token, true)?
                    }
                }
            }
        };
        left = self.expr_with_span(start, left);
        while let Some(token) = self.peek_opt() {
            enum ExprLed {
                App,
                Inst,
            }
            let (led, prec) = {
                if token.as_str() == "[" {
                    (ExprLed::Inst, 1025)
                } else if token.as_str() == "("
                    || token.as_str() == "«"
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
                    left = mk_expr_app(left, right);
                    left = self.expr_with_span(start, left);
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
                        e = mk_expr_inst(e, arg);
                        e = self.expr_with_span(start, e);
                    }
                    left = e;
                }
            }
        }
        left = self.expr_with_span(start, left);
        Ok(left)
    }

    fn local_type_parameters(&mut self) -> Result<Vec<Name>, ParseError> {
        if let Some(_token) = self.expect_symbol_opt(".{") {
            let mut local_types = vec![];
            if self.expect_symbol_opt("}").is_none() {
                loop {
                    let token = self.ident()?;
                    let tv = Name::from_str(token.as_str());
                    if local_types.iter().any(|v| v == &tv) {
                        return Self::fail(token, "duplicate type variable")?;
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
            "class" => {
                let keyword2 = self.keyword()?;
                match keyword2.as_str() {
                    "structure" => {
                        let class_structure_cmd = self.class_structure_cmd(keyword)?;
                        Cmd::ClassStructure(class_structure_cmd)
                    }
                    "instance" => {
                        let class_instance_cmd = self.class_instance_cmd(keyword)?;
                        Cmd::ClassInstance(class_instance_cmd)
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
        let ident = self.ident()?;
        let entity = self.qualified_name(&ident);
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
        let ident = self.ident()?;
        let entity = self.qualified_name(&ident);
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
        let ident = self.ident()?;
        let entity = self.qualified_name(&ident);
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
        let ident = self.ident()?;
        let entity = self.qualified_name(&ident);
        Ok(CmdPrefix {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn nofix_cmd(&mut self, _token: Token) -> Result<CmdNofix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":=")?;
        let ident = self.ident()?;
        let entity = self.qualified_name(&ident);
        Ok(CmdNofix {
            op: op.as_str().to_owned(),
            entity,
        })
    }

    fn def_cmd(&mut self, _token: Token) -> Result<CmdDef, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        for param in &params {
            self.locals.push(param.id);
        }
        self.expect_symbol(":")?;
        let mut t = self.ty()?;
        self.expect_symbol(":=")?;
        let mut m = self.term()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        for param in params.into_iter().rev() {
            t = t.arrow([param.ty.clone()]);
            m = m.abs(&[param]);
        }
        Ok(CmdDef {
            name,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            local_classes,
            ty: t,
            target: m,
        })
    }

    fn axiom_cmd(&mut self, _token: Token) -> Result<CmdAxiom, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        for param in &params {
            self.locals.push(param.id);
        }
        self.expect_symbol(":")?;
        let mut target = self.term()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        target = generalize(&target, &params);
        Ok(CmdAxiom {
            name,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            local_classes,
            target,
        })
    }

    fn lemma_cmd(&mut self, _token: Token) -> Result<CmdLemma, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        for param in &params {
            self.locals.push(param.id);
        }
        self.expect_symbol(":")?;
        let mut p = self.term()?;
        self.expect_symbol(":=")?;
        let mut e = self.expr()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        p = generalize(&p, &params);
        for param in params.into_iter().rev() {
            e = mk_expr_take(param.id, param.ty, e);
        }
        let holes = self.holes.drain(..).collect();
        Ok(CmdLemma {
            name,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            local_classes,
            target: p,
            holes,
            expr: e,
        })
    }

    fn const_cmd(&mut self, _token: Token) -> Result<CmdConst, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        self.expect_symbol(":")?;
        let t = self.ty()?;
        // Parsing finished.
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdConst {
            name,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            local_classes,
            ty: t,
        })
    }

    fn type_const_cmd(&mut self, _token: Token) -> Result<CmdTypeConst, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        self.expect_symbol(":")?;
        let kind = self.kind()?;
        Ok(CmdTypeConst { name, kind })
    }

    fn type_inductive_cmd(&mut self, _token: Token) -> Result<CmdTypeInductive, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let self_id = Id::fresh();
        debug_assert!(
            self.type_self_ref.is_none(),
            "nested type inductive definitions are not supported"
        );
        self.type_self_ref = Some((name.clone(), self_id.clone()));

        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let tv = Name::from_str(token.as_str());
            if local_types.iter().any(|v| v == &tv) {
                return Self::fail(token, "duplicate type variable")?;
            }
            local_types.push(tv.clone());
            self.local_types.push(tv);
        }
        let mut ctors: Vec<DataConstructor> = vec![];
        while let Some(_token) = self.expect_symbol_opt("|") {
            let token = self.ident()?;
            let ctor_name = self.qualified_name(&token);
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
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        self.type_self_ref = None;
        Ok(CmdTypeInductive {
            name,
            self_id,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            ctors,
        })
    }

    fn inductive_cmd(&mut self, _token: Token) -> Result<CmdInductive, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let self_id = Id::fresh();
        debug_assert!(
            self.self_ref.is_none(),
            "nested inductive definitions are not supported"
        );
        self.self_ref = Some((name.clone(), self_id));
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let params = self.typed_parameters()?;
        for param in &params {
            self.locals.push(param.id);
        }
        self.expect_symbol(":")?;
        let target_ty = self.ty()?;
        let mut ctors: Vec<Constructor> = vec![];
        while let Some(_token) = self.expect_symbol_opt("|") {
            let token = self.ident()?;
            let ctor_name = self.qualified_name(&token);
            for ctor in &ctors {
                if ctor_name == ctor.name {
                    return Self::fail(token, "duplicate constructor")?;
                }
            }
            let ctor_params = self.typed_parameters()?;
            for ctor_param in &ctor_params {
                self.locals.push(ctor_param.id);
            }
            self.expect_symbol(":")?;
            let mut target = self.term()?;
            self.locals.truncate(self.locals.len() - ctor_params.len());
            target = generalize(&target, &ctor_params);
            ctors.push(Constructor {
                name: ctor_name,
                target,
            })
        }
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.self_ref = None;
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdInductive {
            name,
            self_id,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            ctors,
            params,
            target_ty,
        })
    }

    fn structure_cmd(&mut self, _token: Token) -> Result<CmdStructure, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let tv = Name::from_str(token.as_str());
            if local_types.iter().any(|v| v == &tv) {
                return Self::fail(token, "duplicate type variable")?;
            }
            local_types.push(tv.clone());
            self.local_types.push(tv);
        }
        self.expect_symbol(":=")?;
        self.expect_symbol("{")?;
        let mut fields = vec![];
        let mut num_consts = 0;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "const" => {
                    let field_name = self.name()?;
                    let field_id = Id::from_name(field_name.clone());
                    self.expect_symbol(":")?;
                    let field_ty = self.ty()?;
                    fields.push(StructureField::Const(StructureConst {
                        name: field_name,
                        ty: field_ty,
                    }));

                    self.locals.push(field_id);
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    let params = self.typed_parameters()?;
                    for param in &params {
                        self.locals.push(param.id);
                    }
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(self.locals.len() - params.len());
                    target = generalize(&target, &params);
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
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdStructure {
            name,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            fields,
        })
    }

    fn instance_cmd(&mut self, _token: Token) -> Result<CmdInstance, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        for param in &params {
            self.locals.push(param.id);
        }
        self.expect_symbol(":")?;
        let target_ty = self.ty()?;
        let mut fields = vec![];
        let mut num_defs = 0;
        self.expect_symbol(":=")?;
        self.expect_symbol("{")?;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "def" => {
                    // TODO: allow to refer to preceding definitions in the same instance.
                    let field_name = self.name()?;
                    let field_id = Id::from_name(field_name.clone());
                    let field_params = self.typed_parameters()?;
                    for field_param in &field_params {
                        self.locals.push(field_param.id);
                    }
                    self.expect_symbol(":")?;
                    let mut field_ty = self.ty()?;
                    self.expect_symbol(":=")?;
                    let mut field_target = self.term()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    for field_param in field_params.into_iter().rev() {
                        field_ty = field_ty.arrow([field_param.ty.clone()]);
                        field_target = field_target.abs(&[field_param]);
                    }
                    fields.push(InstanceField::Def(InstanceDef {
                        name: field_name,
                        ty: field_ty,
                        target: field_target,
                    }));

                    self.locals.push(field_id);
                    num_defs += 1;
                }
                "lemma" => {
                    // TODO: allow to refer to preceding lemmas in the same instance.
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    for field_param in &field_params {
                        self.locals.push(field_param.id);
                    }
                    self.expect_symbol(":")?;
                    let mut field_target = self.term()?;
                    self.expect_symbol(":=")?;
                    let mut expr = self.expr()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    field_target = generalize(&field_target, &field_params);
                    for field_param in field_params.into_iter().rev() {
                        expr = mk_expr_take(field_param.id, field_param.ty, expr);
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
        self.locals.truncate(self.locals.len() - num_defs);
        self.locals.truncate(self.locals.len() - params.len());
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdInstance {
            name,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            local_classes,
            params,
            target_ty,
            fields,
        })
    }

    fn class_structure_cmd(&mut self, _token: Token) -> Result<CmdClassStructure, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let tv = Name::from_str(token.as_str());
            if local_types.iter().any(|v| v == &tv) {
                return Self::fail(token, "duplicate type variable")?;
            }
            local_types.push(tv.clone());
            self.local_types.push(tv);
        }
        self.expect_symbol(":=")?;
        self.expect_symbol("{")?;
        let mut fields = vec![];
        let mut num_consts = 0;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "const" => {
                    let field_name = self.name()?;
                    let field_id = Id::from_name(field_name.clone());
                    self.expect_symbol(":")?;
                    let field_ty = self.ty()?;
                    fields.push(ClassStructureField::Const(ClassStructureConst {
                        name: field_name,
                        ty: field_ty,
                    }));

                    self.locals.push(field_id);
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    let params = self.typed_parameters()?;
                    for param in &params {
                        self.locals.push(param.id);
                    }
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(self.locals.len() - params.len());
                    target = generalize(&target, &params);
                    fields.push(ClassStructureField::Axiom(ClassStructureAxiom {
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
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdClassStructure {
            name,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            fields,
        })
    }

    fn class_instance_cmd(&mut self, _token: Token) -> Result<CmdClassInstance, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        self.expect_symbol(":")?;
        let target = self.class()?;
        self.expect_symbol(":=")?;
        let mut fields = vec![];
        self.expect_symbol("{")?;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "def" => {
                    // TODO: allow to refer to preceding definitions in the same instance.
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    for field_param in &field_params {
                        self.locals.push(field_param.id);
                    }
                    self.expect_symbol(":")?;
                    let mut field_ty = self.ty()?;
                    self.expect_symbol(":=")?;
                    let mut field_target = self.term()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    for field_param in field_params.into_iter().rev() {
                        field_ty = field_ty.arrow([field_param.ty.clone()]);
                        field_target = field_target.abs(&[field_param]);
                    }
                    fields.push(ClassInstanceField::Def(ClassInstanceDef {
                        name: field_name,
                        ty: field_ty,
                        target: field_target,
                    }));
                }
                "lemma" => {
                    // TODO: allow to refer to preceding lemmas in the same instance.
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    for field_param in &field_params {
                        self.locals.push(field_param.id);
                    }
                    self.expect_symbol(":")?;
                    let mut field_target = self.term()?;
                    self.expect_symbol(":=")?;
                    let mut expr = self.expr()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    field_target = generalize(&field_target, &field_params);
                    for field_param in field_params.into_iter().rev() {
                        expr = mk_expr_take(field_param.id, field_param.ty, expr);
                    }
                    let holes = self.holes.drain(..).collect();
                    fields.push(ClassInstanceField::Lemma(ClassInstanceLemma {
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
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdClassInstance {
            name,
            local_types: local_types.into_iter().map(Id::from_name).collect(),
            local_classes,
            target,
            fields,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::{File, Lex};
    use crate::proof::{ExprApp, ExprAssume, ExprAssumpByName};
    use std::collections::HashMap;
    use std::sync::Arc;

    #[allow(clippy::type_complexity)]
    fn setup_tables() -> (
        TokenTable,
        HashMap<QualifiedName, Kind>,
        HashMap<QualifiedName, Const>,
        HashMap<QualifiedName, Axiom>,
        HashMap<QualifiedName, ClassType>,
    ) {
        let tt = TokenTable::default();
        let mut type_const_table = HashMap::new();
        let mut const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();

        let prop = QualifiedName::from_str("Prop");
        type_const_table.insert(prop.clone(), Kind(0));

        let p = QualifiedName::from_str("p");
        const_table.insert(
            p,
            Const {
                local_types: vec![],
                local_classes: vec![],
                ty: mk_type_const(prop),
            },
        );

        (
            tt,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        )
    }

    fn parse_expr(input: &str) -> Expr {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        );
        assert!(
            parser
                .const_table
                .contains_key(&QualifiedName::from_str("p")),
            "const table missing p"
        );
        parser.expr().expect("expression parses")
    }

    fn parse_qualified(input: &str) -> Result<QualifiedName, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, Axiom> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );
        let ident = parser.ident()?;
        Ok(parser.qualified_name(&ident))
    }

    #[test]
    fn assume_alias_is_resolved_by_name() {
        let expr = parse_expr("assume p as this, this");
        let Expr::Assume(assume) = expr else {
            panic!("expected assume expression");
        };

        let ExprAssume {
            metadata: _,
            local_axiom,
            alias,
            expr: body,
        } = *assume;
        assert_eq!(alias, Some(Id::from_name(Name::from_str("this"))));
        let expected = mk_const(QualifiedName::from_str("p"), vec![], vec![]);
        assert!(local_axiom.alpha_eq(&expected));

        let Expr::AssumpByName(assump) = body else {
            panic!("expected body to reference assumption alias");
        };
        let ExprAssumpByName { metadata: _, id } = *assump;
        assert_eq!(id, Id::from_name(Name::from_str("this")));
    }

    #[test]
    fn have_alias_is_resolved_by_name() {
        let expr = parse_expr("assume p as hp, have p as this := hp, this");
        let Expr::Assume(outer) = expr else {
            panic!("expected outer assume expression");
        };

        let ExprAssume {
            metadata: _,
            local_axiom: outer_axiom,
            alias: outer_alias,
            expr: outer_body,
        } = *outer;
        assert_eq!(outer_alias, Some(Id::from_name(Name::from_str("hp"))));
        let expected = mk_const(QualifiedName::from_str("p"), vec![], vec![]);
        assert!(outer_axiom.alpha_eq(&expected));

        let Expr::App(app) = outer_body else {
            panic!("expected have expansion to be an application");
        };
        let ExprApp {
            metadata: _,
            expr1,
            expr2,
        } = *app;

        let Expr::Assume(inner_assume) = expr1 else {
            panic!("expected inner assume for have");
        };
        let ExprAssume {
            metadata: _,
            local_axiom: inner_axiom,
            alias: inner_alias,
            expr: inner_body,
        } = *inner_assume;
        assert_eq!(inner_alias, Some(Id::from_name(Name::from_str("this"))));
        assert!(inner_axiom.alpha_eq(&expected));
        let Expr::AssumpByName(inner_assump) = inner_body else {
            panic!("expected have body to reference alias");
        };
        let ExprAssumpByName {
            metadata: _,
            id: inner_id,
        } = *inner_assump;
        assert_eq!(inner_id, Id::from_name(Name::from_str("this")));

        let Expr::AssumpByName(have_arg) = expr2 else {
            panic!("expected have argument to reference outer alias");
        };
        let ExprAssumpByName {
            metadata: _,
            id: outer_id,
        } = *have_arg;
        assert_eq!(outer_id, Id::from_name(Name::from_str("hp")));
    }

    #[test]
    fn qualified_name_parses_dotted_segments() {
        let name = parse_qualified("foo.bar").expect("parse failed");
        assert_eq!(name.to_string(), "foo.bar");
    }

    #[test]
    fn qualified_name_ignores_whitespace_before_segment() {
        let without = parse_qualified("foo.bar").expect("parse without whitespace");
        let with = parse_qualified("foo .bar").expect("parse with whitespace");
        assert_eq!(with, without);
    }
}
