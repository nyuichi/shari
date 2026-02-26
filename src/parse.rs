use crate::cmd::{
    ClassInstanceDef, ClassInstanceField, ClassInstanceLemma, ClassStructureAxiom,
    ClassStructureConst, ClassStructureField, Cmd, CmdAxiom, CmdClassInstance, CmdClassStructure,
    CmdConst, CmdDef, CmdInductive, CmdInfix, CmdInfixl, CmdInfixr, CmdInstance, CmdLemma,
    CmdNamespace, CmdNofix, CmdPrefix, CmdStructure, CmdTypeConst, CmdTypeInductive, CmdUse,
    Constructor, DataConstructor, Fixity, InstanceDef, InstanceField, InstanceLemma, Namespace,
    Operator, StructureAxiom, StructureConst, StructureField, UseDecl as CmdUseDecl,
};
use crate::proof::{
    Axiom, Expr, LocalStructureAxiom, LocalStructureConst, LocalStructureField, count_forall,
    generalize, guard, mk_expr_app, mk_expr_assume, mk_expr_assump, mk_expr_change, mk_expr_const,
    mk_expr_inst, mk_expr_let_structure, mk_expr_let_term, mk_expr_local, mk_expr_take,
    mk_type_prop,
};
use crate::tt::{
    Class, ClassType, Const, Id, Kind, Local, Name, Path, QualifiedName, Term, Type, mk_const,
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
    Lex(#[from] LexError),
    #[error("parse error: {message} at {span}")]
    Parse { message: String, span: Span },
    #[error("unexpected end of input at {span}")]
    Eof { span: Span },
}

#[derive(Debug, Clone)]
struct UseDecl {
    target: QualifiedName,
    alias: Option<Name>,
}

#[derive(Debug, Clone)]
struct LocalAxiom {
    target: Term,
}

// TODO: instance lemma の中で hole を作ると引数にそれまでの instance def が入っちゃって後々 elab で const に置き換えられるので無駄。あと instance 自体の引数が2回ぐらい hole の引数に入ってしまうバグがありそう。
pub struct Parser<'a> {
    lex: &'a mut Lex,
    tt: &'a TokenTable,
    namespace_table: &'a mut HashMap<Path, Namespace>,
    current_namespace: &'a mut Path,
    type_const_table: &'a HashMap<QualifiedName, Kind>,
    const_table: &'a HashMap<QualifiedName, Const>,
    axiom_table: &'a HashMap<QualifiedName, Axiom>,
    class_predicate_table: &'a HashMap<QualifiedName, ClassType>,
    local_consts: Vec<Name>,
    local_axioms: Vec<(Name, LocalAxiom)>,
    local_types: Vec<Name>,
    locals: Vec<Name>,
    self_ref: Option<(QualifiedName, Id)>,
    type_self_ref: Option<(QualifiedName, Id)>,
    holes: Vec<(Id, Type)>,
}

impl<'a> Parser<'a> {
    #[expect(clippy::too_many_arguments)]
    pub fn new(
        lex: &'a mut Lex,
        tt: &'a TokenTable,
        namespace_table: &'a mut HashMap<Path, Namespace>,
        current_namespace: &'a mut Path,
        type_const_table: &'a HashMap<QualifiedName, Kind>,
        const_table: &'a HashMap<QualifiedName, Const>,
        axiom_table: &'a HashMap<QualifiedName, Axiom>,
        class_predicate_table: &'a HashMap<QualifiedName, ClassType>,
    ) -> Self {
        Self {
            lex,
            tt,
            namespace_table,
            current_namespace,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
            local_consts: vec![],
            local_axioms: vec![],
            local_types: vec![],
            locals: vec![],
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

    fn get_const(&self, name: &QualifiedName) -> Option<&Const> {
        self.const_table.get(name)
    }

    fn has_local_const(&self, name: &Name) -> bool {
        self.local_consts.iter().rev().any(|local| local == name)
    }

    fn get_local_axiom(&self, name: &Name) -> Option<&LocalAxiom> {
        self.local_axioms
            .iter()
            .rev()
            .find_map(|(local_name, local_axiom)| {
                if local_name == name {
                    Some(local_axiom)
                } else {
                    None
                }
            })
    }

    fn has_local_type(&self, name: &Name) -> bool {
        self.local_types.iter().rev().any(|local| local == name)
    }

    fn has_local(&self, name: &Name) -> bool {
        self.locals.iter().rev().any(|local| local == name)
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

    fn keyword_opt(&mut self) -> Option<Token> {
        if let Some(token) = self.peek_opt()
            && token.is_keyword()
        {
            self.advance();
            return Some(token);
        }
        None
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

    fn resolve(&mut self, name: QualifiedName) -> QualifiedName {
        let mut path = (*self.current_namespace).clone();
        for name in name.names() {
            path = if let Some(target) = self.namespace_table[&path].use_table.get(&name) {
                target.to_path()
            } else {
                Path::from_parts(path, name)
            };
            if !self.namespace_table.contains_key(&path) {
                self.namespace_table
                    .insert(path.clone(), Namespace::default());
                let (parent, name) = path.to_parts().unwrap();
                self.namespace_table
                    .get_mut(parent)
                    .unwrap()
                    .use_table
                    .entry(name.clone())
                    .or_insert_with(|| QualifiedName::from_parts(parent.clone(), name.clone()));
            }
        }
        let (parent, name) = path.to_parts().unwrap();
        QualifiedName::from_parts(parent.clone(), name.clone())
    }

    fn register_name(&mut self, name: &QualifiedName) {
        self.namespace_table
            .get_mut(name.path())
            .unwrap()
            .add(name.name().clone(), name.clone());
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
            if name.prefix().is_none() && self.has_local_type(name.name()) {
                return Ok(mk_type_local(Id::from_name(name.name())));
            }
            if let Some(stash) = self.type_self_ref.as_ref().and_then(|(self_name, stash)| {
                if self_name == &name {
                    Some(stash)
                } else {
                    None
                }
            }) {
                return Ok(mk_type_local(*stash));
            }
            let name = self.resolve(name);
            if self.type_const_table.contains_key(&name) {
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
    fn typed_parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError> {
        let mut names = vec![];
        // needs at least one parameter
        names.push(self.name()?);
        while let Some(name) = self.name_opt() {
            names.push(name);
        }
        self.expect_symbol(":")?;
        let t = self.ty()?;
        self.expect_symbol(")")?;
        Ok((names, t))
    }

    /// e.g. `"(x y : T) (z : U)"`
    fn typed_parameters(&mut self) -> Result<Vec<(Name, Type)>, ParseError> {
        let mut params = vec![];
        while let Some(token) = self.expect_symbol_opt("(") {
            let (names, ty) = self.typed_parameter(token)?;
            for name in names {
                params.push((name, ty.clone()));
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

    fn class(&mut self) -> Result<Class, ParseError> {
        let token = self.any_token()?;
        if !token.is_ident() {
            return Self::fail(token, "expected class name");
        }
        let name = self.qualified_name(&token);
        let name = self.resolve(name);
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
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_hole(),
            };
            self.locals.push(name.clone());
            binders.push((name, ty));
        }
        let mut m = self.subterm(0)?;
        self.locals.truncate(self.locals.len() - binders.len());
        let binders = binders
            .into_iter()
            .map(|(name, ty)| Local {
                id: Id::from_name(&name),
                ty,
            })
            .collect::<Vec<_>>();
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
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => mk_fresh_type_hole(),
            };
            self.locals.push(name.clone());
            binders.push((name, ty));
        }
        let mut m = self.subterm(0)?;
        self.locals.truncate(self.locals.len() - binders.len());
        for (name, ty) in binders.into_iter().rev() {
            let x = Local {
                id: Id::from_name(&name),
                ty: ty.clone(),
            };
            m = m.abs(slice::from_ref(&x));
            let f = mem::take(&mut m);
            m = mk_const(binder.clone(), vec![ty], vec![]);
            m = m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_sep(&mut self, _token: Token) -> Result<Term, ParseError> {
        let binder_name = self.name()?;
        let ty;
        if let Some(_token) = self.expect_symbol_opt(":") {
            ty = self.ty()?;
        } else {
            ty = mk_fresh_type_hole();
        }
        self.expect_symbol("|")?;
        self.locals.push(binder_name.clone());
        let mut m = self.subterm(0)?;
        self.locals.pop();
        let x = Local {
            id: Id::from_name(&binder_name),
            ty,
        };
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
                if name.prefix().is_none() && self.has_local(name.name()) {
                    return Ok(mk_local(Id::from_name(name.name())));
                }
                if let Some(stash) = self.self_ref.as_ref().and_then(|(self_name, stash)| {
                    if self_name == &name {
                        Some(stash)
                    } else {
                        None
                    }
                }) {
                    return Ok(mk_local(*stash));
                }
                let local_name = Name::from_str(&name.to_string());
                if self.has_local_const(&local_name) {
                    return Ok(mk_local(Id::from_name(&local_name)));
                }
                self.resolve(name)
            }
        };
        let Some(const_info) = self.get_const(&name).cloned() else {
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
        hole = hole.apply(self.locals.iter().map(|name| mk_local(Id::from_name(name))));

        hole
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.subexpr(0)
    }

    fn expr_var(&mut self, token: Token, auto_inst: bool) -> Result<Expr, ParseError> {
        let name = self.qualified_name(&token);
        let local_name = Name::from_str(&name.to_string());
        if let Some(local_axiom) = self.get_local_axiom(&local_name) {
            let mut expr = mk_expr_local(Id::from_name(&local_name));
            if auto_inst {
                for _ in 0..count_forall(&local_axiom.target) {
                    expr = mk_expr_inst(expr, self.mk_term_hole());
                }
            }
            return Ok(expr);
        }
        let name = self.resolve(name);
        let Some(axiom_info) = self.axiom_table.get(&name).cloned() else {
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

    fn let_structure_expr(&mut self, _token: Token) -> Result<Expr, ParseError> {
        let ident = self.ident()?;
        if let Some(token) = self.peek_opt()
            && token.kind == TokenKind::Field
        {
            return Self::fail(token, "local structure name must be an identifier");
        }
        let structure_name = Name::from_str(ident.as_str());
        if let Some(token) = self.peek_opt()
            && token.is_ident()
        {
            return Self::fail(token, "local type parameters are not allowed");
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
                    self.expect_symbol(":")?;
                    let field_ty = self.ty()?;
                    self.locals.push(field_name.clone());
                    fields.push(LocalStructureField::Const(LocalStructureConst {
                        name: field_name,
                        ty: field_ty,
                    }));
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    let params = self.typed_parameters()?;
                    for (param_name, _) in &params {
                        self.locals.push(param_name.clone());
                    }
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(self.locals.len() - params.len());
                    let params = params
                        .into_iter()
                        .map(|(param_name, param_ty)| Local {
                            id: Id::from_name(&param_name),
                            ty: param_ty,
                        })
                        .collect::<Vec<_>>();
                    target = generalize(&target, &params);
                    fields.push(LocalStructureField::Axiom(LocalStructureAxiom {
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
        self.expect_symbol(",")?;

        let structure_id = Id::from_name(&structure_name);
        let this_ty = mk_type_local(structure_id);
        let this = Local {
            id: Id::fresh_with_name(Name::from_str("this")),
            ty: this_ty.clone(),
        };

        let mut local_consts: Vec<Name> = vec![];
        let mut local_axioms: Vec<(Name, LocalAxiom)> = vec![];
        let mut subst = vec![];
        for field in &fields {
            match field {
                LocalStructureField::Const(LocalStructureConst {
                    name: field_name,
                    ty: _,
                }) => {
                    let fullname = Name::from_str(&format!("{structure_name}.{field_name}"));
                    let id = Id::from_name(&fullname);
                    local_consts.push(fullname);
                    let mut target = mk_local(id);
                    target = target.apply([mk_local(this.id)]);
                    subst.push((Id::from_name(field_name), target));
                }
                LocalStructureField::Axiom(LocalStructureAxiom {
                    name: field_name,
                    target,
                }) => {
                    let fullname = Name::from_str(&format!("{structure_name}.{field_name}"));
                    let mut target = target.clone();
                    target = target.subst(&subst);
                    target = generalize(&target, slice::from_ref(&this));
                    local_axioms.push((fullname, LocalAxiom { target }));
                }
            }
        }

        let abs_name = Name::from_str(&format!("{structure_name}.abs"));
        let mut params = vec![];
        let mut guards = vec![];
        let mut chars = vec![];
        let mut abs_subst = vec![];
        for field in &fields {
            match field {
                LocalStructureField::Const(LocalStructureConst {
                    name: field_name,
                    ty,
                }) => {
                    let param = Local {
                        id: Id::fresh_with_name(field_name.clone()),
                        ty: ty.clone(),
                    };

                    let fullname = Name::from_str(&format!("{structure_name}.{field_name}"));
                    let id = Id::from_name(&fullname);
                    let mut rhs = mk_local(id);
                    rhs = rhs.apply([mk_local(this.id)]);

                    let mut char =
                        mk_const(QualifiedName::from_str("eq"), vec![ty.clone()], vec![]);
                    char = char.apply([mk_local(param.id), rhs]);
                    chars.push(char);

                    abs_subst.push((Id::from_name(field_name), mk_local(param.id)));
                    params.push(param);
                }
                LocalStructureField::Axiom(LocalStructureAxiom { target, .. }) => {
                    let mut target = target.clone();
                    target = target.subst(&abs_subst);
                    guards.push(target);
                }
            }
        }

        // These are visible while parsing `body` (e.g. `@foo.abs`),
        // and the target is needed to count implicit instantiations.
        let mut abs = mk_const(
            QualifiedName::from_str("uexists"),
            vec![this_ty.clone()],
            vec![],
        );
        abs = abs.apply([{
            let mut char = chars
                .into_iter()
                .reduce(|left, right| {
                    let mut conj = mk_const(QualifiedName::from_str("and"), vec![], vec![]);
                    conj = conj.apply([left, right]);
                    conj
                })
                .unwrap_or_else(|| mk_const(QualifiedName::from_str("true"), vec![], vec![]));
            char = char.abs(slice::from_ref(&this));
            char
        }]);
        abs = guard(&abs, guards);
        abs = generalize(&abs, &params);
        local_axioms.push((abs_name, LocalAxiom { target: abs }));

        let local_const_len = self.local_consts.len();
        let local_axiom_len = self.local_axioms.len();
        self.local_consts.extend(local_consts);
        self.local_axioms.extend(local_axioms);
        self.local_types.push(structure_name.clone());
        let body = match self.expr() {
            Ok(body) => body,
            Err(err) => {
                self.local_axioms.truncate(local_axiom_len);
                self.local_consts.truncate(local_const_len);
                self.local_types.pop();
                return Err(err);
            }
        };
        self.local_axioms.truncate(local_axiom_len);
        self.local_consts.truncate(local_const_len);
        self.local_types.pop();
        Ok(mk_expr_let_structure(structure_name, fields, body))
    }

    fn let_term_expr(&mut self, _let_token: Token) -> Result<Expr, ParseError> {
        let name = self.name()?;
        let ty = if self.expect_symbol_opt(":").is_some() {
            Some(self.ty()?)
        } else {
            None
        };
        self.expect_symbol(":=")?;
        let value = self.term()?;
        self.expect_symbol(",")?;

        let local_const_len = self.local_consts.len();
        self.local_consts.push(name.clone());
        let body = match self.expr() {
            Ok(body) => body,
            Err(err) => {
                self.local_consts.truncate(local_const_len);
                return Err(err);
            }
        };
        self.local_consts.truncate(local_const_len);
        Ok(mk_expr_let_term(name, ty, value, body))
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
                let expr = self.expr_var(token, false)?;
                break 'left expr;
            }
            let token = self.ident()?;
            match token.as_str() {
                "assume" => {
                    let m = self.term()?;
                    let alias = self.alias_opt()?;
                    self.expect_symbol(",")?;
                    let local_axioms_len = self.local_axioms.len();
                    if let Some(alias_name) = &alias {
                        self.local_axioms
                            .push((alias_name.clone(), LocalAxiom { target: m.clone() }));
                    }
                    let expr = match self.expr() {
                        Ok(expr) => expr,
                        Err(err) => {
                            self.local_axioms.truncate(local_axioms_len);
                            return Err(err);
                        }
                    };
                    self.local_axioms.truncate(local_axioms_len);
                    mk_expr_assume(m, alias.as_ref().map(Id::from_name), expr)
                }
                "take" => {
                    self.expect_symbol("(")?;
                    let local_name = self.name()?;
                    self.expect_symbol(":")?;
                    let ty = self.ty()?;
                    self.expect_symbol(")")?;
                    self.expect_symbol(",")?;
                    self.locals.push(local_name.clone());
                    let e = self.expr()?;
                    self.locals.pop();
                    mk_expr_take(Id::from_name(&local_name), ty, e)
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
                    let local_axioms_len = self.local_axioms.len();
                    if let Some(alias_name) = &alias {
                        self.local_axioms
                            .push((alias_name.clone(), LocalAxiom { target: m.clone() }));
                    }
                    let e2 = match self.expr() {
                        Ok(expr) => expr,
                        Err(err) => {
                            self.local_axioms.truncate(local_axioms_len);
                            return Err(err);
                        }
                    };
                    self.local_axioms.truncate(local_axioms_len);
                    Self::mk_have(m, alias.as_ref().map(Id::from_name), e1, e2)
                }
                "obtain" => {
                    self.expect_symbol("(")?;
                    let local_name = self.name()?;
                    self.expect_symbol(":")?;
                    let ty = self.ty()?;
                    self.expect_symbol(")")?;
                    self.expect_symbol(",")?;
                    self.locals.push(local_name.clone());
                    let p = self.term()?;
                    self.locals.pop();
                    let alias = self.alias_opt()?;
                    self.expect_symbol(":=")?;
                    let e1 = self.expr()?;
                    self.expect_symbol(",")?;
                    self.locals.push(local_name.clone());
                    let local_axioms_len = self.local_axioms.len();
                    if let Some(alias_name) = &alias {
                        self.local_axioms
                            .push((alias_name.clone(), LocalAxiom { target: p.clone() }));
                    }
                    let e2 = match self.expr() {
                        Ok(expr) => expr,
                        Err(err) => {
                            self.local_axioms.truncate(local_axioms_len);
                            self.locals.pop();
                            return Err(err);
                        }
                    };
                    self.local_axioms.truncate(local_axioms_len);
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
                    let e_body = mk_expr_assume(p, alias.as_ref().map(Id::from_name), e2);
                    let e_body = mk_expr_take(Id::from_name(&local_name), ty, e_body);
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
                "let" => {
                    if let Some(keyword) = self.keyword_opt() {
                        match keyword.as_str() {
                            "structure" => self.let_structure_expr(keyword)?,
                            _ => {
                                return Self::fail(keyword, "expected structure or binder name");
                            }
                        }
                    } else {
                        self.let_term_expr(token)?
                    }
                }
                _ => self.expr_var(token, true)?,
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
            "namespace" => {
                let namespace_cmd = self.namespace_cmd(keyword)?;
                Cmd::Namespace(namespace_cmd)
            }
            "use" => {
                let use_cmd = self.use_cmd(keyword)?;
                Cmd::Use(use_cmd)
            }
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

    fn namespace_cmd(&mut self, _token: Token) -> Result<CmdNamespace, ParseError> {
        let name = self.ident()?;
        let name = self.qualified_name(&name);
        let name = self.resolve(name);
        self.register_name(&name);
        let path = name.to_path();
        self.expect_symbol("{")?;
        let prev_namespace = self.current_namespace.clone();
        *self.current_namespace = path.clone();
        let mut cmds = vec![];
        while self.expect_symbol_opt("}").is_none() {
            match self.cmd() {
                Ok(cmd) => cmds.push(cmd),
                Err(err) => {
                    *self.current_namespace = prev_namespace;
                    return Err(err);
                }
            }
        }
        *self.current_namespace = prev_namespace;
        Ok(CmdNamespace { path, cmds })
    }

    fn use_group(
        &mut self,
        prefix: Option<&QualifiedName>,
        decls: &mut Vec<UseDecl>,
    ) -> Result<(), ParseError> {
        if self.expect_symbol_opt("}").is_some() {
            return Ok(());
        }
        loop {
            self.use_entry(prefix, decls)?;
            if self.expect_symbol_opt(",").is_some() {
                if let Some(token) = self.peek_opt()
                    && token.is_symbol()
                    && token.as_str() == "}"
                {
                    return Self::fail(token, "expected use entry after ','");
                }
                continue;
            }
            self.expect_symbol("}")?;
            return Ok(());
        }
    }

    fn use_entry(
        &mut self,
        prefix: Option<&QualifiedName>,
        decls: &mut Vec<UseDecl>,
    ) -> Result<(), ParseError> {
        if self.expect_symbol_opt("{").is_some() {
            return self.use_group(prefix, decls);
        }
        let token = self.ident()?;
        let mut target = self.qualified_name(&token);
        if let Some(prefix) = prefix {
            target = prefix.append(&target);
        }
        if self.expect_symbol_opt(".{").is_some() {
            return self.use_group(Some(&target), decls);
        }
        let alias = self.alias_opt()?;
        decls.push(UseDecl { target, alias });
        Ok(())
    }

    fn use_cmd(&mut self, _token: Token) -> Result<CmdUse, ParseError> {
        let mut parsed_decls = vec![];
        if self.expect_symbol_opt("{").is_some() {
            self.use_group(None, &mut parsed_decls)?;
        } else {
            self.use_entry(None, &mut parsed_decls)?;
        }
        if let Some(token) = self.expect_symbol_opt(",") {
            return Self::fail(
                token,
                "comma-separated targets require braces; use 'use prod.{fst, snd}'",
            );
        }

        let mut decls = vec![];
        let current_namespace = self.current_namespace.clone();
        for decl in parsed_decls {
            let UseDecl { target, alias } = decl;
            let target = self.resolve(target);
            let alias = alias.unwrap_or_else(|| target.name().clone());
            self.namespace_table
                .get_mut(&current_namespace)
                .expect("current namespace must exist")
                .add(alias.clone(), target.clone());
            decls.push(CmdUseDecl { alias, target });
        }

        Ok(CmdUse { decls })
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
        let entity = self.resolve(entity);
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
        let entity = self.resolve(entity);
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
        let entity = self.resolve(entity);
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
        let entity = self.resolve(entity);
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
        let entity = self.resolve(entity);
        Ok(CmdNofix {
            op: op.as_str().to_owned(),
            entity,
        })
    }

    fn def_cmd(&mut self, _token: Token) -> Result<CmdDef, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        for (param_name, _) in &params {
            self.locals.push(param_name.clone());
        }
        self.expect_symbol(":")?;
        let mut t = self.ty()?;
        self.expect_symbol(":=")?;
        let mut m = self.term()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        for (param_name, param_ty) in params.into_iter().rev() {
            t = t.arrow([param_ty.clone()]);
            m = m.abs(&[Local {
                id: Id::from_name(&param_name),
                ty: param_ty,
            }]);
        }
        Ok(CmdDef {
            name,
            local_types: local_types.iter().map(Id::from_name).collect(),
            local_classes,
            ty: t,
            target: m,
        })
    }

    fn axiom_cmd(&mut self, _token: Token) -> Result<CmdAxiom, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        for (param_name, _) in &params {
            self.locals.push(param_name.clone());
        }
        self.expect_symbol(":")?;
        let mut target = self.term()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        let params = params
            .into_iter()
            .map(|(param_name, param_ty)| Local {
                id: Id::from_name(&param_name),
                ty: param_ty,
            })
            .collect::<Vec<_>>();
        target = generalize(&target, &params);
        Ok(CmdAxiom {
            name,
            local_types: local_types.iter().map(Id::from_name).collect(),
            local_classes,
            target,
        })
    }

    fn lemma_cmd(&mut self, _token: Token) -> Result<CmdLemma, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        for (param_name, _) in &params {
            self.locals.push(param_name.clone());
        }
        self.expect_symbol(":")?;
        let mut p = self.term()?;
        self.expect_symbol(":=")?;
        let mut e = self.expr()?;
        // Parsing finished.
        self.locals.truncate(self.locals.len() - params.len());
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        let params = params
            .into_iter()
            .map(|(param_name, param_ty)| Local {
                id: Id::from_name(&param_name),
                ty: param_ty,
            })
            .collect::<Vec<_>>();
        p = generalize(&p, &params);
        for param in params.into_iter().rev() {
            e = mk_expr_take(param.id, param.ty, e);
        }
        let holes = self.holes.drain(..).collect();
        Ok(CmdLemma {
            name,
            local_types: local_types.iter().map(Id::from_name).collect(),
            local_classes,
            target: p,
            holes,
            expr: e,
        })
    }

    fn const_cmd(&mut self, _token: Token) -> Result<CmdConst, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
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
            local_types: local_types.iter().map(Id::from_name).collect(),
            local_classes,
            ty: t,
        })
    }

    fn type_const_cmd(&mut self, _token: Token) -> Result<CmdTypeConst, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
        self.expect_symbol(":")?;
        let kind = self.kind()?;
        Ok(CmdTypeConst { name, kind })
    }

    fn type_inductive_cmd(&mut self, _token: Token) -> Result<CmdTypeInductive, ParseError> {
        let ident = self.ident()?;
        let literal_name = self.qualified_name(&ident);
        let name = self.resolve(literal_name.clone());
        self.register_name(&name);
        let self_id = Id::fresh();
        debug_assert!(
            self.type_self_ref.is_none(),
            "nested type inductive definitions are not supported"
        );
        self.type_self_ref = Some((literal_name, self_id));

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
            let ctor_name = self.resolve(ctor_name);
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
            local_types: local_types.iter().map(Id::from_name).collect(),
            ctors,
        })
    }

    fn inductive_cmd(&mut self, _token: Token) -> Result<CmdInductive, ParseError> {
        let ident = self.ident()?;
        let literal_name = self.qualified_name(&ident);
        let name = self.resolve(literal_name.clone());
        self.register_name(&name);
        let self_id = Id::fresh();
        debug_assert!(
            self.self_ref.is_none(),
            "nested inductive definitions are not supported"
        );
        self.self_ref = Some((literal_name, self_id));
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let params = self.typed_parameters()?;
        for (param_name, _) in &params {
            self.locals.push(param_name.clone());
        }
        self.expect_symbol(":")?;
        let target_ty = self.ty()?;
        let mut ctors: Vec<Constructor> = vec![];
        while let Some(_token) = self.expect_symbol_opt("|") {
            let token = self.ident()?;
            let ctor_name = self.qualified_name(&token);
            let ctor_name = self.resolve(ctor_name);
            for ctor in &ctors {
                if ctor_name == ctor.name {
                    return Self::fail(token, "duplicate constructor")?;
                }
            }
            let ctor_params = self.typed_parameters()?;
            for (ctor_param_name, _) in &ctor_params {
                self.locals.push(ctor_param_name.clone());
            }
            self.expect_symbol(":")?;
            let mut target = self.term()?;
            self.locals.truncate(self.locals.len() - ctor_params.len());
            let ctor_params = ctor_params
                .into_iter()
                .map(|(ctor_param_name, ctor_param_ty)| Local {
                    id: Id::from_name(&ctor_param_name),
                    ty: ctor_param_ty,
                })
                .collect::<Vec<_>>();
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
            local_types: local_types.iter().map(Id::from_name).collect(),
            ctors,
            params: params
                .into_iter()
                .map(|(param_name, param_ty)| Local {
                    id: Id::from_name(&param_name),
                    ty: param_ty,
                })
                .collect(),
            target_ty,
        })
    }

    fn structure_cmd(&mut self, _token: Token) -> Result<CmdStructure, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
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
                    self.expect_symbol(":")?;
                    let field_ty = self.ty()?;
                    self.locals.push(field_name.clone());
                    fields.push(StructureField::Const(StructureConst {
                        name: field_name,
                        ty: field_ty,
                    }));
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    let params = self.typed_parameters()?;
                    for (param_name, _) in &params {
                        self.locals.push(param_name.clone());
                    }
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(self.locals.len() - params.len());
                    let params = params
                        .into_iter()
                        .map(|(param_name, param_ty)| Local {
                            id: Id::from_name(&param_name),
                            ty: param_ty,
                        })
                        .collect::<Vec<_>>();
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
            local_types: local_types.iter().map(Id::from_name).collect(),
            fields,
        })
    }

    fn instance_cmd(&mut self, _token: Token) -> Result<CmdInstance, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
        let local_types = self.local_type_parameters()?;
        for ty in &local_types {
            self.local_types.push(ty.clone());
        }
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        for (param_name, _) in &params {
            self.locals.push(param_name.clone());
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
                    self.locals.push(field_name.clone());
                    let field_params = self.typed_parameters()?;
                    for (field_param_name, _) in &field_params {
                        self.locals.push(field_param_name.clone());
                    }
                    self.expect_symbol(":")?;
                    let mut field_ty = self.ty()?;
                    self.expect_symbol(":=")?;
                    let mut field_target = self.term()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    for (field_param_name, field_param_ty) in field_params.into_iter().rev() {
                        field_ty = field_ty.arrow([field_param_ty.clone()]);
                        field_target = field_target.abs(&[Local {
                            id: Id::from_name(&field_param_name),
                            ty: field_param_ty,
                        }]);
                    }
                    fields.push(InstanceField::Def(InstanceDef {
                        name: field_name,
                        ty: field_ty,
                        target: field_target,
                    }));
                    num_defs += 1;
                }
                "lemma" => {
                    // TODO: allow to refer to preceding lemmas in the same instance.
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    for (field_param_name, _) in &field_params {
                        self.locals.push(field_param_name.clone());
                    }
                    self.expect_symbol(":")?;
                    let mut field_target = self.term()?;
                    self.expect_symbol(":=")?;
                    let mut expr = self.expr()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    let field_params = field_params
                        .into_iter()
                        .map(|(field_param_name, field_param_ty)| Local {
                            id: Id::from_name(&field_param_name),
                            ty: field_param_ty,
                        })
                        .collect::<Vec<_>>();
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
            local_types: local_types.iter().map(Id::from_name).collect(),
            local_classes,
            params: params
                .into_iter()
                .map(|(param_name, param_ty)| Local {
                    id: Id::from_name(&param_name),
                    ty: param_ty,
                })
                .collect(),
            target_ty,
            fields,
        })
    }

    fn class_structure_cmd(&mut self, _token: Token) -> Result<CmdClassStructure, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
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
                    self.expect_symbol(":")?;
                    let field_ty = self.ty()?;
                    self.locals.push(field_name.clone());
                    fields.push(ClassStructureField::Const(ClassStructureConst {
                        name: field_name,
                        ty: field_ty,
                    }));
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    let params = self.typed_parameters()?;
                    for (param_name, _) in &params {
                        self.locals.push(param_name.clone());
                    }
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(self.locals.len() - params.len());
                    let params = params
                        .into_iter()
                        .map(|(param_name, param_ty)| Local {
                            id: Id::from_name(&param_name),
                            ty: param_ty,
                        })
                        .collect::<Vec<_>>();
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
            local_types: local_types.iter().map(Id::from_name).collect(),
            fields,
        })
    }

    fn class_instance_cmd(&mut self, _token: Token) -> Result<CmdClassInstance, ParseError> {
        let ident = self.ident()?;
        let name = self.qualified_name(&ident);
        let name = self.resolve(name);
        self.register_name(&name);
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
                    for (field_param_name, _) in &field_params {
                        self.locals.push(field_param_name.clone());
                    }
                    self.expect_symbol(":")?;
                    let mut field_ty = self.ty()?;
                    self.expect_symbol(":=")?;
                    let mut field_target = self.term()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    for (field_param_name, field_param_ty) in field_params.into_iter().rev() {
                        field_ty = field_ty.arrow([field_param_ty.clone()]);
                        field_target = field_target.abs(&[Local {
                            id: Id::from_name(&field_param_name),
                            ty: field_param_ty,
                        }]);
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
                    for (field_param_name, _) in &field_params {
                        self.locals.push(field_param_name.clone());
                    }
                    self.expect_symbol(":")?;
                    let mut field_target = self.term()?;
                    self.expect_symbol(":=")?;
                    let mut expr = self.expr()?;
                    self.locals.truncate(self.locals.len() - field_params.len());
                    let field_params = field_params
                        .into_iter()
                        .map(|(field_param_name, field_param_ty)| Local {
                            id: Id::from_name(&field_param_name),
                            ty: field_param_ty,
                        })
                        .collect::<Vec<_>>();
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
            local_types: local_types.iter().map(Id::from_name).collect(),
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
    use crate::proof::{ExprApp, ExprAssume, ExprInst, ExprLetTerm, ExprLocal};
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

    fn ensure_namespace_path_for_tests(
        namespace_table: &mut HashMap<Path, Namespace>,
        namespace: &Path,
    ) {
        if namespace == &Path::toplevel() {
            return;
        }

        let mut parent = Path::toplevel();
        for segment in namespace.names() {
            let child = Path::from_parts(parent.clone(), segment.clone());
            if !namespace_table.contains_key(&child) {
                namespace_table.insert(child.clone(), Namespace::default());
            }
            namespace_table
                .get_mut(&parent)
                .expect("parent namespace must exist")
                .use_table
                .entry(segment.clone())
                .or_insert_with(|| QualifiedName::from_parts(parent.clone(), segment.clone()));
            parent = child;
        }
    }

    fn register_global_name_for_tests(
        namespace_table: &mut HashMap<Path, Namespace>,
        name: &QualifiedName,
    ) {
        let owner_namespace = name.path().clone();
        ensure_namespace_path_for_tests(namespace_table, &owner_namespace);
        namespace_table
            .get_mut(&owner_namespace)
            .expect("owner namespace must exist")
            .use_table
            .entry(name.name().clone())
            .or_insert_with(|| name.clone());
    }

    fn seed_namespace_table_from_globals(
        namespace_table: &mut HashMap<Path, Namespace>,
        type_const_table: &HashMap<QualifiedName, Kind>,
        const_table: &HashMap<QualifiedName, Const>,
        axiom_table: &HashMap<QualifiedName, Axiom>,
        class_predicate_table: &HashMap<QualifiedName, ClassType>,
    ) {
        let mut names = vec![];
        names.extend(type_const_table.keys().cloned());
        names.extend(const_table.keys().cloned());
        names.extend(axiom_table.keys().cloned());
        names.extend(class_predicate_table.keys().cloned());
        for name in names {
            register_global_name_for_tests(namespace_table, &name);
        }
    }

    fn parse_expr(input: &str) -> Expr {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let top_namespace = Path::toplevel();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            top_namespace.clone(),
            Namespace {
                use_table: std::mem::take(&mut use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        );
        let mut current_namespace = top_namespace;
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &mut namespace_table,
            &mut current_namespace,
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
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let top_namespace = Path::toplevel();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            top_namespace.clone(),
            Namespace {
                use_table: std::mem::take(&mut use_table),
            },
        );
        let mut current_namespace = top_namespace;
        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, Axiom> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &mut namespace_table,
            &mut current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );
        let ident = parser.ident()?;
        Ok(parser.qualified_name(&ident))
    }

    fn parse_cmd_with_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, QualifiedName>,
        type_const_table: &HashMap<QualifiedName, Kind>,
        const_table: &HashMap<QualifiedName, Const>,
        axiom_table: &HashMap<QualifiedName, Axiom>,
        class_predicate_table: &HashMap<QualifiedName, ClassType>,
    ) -> Result<Cmd, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let top_namespace = Path::toplevel();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            top_namespace.clone(),
            Namespace {
                use_table: std::mem::take(use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let mut current_namespace = top_namespace.clone();
        let mut parser = Parser::new(
            &mut lex,
            tt,
            &mut namespace_table,
            &mut current_namespace,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let cmd = parser.cmd();
        let top_entry = namespace_table
            .remove(&top_namespace)
            .expect("top-level namespace entry must exist");
        *use_table = top_entry.use_table;
        cmd
    }

    fn parse_term_with_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, QualifiedName>,
        type_const_table: &HashMap<QualifiedName, Kind>,
        const_table: &HashMap<QualifiedName, Const>,
        axiom_table: &HashMap<QualifiedName, Axiom>,
        class_predicate_table: &HashMap<QualifiedName, ClassType>,
    ) -> Result<Term, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let top_namespace = Path::toplevel();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            top_namespace.clone(),
            Namespace {
                use_table: std::mem::take(use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let mut current_namespace = top_namespace.clone();
        let mut parser = Parser::new(
            &mut lex,
            tt,
            &mut namespace_table,
            &mut current_namespace,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let term = parser.term();
        let top_entry = namespace_table
            .remove(&top_namespace)
            .expect("top-level namespace entry must exist");
        *use_table = top_entry.use_table;
        term
    }

    fn parse_expr_with_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, QualifiedName>,
        type_const_table: &HashMap<QualifiedName, Kind>,
        const_table: &HashMap<QualifiedName, Const>,
        axiom_table: &HashMap<QualifiedName, Axiom>,
        class_predicate_table: &HashMap<QualifiedName, ClassType>,
    ) -> Result<Expr, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let top_namespace = Path::toplevel();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            top_namespace.clone(),
            Namespace {
                use_table: std::mem::take(use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let mut current_namespace = top_namespace.clone();
        let mut parser = Parser::new(
            &mut lex,
            tt,
            &mut namespace_table,
            &mut current_namespace,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let expr = parser.expr();
        let top_entry = namespace_table
            .remove(&top_namespace)
            .expect("top-level namespace entry must exist");
        *use_table = top_entry.use_table;
        expr
    }

    fn qualified(value: &str) -> QualifiedName {
        let mut parts = value.split('.');
        let first = parts.next().expect("qualified name must not be empty");
        let mut name = QualifiedName::from_str(first);
        for part in parts {
            name = name.extend(part);
        }
        name
    }

    fn path(value: &str) -> Path {
        let mut path = Path::toplevel();
        if value.is_empty() {
            return path;
        }
        for part in value.split('.') {
            path = Path::from_parts(path, Name::from_str(part));
        }
        path
    }

    fn insert_prop_const(const_table: &mut HashMap<QualifiedName, Const>, name: &str) {
        const_table.insert(
            qualified(name),
            Const {
                local_types: vec![],
                local_classes: vec![],
                ty: mk_type_const(QualifiedName::from_str("Prop")),
            },
        );
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
        assert_eq!(alias, Some(Id::from_name(&Name::from_str("this"))));
        let expected = mk_const(QualifiedName::from_str("p"), vec![], vec![]);
        assert!(local_axiom.alpha_eq(&expected));

        let Expr::Local(assump) = body else {
            panic!("expected body to reference assumption alias");
        };
        let ExprLocal { metadata: _, id } = *assump;
        assert_eq!(id, Id::from_name(&Name::from_str("this")));
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
        assert_eq!(outer_alias, Some(Id::from_name(&Name::from_str("hp"))));
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
        assert_eq!(inner_alias, Some(Id::from_name(&Name::from_str("this"))));
        assert!(inner_axiom.alpha_eq(&expected));
        let Expr::Local(inner_assump) = inner_body else {
            panic!("expected have body to reference alias");
        };
        let ExprLocal {
            metadata: _,
            id: inner_id,
        } = *inner_assump;
        assert_eq!(inner_id, Id::from_name(&Name::from_str("this")));

        let Expr::Local(have_arg) = expr2 else {
            panic!("expected have argument to reference outer alias");
        };
        let ExprLocal {
            metadata: _,
            id: outer_id,
        } = *have_arg;
        assert_eq!(outer_id, Id::from_name(&Name::from_str("hp")));
    }

    #[test]
    fn assume_alias_auto_instantiates_forall() {
        let expr = parse_expr("assume ∀ (x : Prop), p as h, h");
        let Expr::Assume(assume) = expr else {
            panic!("expected assume expression");
        };
        let ExprAssume {
            metadata: _,
            local_axiom: _,
            alias: _,
            expr: body,
        } = *assume;
        let Expr::Inst(inst) = body else {
            panic!("expected implicit instantiation on local axiom alias");
        };
        let ExprInst {
            metadata: _,
            expr: head,
            arg,
        } = *inst;
        let Expr::Local(local_axiom) = head else {
            panic!("expected local axiom as instantiation head");
        };
        assert_eq!(local_axiom.id, Id::from_name(&Name::from_str("h")));
        assert!(arg.head().is_hole());
    }

    #[test]
    fn term_hole_uses_canonical_ids_for_local_context() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let top_namespace = Path::toplevel();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(top_namespace.clone(), Namespace::default());
        seed_namespace_table_from_globals(
            &mut namespace_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        );
        let mut current_namespace = top_namespace;
        let file = Arc::new(File::new("<test>", "_"));
        let mut lex = Lex::new(file);
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &mut namespace_table,
            &mut current_namespace,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        );

        let local_name = Name::from_str("x");
        let generated_id = Id::fresh_with_name(local_name.clone());
        let canonical_id = Id::from_name(&local_name);
        assert_ne!(generated_id, canonical_id);
        parser.locals.push(local_name);
        let term = parser.term().expect("term parses");
        let args = term.args();
        assert_eq!(args.len(), 1);
        let Term::Local(local) = args[0] else {
            panic!("expected local argument");
        };
        assert_eq!(local.id, canonical_id);
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

    #[test]
    fn use_scoped_group_expands_to_leaf_decls() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "prod.fst");
        insert_prop_const(&mut consts, "prod.snd");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "use prod.{fst, snd}",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let Cmd::Use(CmdUse { decls }) = cmd else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].alias, Name::from_str("fst"));
        assert_eq!(decls[0].target, qualified("prod.fst"));
        assert_eq!(decls[1].alias, Name::from_str("snd"));
        assert_eq!(decls[1].target, qualified("prod.snd"));
    }

    #[test]
    fn use_chain_normalizes_alias_target() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "foo");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        use_table.insert(Name::from_str("bar"), qualified("foo"));
        let cmd = parse_cmd_with_tables(
            "use bar as baz",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let Cmd::Use(CmdUse { decls }) = cmd else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].alias, Name::from_str("baz"));
        assert_eq!(decls[0].target, qualified("foo"));
    }

    #[test]
    fn use_target_rewrites_alias_head_without_target_validation() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        use_table.insert(Name::from_str("bar"), qualified("foo"));
        let cmd = parse_cmd_with_tables(
            "use bar.baz as qux",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let Cmd::Use(CmdUse { decls }) = cmd else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].alias, Name::from_str("qux"));
        assert_eq!(decls[0].target, qualified("foo.baz"));
    }

    #[test]
    fn use_shadowing_rebinds_alias_to_new_target() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "foo");
        insert_prop_const(&mut consts, "bar");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        use_table.insert(Name::from_str("name"), qualified("foo"));
        let cmd = parse_cmd_with_tables(
            "use bar as name",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let Cmd::Use(CmdUse { decls }) = cmd else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].alias, Name::from_str("name"));
        assert_eq!(decls[0].target, qualified("bar"));
    }

    #[test]
    fn use_group_alias_chain_is_resolved_left_to_right() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "hoge");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "use {hoge as fuga, fuga as piyo}",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let Cmd::Use(CmdUse { decls }) = cmd else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].alias, Name::from_str("fuga"));
        assert_eq!(decls[0].target, qualified("hoge"));
        assert_eq!(decls[1].alias, Name::from_str("piyo"));
        assert_eq!(decls[1].target, qualified("hoge"));
    }

    #[test]
    fn use_unknown_target_is_accepted() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "use future.symbol as fs",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let Cmd::Use(CmdUse { decls }) = cmd else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].alias, Name::from_str("fs"));
        assert_eq!(decls[0].target, qualified("future.symbol"));
    }

    #[test]
    fn use_unknown_target_chain_in_same_group() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "use {future as f, f as g}",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let Cmd::Use(CmdUse { decls }) = cmd else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].alias, Name::from_str("f"));
        assert_eq!(decls[0].target, qualified("future"));
        assert_eq!(decls[1].alias, Name::from_str("g"));
        assert_eq!(decls[1].target, qualified("future"));
    }

    #[test]
    fn use_unknown_target_fails_when_referenced() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        parse_cmd_with_tables(
            "use unknown as a",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("first use command parses");
        parse_cmd_with_tables(
            "use a as b",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("second use command parses");
        let err = parse_term_with_tables(
            "b",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("reference should fail when target entity is undefined");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "unknown variable");
    }

    #[test]
    fn use_unknown_target_alias_fails_in_def_body() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        parse_cmd_with_tables(
            "use unknown as a",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("first use command parses");
        parse_cmd_with_tables(
            "use a as b",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("second use command parses");
        let err = parse_cmd_with_tables(
            "def x : Prop := b",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("definition body should fail when alias target entity is undefined");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "unknown variable");
    }

    #[test]
    fn inductive_self_reference_does_not_use_resolved_alias() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        parse_cmd_with_tables(
            "use foo as alias",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let err = parse_cmd_with_tables(
            "inductive foo : Prop | mk : alias",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("constructor target must not treat alias as self");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "unknown variable");
    }

    #[test]
    fn type_inductive_self_reference_does_not_use_resolved_alias() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        parse_cmd_with_tables(
            "use foo as alias",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let err = parse_cmd_with_tables(
            "type inductive foo | mk : alias",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("constructor type must not treat alias as self");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "unknown type constant");
    }

    #[test]
    fn use_comma_without_braces_is_rejected() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "prod.fst");
        insert_prop_const(&mut consts, "prod.snd");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let err = parse_cmd_with_tables(
            "use prod.fst, prod.snd",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("command should fail");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert!(
            message.contains("comma-separated targets require braces"),
            "message = {message}"
        );
    }

    #[test]
    fn term_resolution_rewrites_use_alias_head() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "prod.fst.default");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        use_table.insert(Name::from_str("fst"), qualified("prod.fst"));
        let term = parse_term_with_tables(
            "fst.default",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("term parses");
        let Term::Const(inner) = term else {
            panic!("expected constant term");
        };
        assert_eq!(inner.name, qualified("prod.fst.default"));
    }

    #[test]
    fn infix_entity_rewrites_alias_head_without_target_validation() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        parse_cmd_with_tables(
            "use foo as bar",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let cmd = parse_cmd_with_tables(
            "infix * : 50 := bar.baz",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("infix command parses");
        let Cmd::Infix(CmdInfix {
            op: _,
            prec: _,
            entity,
        }) = cmd
        else {
            panic!("expected infix command");
        };
        assert_eq!(entity, qualified("foo.baz"));
    }

    #[test]
    fn prefix_entity_rewrites_alias_head_without_target_validation() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        parse_cmd_with_tables(
            "use foo as bar",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let cmd = parse_cmd_with_tables(
            "prefix ! : 50 := bar.baz",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("prefix command parses");
        let Cmd::Prefix(CmdPrefix {
            op: _,
            prec: _,
            entity,
        }) = cmd
        else {
            panic!("expected prefix command");
        };
        assert_eq!(entity, qualified("foo.baz"));
    }

    #[test]
    fn nofix_entity_rewrites_alias_head_without_target_validation() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        parse_cmd_with_tables(
            "use foo as bar",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("use command parses");
        let cmd = parse_cmd_with_tables(
            "nofix ! := bar.baz",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("nofix command parses");
        let Cmd::Nofix(CmdNofix { op: _, entity }) = cmd else {
            panic!("expected nofix command");
        };
        assert_eq!(entity, qualified("foo.baz"));
    }

    #[test]
    fn infix_entity_resolves_aliases_left_to_right_across_namespaces() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "namespace foo { use qux as inner namespace qux { use real as leaf } infix * : 50 := inner.leaf.tail }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace command parses");
        let Cmd::Namespace(namespace_cmd) = cmd else {
            panic!("expected namespace command");
        };
        assert_eq!(namespace_cmd.cmds.len(), 3);
        let Cmd::Infix(CmdInfix {
            op: _,
            prec: _,
            entity,
        }) = &namespace_cmd.cmds[2]
        else {
            panic!("expected infix command");
        };
        assert_eq!(entity, &qualified("foo.qux.real.tail"));
    }

    #[test]
    fn declaration_name_resolution_rewrites_use_alias_head() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        use_table.insert(Name::from_str("alias"), qualified("prod"));
        let cmd = parse_cmd_with_tables(
            "type const alias.elem : Type",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("type const command parses");
        let Cmd::TypeConst(CmdTypeConst { name, kind: _ }) = cmd else {
            panic!("expected type_const command");
        };
        assert_eq!(name, qualified("prod.elem"));
    }

    #[test]
    fn type_inductive_ctor_resolution_rewrites_use_alias_head() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        use_table.insert(Name::from_str("alias"), qualified("prod"));
        let cmd = parse_cmd_with_tables(
            "type inductive alias.list | alias.nil : alias.list",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("type inductive command parses");
        let Cmd::TypeInductive(CmdTypeInductive {
            name,
            self_id: _,
            local_types: _,
            ctors,
        }) = cmd
        else {
            panic!("expected type_inductive command");
        };
        assert_eq!(name, qualified("prod.list"));
        assert_eq!(ctors.len(), 1);
        assert_eq!(ctors[0].name, qualified("prod.nil"));
    }

    #[test]
    fn type_inductive_ctor_registers_top_level_alias() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        parse_cmd_with_tables(
            "type inductive foo | ctor : foo",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("type inductive command parses");
        assert!(
            use_table.contains_key(&Name::from_str("ctor")),
            "constructor alias should be registered in the current namespace"
        );
    }

    #[test]
    fn resolve_to_path_resolves_each_segment_without_parent_alias_entry() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let top_namespace = Path::toplevel();
        namespace_table.insert(top_namespace, Namespace::default());
        namespace_table.insert(path("foo"), Namespace::default());
        namespace_table.insert(path("foo.qux.real"), Namespace::default());
        let mut qux_namespace = Namespace::default();
        qux_namespace.add(Name::from_str("leaf"), qualified("foo.qux.real"));
        namespace_table.insert(path("foo.qux"), qux_namespace);
        let mut current_namespace = path("foo");
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &mut namespace_table,
            &mut current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("qux.leaf")).to_path();
        assert_eq!(resolved, path("foo.qux.real"));
    }

    #[test]
    fn resolve_resolves_each_segment_without_parent_alias_entry() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let top_namespace = Path::toplevel();
        namespace_table.insert(top_namespace, Namespace::default());
        namespace_table.insert(path("foo"), Namespace::default());
        namespace_table.insert(path("foo.qux.real"), Namespace::default());
        let mut qux_namespace = Namespace::default();
        qux_namespace.add(Name::from_str("leaf"), qualified("foo.qux.real"));
        namespace_table.insert(path("foo.qux"), qux_namespace);
        let mut current_namespace = path("foo");
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &mut namespace_table,
            &mut current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("qux.leaf"));
        assert_eq!(resolved, qualified("foo.qux.real"));
    }

    #[test]
    fn resolve_creates_missing_namespaces_along_path() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let top_namespace = Path::toplevel();
        namespace_table.insert(top_namespace.clone(), Namespace::default());
        let mut current_namespace = top_namespace;
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &mut namespace_table,
            &mut current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("qux.quux"));
        assert_eq!(resolved, qualified("qux.quux"));
        assert!(parser.namespace_table.contains_key(&path("qux")));
        assert_eq!(
            parser.namespace_table[&Path::toplevel()]
                .use_table
                .get(&Name::from_str("qux")),
            Some(&qualified("qux"))
        );
    }

    #[test]
    fn resolve_resolves_each_segment_without_parent_alias_entry_with_tail() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let top_namespace = Path::toplevel();
        namespace_table.insert(top_namespace, Namespace::default());
        namespace_table.insert(path("foo"), Namespace::default());
        namespace_table.insert(path("foo.qux.real"), Namespace::default());
        let mut qux_namespace = Namespace::default();
        qux_namespace.add(Name::from_str("leaf"), qualified("foo.qux.real"));
        namespace_table.insert(path("foo.qux"), qux_namespace);
        let mut current_namespace = path("foo");
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &mut namespace_table,
            &mut current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("qux.leaf.tail"));
        assert_eq!(resolved, qualified("foo.qux.real.tail"));
    }

    #[test]
    fn let_term_expr_without_type_annotation_parses() {
        let expr = parse_expr("let c := p, assume c as h, h");
        let Expr::LetTerm(let_term) = expr else {
            panic!("expected let-term expression");
        };
        let ExprLetTerm {
            metadata: _,
            name,
            ty,
            value,
            body,
        } = *let_term;
        assert_eq!(name, Name::from_str("c"));
        assert!(ty.is_none());
        let Term::Const(value_const) = value else {
            panic!("expected const term in let value");
        };
        assert_eq!(value_const.name, qualified("p"));
        let Expr::Assume(assume) = body else {
            panic!("expected assume expression in let body");
        };
        let ExprAssume {
            metadata: _,
            local_axiom,
            alias: _,
            expr: _,
        } = *assume;
        let Term::Local(local_const) = local_axiom else {
            panic!("expected local term in let body");
        };
        assert_eq!(local_const.id, Id::from_name(&Name::from_str("c")));
    }

    #[test]
    fn let_term_expr_with_type_annotation_parses() {
        let expr = parse_expr("let c : Prop := p, assume c as h, h");
        let Expr::LetTerm(let_term) = expr else {
            panic!("expected let-term expression");
        };
        let ExprLetTerm {
            metadata: _,
            name: _,
            ty,
            value: _,
            body: _,
        } = *let_term;
        let Some(ty) = ty else {
            panic!("expected type annotation");
        };
        assert_eq!(ty, mk_type_const(qualified("Prop")));
    }

    #[test]
    fn let_term_expr_rejects_qualified_binder() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let err = parse_expr_with_tables(
            "let Foo.bar := p, assume Foo.bar as h, h",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("qualified let-term binder should be rejected");
        assert!(err.to_string().contains("expected symbol ':='"));
    }

    #[test]
    fn let_term_expr_rejects_qualified_binder_with_whitespace() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let err = parse_expr_with_tables(
            "let Foo .bar := p, assume Foo .bar as h, h",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("qualified let-term binder should be rejected");
        assert!(err.to_string().contains("expected symbol ':='"));
    }

    #[test]
    fn let_term_binder_name_is_not_resolved_and_shadows_globals() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "global.target");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        use_table.insert(Name::from_str("c"), qualified("global.target"));
        let expr = parse_expr_with_tables(
            "let c := p, assume c as h, h",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("expression parses");
        let Expr::LetTerm(let_term) = expr else {
            panic!("expected let-term expression");
        };
        let ExprLetTerm {
            metadata: _,
            name,
            ty: _,
            value: _,
            body,
        } = *let_term;
        assert_eq!(name, Name::from_str("c"));
        let Expr::Assume(assume) = body else {
            panic!("expected assume expression in let body");
        };
        let ExprAssume {
            metadata: _,
            local_axiom,
            alias: _,
            expr: _,
        } = *assume;
        let Term::Local(local_const) = local_axiom else {
            panic!("expected local term in let body");
        };
        assert_eq!(local_const.id, Id::from_name(&Name::from_str("c")));
    }

    #[test]
    fn let_structure_body_uses_local_term() {
        let expr = parse_expr("let structure foo := { const f : Prop }, assume foo.f as h, h");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Expr::Assume(assume) = let_structure.body else {
            panic!("expected assume expression in let structure body");
        };
        let ExprAssume {
            metadata: _,
            local_axiom,
            alias: _,
            expr: _,
        } = *assume;
        let Term::Local(local_const) = local_axiom else {
            panic!("expected local term");
        };
        assert_eq!(local_const.id, Id::from_name(&Name::from_str("foo.f")));
    }

    #[test]
    fn let_structure_shadowing_prefers_inner_local() {
        let expr = parse_expr(
            "let structure foo := { const f : Prop }, \
             let structure foo := { const f : Prop }, \
             assume foo.f as h, h",
        );
        let Expr::LetStructure(outer) = expr else {
            panic!("expected outer let structure expression");
        };
        let Expr::LetStructure(inner) = outer.body else {
            panic!("expected inner let structure expression");
        };
        let Expr::Assume(assume) = inner.body else {
            panic!("expected assume expression in inner let structure body");
        };
        let ExprAssume {
            metadata: _,
            local_axiom,
            alias: _,
            expr: _,
        } = *assume;
        let Term::Local(local_const) = local_axiom else {
            panic!("expected local term");
        };
        assert_eq!(local_const.id, Id::from_name(&Name::from_str("foo.f")));
    }

    #[test]
    fn let_structure_local_has_priority_over_global_const() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "foo.f");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let expr = parse_expr_with_tables(
            "let structure foo := { const f : Prop }, assume foo.f as h, h",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("expression parses");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Expr::Assume(assume) = let_structure.body else {
            panic!("expected assume expression in let structure body");
        };
        let ExprAssume {
            metadata: _,
            local_axiom,
            alias: _,
            expr: _,
        } = *assume;
        let Term::Local(local_const) = local_axiom else {
            panic!("expected local term");
        };
        assert_eq!(local_const.id, Id::from_name(&Name::from_str("foo.f")));
    }

    #[test]
    fn let_structure_local_axiom_is_parsed_as_local_expr() {
        let expr = parse_expr("let structure foo := { const f : Prop axiom a : f }, @foo.a");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Expr::Local(local_axiom) = let_structure.body else {
            panic!("expected local expression in let structure body");
        };
        assert_eq!(local_axiom.id, Id::from_name(&Name::from_str("foo.a")));
    }

    #[test]
    fn let_structure_local_axiom_ignores_whitespace_before_segment() {
        let expr = parse_expr("let structure foo := { const f : Prop axiom a : f }, @foo .a");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Expr::Local(local_axiom) = let_structure.body else {
            panic!("expected local expression in let structure body");
        };
        assert_eq!(local_axiom.id, Id::from_name(&Name::from_str("foo.a")));
    }

    #[test]
    fn let_structure_local_axiom_without_at_is_parsed_as_local_expr() {
        let expr = parse_expr("let structure foo := { const f : Prop axiom a : f }, foo.a");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Expr::Inst(inst) = let_structure.body else {
            panic!("expected implicit instantiation in let structure body");
        };
        let ExprInst {
            metadata: _,
            expr: head,
            arg,
        } = *inst;
        let Expr::Local(local_axiom) = head else {
            panic!("expected local axiom as instantiation head");
        };
        assert_eq!(local_axiom.id, Id::from_name(&Name::from_str("foo.a")));
        assert!(arg.head().is_hole());
    }

    #[test]
    fn namespace_command_parses_const_with_prefixed_name() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(qualified("Type"), Kind(0));
        type_consts.insert(qualified("foo.Prop"), Kind(0));
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "namespace foo { const bar : Prop }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace command parses");
        let Cmd::Namespace(namespace_cmd) = cmd else {
            panic!("expected namespace command");
        };
        assert_eq!(namespace_cmd.path, path("foo"));
        assert_eq!(namespace_cmd.cmds.len(), 1);
        let Cmd::Const(inner) = &namespace_cmd.cmds[0] else {
            panic!("expected const command");
        };
        assert_eq!(inner.name, qualified("foo.bar"));
    }

    #[test]
    fn namespace_qualified_declaration_creates_child_path() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(qualified("Type"), Kind(0));
        type_consts.insert(qualified("foo.bar.Prop"), Kind(0));
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "namespace foo.bar { const qux.quux : Prop }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace command parses");
        let Cmd::Namespace(namespace_cmd) = cmd else {
            panic!("expected namespace command");
        };
        assert_eq!(namespace_cmd.path, path("foo.bar"));
        assert_eq!(namespace_cmd.cmds.len(), 1);
        let Cmd::Const(inner) = &namespace_cmd.cmds[0] else {
            panic!("expected const command");
        };
        assert_eq!(inner.name, qualified("foo.bar.qux.quux"));
    }

    #[test]
    fn qualified_def_at_top_level_creates_missing_namespace() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "def qux.quux : Prop := p",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("def command parses");
        let Cmd::Def(def_cmd) = cmd else {
            panic!("expected def command");
        };
        assert_eq!(def_cmd.name, qualified("qux.quux"));
    }

    #[test]
    fn namespace_qualified_def_creates_missing_namespace_under_current() {
        let (tt, mut type_consts, mut consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(qualified("foo.Prop"), Kind(0));
        insert_prop_const(&mut consts, "foo.p");
        let mut use_table: HashMap<Name, QualifiedName> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "namespace foo { def qux.quux : Prop := p }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace command parses");
        let Cmd::Namespace(namespace_cmd) = cmd else {
            panic!("expected namespace command");
        };
        assert_eq!(namespace_cmd.path, path("foo"));
        assert_eq!(namespace_cmd.cmds.len(), 1);
        let Cmd::Def(def_cmd) = &namespace_cmd.cmds[0] else {
            panic!("expected def command");
        };
        assert_eq!(def_cmd.name, qualified("foo.qux.quux"));
    }
}
