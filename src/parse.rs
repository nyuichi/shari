use crate::cmd::{
    ClassInstanceDef, ClassInstanceField, ClassInstanceLemma, ClassStructureAxiom,
    ClassStructureConst, ClassStructureField, Cmd, CmdAxiom, CmdClassInstance, CmdClassStructure,
    CmdConst, CmdDef, CmdInductive, CmdInfix, CmdInfixl, CmdInfixr, CmdInstance, CmdLemma,
    CmdNamespaceStart, CmdNofix, CmdPrefix, CmdStructure, CmdTypeConst, CmdTypeDef,
    CmdTypeInductive, CmdTypeInfix, CmdTypeInfixl, CmdTypeInfixr, CmdTypeNofix, CmdTypePrefix,
    CmdUse, Fixity, InductiveConstructor, InstanceDef, InstanceField, InstanceLemma, Namespace,
    Operator, Path, StructureAxiom, StructureConst, StructureField, TypeInductiveConstructor,
    UseDecl,
};
use crate::proof::{
    Axiom, Expr, LocalStructureAxiom, LocalStructureConst, LocalStructureField, count_forall,
    generalize, guard, mk_expr_app, mk_expr_assume, mk_expr_assump, mk_expr_change, mk_expr_const,
    mk_expr_inst, mk_expr_let_structure, mk_expr_let_term, mk_expr_local, mk_expr_take,
};
use crate::tt::{
    Class, ClassType, Const, GlobalId, Id, Kind, Local, LocalType, Name, Term, Type, mk_const,
    mk_fresh_hole, mk_fresh_type_hole, mk_instance_hole, mk_local, mk_type_arrow, mk_type_const,
    mk_type_local,
};

use crate::lex::{Lex, LexError, LexState, Span, Token, TokenKind};
use anyhow::bail;
use std::collections::HashMap;
use std::iter::zip;
use std::sync::{Arc, LazyLock};
use std::{mem, slice};
use thiserror::Error;

fn global_id(value: &str) -> GlobalId {
    GlobalId::from_name(Name::from_str(value))
}

#[derive(Default, Debug, Clone)]
pub struct TokenTable {
    led: HashMap<String, Operator>,
    nud: HashMap<String, Operator>,
    type_led: HashMap<String, Operator>,
    type_nud: HashMap<String, Operator>,
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

    pub fn add_type(&mut self, op: Operator) -> anyhow::Result<()> {
        match op.fixity {
            Fixity::Infix | Fixity::Infixl | Fixity::Infixr => {
                let sym = op.symbol.clone();
                if self.type_led.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
            Fixity::Nofix | Fixity::Prefix => {
                let sym = op.symbol.clone();
                if self.type_nud.insert(sym, op).is_some() {
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
    fn name(self) -> GlobalId {
        static FST: LazyLock<GlobalId> = LazyLock::new(|| global_id("fst"));
        static SND: LazyLock<GlobalId> = LazyLock::new(|| global_id("snd"));

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
            TokenKind::Field => Some(Led::App),
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
            TokenKind::Field => Some(Nud::Var),
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

    fn get_type_led(&self, token: &Token) -> Option<Operator> {
        match token.kind {
            TokenKind::Symbol => self.type_led.get(token.as_str()).cloned(),
            _ => None,
        }
    }

    fn get_type_nud(&self, token: &Token) -> Option<Operator> {
        match token.kind {
            TokenKind::Ident | TokenKind::Symbol => self.type_nud.get(token.as_str()).cloned(),
            TokenKind::Field | TokenKind::NumLit | TokenKind::Keyword => None,
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
struct LocalConst {
    id: Id,
    name: QualifiedName,
}

#[derive(Debug, Clone)]
struct LocalAxiom {
    id: Id,
    target: Term,
}

#[derive(Debug, Clone)]
struct LocalBinding {
    id: Id,
    name: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct QualifiedName {
    is_absolute: bool,
    names: Vec<Name>,
}

impl QualifiedName {
    fn from_token(token: &Token) -> Self {
        match token.kind {
            TokenKind::Ident => Self {
                is_absolute: false,
                names: vec![Name::from_str(token.as_str())],
            },
            TokenKind::Field => Self {
                is_absolute: true,
                names: vec![Name::from_str(
                    token
                        .as_str()
                        .strip_prefix('.')
                        .expect("field token must start with '.'"),
                )],
            },
            _ => unreachable!("qualified_name token must be an identifier or field"),
        }
    }

    fn from_name(name: Name) -> Self {
        Self {
            is_absolute: false,
            names: vec![name],
        }
    }

    fn from_path(path: &Path) -> Self {
        Self {
            is_absolute: true,
            names: path.names().to_vec(),
        }
    }

    fn extend(&self, name: Name) -> Self {
        let mut names = self.names.clone();
        names.push(name);
        Self {
            is_absolute: self.is_absolute,
            names,
        }
    }

    fn last(&self) -> &Name {
        self.names
            .last()
            .expect("qualified name must have at least one segment")
    }

    fn as_name(&self) -> Option<&Name> {
        if !self.is_absolute && self.names.len() == 1 {
            self.names.first()
        } else {
            None
        }
    }
}

// TODO: instance lemma の中で hole を作ると引数にそれまでの instance def が入っちゃって後々 elab で const に置き換えられるので無駄。あと instance 自体の引数が2回ぐらい hole の引数に入ってしまうバグがありそう。
pub struct Parser<'a> {
    lex: &'a mut Lex,
    tt: &'a TokenTable,
    namespace_table: &'a HashMap<Path, Namespace>,
    current_namespace: &'a Path,
    type_const_table: &'a HashMap<GlobalId, Kind>,
    type_def_table: &'a HashMap<GlobalId, CmdTypeDef>,
    const_table: &'a HashMap<GlobalId, Const>,
    axiom_table: &'a HashMap<GlobalId, Axiom>,
    class_predicate_table: &'a HashMap<GlobalId, ClassType>,
    structure_table: &'a HashMap<GlobalId, CmdStructure>,
    local_consts: Vec<LocalConst>,
    local_axioms: Vec<(QualifiedName, LocalAxiom)>,
    local_types: Vec<LocalBinding>,
    locals: Vec<LocalBinding>,
    this_ref: Option<(QualifiedName, Id)>,
    type_this_ref: Option<(QualifiedName, Id)>,
    holes: Vec<(Id, Type)>,
}

impl<'a> Parser<'a> {
    #[expect(clippy::too_many_arguments)]
    pub fn new(
        lex: &'a mut Lex,
        tt: &'a TokenTable,
        namespace_table: &'a HashMap<Path, Namespace>,
        current_namespace: &'a Path,
        type_const_table: &'a HashMap<GlobalId, Kind>,
        type_def_table: &'a HashMap<GlobalId, CmdTypeDef>,
        const_table: &'a HashMap<GlobalId, Const>,
        axiom_table: &'a HashMap<GlobalId, Axiom>,
        class_predicate_table: &'a HashMap<GlobalId, ClassType>,
        structure_table: &'a HashMap<GlobalId, CmdStructure>,
    ) -> Self {
        Self {
            lex,
            tt,
            namespace_table,
            current_namespace,
            type_const_table,
            type_def_table,
            const_table,
            axiom_table,
            class_predicate_table,
            structure_table,
            local_consts: vec![],
            local_axioms: vec![],
            local_types: vec![],
            locals: vec![],
            this_ref: None,
            type_this_ref: None,
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

    fn get_const(&self, id: &GlobalId) -> Option<&Const> {
        self.const_table.get(id)
    }

    fn get_local_const(&self, name: &QualifiedName) -> Option<&LocalConst> {
        self.local_consts
            .iter()
            .rev()
            .find(|local_const| &local_const.name == name)
    }

    fn get_local_axiom(&self, name: &QualifiedName) -> Option<&LocalAxiom> {
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

    fn get_local_type(&self, name: &Name) -> Option<Id> {
        self.local_types
            .iter()
            .rev()
            .find(|local| &local.name == name)
            .map(|local| local.id)
    }

    fn get_local(&self, name: &Name) -> Option<Id> {
        self.locals
            .iter()
            .rev()
            .find(|local| &local.name == name)
            .map(|local| local.id)
    }

    fn push_local_const(&mut self, name: QualifiedName, id: Id) {
        self.local_consts.push(LocalConst { id, name });
    }

    fn push_local_axiom(&mut self, name: QualifiedName, id: Id, target: Term) {
        self.local_axioms.push((name, LocalAxiom { id, target }));
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
        let mut name = QualifiedName::from_token(token);
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
            name = name.extend(Name::from_str(suffix));
        }
        name
    }

    fn resolve(&self, name: QualifiedName) -> Path {
        let mut path = if name.is_absolute {
            Path::root()
        } else {
            self.current_namespace.clone()
        };
        let mut names = name.names.into_iter();
        while let Some(name) = names.next() {
            let Some(namespace) = self.namespace_table.get(&path) else {
                path = path.extend(name);
                for tail in names {
                    path = path.extend(tail);
                }
                return path;
            };
            let Some(target) = namespace.use_table.get(&name) else {
                path = path.extend(name);
                for tail in names {
                    path = path.extend(tail);
                }
                return path;
            };
            path = target.clone();
        }
        path
    }

    fn global_reference_name(&mut self, token: Option<&Token>) -> Result<Path, ParseError> {
        let token = match token {
            Some(token) => token.clone(),
            None => {
                let token = self.any_token()?;
                if !token.is_ident() && !token.is_field() {
                    return Self::fail(token, "expected identifier");
                }
                token
            }
        };
        assert!(
            token.is_ident() || token.is_field(),
            "global reference token must be identifier or field"
        );
        let literal_name = self.qualified_name(&token);
        Ok(self.resolve(literal_name))
    }

    fn global_declaration_name(&mut self, token: Option<&Token>) -> Result<Path, ParseError> {
        let token = match token {
            Some(token) => token.clone(),
            None => self.any_token()?,
        };
        if token.is_field() {
            return Self::fail(token, "absolute path is not allowed in declaration head");
        }
        if !token.is_ident() {
            return Self::fail(token, "expected identifier");
        }
        let literal_name = self.qualified_name(&token);
        Ok(self.resolve(literal_name))
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

    fn type_var(&mut self, token: Token, entity: Option<GlobalId>) -> Result<Type, ParseError> {
        let name = match entity {
            Some(entity) => entity,
            None => {
                let name = self.qualified_name(&token);
                if !name.is_absolute {
                    if let Some(local_name) = name.as_name()
                        && let Some(id) = self.get_local_type(local_name)
                    {
                        return Ok(mk_type_local(id));
                    }
                    if let Some((_, stash)) =
                        self.type_this_ref.as_ref().and_then(|(this_name, stash)| {
                            if this_name == &name {
                                Some((this_name, stash))
                            } else {
                                None
                            }
                        })
                    {
                        return Ok(mk_type_local(*stash));
                    }
                }
                self.resolve(name).to_global_id()
            }
        };
        let args = if let Some(type_def) = self.type_def_table.get(&name) {
            let mut args = Vec::with_capacity(type_def.local_types.len());
            for _ in &type_def.local_types {
                args.push(self.subty(1024)?);
            }
            args
        } else {
            vec![]
        };
        if self.type_const_table.contains_key(&name) {
            let mut ty = mk_type_const(name);
            for arg in args {
                ty = ty.apply([arg]);
            }
            return Ok(ty);
        }
        if let Some(type_def) = self.type_def_table.get(&name).cloned() {
            if type_def.local_types.len() != args.len() {
                return Self::fail(token, "type notation target has wrong arity");
            }
            let subst = type_def
                .local_types
                .into_iter()
                .zip(args)
                .map(|(local_type, arg)| (local_type.id, arg))
                .collect::<Vec<_>>();
            return Ok(type_def.target.subst(&subst));
        }
        Self::fail(token, "unknown type constant")
    }

    fn type_primary(&mut self) -> Result<Type, ParseError> {
        let token = self.any_token()?;
        if token.is_symbol() && token.as_str() == "(" {
            let t = self.ty()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else if let Some(op) = self.tt.get_type_nud(&token) {
            match op.fixity {
                Fixity::Nofix => self.type_var(token, Some(op.entity)),
                Fixity::Prefix => {
                    let arg = self.subty(op.prec)?;
                    if self.type_const_table.contains_key(&op.entity) {
                        Ok(mk_type_const(op.entity).apply([arg]))
                    } else if let Some(type_def) = self.type_def_table.get(&op.entity).cloned() {
                        if type_def.local_types.len() != 1 {
                            Self::fail(token, "type notation target has wrong arity")
                        } else {
                            Ok(type_def.target.subst(&[(type_def.local_types[0].id, arg)]))
                        }
                    } else {
                        Self::fail(token, "unknown type constant")
                    }
                }
                Fixity::Infix | Fixity::Infixl | Fixity::Infixr => unreachable!(),
            }
        } else if token.is_ident() || token.is_field() {
            self.type_var(token, None)
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
            } else if let Some(op) = self.tt.get_type_led(&token) {
                if rbp >= op.prec {
                    break;
                }
                self.advance();
                let rhs_prec = match op.fixity {
                    Fixity::Infix | Fixity::Infixl => op.prec,
                    Fixity::Infixr => op.prec - 1,
                    Fixity::Nofix | Fixity::Prefix => unreachable!(),
                };
                let rhs = self.subty(rhs_prec)?;
                if self.type_const_table.contains_key(&op.entity) {
                    t = mk_type_const(op.entity).apply([t, rhs]);
                } else if let Some(type_def) = self.type_def_table.get(&op.entity).cloned() {
                    if type_def.local_types.len() != 2 {
                        return Self::fail(token, "type notation target has wrong arity");
                    }
                    t = type_def.target.subst(&[
                        (type_def.local_types[0].id, t),
                        (type_def.local_types[1].id, rhs),
                    ]);
                } else {
                    return Self::fail(token, "unknown type constant");
                }
                t = self.type_with_span(start, t);
            } else if token.is_ident()
                || token.is_field()
                || (token.is_symbol() && token.as_str() == "(")
                || self.tt.get_type_nud(&token).is_some()
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
        if !token.is_ident() && !token.is_field() {
            return Self::fail(token, "expected class name");
        }
        let id = self.global_reference_name(Some(&token))?.to_global_id();
        if !self.class_predicate_table.contains_key(&id) {
            return Self::fail(token, "unknown class");
        }
        let mut args = vec![];
        while let Some(t) = self.optional(|this| this.subty(1024)) {
            args.push(t);
        }
        Ok(Class { id, args })
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
            let id = Id::fresh();
            self.locals.push(LocalBinding {
                name: name.clone(),
                id,
            });
            binders.push(Local {
                id,
                name: Some(name),
                ty,
            });
        }
        let mut m = self.subterm(0)?;
        self.locals.truncate(self.locals.len() - binders.len());
        m = m.abs(&binders);
        Ok(m)
    }

    fn term_binder(&mut self, token: Token, binder: &GlobalId) -> Result<Term, ParseError> {
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
            let id = Id::fresh();
            self.locals.push(LocalBinding {
                name: name.clone(),
                id,
            });
            binders.push(Local {
                id,
                name: Some(name),
                ty,
            });
        }
        let mut m = self.subterm(0)?;
        self.locals.truncate(self.locals.len() - binders.len());
        for x in binders.into_iter().rev() {
            m = m.abs(slice::from_ref(&x));
            let f = mem::take(&mut m);
            m = mk_const(binder.clone(), vec![x.ty.clone()], vec![]);
            m = m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_sep(&mut self, _token: Token) -> Result<Term, ParseError> {
        let name = self.name()?;
        let ty;
        if let Some(_token) = self.expect_symbol_opt(":") {
            ty = self.ty()?;
        } else {
            ty = mk_fresh_type_hole();
        }
        self.expect_symbol("|")?;
        let id = Id::fresh();
        self.locals.push(LocalBinding {
            name: name.clone(),
            id,
        });
        let mut m = self.subterm(0)?;
        self.locals.pop();
        let x = Local {
            id,
            name: Some(name),
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
            global_id("pair"),
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

    fn term_var(&mut self, token: Token, entity: Option<GlobalId>) -> Result<Term, ParseError> {
        let name = match entity {
            Some(entity) => entity,
            None => {
                let name = self.qualified_name(&token);
                if !name.is_absolute {
                    if let Some(local_name) = name.as_name()
                        && let Some(id) = self.get_local(local_name)
                    {
                        return Ok(mk_local(id));
                    }
                    if let Some((_, stash)) =
                        self.this_ref.as_ref().and_then(|(this_name, stash)| {
                            if this_name == &name {
                                Some((this_name, stash))
                            } else {
                                None
                            }
                        })
                    {
                        return Ok(mk_local(*stash));
                    }
                    if let Some(local_const) = self.get_local_const(&name) {
                        return Ok(mk_local(local_const.id));
                    }
                }
                self.resolve(name).to_global_id()
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
            Nud::Forall => self.term_binder(token, &global_id("forall"))?,
            Nud::Exists => self.term_binder(token, &global_id("exists"))?,
            Nud::Uexists => self.term_binder(token, &global_id("uexists"))?,
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
        hole = hole.apply(self.locals.iter().map(|local| mk_local(local.id)));

        hole
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.subexpr(0)
    }

    fn expr_var(&mut self, token: Token, auto_inst: bool) -> Result<Expr, ParseError> {
        let name = self.qualified_name(&token);
        if !name.is_absolute
            && let Some(local_axiom) = self.get_local_axiom(&name)
        {
            let mut expr = mk_expr_local(local_axiom.id);
            if auto_inst {
                for _ in 0..count_forall(&local_axiom.target) {
                    expr = mk_expr_inst(expr, self.mk_term_hole());
                }
            }
            return Ok(expr);
        }
        let name = self.resolve(name).to_global_id();
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

    fn mk_have(m: Term, alias: Option<(Id, Name)>, e: Expr, body: Expr) -> Expr {
        mk_expr_app(mk_expr_assume(m, alias, body), e)
    }

    fn mk_obtain(
        &mut self,
        binder: Local,
        p: Term,
        alias: Option<(Id, Name)>,
        e1: Expr,
        e2: Expr,
    ) -> Expr {
        // Expand[obtain (x : τ), p := e1, e2] := exists.ind.{τ}[_, _] e1 (take (x : τ), assume p, e2)
        let e = mk_expr_const(global_id("exists.ind"), vec![binder.ty.clone()], vec![]);
        let e = mk_expr_inst(e, self.mk_term_hole());
        let e = mk_expr_inst(e, self.mk_term_hole());
        let e = mk_expr_app(e, e1);
        let e_body = mk_expr_assume(p, alias, e2);
        let e_body = mk_expr_take(binder.id, binder.name, binder.ty, e_body);
        mk_expr_app(e, e_body)
    }

    fn mk_eq(lhs: Term, rhs: Term) -> Term {
        let mut eq = mk_const(global_id("eq"), vec![mk_fresh_type_hole()], vec![]);
        eq = eq.apply([lhs, rhs]);
        eq
    }

    fn obtain_instance_expr(&mut self) -> Result<Expr, ParseError> {
        let obtain_start = self.lex.save();
        let local_name = self.name()?;
        self.expect_symbol(":")?;
        let ty_start = self.lex.save();
        let target_ty = self.ty()?;
        let Type::Const(structure_head) = target_ty.head() else {
            return Err(ParseError::Parse {
                message: "type of obtain instance must be a structure".to_string(),
                span: self.span_since(ty_start),
            });
        };
        let structure_name = structure_head.id.clone();
        let Some(cmd_structure) = self.structure_table.get(&structure_name).cloned() else {
            return Err(ParseError::Parse {
                message: "type of obtain instance must be a structure".to_string(),
                span: self.span_since(ty_start),
            });
        };

        self.expect_symbol(":=")?;
        self.expect_symbol("{")?;
        let local_const_len = self.local_consts.len();
        let local_axiom_len = self.local_axioms.len();
        let local_id = Id::fresh();
        let mut fields = vec![];
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "def" => {
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    let field_param_start = self.locals.len();
                    let field_params = field_params
                        .into_iter()
                        .map(|(field_param_name, field_param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    name: field_param_name.clone(),
                                    id,
                                });
                                id
                            },
                            name: Some(field_param_name),
                            ty: field_param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut field_ty = self.ty()?;
                    self.expect_symbol(":=")?;
                    let mut field_target = self.term()?;
                    self.locals.truncate(field_param_start);
                    for field_param in field_params.into_iter().rev() {
                        field_ty = field_ty.arrow([field_param.ty.clone()]);
                        field_target = field_target.abs(&[field_param]);
                    }
                    let field_id = Id::fresh();
                    self.push_local_const(QualifiedName::from_name(field_name.clone()), field_id);
                    fields.push(InstanceField::Def(InstanceDef {
                        field_id,
                        field_name: field_name.clone(),
                        id: Path::root()
                            .extend(local_name.clone())
                            .extend(field_name.clone())
                            .to_global_id(),
                        spec_id: Path::root()
                            .extend(local_name.clone())
                            .extend(field_name.clone())
                            .extend(Name::from_str("spec"))
                            .to_global_id(),
                        ty: field_ty,
                        target: field_target,
                    }));
                }
                "lemma" => {
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    let field_param_start = self.locals.len();
                    let field_params = field_params
                        .into_iter()
                        .map(|(field_param_name, field_param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    name: field_param_name.clone(),
                                    id,
                                });
                                id
                            },
                            name: Some(field_param_name),
                            ty: field_param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut field_target = self.term()?;
                    self.expect_symbol(":=")?;
                    let mut expr = self.expr()?;
                    self.locals.truncate(field_param_start);
                    field_target = generalize(&field_target, &field_params);
                    for field_param in field_params.into_iter().rev() {
                        expr = mk_expr_take(
                            field_param.id,
                            field_param.name.clone(),
                            field_param.ty,
                            expr,
                        );
                    }
                    let holes = self.holes.drain(..).collect();
                    let field_id = Id::fresh();
                    self.push_local_axiom(
                        QualifiedName::from_name(field_name.clone()),
                        field_id,
                        field_target.clone(),
                    );
                    fields.push(InstanceField::Lemma(InstanceLemma {
                        field_id,
                        field_name: field_name.clone(),
                        id: Path::root()
                            .extend(local_name.clone())
                            .extend(field_name.clone())
                            .to_global_id(),
                        target: field_target,
                        holes,
                        expr,
                    }));
                }
                _ => Self::fail(keyword, "unknown command in obtain instance")?,
            }
        }

        if cmd_structure.fields.len() != fields.len() {
            self.local_consts.truncate(local_const_len);
            self.local_axioms.truncate(local_axiom_len);
            return Err(ParseError::Parse {
                message: "number of fields mismatch".to_string(),
                span: self.span_since(obtain_start),
            });
        }
        for (structure_field, field) in zip(&cmd_structure.fields, &fields) {
            match (structure_field, field) {
                (
                    StructureField::Const(StructureConst {
                        field_name: structure_field_name,
                        ..
                    }),
                    InstanceField::Def(InstanceDef { field_name, .. }),
                )
                | (
                    StructureField::Axiom(StructureAxiom {
                        field_name: structure_field_name,
                        ..
                    }),
                    InstanceField::Lemma(InstanceLemma { field_name, .. }),
                ) => {
                    if structure_field_name != field_name {
                        self.local_consts.truncate(local_const_len);
                        self.local_axioms.truncate(local_axiom_len);
                        return Err(ParseError::Parse {
                            message: "field name mismatch".to_string(),
                            span: self.span_since(obtain_start),
                        });
                    }
                }
                (StructureField::Const(_), _) => {
                    self.local_consts.truncate(local_const_len);
                    self.local_axioms.truncate(local_axiom_len);
                    return Err(ParseError::Parse {
                        message: "definition expected".to_string(),
                        span: self.span_since(obtain_start),
                    });
                }
                (StructureField::Axiom(_), _) => {
                    self.local_consts.truncate(local_const_len);
                    self.local_axioms.truncate(local_axiom_len);
                    return Err(ParseError::Parse {
                        message: "lemma expected".to_string(),
                        span: self.span_since(obtain_start),
                    });
                }
            }
        }

        self.local_consts.truncate(local_const_len);
        self.local_axioms.truncate(local_axiom_len);
        self.expect_symbol(",")?;

        let body_local_const_len = self.local_consts.len();
        let body_local_axiom_len = self.local_axioms.len();
        self.locals.push(LocalBinding {
            name: local_name.clone(),
            id: local_id,
        });
        for field in &fields {
            match field {
                InstanceField::Def(InstanceDef {
                    field_id,
                    field_name,
                    ..
                }) => {
                    self.push_local_const(
                        QualifiedName::from_name(local_name.clone()).extend(field_name.clone()),
                        *field_id,
                    );
                }
                InstanceField::Lemma(InstanceLemma {
                    field_id,
                    field_name,
                    target,
                    ..
                }) => {
                    self.push_local_axiom(
                        QualifiedName::from_name(local_name.clone()).extend(field_name.clone()),
                        *field_id,
                        target.clone(),
                    );
                }
            }
        }
        let body = match self.expr() {
            Ok(body) => body,
            Err(err) => {
                self.local_axioms.truncate(body_local_axiom_len);
                self.local_consts.truncate(body_local_const_len);
                self.locals.pop();
                return Err(err);
            }
        };
        self.local_axioms.truncate(body_local_axiom_len);
        self.local_consts.truncate(body_local_const_len);
        self.locals.pop();

        let mut type_subst = Vec::with_capacity(cmd_structure.local_types.len());
        for (x, t) in zip(&cmd_structure.local_types, target_ty.args()) {
            type_subst.push((x.id, t.clone()));
        }

        let mut char_terms = vec![];
        for (structure_field, field) in zip(&cmd_structure.fields, &fields) {
            let (
                StructureField::Const(StructureConst { id, ty, .. }),
                InstanceField::Def(InstanceDef { field_id, .. }),
            ) = (structure_field, field)
            else {
                continue;
            };
            let mut rhs = mk_const(
                id.clone(),
                target_ty.args().into_iter().cloned().collect(),
                vec![],
            );
            rhs = rhs.apply([mk_local(local_id)]);
            let mut char_term = mk_const(global_id("eq"), vec![ty.subst(&type_subst)], vec![]);
            char_term = char_term.apply([mk_local(*field_id), rhs]);
            char_terms.push(char_term);
        }
        let char_prop = char_terms
            .into_iter()
            .reduce(|left, right| {
                let mut and = mk_const(global_id("and"), vec![], vec![]);
                and = and.apply([left, right]);
                and
            })
            .unwrap_or_else(|| mk_const(global_id("true"), vec![], vec![]));

        let this = Local {
            id: Id::fresh(),
            name: Some(Name::from_str("this")),
            ty: target_ty.clone(),
        };
        let mut abs_char_terms = vec![];
        for (structure_field, field) in zip(&cmd_structure.fields, &fields) {
            let (
                StructureField::Const(StructureConst { id, ty, .. }),
                InstanceField::Def(InstanceDef { field_id, .. }),
            ) = (structure_field, field)
            else {
                continue;
            };
            let mut rhs = mk_const(
                id.clone(),
                target_ty.args().into_iter().cloned().collect(),
                vec![],
            );
            rhs = rhs.apply([mk_local(this.id)]);
            let mut char_term = mk_const(global_id("eq"), vec![ty.subst(&type_subst)], vec![]);
            char_term = char_term.apply([mk_local(*field_id), rhs]);
            abs_char_terms.push(char_term);
        }
        let abs_char = abs_char_terms
            .into_iter()
            .reduce(|left, right| {
                let mut and = mk_const(global_id("and"), vec![], vec![]);
                and = and.apply([left, right]);
                and
            })
            .unwrap_or_else(|| mk_const(global_id("true"), vec![], vec![]))
            .abs(slice::from_ref(&this));

        let mut abs_expr = mk_expr_const(
            cmd_structure.abs_id.clone(),
            target_ty.args().into_iter().cloned().collect(),
            vec![],
        );
        for (structure_field, field) in zip(&cmd_structure.fields, &fields) {
            let (
                StructureField::Const(StructureConst { .. }),
                InstanceField::Def(InstanceDef { field_id, .. }),
            ) = (structure_field, field)
            else {
                continue;
            };
            abs_expr = mk_expr_inst(abs_expr, mk_local(*field_id));
        }
        for (structure_field, field) in zip(&cmd_structure.fields, &fields) {
            let (
                StructureField::Axiom(StructureAxiom { .. }),
                InstanceField::Lemma(InstanceLemma { field_id, .. }),
            ) = (structure_field, field)
            else {
                continue;
            };
            abs_expr = mk_expr_app(abs_expr, mk_expr_local(*field_id));
        }

        let mut exists_expr =
            mk_expr_const(global_id("uexists.exists"), vec![target_ty.clone()], vec![]);
        exists_expr = mk_expr_inst(exists_expr, abs_char);
        let witness = mk_expr_app(exists_expr, abs_expr);

        let mut expr = self.mk_obtain(
            Local {
                id: local_id,
                name: Some(local_name.clone()),
                ty: target_ty,
            },
            char_prop,
            None,
            witness,
            body,
        );
        for field in fields.into_iter().rev() {
            expr = match field {
                InstanceField::Def(InstanceDef {
                    field_id,
                    id,
                    ty,
                    target,
                    ..
                }) => mk_expr_let_term(
                    field_id,
                    Some(Name::from_str(&id.to_string())),
                    Some(ty),
                    target,
                    expr,
                ),
                InstanceField::Lemma(InstanceLemma {
                    field_id,
                    id,
                    target,
                    expr: proof,
                    ..
                }) => Self::mk_have(
                    target,
                    Some((field_id, Name::from_str(&id.to_string()))),
                    proof,
                    expr,
                ),
            };
        }
        Ok(expr)
    }

    fn mk_eq_trans(&mut self, e1: Expr, e2: Expr) -> Expr {
        let id = global_id("eq.trans");
        let ty_args = vec![mk_fresh_type_hole()];
        let instances = vec![];
        let mut eq_trans = mk_expr_const(id, ty_args, instances);
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
        let name = Name::from_str(ident.as_str());
        if let Some(token) = self.peek_opt()
            && token.is_ident()
        {
            return Self::fail(token, "local type parameters are not allowed");
        }
        let structure_name = QualifiedName::from_name(name.clone());
        self.expect_symbol(":=")?;
        self.expect_symbol("{")?;
        let mut fields = vec![];
        let mut num_consts = 0;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "const" => {
                    let field_name = self.name()?;
                    if fields.iter().any(|field| match field {
                        LocalStructureField::Const(field) => field.field_name == field_name,
                        LocalStructureField::Axiom(field) => field.field_name == field_name,
                    }) {
                        return Self::fail(keyword, "duplicate field");
                    }
                    self.expect_symbol(":")?;
                    let field_ty = self.ty()?;
                    let bare_id = Id::fresh();
                    self.locals.push(LocalBinding {
                        name: field_name.clone(),
                        id: bare_id,
                    });
                    let id = Id::fresh();
                    let qualified_name = structure_name.extend(field_name.clone());
                    let name = Name::from_str(
                        &qualified_name
                            .names
                            .iter()
                            .map(Name::as_str)
                            .collect::<Vec<_>>()
                            .join("."),
                    );
                    fields.push(LocalStructureField::Const(LocalStructureConst {
                        field_id: bare_id,
                        id,
                        field_name,
                        name,
                        ty: field_ty,
                    }));
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    if fields.iter().any(|field| match field {
                        LocalStructureField::Const(field) => field.field_name == field_name,
                        LocalStructureField::Axiom(field) => field.field_name == field_name,
                    }) {
                        return Self::fail(keyword, "duplicate field");
                    }
                    let params = self.typed_parameters()?;
                    let params_start = self.locals.len();
                    let params = params
                        .into_iter()
                        .map(|(param_name, param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    id,
                                    name: param_name.clone(),
                                });
                                id
                            },
                            name: Some(param_name),
                            ty: param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(params_start);
                    target = generalize(&target, &params);
                    let id = Id::fresh();
                    fields.push(LocalStructureField::Axiom(LocalStructureAxiom {
                        id,
                        field_name,
                        target,
                    }))
                }
                _ => return Self::fail(keyword, "expected const or axiom"),
            }
        }
        self.locals.truncate(self.locals.len() - num_consts);
        self.expect_symbol(",")?;

        let structure_id = Id::fresh();
        self.local_types.push(LocalBinding {
            id: structure_id,
            name: name.clone(),
        });
        let this_ty = mk_type_local(structure_id);
        let this = Local {
            id: Id::fresh(),
            name: Some(Name::from_str("this")),
            ty: this_ty.clone(),
        };
        let mut local_consts = vec![];
        let mut local_axioms = vec![];
        let mut subst = vec![];
        for field in &fields {
            match field {
                LocalStructureField::Const(LocalStructureConst {
                    field_id,
                    field_name,
                    id,
                    ty: _,
                    ..
                }) => {
                    let fullname = structure_name.extend(field_name.clone());
                    local_consts.push(LocalConst {
                        id: *id,
                        name: fullname.clone(),
                    });
                    let mut target = mk_local(*id);
                    target = target.apply([mk_local(this.id)]);
                    subst.push((*field_id, target));
                }
                LocalStructureField::Axiom(LocalStructureAxiom {
                    id,
                    field_name,
                    target,
                }) => {
                    let fullname = structure_name.extend(field_name.clone());
                    let mut target = target.clone();
                    target = target.subst(&subst);
                    target = generalize(&target, slice::from_ref(&this));
                    local_axioms.push((fullname, LocalAxiom { id: *id, target }));
                }
            }
        }

        let abs_name = structure_name.extend(Name::from_str("abs"));
        let abs_id = Id::fresh();
        let mut params = vec![];
        let mut guards = vec![];
        let mut chars = vec![];
        let mut abs_subst = vec![];
        for field in &fields {
            match field {
                LocalStructureField::Const(LocalStructureConst {
                    field_id, id, ty, ..
                }) => {
                    let param = Local {
                        id: *field_id,
                        name: None,
                        ty: ty.clone(),
                    };
                    let mut rhs = mk_local(*id);
                    rhs = rhs.apply([mk_local(this.id)]);

                    let mut char = mk_const(global_id("eq"), vec![ty.clone()], vec![]);
                    char = char.apply([mk_local(param.id), rhs]);
                    chars.push(char);
                    abs_subst.push((*field_id, mk_local(param.id)));
                    params.push(param);
                }
                LocalStructureField::Axiom(LocalStructureAxiom { target, .. }) => {
                    let mut target = target.clone();
                    target = target.subst(&abs_subst);
                    guards.push(target);
                }
            }
        }

        let mut abs = mk_const(global_id("uexists"), vec![this_ty.clone()], vec![]);
        abs = abs.apply([{
            let mut char = chars
                .into_iter()
                .reduce(|left, right| {
                    let mut conj = mk_const(global_id("and"), vec![], vec![]);
                    conj = conj.apply([left, right]);
                    conj
                })
                .unwrap_or_else(|| mk_const(global_id("true"), vec![], vec![]));
            char = char.abs(slice::from_ref(&this));
            char
        }]);
        abs = guard(&abs, guards);
        abs = generalize(&abs, &params);
        local_axioms.push((
            abs_name,
            LocalAxiom {
                id: abs_id,
                target: abs,
            },
        ));

        let local_const_len = self.local_consts.len();
        let local_axiom_len = self.local_axioms.len();
        // These are visible while parsing `body` (e.g. `@foo.abs`),
        // and the target is needed to count implicit instantiations.
        self.local_consts.extend(local_consts);
        self.local_axioms.extend(local_axioms);
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
        Ok(mk_expr_let_structure(
            structure_id,
            name,
            abs_id,
            fields,
            body,
        ))
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
        let id = Id::fresh();
        self.push_local_const(QualifiedName::from_name(name.clone()), id);
        let body = match self.expr() {
            Ok(body) => body,
            Err(err) => {
                self.local_consts.truncate(local_const_len);
                return Err(err);
            }
        };
        self.local_consts.truncate(local_const_len);
        Ok(mk_expr_let_term(id, Some(name), ty, value, body))
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
                let token = self.any_token()?;
                if !token.is_ident() && !token.is_field() {
                    return Self::fail(token, "expected identifier");
                }
                let expr = self.expr_var(token, false)?;
                break 'left expr;
            }
            let token = self.any_token()?;
            if !token.is_ident() && !token.is_field() {
                return Self::fail(token, "expected identifier");
            }
            if token.is_field() {
                break 'left self.expr_var(token, true)?;
            }
            match token.as_str() {
                "assume" => {
                    let m = self.term()?;
                    let alias = self.alias_opt()?;
                    self.expect_symbol(",")?;
                    let local_axioms_len = self.local_axioms.len();
                    let alias_id = alias
                        .as_ref()
                        .map(|alias_name| (Id::fresh(), alias_name.clone()));
                    if let Some(alias_name) = &alias {
                        self.push_local_axiom(
                            QualifiedName::from_name(alias_name.clone()),
                            alias_id.as_ref().expect("alias id exists").0,
                            m.clone(),
                        );
                    }
                    let expr = match self.expr() {
                        Ok(expr) => expr,
                        Err(err) => {
                            self.local_axioms.truncate(local_axioms_len);
                            return Err(err);
                        }
                    };
                    self.local_axioms.truncate(local_axioms_len);
                    mk_expr_assume(m, alias_id, expr)
                }
                "take" => {
                    self.expect_symbol("(")?;
                    let local_name = self.name()?;
                    self.expect_symbol(":")?;
                    let ty = self.ty()?;
                    self.expect_symbol(")")?;
                    self.expect_symbol(",")?;
                    let local_id = Id::fresh();
                    self.locals.push(LocalBinding {
                        name: local_name.clone(),
                        id: local_id,
                    });
                    let e = self.expr()?;
                    self.locals.pop();
                    mk_expr_take(local_id, Some(local_name), ty, e)
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
                    let alias_id = alias
                        .as_ref()
                        .map(|alias_name| (Id::fresh(), alias_name.clone()));
                    if let Some(alias_name) = &alias {
                        self.push_local_axiom(
                            QualifiedName::from_name(alias_name.clone()),
                            alias_id.as_ref().expect("alias id exists").0,
                            m.clone(),
                        );
                    }
                    let e2 = match self.expr() {
                        Ok(expr) => expr,
                        Err(err) => {
                            self.local_axioms.truncate(local_axioms_len);
                            return Err(err);
                        }
                    };
                    self.local_axioms.truncate(local_axioms_len);
                    Self::mk_have(m, alias_id, e1, e2)
                }
                "obtain" => {
                    if self
                        .peek_opt()
                        .is_some_and(|token| token.is_keyword() && token.as_str() == "instance")
                    {
                        self.advance();
                        break 'left self.obtain_instance_expr()?;
                    }
                    self.expect_symbol("(")?;
                    let local_name = self.name()?;
                    self.expect_symbol(":")?;
                    let ty = self.ty()?;
                    self.expect_symbol(")")?;
                    self.expect_symbol(",")?;
                    let local_id = Id::fresh();
                    self.locals.push(LocalBinding {
                        name: local_name.clone(),
                        id: local_id,
                    });
                    let p = self.term()?;
                    self.locals.pop();
                    let alias = self.alias_opt()?;
                    self.expect_symbol(":=")?;
                    let e1 = self.expr()?;
                    self.expect_symbol(",")?;
                    self.locals.push(LocalBinding {
                        name: local_name.clone(),
                        id: local_id,
                    });
                    let local_axioms_len = self.local_axioms.len();
                    let alias_id = alias
                        .as_ref()
                        .map(|alias_name| (Id::fresh(), alias_name.clone()));
                    if let Some(alias_name) = &alias {
                        self.push_local_axiom(
                            QualifiedName::from_name(alias_name.clone()),
                            alias_id.as_ref().expect("alias id exists").0,
                            p.clone(),
                        );
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
                    self.mk_obtain(
                        Local {
                            id: local_id,
                            name: Some(local_name),
                            ty,
                        },
                        p,
                        alias_id,
                        e1,
                        e2,
                    )
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
                    || token.is_field()
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
                    if local_types.iter().any(|name: &Name| name == &tv) {
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
        if let Some(_token) = self.expect_symbol_opt("}") {
            return Ok(Cmd::BlockEnd);
        }
        let keyword = self.keyword()?;
        let cmd = match keyword.as_str() {
            "namespace" => {
                let namespace_cmd = self.namespace_cmd(keyword)?;
                Cmd::NamespaceStart(namespace_cmd)
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
                    "infixr" => {
                        let type_infixr_cmd = self.type_infixr_cmd(keyword)?;
                        Cmd::TypeInfixr(type_infixr_cmd)
                    }
                    "infixl" => {
                        let type_infixl_cmd = self.type_infixl_cmd(keyword)?;
                        Cmd::TypeInfixl(type_infixl_cmd)
                    }
                    "infix" => {
                        let type_infix_cmd = self.type_infix_cmd(keyword)?;
                        Cmd::TypeInfix(type_infix_cmd)
                    }
                    "prefix" => {
                        let type_prefix_cmd = self.type_prefix_cmd(keyword)?;
                        Cmd::TypePrefix(type_prefix_cmd)
                    }
                    "nofix" => {
                        let type_nofix_cmd = self.type_nofix_cmd(keyword)?;
                        Cmd::TypeNofix(type_nofix_cmd)
                    }
                    "const" => {
                        let type_const_cmd = self.type_const_cmd(keyword)?;
                        Cmd::TypeConst(type_const_cmd)
                    }
                    "def" => {
                        let type_def_cmd = self.type_def_cmd(keyword)?;
                        Cmd::TypeDef(type_def_cmd)
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

    fn namespace_cmd(&mut self, _token: Token) -> Result<CmdNamespaceStart, ParseError> {
        let path = self.global_reference_name(None)?;
        self.expect_symbol("{")?;
        Ok(CmdNamespaceStart { path })
    }

    fn use_group(
        &mut self,
        base: &Path,
        prefix: Option<&QualifiedName>,
        decls: &mut Vec<UseDecl>,
    ) -> Result<(), ParseError> {
        if self.expect_symbol_opt("}").is_some() {
            return Ok(());
        }
        loop {
            self.use_entry(base, prefix, true, decls)?;
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
        base: &Path,
        prefix: Option<&QualifiedName>,
        in_group: bool,
        decls: &mut Vec<UseDecl>,
    ) -> Result<(), ParseError> {
        if self.expect_symbol_opt("{").is_some() {
            return self.use_group(base, prefix, decls);
        }
        let token = self.any_token()?;
        if !token.is_ident() && !token.is_field() {
            return Self::fail(token, "expected identifier");
        }
        if in_group && token.is_field() {
            return Self::fail(token, "absolute path is not allowed in use group");
        }
        let mut target = self.qualified_name(&token);
        if let Some(prefix) = prefix {
            debug_assert!(
                !target.is_absolute,
                "absolute suffixes are rejected before append"
            );
            let mut combined = prefix.clone();
            for name in target.names {
                combined = combined.extend(name);
            }
            target = combined;
        }
        if self.expect_symbol_opt(".{").is_some() {
            return self.use_group(base, Some(&target), decls);
        }
        let alias = self.alias_opt()?.unwrap_or_else(|| target.last().clone());
        let target = if target.is_absolute {
            self.resolve(target)
        } else {
            let mut qualified = QualifiedName::from_path(base);
            for name in target.names {
                qualified = qualified.extend(name);
            }
            self.resolve(qualified)
        };
        decls.push(UseDecl { alias, target });
        Ok(())
    }

    fn use_cmd(&mut self, _token: Token) -> Result<CmdUse, ParseError> {
        let mut decls = vec![];
        if self.expect_symbol_opt(".{").is_some() {
            self.use_group(&Path::root(), None, &mut decls)?;
        } else if self.expect_symbol_opt("{").is_some() {
            let base = self.current_namespace.clone();
            self.use_group(&base, None, &mut decls)?;
        } else {
            let absolute = self.peek_opt().is_some_and(|token| token.is_field());
            let base = if absolute {
                Path::root()
            } else {
                self.current_namespace.clone()
            };
            self.use_entry(&base, None, false, &mut decls)?;
        }
        if let Some(token) = self.expect_symbol_opt(",") {
            return Self::fail(
                token,
                "comma-separated targets require braces; use 'use prod.{fst, snd}'",
            );
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
        let entity = self.global_reference_name(None)?.to_global_id();
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
        let entity = self.global_reference_name(None)?.to_global_id();
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
        let entity = self.global_reference_name(None)?.to_global_id();
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
        let entity = self.global_reference_name(None)?.to_global_id();
        Ok(CmdPrefix {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn nofix_cmd(&mut self, _token: Token) -> Result<CmdNofix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":=")?;
        let entity = self.global_reference_name(None)?.to_global_id();
        Ok(CmdNofix {
            op: op.as_str().to_owned(),
            entity,
        })
    }

    fn type_infixr_cmd(&mut self, _token: Token) -> Result<CmdTypeInfixr, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.global_reference_name(None)?.to_global_id();
        Ok(CmdTypeInfixr {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn type_infixl_cmd(&mut self, _token: Token) -> Result<CmdTypeInfixl, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.global_reference_name(None)?.to_global_id();
        Ok(CmdTypeInfixl {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn type_infix_cmd(&mut self, _token: Token) -> Result<CmdTypeInfix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.global_reference_name(None)?.to_global_id();
        Ok(CmdTypeInfix {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn type_prefix_cmd(&mut self, _token: Token) -> Result<CmdTypePrefix, ParseError> {
        let op = self.symbol()?;
        self.expect_symbol(":")?;
        let prec_token = self.num_lit()?;
        let prec = prec_token
            .as_str()
            .parse::<usize>()
            .expect("numeral literal too big");
        self.expect_symbol(":=")?;
        let entity = self.global_reference_name(None)?.to_global_id();
        Ok(CmdTypePrefix {
            op: op.as_str().to_owned(),
            prec,
            entity,
        })
    }

    fn type_nofix_cmd(&mut self, _token: Token) -> Result<CmdTypeNofix, ParseError> {
        let op = self.any_token()?;
        if !op.is_ident() && !op.is_symbol() {
            return Self::fail(op, "expected type operator");
        }
        self.expect_symbol(":=")?;
        let entity = self.global_reference_name(None)?.to_global_id();
        Ok(CmdTypeNofix {
            op: op.as_str().to_owned(),
            entity,
        })
    }

    fn def_cmd(&mut self, _token: Token) -> Result<CmdDef, ParseError> {
        let id = self.global_declaration_name(None)?.to_global_id();
        let local_types = self.local_type_parameters()?;
        let local_types = local_types
            .into_iter()
            .map(|name| {
                let id = Id::fresh();
                self.local_types.push(LocalBinding {
                    id,
                    name: name.clone(),
                });
                LocalType {
                    id,
                    name: Some(name),
                }
            })
            .collect::<Vec<_>>();
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        let params_start = self.locals.len();
        let params = params
            .into_iter()
            .map(|(param_name, param_ty)| Local {
                id: {
                    let id = Id::fresh();
                    self.locals.push(LocalBinding {
                        name: param_name.clone(),
                        id,
                    });
                    id
                },
                name: Some(param_name),
                ty: param_ty,
            })
            .collect::<Vec<_>>();
        self.expect_symbol(":")?;
        let mut t = self.ty()?;
        self.expect_symbol(":=")?;
        let mut m = self.term()?;
        // Parsing finished.
        self.locals.truncate(params_start);
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        for param in params.into_iter().rev() {
            t = t.arrow([param.ty.clone()]);
            m = m.abs(&[param]);
        }
        Ok(CmdDef {
            id,
            local_types,
            local_classes,
            ty: t,
            target: m,
        })
    }

    fn axiom_cmd(&mut self, _token: Token) -> Result<CmdAxiom, ParseError> {
        let id = self.global_declaration_name(None)?.to_global_id();
        let local_types = self.local_type_parameters()?;
        let local_types = local_types
            .into_iter()
            .map(|name| {
                let id = Id::fresh();
                self.local_types.push(LocalBinding {
                    name: name.clone(),
                    id,
                });
                LocalType {
                    id,
                    name: Some(name),
                }
            })
            .collect::<Vec<_>>();
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        let params_start = self.locals.len();
        let params = params
            .into_iter()
            .map(|(param_name, param_ty)| Local {
                id: {
                    let id = Id::fresh();
                    self.locals.push(LocalBinding {
                        name: param_name.clone(),
                        id,
                    });
                    id
                },
                name: Some(param_name),
                ty: param_ty,
            })
            .collect::<Vec<_>>();
        self.expect_symbol(":")?;
        let mut target = self.term()?;
        // Parsing finished.
        self.locals.truncate(params_start);
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        target = generalize(&target, &params);
        Ok(CmdAxiom {
            id,
            local_types,
            local_classes,
            target,
        })
    }

    fn lemma_cmd(&mut self, _token: Token) -> Result<CmdLemma, ParseError> {
        let id = self.global_declaration_name(None)?.to_global_id();
        let local_types = self.local_type_parameters()?;
        let local_types = local_types
            .into_iter()
            .map(|name| {
                let id = Id::fresh();
                self.local_types.push(LocalBinding {
                    name: name.clone(),
                    id,
                });
                LocalType {
                    id,
                    name: Some(name),
                }
            })
            .collect::<Vec<_>>();
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        let params_start = self.locals.len();
        let params = params
            .into_iter()
            .map(|(param_name, param_ty)| Local {
                id: {
                    let id = Id::fresh();
                    self.locals.push(LocalBinding {
                        name: param_name.clone(),
                        id,
                    });
                    id
                },
                name: Some(param_name),
                ty: param_ty,
            })
            .collect::<Vec<_>>();
        self.expect_symbol(":")?;
        let mut p = self.term()?;
        self.expect_symbol(":=")?;
        let mut e = self.expr()?;
        // Parsing finished.
        self.locals.truncate(params_start);
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        p = generalize(&p, &params);
        for param in params.into_iter().rev() {
            e = mk_expr_take(param.id, param.name.clone(), param.ty, e);
        }
        let holes = self.holes.drain(..).collect();
        Ok(CmdLemma {
            id,
            local_types,
            local_classes,
            target: p,
            holes,
            expr: e,
        })
    }

    fn const_cmd(&mut self, _token: Token) -> Result<CmdConst, ParseError> {
        let id = self.global_declaration_name(None)?.to_global_id();
        let local_types = self.local_type_parameters()?;
        let local_types = local_types
            .into_iter()
            .map(|name| {
                let id = Id::fresh();
                self.local_types.push(LocalBinding {
                    name: name.clone(),
                    id,
                });
                LocalType {
                    id,
                    name: Some(name),
                }
            })
            .collect::<Vec<_>>();
        let local_classes = self.local_class_parameters()?;
        self.expect_symbol(":")?;
        let t = self.ty()?;
        // Parsing finished.
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdConst {
            id,
            local_types,
            local_classes,
            ty: t,
        })
    }

    fn type_const_cmd(&mut self, _token: Token) -> Result<CmdTypeConst, ParseError> {
        let id = self.global_declaration_name(None)?.to_global_id();
        self.expect_symbol(":")?;
        let kind = self.kind()?;
        Ok(CmdTypeConst { id, kind })
    }

    fn type_def_cmd(&mut self, _token: Token) -> Result<CmdTypeDef, ParseError> {
        let id = self.global_declaration_name(None)?.to_global_id();
        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let local_type = Name::from_str(token.as_str());
            if local_types
                .iter()
                .any(|binding: &LocalBinding| binding.name == local_type)
            {
                return Self::fail(token, "duplicate type variable");
            }
            let id = Id::fresh();
            self.local_types.push(LocalBinding {
                id,
                name: local_type.clone(),
            });
            local_types.push(LocalBinding {
                id,
                name: local_type,
            });
        }
        self.expect_symbol(":=")?;
        let target = self.ty()?;
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdTypeDef {
            id,
            local_types: local_types
                .iter()
                .map(|binding| LocalType {
                    id: binding.id,
                    name: Some(binding.name.clone()),
                })
                .collect(),
            target,
        })
    }

    fn type_inductive_cmd(&mut self, _token: Token) -> Result<CmdTypeInductive, ParseError> {
        let token = self.ident()?;
        let state = self.lex.save();
        let literal_name = self.qualified_name(&token);
        self.lex.restore(state);
        let name = self.global_declaration_name(Some(&token))?;
        let id = name.to_global_id();
        let this_name = name
            .names()
            .last()
            .expect("declaration path must not be root")
            .clone();
        let this = Id::fresh();
        debug_assert!(
            self.type_this_ref.is_none(),
            "nested type inductive definitions are not supported"
        );
        self.type_this_ref = Some((literal_name, this));

        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let tv = Name::from_str(token.as_str());
            if local_types
                .iter()
                .any(|binding: &LocalBinding| binding.name == tv)
            {
                return Self::fail(token, "duplicate type variable")?;
            }
            let id = Id::fresh();
            self.local_types.push(LocalBinding {
                id,
                name: tv.clone(),
            });
            local_types.push(LocalBinding { id, name: tv });
        }
        let mut ctors: Vec<TypeInductiveConstructor> = vec![];
        while let Some(_token) = self.expect_symbol_opt("|") {
            let token = self.ident()?;
            let ctor_name = Name::from_str(token.as_str());
            for ctor in &ctors {
                if ctor_name == ctor.name {
                    return Self::fail(token, "duplicate constructor")?;
                }
            }
            self.expect_symbol(":")?;
            let ty = self.ty()?;
            ctors.push(TypeInductiveConstructor {
                ctor_id: name.clone().extend(ctor_name.clone()).to_global_id(),
                name: ctor_name.clone(),
                ctor_spec_id: name
                    .clone()
                    .extend(ctor_name.clone())
                    .extend(Name::from_str("spec"))
                    .to_global_id(),
                ty,
            })
        }
        // Parsing finished. We can now safely tear off.
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        self.type_this_ref = None;
        let ind_id = name.clone().extend(Name::from_str("ind")).to_global_id();
        let rec_id = name.extend(Name::from_str("rec")).to_global_id();
        Ok(CmdTypeInductive {
            id,
            this,
            this_name,
            local_types: local_types
                .iter()
                .map(|binding| LocalType {
                    id: binding.id,
                    name: Some(binding.name.clone()),
                })
                .collect(),
            ind_id,
            rec_id,
            ctors,
        })
    }

    fn inductive_cmd(&mut self, _token: Token) -> Result<CmdInductive, ParseError> {
        let ident = self.ident()?;
        let state = self.lex.save();
        let literal_name = self.qualified_name(&ident);
        self.lex.restore(state);
        let name = self.global_declaration_name(Some(&ident))?;
        let id = name.to_global_id();
        let this_name = name
            .names()
            .last()
            .expect("declaration path must not be root")
            .clone();
        let this = Id::fresh();
        debug_assert!(
            self.this_ref.is_none(),
            "nested inductive definitions are not supported"
        );
        self.this_ref = Some((literal_name, this));
        let local_types = self.local_type_parameters()?;
        let local_types = local_types
            .into_iter()
            .map(|name| {
                let id = Id::fresh();
                self.local_types.push(LocalBinding { id, name });
                LocalType {
                    id,
                    name: Some(
                        self.local_types
                            .last()
                            .expect("just pushed local type")
                            .name
                            .clone(),
                    ),
                }
            })
            .collect::<Vec<_>>();
        let params = self.typed_parameters()?;
        let params_start = self.locals.len();
        let params = params
            .into_iter()
            .map(|(param_name, param_ty)| Local {
                id: {
                    let id = Id::fresh();
                    self.locals.push(LocalBinding {
                        id,
                        name: param_name.clone(),
                    });
                    id
                },
                name: Some(param_name),
                ty: param_ty,
            })
            .collect::<Vec<_>>();
        self.expect_symbol(":")?;
        let target_ty = self.ty()?;
        let mut ctors: Vec<InductiveConstructor> = vec![];
        while let Some(_token) = self.expect_symbol_opt("|") {
            let token = self.ident()?;
            let ctor_name = Name::from_str(token.as_str());
            for ctor in &ctors {
                if ctor_name == ctor.name {
                    return Self::fail(token, "duplicate constructor")?;
                }
            }
            let ctor_params = self.typed_parameters()?;
            let ctor_params_start = self.locals.len();
            let ctor_params = ctor_params
                .into_iter()
                .map(|(ctor_param_name, ctor_param_ty)| Local {
                    id: {
                        let id = Id::fresh();
                        self.locals.push(LocalBinding {
                            id,
                            name: ctor_param_name.clone(),
                        });
                        id
                    },
                    name: Some(ctor_param_name),
                    ty: ctor_param_ty,
                })
                .collect::<Vec<_>>();
            self.expect_symbol(":")?;
            let mut target = self.term()?;
            self.locals.truncate(ctor_params_start);
            target = generalize(&target, &ctor_params);
            ctors.push(InductiveConstructor {
                ctor_id: name.clone().extend(ctor_name.clone()).to_global_id(),
                name: ctor_name.clone(),
                target,
            })
        }
        // Parsing finished.
        self.locals.truncate(params_start);
        self.this_ref = None;
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        let ind_id = name.extend(Name::from_str("ind")).to_global_id();
        Ok(CmdInductive {
            id,
            this,
            this_name,
            local_types,
            params,
            target_ty,
            ind_id,
            ctors,
        })
    }

    fn structure_cmd(&mut self, _token: Token) -> Result<CmdStructure, ParseError> {
        let name = self.global_declaration_name(None)?;
        let id = name.to_global_id();
        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let tv = Name::from_str(token.as_str());
            if local_types
                .iter()
                .any(|binding: &LocalBinding| binding.name == tv)
            {
                return Self::fail(token, "duplicate type variable")?;
            }
            let id = Id::fresh();
            self.local_types.push(LocalBinding {
                name: tv.clone(),
                id,
            });
            local_types.push(LocalBinding { name: tv, id });
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
                    let field_id = Id::fresh();
                    let field_qualified_name =
                        name.clone().extend(field_name.clone()).to_global_id();
                    fields.push(StructureField::Const(StructureConst {
                        field_id,
                        field_name: field_name.clone(),
                        id: field_qualified_name,
                        ty: field_ty,
                    }));
                    self.locals.push(LocalBinding {
                        name: field_name.clone(),
                        id: field_id,
                    });
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    let params = self.typed_parameters()?;
                    let params_start = self.locals.len();
                    let params = params
                        .into_iter()
                        .map(|(param_name, param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    name: param_name.clone(),
                                    id,
                                });
                                id
                            },
                            name: Some(param_name),
                            ty: param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(params_start);
                    target = generalize(&target, &params);
                    let field_qualified_name =
                        name.clone().extend(field_name.clone()).to_global_id();
                    fields.push(StructureField::Axiom(StructureAxiom {
                        id: field_qualified_name,
                        field_name,
                        target,
                    }))
                }
                _ => {
                    return Self::fail(keyword, "expected const or axiom");
                }
            }
        }
        // Parsing finished.
        self.locals.truncate(self.locals.len() - num_consts);
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        let abs_id = name.extend(Name::from_str("abs")).to_global_id();
        Ok(CmdStructure {
            id,
            local_types: local_types
                .iter()
                .map(|ty| LocalType {
                    id: ty.id,
                    name: Some(ty.name.clone()),
                })
                .collect(),
            abs_id,
            fields,
        })
    }

    fn instance_cmd(&mut self, _token: Token) -> Result<CmdInstance, ParseError> {
        let name = self.global_declaration_name(None)?;
        let id = name.to_global_id();
        let local_types = self.local_type_parameters()?;
        let local_types = local_types
            .into_iter()
            .map(|name| {
                let id = Id::fresh();
                self.local_types.push(LocalBinding {
                    name: name.clone(),
                    id,
                });
                LocalType {
                    id,
                    name: Some(name),
                }
            })
            .collect::<Vec<_>>();
        let local_classes = self.local_class_parameters()?;
        let params = self.typed_parameters()?;
        let params_start = self.locals.len();
        let params = params
            .into_iter()
            .map(|(param_name, param_ty)| Local {
                id: {
                    let id = Id::fresh();
                    self.locals.push(LocalBinding {
                        name: param_name.clone(),
                        id,
                    });
                    id
                },
                name: Some(param_name),
                ty: param_ty,
            })
            .collect::<Vec<_>>();
        self.expect_symbol(":")?;
        let target_ty = self.ty()?;
        let mut fields = vec![];
        let mut num_defs = 0;
        let local_axiom_len = self.local_axioms.len();
        self.expect_symbol(":=")?;
        self.expect_symbol("{")?;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "def" => {
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    let field_params_start = self.locals.len();
                    let field_params = field_params
                        .into_iter()
                        .map(|(field_param_name, field_param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    name: field_param_name.clone(),
                                    id,
                                });
                                id
                            },
                            name: Some(field_param_name),
                            ty: field_param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut field_ty = self.ty()?;
                    self.expect_symbol(":=")?;
                    let mut field_target = self.term()?;
                    self.locals.truncate(field_params_start);
                    for field_param in field_params.into_iter().rev() {
                        field_ty = field_ty.arrow([field_param.ty.clone()]);
                        field_target = field_target.abs(&[field_param]);
                    }
                    let field_id = Id::fresh();
                    let field_qualified_name =
                        name.clone().extend(field_name.clone()).to_global_id();
                    fields.push(InstanceField::Def(InstanceDef {
                        field_id,
                        field_name: field_name.clone(),
                        id: field_qualified_name,
                        spec_id: name
                            .clone()
                            .extend(field_name.clone())
                            .extend(Name::from_str("spec"))
                            .to_global_id(),
                        ty: field_ty,
                        target: field_target,
                    }));
                    self.locals.push(LocalBinding {
                        name: field_name.clone(),
                        id: field_id,
                    });
                    num_defs += 1;
                }
                "lemma" => {
                    let field_name = self.name()?;
                    let field_id = Id::fresh();
                    let field_params = self.typed_parameters()?;
                    let field_params_start = self.locals.len();
                    let field_params = field_params
                        .into_iter()
                        .map(|(field_param_name, field_param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    name: field_param_name.clone(),
                                    id,
                                });
                                id
                            },
                            name: Some(field_param_name),
                            ty: field_param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut field_target = self.term()?;
                    self.expect_symbol(":=")?;
                    let mut expr = self.expr()?;
                    self.locals.truncate(field_params_start);
                    field_target = generalize(&field_target, &field_params);
                    for field_param in field_params.into_iter().rev() {
                        expr = mk_expr_take(
                            field_param.id,
                            field_param.name.clone(),
                            field_param.ty,
                            expr,
                        );
                    }
                    let holes = self.holes.drain(..).collect();
                    self.push_local_axiom(
                        QualifiedName::from_name(field_name.clone()),
                        field_id,
                        field_target.clone(),
                    );
                    let field_qualified_name =
                        name.clone().extend(field_name.clone()).to_global_id();
                    fields.push(InstanceField::Lemma(InstanceLemma {
                        field_id,
                        field_name,
                        id: field_qualified_name,
                        target: field_target,
                        holes,
                        expr,
                    }))
                }
                _ => Self::fail(keyword, "unknown command in instance")?,
            }
        }
        // Parsing finished.
        self.locals.truncate(self.locals.len() - num_defs);
        self.locals.truncate(params_start);
        self.local_axioms.truncate(local_axiom_len);
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdInstance {
            id,
            local_types,
            local_classes,
            params,
            target_ty,
            fields,
        })
    }

    fn class_structure_cmd(&mut self, _token: Token) -> Result<CmdClassStructure, ParseError> {
        let name = self.global_declaration_name(None)?;
        let id = name.to_global_id();
        let mut local_types = vec![];
        while let Some(token) = self.ident_opt() {
            let tv = Name::from_str(token.as_str());
            if local_types
                .iter()
                .any(|binding: &LocalBinding| binding.name == tv)
            {
                return Self::fail(token, "duplicate type variable")?;
            }
            let id = Id::fresh();
            self.local_types.push(LocalBinding {
                name: tv.clone(),
                id,
            });
            local_types.push(LocalBinding { name: tv, id });
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
                    let field_id = Id::fresh();
                    let field_qualified_name =
                        name.clone().extend(field_name.clone()).to_global_id();
                    fields.push(ClassStructureField::Const(ClassStructureConst {
                        field_id,
                        field_name: field_name.clone(),
                        id: field_qualified_name,
                        ty: field_ty,
                    }));
                    self.locals.push(LocalBinding {
                        name: field_name.clone(),
                        id: field_id,
                    });
                    num_consts += 1;
                }
                "axiom" => {
                    let field_name = self.name()?;
                    let params = self.typed_parameters()?;
                    let params_start = self.locals.len();
                    let params = params
                        .into_iter()
                        .map(|(param_name, param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    name: param_name.clone(),
                                    id,
                                });
                                id
                            },
                            name: Some(param_name),
                            ty: param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut target = self.term()?;
                    self.locals.truncate(params_start);
                    target = generalize(&target, &params);
                    let field_qualified_name =
                        name.clone().extend(field_name.clone()).to_global_id();
                    fields.push(ClassStructureField::Axiom(ClassStructureAxiom {
                        id: field_qualified_name,
                        field_name,
                        target,
                    }))
                }
                _ => {
                    return Self::fail(keyword, "expected const or axiom");
                }
            }
        }
        // Parsing finished.
        self.locals.truncate(self.locals.len() - num_consts);
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdClassStructure {
            id,
            local_types: local_types
                .iter()
                .map(|ty| LocalType {
                    id: ty.id,
                    name: Some(ty.name.clone()),
                })
                .collect(),
            fields,
        })
    }

    fn class_instance_cmd(&mut self, _token: Token) -> Result<CmdClassInstance, ParseError> {
        let name = self.global_declaration_name(None)?;
        let id = name.to_global_id();
        let local_types = self.local_type_parameters()?;
        let local_types = local_types
            .into_iter()
            .map(|name| {
                let id = Id::fresh();
                self.local_types.push(LocalBinding { name, id });
                LocalType {
                    id,
                    name: Some(
                        self.local_types
                            .last()
                            .expect("just pushed local type")
                            .name
                            .clone(),
                    ),
                }
            })
            .collect::<Vec<_>>();
        let local_classes = self.local_class_parameters()?;
        self.expect_symbol(":")?;
        let target = self.class()?;
        self.expect_symbol(":=")?;
        let mut fields = vec![];
        let mut num_defs = 0;
        let local_axiom_len = self.local_axioms.len();
        self.expect_symbol("{")?;
        while self.expect_symbol_opt("}").is_none() {
            let keyword = self.keyword()?;
            match keyword.as_str() {
                "def" => {
                    let field_name = self.name()?;
                    let field_params = self.typed_parameters()?;
                    let field_params_start = self.locals.len();
                    let field_params = field_params
                        .into_iter()
                        .map(|(field_param_name, field_param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    name: field_param_name.clone(),
                                    id,
                                });
                                id
                            },
                            name: Some(field_param_name),
                            ty: field_param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut field_ty = self.ty()?;
                    self.expect_symbol(":=")?;
                    let mut field_target = self.term()?;
                    self.locals.truncate(field_params_start);
                    for field_param in field_params.into_iter().rev() {
                        field_ty = field_ty.arrow([field_param.ty.clone()]);
                        field_target = field_target.abs(&[field_param]);
                    }
                    let field_id = Id::fresh();
                    fields.push(ClassInstanceField::Def(ClassInstanceDef {
                        field_id,
                        field_name: field_name.clone(),
                        ty: field_ty,
                        target: field_target,
                    }));
                    self.locals.push(LocalBinding {
                        name: field_name.clone(),
                        id: field_id,
                    });
                    num_defs += 1;
                }
                "lemma" => {
                    let field_name = self.name()?;
                    let field_id = Id::fresh();
                    let field_params = self.typed_parameters()?;
                    let field_params_start = self.locals.len();
                    let field_params = field_params
                        .into_iter()
                        .map(|(field_param_name, field_param_ty)| Local {
                            id: {
                                let id = Id::fresh();
                                self.locals.push(LocalBinding {
                                    name: field_param_name.clone(),
                                    id,
                                });
                                id
                            },
                            name: Some(field_param_name),
                            ty: field_param_ty,
                        })
                        .collect::<Vec<_>>();
                    self.expect_symbol(":")?;
                    let mut field_target = self.term()?;
                    self.expect_symbol(":=")?;
                    let mut expr = self.expr()?;
                    self.locals.truncate(field_params_start);
                    field_target = generalize(&field_target, &field_params);
                    for field_param in field_params.into_iter().rev() {
                        expr = mk_expr_take(
                            field_param.id,
                            field_param.name.clone(),
                            field_param.ty,
                            expr,
                        );
                    }
                    let holes = self.holes.drain(..).collect();
                    self.push_local_axiom(
                        QualifiedName::from_name(field_name.clone()),
                        field_id,
                        field_target.clone(),
                    );
                    fields.push(ClassInstanceField::Lemma(ClassInstanceLemma {
                        field_id,
                        field_name,
                        target: field_target,
                        holes,
                        expr,
                    }))
                }
                _ => Self::fail(keyword, "unknown command in instance")?,
            }
        }
        // Parsing finished.
        self.locals.truncate(self.locals.len() - num_defs);
        self.local_axioms.truncate(local_axiom_len);
        self.local_types
            .truncate(self.local_types.len() - local_types.len());
        Ok(CmdClassInstance {
            id,
            local_types,
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
    use crate::proof::{
        ExprApp, ExprAssume, ExprConst, ExprInst, ExprLetTerm, ExprLocal, mk_type_prop,
        ungeneralize, unguard,
    };
    use crate::tt::GlobalId;
    use std::collections::HashMap;
    use std::sync::{Arc, LazyLock};

    #[allow(clippy::type_complexity)]
    fn setup_tables() -> (
        TokenTable,
        HashMap<GlobalId, Kind>,
        HashMap<GlobalId, Const>,
        HashMap<GlobalId, Axiom>,
        HashMap<GlobalId, ClassType>,
    ) {
        let tt = TokenTable::default();
        let mut type_const_table = HashMap::new();
        let mut const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();

        let prop = global_id("Prop");
        type_const_table.insert(prop.clone(), Kind(0));

        let p = global_id("p");
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

    #[expect(clippy::too_many_arguments)]
    fn new_parser_without_type_defs<'a>(
        lex: &'a mut Lex,
        tt: &'a TokenTable,
        namespace_table: &'a HashMap<Path, Namespace>,
        current_namespace: &'a Path,
        type_const_table: &'a HashMap<GlobalId, Kind>,
        const_table: &'a HashMap<GlobalId, Const>,
        axiom_table: &'a HashMap<GlobalId, Axiom>,
        class_predicate_table: &'a HashMap<GlobalId, ClassType>,
    ) -> Parser<'a> {
        static EMPTY_TYPE_DEF_TABLE: LazyLock<HashMap<GlobalId, CmdTypeDef>> =
            LazyLock::new(HashMap::new);
        static EMPTY_STRUCTURE_TABLE: LazyLock<HashMap<GlobalId, CmdStructure>> =
            LazyLock::new(HashMap::new);
        Parser::new(
            lex,
            tt,
            namespace_table,
            current_namespace,
            type_const_table,
            &EMPTY_TYPE_DEF_TABLE,
            const_table,
            axiom_table,
            class_predicate_table,
            &EMPTY_STRUCTURE_TABLE,
        )
    }

    fn ensure_namespace_path_for_tests(
        namespace_table: &mut HashMap<Path, Namespace>,
        namespace: &Path,
    ) {
        if namespace == &Path::root() {
            return;
        }

        let mut parent = Path::root();
        for segment in namespace.names() {
            let child = parent.clone().extend(segment.clone());
            if !namespace_table.contains_key(&child) {
                namespace_table.insert(child.clone(), Namespace::default());
            }
            namespace_table
                .get_mut(&parent)
                .expect("parent namespace must exist")
                .use_table
                .entry(segment.clone())
                .or_insert_with(|| parent.clone().extend(segment.clone()));
            parent = child;
        }
    }

    fn register_global_name_for_tests(namespace_table: &mut HashMap<Path, Namespace>, name: &Path) {
        let mut owner_namespace = Path::root();
        let (leaf, parents) = name
            .names()
            .split_last()
            .expect("global path must not be root");
        for segment in parents {
            owner_namespace = owner_namespace.extend(segment.clone());
        }
        ensure_namespace_path_for_tests(namespace_table, &owner_namespace);
        namespace_table
            .get_mut(&owner_namespace)
            .expect("owner namespace must exist")
            .use_table
            .entry(leaf.clone())
            .or_insert_with(|| name.clone());
    }

    fn path_from_global_id(id: &GlobalId) -> Path {
        path(&id.to_string())
    }

    fn seed_namespace_table_from_globals(
        namespace_table: &mut HashMap<Path, Namespace>,
        type_const_table: &HashMap<GlobalId, Kind>,
        type_def_table: &HashMap<GlobalId, CmdTypeDef>,
        const_table: &HashMap<GlobalId, Const>,
        axiom_table: &HashMap<GlobalId, Axiom>,
        class_predicate_table: &HashMap<GlobalId, ClassType>,
    ) {
        let mut names = vec![];
        names.extend(type_const_table.keys().map(path_from_global_id));
        names.extend(type_def_table.keys().map(path_from_global_id));
        names.extend(const_table.keys().map(path_from_global_id));
        names.extend(axiom_table.keys().map(path_from_global_id));
        names.extend(class_predicate_table.keys().map(path_from_global_id));
        for name in names {
            register_global_name_for_tests(namespace_table, &name);
        }
    }

    fn ensure_use_target_prefixes_for_tests(
        namespace_table: &mut HashMap<Path, Namespace>,
        current_namespace: &Path,
    ) {
        let targets = namespace_table
            .get(current_namespace)
            .expect("current namespace must exist")
            .use_table
            .values()
            .cloned()
            .collect::<Vec<_>>();
        for target in targets {
            ensure_namespace_path_for_tests(namespace_table, &target);
        }
    }

    fn apply_use_cmd_for_tests(
        namespace_table: &mut HashMap<Path, Namespace>,
        current_namespace: &Path,
        cmd: &CmdUse,
    ) {
        ensure_namespace_path_for_tests(namespace_table, current_namespace);
        for decl in &cmd.decls {
            namespace_table
                .get_mut(current_namespace)
                .expect("current namespace must exist")
                .add(decl.alias.clone(), decl.target.clone());
        }
    }

    fn parse_expr(input: &str) -> Expr {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let type_defs = HashMap::new();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            root_namespace.clone(),
            Namespace {
                use_table: std::mem::take(&mut use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            &type_consts,
            &type_defs,
            &consts,
            &axioms,
            &class_predicates,
        );
        let current_namespace = root_namespace;
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let mut parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        );
        assert!(
            parser.const_table.contains_key(&global_id("p")),
            "const table missing p"
        );
        parser.expr().expect("expression parses")
    }

    fn parse_qualified(input: &str) -> Result<QualifiedName, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            root_namespace.clone(),
            Namespace {
                use_table: std::mem::take(&mut use_table),
            },
        );
        let current_namespace = root_namespace;
        let type_const_table: HashMap<GlobalId, Kind> = HashMap::new();
        let const_table: HashMap<GlobalId, Const> = HashMap::new();
        let axiom_table: HashMap<GlobalId, Axiom> = HashMap::new();
        let class_predicate_table: HashMap<GlobalId, ClassType> = HashMap::new();
        let mut parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );
        let token = parser.any_token()?;
        Ok(parser.qualified_name(&token))
    }

    fn parse_cmd_with_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, Path>,
        type_const_table: &HashMap<GlobalId, Kind>,
        const_table: &HashMap<GlobalId, Const>,
        axiom_table: &HashMap<GlobalId, Axiom>,
        class_predicate_table: &HashMap<GlobalId, ClassType>,
    ) -> Result<Cmd, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let type_def_table: HashMap<GlobalId, CmdTypeDef> = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            root_namespace.clone(),
            Namespace {
                use_table: std::mem::take(use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            type_const_table,
            &type_def_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let current_namespace = root_namespace.clone();
        ensure_use_target_prefixes_for_tests(&mut namespace_table, &current_namespace);
        let structure_table: HashMap<GlobalId, CmdStructure> = HashMap::new();
        let mut parser = Parser::new(
            &mut lex,
            tt,
            &namespace_table,
            &current_namespace,
            type_const_table,
            &type_def_table,
            const_table,
            axiom_table,
            class_predicate_table,
            &structure_table,
        );
        let cmd = parser.cmd();
        if let Ok(Cmd::Use(use_cmd)) = &cmd {
            apply_use_cmd_for_tests(&mut namespace_table, &current_namespace, use_cmd);
        }
        let top_entry = namespace_table
            .remove(&root_namespace)
            .expect("root namespace entry must exist");
        *use_table = top_entry.use_table;
        cmd
    }

    fn parse_cmds_with_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, Path>,
        type_const_table: &HashMap<GlobalId, Kind>,
        const_table: &HashMap<GlobalId, Const>,
        axiom_table: &HashMap<GlobalId, Axiom>,
        class_predicate_table: &HashMap<GlobalId, ClassType>,
    ) -> Result<Vec<Cmd>, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let mut tt = tt.clone();
        let mut type_const_table = type_const_table.clone();
        let mut type_def_table: HashMap<GlobalId, CmdTypeDef> = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            root_namespace.clone(),
            Namespace {
                use_table: std::mem::take(use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            &type_const_table,
            &type_def_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let mut cmds = vec![];
        let mut namespace_stack = vec![];
        let mut current_namespace = root_namespace.clone();
        let mut structure_table: HashMap<GlobalId, CmdStructure> = HashMap::new();
        while !lex.is_eof() {
            ensure_use_target_prefixes_for_tests(&mut namespace_table, &current_namespace);
            let mut parser = Parser::new(
                &mut lex,
                &tt,
                &namespace_table,
                &current_namespace,
                &type_const_table,
                &type_def_table,
                const_table,
                axiom_table,
                class_predicate_table,
                &structure_table,
            );
            let cmd = parser.cmd()?;
            if let Cmd::Use(use_cmd) = &cmd {
                apply_use_cmd_for_tests(&mut namespace_table, &current_namespace, use_cmd);
            }
            match &cmd {
                Cmd::NamespaceStart(CmdNamespaceStart { path }) => {
                    ensure_namespace_path_for_tests(&mut namespace_table, path);
                    namespace_stack.push(current_namespace.clone());
                    current_namespace = path.clone();
                }
                Cmd::BlockEnd => {
                    if let Some(previous_namespace) = namespace_stack.pop() {
                        current_namespace = previous_namespace;
                    }
                }
                Cmd::TypeConst(CmdTypeConst { id, kind }) => {
                    type_const_table.insert(id.clone(), kind.clone());
                }
                Cmd::TypeDef(cmd) => {
                    type_def_table.insert(cmd.id.clone(), cmd.clone());
                }
                Cmd::Structure(cmd) => {
                    structure_table.insert(cmd.id.clone(), cmd.clone());
                }
                Cmd::Infix(cmd) => {
                    tt.add(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Infix,
                        prec: cmd.prec,
                        entity: cmd.entity.clone(),
                    })
                    .expect("term infix notation registers");
                }
                Cmd::Infixr(cmd) => {
                    tt.add(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Infixr,
                        prec: cmd.prec,
                        entity: cmd.entity.clone(),
                    })
                    .expect("term infixr notation registers");
                }
                Cmd::Infixl(cmd) => {
                    tt.add(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Infixl,
                        prec: cmd.prec,
                        entity: cmd.entity.clone(),
                    })
                    .expect("term infixl notation registers");
                }
                Cmd::Prefix(cmd) => {
                    tt.add(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Prefix,
                        prec: cmd.prec,
                        entity: cmd.entity.clone(),
                    })
                    .expect("term prefix notation registers");
                }
                Cmd::Nofix(cmd) => {
                    tt.add(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Nofix,
                        prec: usize::MAX,
                        entity: cmd.entity.clone(),
                    })
                    .expect("term nofix notation registers");
                }
                Cmd::TypeInfix(cmd) => {
                    tt.add_type(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Infix,
                        prec: cmd.prec,
                        entity: cmd.entity.clone(),
                    })
                    .expect("type infix notation registers");
                }
                Cmd::TypeInfixr(cmd) => {
                    tt.add_type(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Infixr,
                        prec: cmd.prec,
                        entity: cmd.entity.clone(),
                    })
                    .expect("type infixr notation registers");
                }
                Cmd::TypeInfixl(cmd) => {
                    tt.add_type(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Infixl,
                        prec: cmd.prec,
                        entity: cmd.entity.clone(),
                    })
                    .expect("type infixl notation registers");
                }
                Cmd::TypePrefix(cmd) => {
                    tt.add_type(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Prefix,
                        prec: cmd.prec,
                        entity: cmd.entity.clone(),
                    })
                    .expect("type prefix notation registers");
                }
                Cmd::TypeNofix(cmd) => {
                    tt.add_type(Operator {
                        symbol: cmd.op.clone(),
                        fixity: Fixity::Nofix,
                        prec: usize::MAX,
                        entity: cmd.entity.clone(),
                    })
                    .expect("type nofix notation registers");
                }
                _ => {}
            }
            cmds.push(cmd);
        }
        let top_entry = namespace_table
            .remove(&root_namespace)
            .expect("root namespace entry must exist");
        *use_table = top_entry.use_table;
        Ok(cmds)
    }

    fn parse_term_with_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, Path>,
        type_const_table: &HashMap<GlobalId, Kind>,
        const_table: &HashMap<GlobalId, Const>,
        axiom_table: &HashMap<GlobalId, Axiom>,
        class_predicate_table: &HashMap<GlobalId, ClassType>,
    ) -> Result<Term, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let type_def_table = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            root_namespace.clone(),
            Namespace {
                use_table: std::mem::take(use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            type_const_table,
            &type_def_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let current_namespace = root_namespace.clone();
        ensure_use_target_prefixes_for_tests(&mut namespace_table, &current_namespace);
        let mut parser = new_parser_without_type_defs(
            &mut lex,
            tt,
            &namespace_table,
            &current_namespace,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let term = parser.term();
        let top_entry = namespace_table
            .remove(&root_namespace)
            .expect("root namespace entry must exist");
        *use_table = top_entry.use_table;
        term
    }

    fn parse_type_with_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, Path>,
        type_const_table: &HashMap<GlobalId, Kind>,
        const_table: &HashMap<GlobalId, Const>,
        axiom_table: &HashMap<GlobalId, Axiom>,
        class_predicate_table: &HashMap<GlobalId, ClassType>,
    ) -> Result<Type, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let type_def_table = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            root_namespace.clone(),
            Namespace {
                use_table: std::mem::take(use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            type_const_table,
            &type_def_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let current_namespace = root_namespace.clone();
        ensure_use_target_prefixes_for_tests(&mut namespace_table, &current_namespace);
        let mut parser = new_parser_without_type_defs(
            &mut lex,
            tt,
            &namespace_table,
            &current_namespace,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let ty = parser.ty();
        let top_entry = namespace_table
            .remove(&root_namespace)
            .expect("root namespace entry must exist");
        *use_table = top_entry.use_table;
        ty
    }

    fn parse_expr_with_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, Path>,
        type_const_table: &HashMap<GlobalId, Kind>,
        const_table: &HashMap<GlobalId, Const>,
        axiom_table: &HashMap<GlobalId, Axiom>,
        class_predicate_table: &HashMap<GlobalId, ClassType>,
    ) -> Result<Expr, ParseError> {
        let structure_table = HashMap::new();
        parse_expr_with_structure_tables(
            input,
            tt,
            use_table,
            type_const_table,
            const_table,
            axiom_table,
            class_predicate_table,
            &structure_table,
        )
    }

    #[expect(clippy::too_many_arguments)]
    fn parse_expr_with_structure_tables(
        input: &str,
        tt: &TokenTable,
        use_table: &mut HashMap<Name, Path>,
        type_const_table: &HashMap<GlobalId, Kind>,
        const_table: &HashMap<GlobalId, Const>,
        axiom_table: &HashMap<GlobalId, Axiom>,
        class_predicate_table: &HashMap<GlobalId, ClassType>,
        structure_table: &HashMap<GlobalId, CmdStructure>,
    ) -> Result<Expr, ParseError> {
        let file = Arc::new(File::new("<test>", input));
        let mut lex = Lex::new(file);
        let type_def_table = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            root_namespace.clone(),
            Namespace {
                use_table: std::mem::take(use_table),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            type_const_table,
            &type_def_table,
            const_table,
            axiom_table,
            class_predicate_table,
        );
        let current_namespace = root_namespace.clone();
        ensure_use_target_prefixes_for_tests(&mut namespace_table, &current_namespace);
        let mut parser = Parser::new(
            &mut lex,
            tt,
            &namespace_table,
            &current_namespace,
            type_const_table,
            &type_def_table,
            const_table,
            axiom_table,
            class_predicate_table,
            structure_table,
        );
        let expr = parser.expr();
        let top_entry = namespace_table
            .remove(&root_namespace)
            .expect("root namespace entry must exist");
        *use_table = top_entry.use_table;
        expr
    }

    fn qualified(value: &str) -> QualifiedName {
        let mut parts = value.split('.');
        let first = parts.next().expect("qualified name must not be empty");
        let mut name = QualifiedName::from_name(Name::from_str(first));
        for part in parts {
            name = name.extend(Name::from_str(part));
        }
        name
    }

    fn global_id(value: &str) -> GlobalId {
        GlobalId::from_name(Name::from_str(value))
    }

    fn path(value: &str) -> Path {
        let mut path = Path::root();
        if value.is_empty() {
            return path;
        }
        for part in value.split('.') {
            path = path.extend(Name::from_str(part));
        }
        path
    }

    fn insert_prop_const(const_table: &mut HashMap<GlobalId, Const>, name: &str) {
        const_table.insert(
            global_id(name),
            Const {
                local_types: vec![],
                local_classes: vec![],
                ty: mk_type_const(global_id("Prop")),
            },
        );
    }

    fn assert_declaration_head_error(err: ParseError, expected: &str) {
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, expected);
    }

    #[test]
    fn qualified_name_tracks_relative_segments() {
        let name = parse_qualified("foo.bar").expect("qualified name parses");
        let foo = Name::from_str("foo");

        assert!(!name.is_absolute);
        assert_eq!(
            name.names,
            vec![Name::from_str("foo"), Name::from_str("bar")]
        );
        assert_eq!(QualifiedName::from_name(foo.clone()).as_name(), Some(&foo));
    }

    #[test]
    fn qualified_name_tracks_absolute_segments() {
        let name = parse_qualified(".foo.bar").expect("absolute qualified name parses");

        assert!(name.is_absolute);
        assert_eq!(
            name.names,
            vec![Name::from_str("foo"), Name::from_str("bar")]
        );
        assert_eq!(name.as_name(), None);
    }

    #[test]
    fn assume_alias_uses_parser_generated_id() {
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
        let (alias, alias_name) = alias.expect("expected alias id");
        assert_eq!(alias_name, Name::from_str("this"));
        let expected = mk_const(global_id("p"), vec![], vec![]);
        assert!(local_axiom.alpha_eq(&expected));

        let Expr::Local(assump) = body else {
            panic!("expected body to reference assumption alias");
        };
        let ExprLocal { metadata: _, id } = *assump;
        assert_eq!(id, alias);
    }

    #[test]
    fn have_alias_uses_parser_generated_ids() {
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
        let (outer_alias, outer_alias_name) = outer_alias.expect("expected outer alias");
        assert_eq!(outer_alias_name, Name::from_str("hp"));
        let expected = mk_const(global_id("p"), vec![], vec![]);
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
        let (inner_alias, inner_alias_name) = inner_alias.expect("expected inner alias");
        assert_eq!(inner_alias_name, Name::from_str("this"));
        assert!(inner_axiom.alpha_eq(&expected));
        let Expr::Local(inner_assump) = inner_body else {
            panic!("expected have body to reference alias");
        };
        let ExprLocal {
            metadata: _,
            id: inner_id,
        } = *inner_assump;
        assert_eq!(inner_id, inner_alias);

        let Expr::Local(have_arg) = expr2 else {
            panic!("expected have argument to reference outer alias");
        };
        let ExprLocal {
            metadata: _,
            id: outer_id,
        } = *have_arg;
        assert_eq!(outer_id, outer_alias);
    }

    #[test]
    fn shadowed_assume_alias_gets_fresh_ids() {
        let expr = parse_expr("assume p as h, have p as h := h, h");
        let Expr::Assume(outer) = expr else {
            panic!("expected outer assume");
        };
        let outer_alias = outer.alias.expect("outer alias");

        let Expr::App(inner_app) = outer.expr else {
            panic!("expected have expansion");
        };
        let Expr::Assume(inner_assume) = inner_app.expr1 else {
            panic!("expected inner assume");
        };
        let inner_alias = inner_assume.alias.expect("inner alias");

        assert_ne!(outer_alias, inner_alias);

        let Expr::Local(outer_proof) = inner_app.expr2 else {
            panic!("expected outer proof local");
        };
        assert_eq!(outer_proof.id, outer_alias.0);

        let Expr::Local(inner_body) = inner_assume.expr else {
            panic!("expected inner body local");
        };
        assert_eq!(inner_body.id, inner_alias.0);
    }

    #[test]
    fn assume_alias_auto_instantiates_forall_with_alias_id() {
        let expr = parse_expr("assume ∀ (x : Prop), p as h, h");
        let Expr::Assume(assume) = expr else {
            panic!("expected assume expression");
        };
        let ExprAssume {
            metadata: _,
            local_axiom: _,
            alias,
            expr: body,
        } = *assume;
        let alias = alias.expect("expected alias id");
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
        assert_eq!(local_axiom.id, alias.0);
        assert!(arg.head().is_hole());
    }

    #[test]
    fn term_hole_uses_current_local_ids_for_local_context() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let type_defs = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(root_namespace.clone(), Namespace::default());
        seed_namespace_table_from_globals(
            &mut namespace_table,
            &type_consts,
            &type_defs,
            &consts,
            &axioms,
            &class_predicates,
        );
        let current_namespace = root_namespace;
        let file = Arc::new(File::new("<test>", "_"));
        let mut lex = Lex::new(file);
        let mut parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        );

        let local_name = Name::from_str("x");
        let generated_id = Id::fresh();
        parser.locals.push(LocalBinding {
            name: local_name,
            id: generated_id,
        });
        let term = parser.term().expect("term parses");
        let args = term.args();
        assert_eq!(args.len(), 1);
        let Term::Local(local) = args[0] else {
            panic!("expected local argument");
        };
        assert_eq!(local.id, generated_id);
    }

    #[test]
    fn shadowed_take_binder_keeps_outer_id_in_assumption_target() {
        let expr = parse_expr("take (x : Prop), assume x as h, take (x : Prop), h");
        let Expr::Take(outer_take) = expr else {
            panic!("expected outer take");
        };
        let outer_id = outer_take.id;

        let Expr::Assume(assume) = outer_take.expr else {
            panic!("expected assume inside outer take");
        };
        let Term::Local(assume_target) = assume.local_axiom else {
            panic!("expected local assumption target");
        };
        assert_eq!(assume_target.id, outer_id);

        let Expr::Take(inner_take) = assume.expr else {
            panic!("expected inner take");
        };
        assert_ne!(inner_take.id, outer_id);
    }

    #[test]
    fn obtain_binder_body_reuses_same_id_as_take() {
        let expr = parse_expr("assume p as hp, obtain (x : Prop), x := hp, «x»");
        let Expr::Assume(outer_assume) = expr else {
            panic!("expected outer assume");
        };
        let Expr::App(app) = outer_assume.expr else {
            panic!("expected obtain expansion inside assume");
        };
        let Expr::Take(take) = app.expr2 else {
            panic!("expected obtain body to be wrapped in take");
        };
        let take_id = take.id;

        let Expr::Assume(assume) = take.expr else {
            panic!("expected take body to start with assume");
        };
        let Term::Local(assume_target) = assume.local_axiom else {
            panic!("expected obtain proposition to reference local binder");
        };
        assert_eq!(assume_target.id, take_id);

        let Expr::Assump(body_assump) = assume.expr else {
            panic!("expected obtain body to reference local binder through assump");
        };
        let Term::Local(body_local) = body_assump.target else {
            panic!("expected body assump to target local binder");
        };
        assert_eq!(body_local.id, take_id);
    }

    #[test]
    fn parser_local_bindings_use_qualified_name_keys() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let type_defs = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(root_namespace.clone(), Namespace::default());
        seed_namespace_table_from_globals(
            &mut namespace_table,
            &type_consts,
            &type_defs,
            &consts,
            &axioms,
            &class_predicates,
        );
        let current_namespace = root_namespace;
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let mut parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        );

        let local_const_name = qualified("foo.c");
        let local_axiom_name = qualified("foo.a");
        let local_const_id = Id::fresh();
        parser.push_local_const(local_const_name.clone(), local_const_id);
        parser.push_local_axiom(
            local_axiom_name.clone(),
            Id::fresh(),
            mk_const(global_id("p"), vec![], vec![]),
        );

        assert!(parser.get_local_const(&local_const_name).is_some());
        assert!(parser.get_local_axiom(&local_axiom_name).is_some());
    }

    #[test]
    fn qualified_name_parses_dotted_segments() {
        let name = parse_qualified("foo.bar").expect("parse failed");
        assert_eq!(
            name.names,
            vec![Name::from_str("foo"), Name::from_str("bar")]
        );
    }

    #[test]
    fn qualified_name_ignores_whitespace_before_segment() {
        let without = parse_qualified("foo.bar").expect("parse without whitespace");
        let with = parse_qualified("foo .bar").expect("parse with whitespace");
        assert_eq!(with, without);
    }

    #[test]
    fn absolute_global_term_name_parses_with_and_without_whitespace() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "foo.bar");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let without = parse_term_with_tables(
            ".foo.bar",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("term without whitespace parses");
        let with = parse_term_with_tables(
            ".foo .bar",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("term with whitespace parses");
        let Term::Const(without_const) = without else {
            panic!("expected constant term without whitespace");
        };
        let Term::Const(with_const) = with else {
            panic!("expected constant term with whitespace");
        };
        assert_eq!(without_const.id, global_id("foo.bar"));
        assert_eq!(with_const.id, without_const.id);
    }

    #[test]
    fn absolute_type_reference_is_resolved_from_root() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { const x : .Prop }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::Const(CmdConst {
            id: _,
            local_types: _,
            local_classes: _,
            ty,
        }) = &cmds[1]
        else {
            panic!("expected const command");
        };
        assert_eq!(ty, &mk_type_const(global_id("Prop")));
    }

    #[test]
    fn absolute_class_reference_is_resolved_from_root() {
        let (tt, type_consts, consts, axioms, mut class_predicates) = setup_tables();
        class_predicates.insert(global_id("C"), ClassType { arity: 0 });
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { const x [.C] : .Prop }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::Const(CmdConst {
            id: _,
            local_types: _,
            local_classes,
            ty: _,
        }) = &cmds[1]
        else {
            panic!("expected const command");
        };
        assert_eq!(local_classes.len(), 1);
        assert_eq!(local_classes[0].id, global_id("C"));
    }

    #[test]
    fn absolute_term_reference_is_resolved_from_root() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { def x : .Prop := .p }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::Def(CmdDef {
            id: _,
            local_types: _,
            local_classes: _,
            ty: _,
            target,
        }) = &cmds[1]
        else {
            panic!("expected def command");
        };
        let Term::Const(const_term) = target else {
            panic!("expected constant in def body");
        };
        assert_eq!(const_term.id, global_id("p"));
    }

    #[test]
    fn absolute_expr_reference_is_resolved_from_root() {
        let (tt, type_consts, consts, mut axioms, class_predicates) = setup_tables();
        axioms.insert(
            global_id("h"),
            Axiom {
                local_types: vec![],
                local_classes: vec![],
                target: mk_const(global_id("p"), vec![], vec![]),
            },
        );
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { lemma l : .p := @.h }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::Lemma(CmdLemma {
            id: _,
            local_types: _,
            local_classes: _,
            target: _,
            holes: _,
            expr,
        }) = &cmds[1]
        else {
            panic!("expected lemma command");
        };
        let Expr::Const(expr_const) = expr else {
            panic!("expected proof constant expression");
        };
        let ExprConst {
            metadata: _,
            id,
            ty_args: _,
            instances: _,
        } = &**expr_const;
        assert_eq!(id, &global_id("h"));
    }

    #[test]
    fn absolute_namespace_target_is_resolved_from_root() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { namespace .bar { } }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::NamespaceStart(outer) = &cmds[0] else {
            panic!("expected outer namespace start");
        };
        assert_eq!(outer.path, path("foo"));
        let Cmd::NamespaceStart(inner) = &cmds[1] else {
            panic!("expected inner namespace start");
        };
        assert_eq!(inner.path, path("bar"));
        assert!(matches!(cmds[2], Cmd::BlockEnd));
        assert!(matches!(cmds[3], Cmd::BlockEnd));
    }

    #[test]
    fn absolute_use_target_is_resolved_from_root() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { use .bar as baz }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::Use(CmdUse { decls }) = &cmds[1] else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].target, path("bar"));
    }

    #[test]
    fn use_command_display_uses_resolved_targets_only() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { use .bar as baz }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        assert_eq!(format!("{}", cmds[1]), "use bar as baz");
    }

    #[test]
    fn absolute_fixity_entities_are_resolved_from_root() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let scenarios = [
            ("infixr * : 50 := .p", "infixr"),
            ("infixl * : 50 := .p", "infixl"),
            ("infix * : 50 := .p", "infix"),
            ("prefix ! : 50 := .p", "prefix"),
            ("nofix ! := .p", "nofix"),
        ];
        for (command, label) in scenarios {
            let input = format!("namespace foo {{ {command} }}");
            let mut use_table: HashMap<Name, Path> = HashMap::new();
            let cmds = parse_cmds_with_tables(
                &input,
                &tt,
                &mut use_table,
                &type_consts,
                &consts,
                &axioms,
                &class_predicates,
            )
            .expect("commands parse");
            let entity = match &cmds[1] {
                Cmd::Infixr(cmd) => &cmd.entity,
                Cmd::Infixl(cmd) => &cmd.entity,
                Cmd::Infix(cmd) => &cmd.entity,
                Cmd::Prefix(cmd) => &cmd.entity,
                Cmd::Nofix(cmd) => &cmd.entity,
                _ => panic!("expected fixity command"),
            };
            assert_eq!(entity, &global_id("p"), "label = {label}");
        }
    }

    #[test]
    fn declaration_heads_reject_absolute_paths() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let inputs = [
            (
                "def .x : Prop := p",
                "absolute path is not allowed in declaration head",
            ),
            (
                "axiom .x : p",
                "absolute path is not allowed in declaration head",
            ),
            (
                "lemma .x : p := p",
                "absolute path is not allowed in declaration head",
            ),
            (
                "const .x : Prop",
                "absolute path is not allowed in declaration head",
            ),
            (
                "type const .x : Type",
                "absolute path is not allowed in declaration head",
            ),
            ("type inductive .x", "expected identifier"),
            ("type inductive x | .mk : x", "expected identifier"),
            ("inductive .x : Prop", "expected identifier"),
            ("inductive x : Prop | .mk : x", "expected identifier"),
            (
                "structure .x := { }",
                "absolute path is not allowed in declaration head",
            ),
            (
                "instance .x : Prop := { }",
                "absolute path is not allowed in declaration head",
            ),
            (
                "class structure .x := { }",
                "absolute path is not allowed in declaration head",
            ),
            (
                "class instance .x : C := { }",
                "absolute path is not allowed in declaration head",
            ),
        ];
        for (input, expected_message) in inputs {
            let mut use_table: HashMap<Name, Path> = HashMap::new();
            let err = parse_cmd_with_tables(
                input,
                &tt,
                &mut use_table,
                &type_consts,
                &consts,
                &axioms,
                &class_predicates,
            )
            .expect_err("absolute declaration head should be rejected");
            assert_declaration_head_error(err, expected_message);
        }
    }

    #[test]
    fn instance_def_can_reference_preceding_definition() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "instance inst : Prop := { def a : Prop := p def b : Prop := a }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("instance parses");
        let Cmd::Instance(CmdInstance {
            id: _,
            local_types: _,
            local_classes: _,
            params: _,
            target_ty: _,
            fields,
        }) = cmd
        else {
            panic!("expected instance command");
        };
        let InstanceField::Def(InstanceDef {
            field_id: _,
            field_name,
            id,
            spec_id,
            ty: _,
            target,
        }) = &fields[1]
        else {
            panic!("expected second field to be a definition");
        };
        assert_eq!(field_name, &Name::from_str("b"));
        assert_eq!(id, &global_id("inst.b"));
        assert_eq!(spec_id, &global_id("inst.b.spec"));
        let Term::Local(local) = target else {
            panic!("expected second definition to reference a local");
        };
        let InstanceField::Def(InstanceDef {
            field_id: first_field_id,
            ..
        }) = &fields[0]
        else {
            panic!("expected first field to be a definition");
        };
        assert_eq!(local.id, *first_field_id);
    }

    #[test]
    fn class_instance_def_can_reference_preceding_definition() {
        let (tt, type_consts, consts, axioms, mut class_predicates) = setup_tables();
        class_predicates.insert(global_id("C"), ClassType { arity: 0 });
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "class instance inst : C := { def a : Prop := p def b : Prop := a }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("class instance parses");
        let Cmd::ClassInstance(CmdClassInstance {
            id: _,
            local_types: _,
            local_classes: _,
            target: _,
            fields,
        }) = cmd
        else {
            panic!("expected class instance command");
        };
        let ClassInstanceField::Def(ClassInstanceDef {
            field_id: _,
            field_name,
            ty: _,
            target,
            ..
        }) = &fields[1]
        else {
            panic!("expected second field to be a definition");
        };
        assert_eq!(field_name, &Name::from_str("b"));
        let Term::Local(local) = target else {
            panic!("expected second definition to reference a local");
        };
        let ClassInstanceField::Def(ClassInstanceDef {
            field_id: first_field_id,
            ..
        }) = &fields[0]
        else {
            panic!("expected first field to be a definition");
        };
        assert_eq!(local.id, *first_field_id);
    }

    #[test]
    fn instance_field_name_does_not_shadow_outer_param_in_rhs() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("U"), Kind(0));
        type_consts.insert(global_id("foo"), Kind(0));
        let structure_field_id = Id::fresh();
        let structure_table = HashMap::from([(
            global_id("foo"),
            CmdStructure {
                id: global_id("foo"),
                local_types: vec![],
                abs_id: global_id("foo.abs"),
                fields: vec![StructureField::Const(StructureConst {
                    field_id: structure_field_id,
                    field_name: Name::from_str("rep"),
                    id: global_id("foo.rep"),
                    ty: mk_type_const(global_id("U")),
                })],
            },
        )]);
        let file = Arc::new(File::new(
            "<test>",
            "instance inst (rep : U) : foo := { def rep : U := rep }",
        ));
        let mut lex = Lex::new(file);
        let type_def_table = HashMap::new();
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        namespace_table.insert(
            root_namespace.clone(),
            Namespace {
                use_table: HashMap::new(),
            },
        );
        seed_namespace_table_from_globals(
            &mut namespace_table,
            &type_consts,
            &type_def_table,
            &consts,
            &axioms,
            &class_predicates,
        );
        let current_namespace = root_namespace;
        ensure_use_target_prefixes_for_tests(&mut namespace_table, &current_namespace);
        let mut parser = Parser::new(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_consts,
            &type_def_table,
            &consts,
            &axioms,
            &class_predicates,
            &structure_table,
        );
        let cmd = parser.cmd().expect("instance parses");
        let Cmd::Instance(CmdInstance { params, fields, .. }) = cmd else {
            panic!("expected instance command");
        };
        let outer_param_id = params[0].id;
        let InstanceField::Def(InstanceDef { target, .. }) = &fields[0] else {
            panic!("expected definition field");
        };
        let Term::Local(local) = target else {
            panic!("expected field target to reference outer parameter");
        };
        assert_eq!(local.id, outer_param_id);
    }

    #[test]
    fn instance_lemma_can_reference_preceding_lemma() {
        let (tt, type_consts, consts, mut axioms, class_predicates) = setup_tables();
        axioms.insert(
            global_id("hp"),
            Axiom {
                local_types: vec![],
                local_classes: vec![],
                target: mk_const(global_id("p"), vec![], vec![]),
            },
        );
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "instance inst : Prop := { lemma h1 : p := hp lemma h2 : p := h1 }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("instance parses");
        let Cmd::Instance(CmdInstance {
            id: _,
            local_types: _,
            local_classes: _,
            params: _,
            target_ty: _,
            fields,
        }) = cmd
        else {
            panic!("expected instance command");
        };
        let InstanceField::Lemma(InstanceLemma {
            field_id: _,
            field_name,
            id,
            target: _,
            holes: _,
            expr,
        }) = &fields[1]
        else {
            panic!("expected second field to be a lemma");
        };
        assert_eq!(field_name, &Name::from_str("h2"));
        assert_eq!(id, &global_id("inst.h2"));
        let Expr::Local(local) = expr else {
            panic!("expected second lemma expression to reference a local lemma");
        };
        let ExprLocal {
            metadata: _, id, ..
        } = &**local;
        let InstanceField::Lemma(InstanceLemma {
            field_id: first_field_id,
            ..
        }) = &fields[0]
        else {
            panic!("expected first field to be a lemma");
        };
        assert_eq!(*id, *first_field_id);
    }

    #[test]
    fn class_instance_lemma_can_reference_preceding_lemma() {
        let (tt, type_consts, consts, mut axioms, mut class_predicates) = setup_tables();
        axioms.insert(
            global_id("hp"),
            Axiom {
                local_types: vec![],
                local_classes: vec![],
                target: mk_const(global_id("p"), vec![], vec![]),
            },
        );
        class_predicates.insert(global_id("C"), ClassType { arity: 0 });
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "class instance inst : C := { lemma h1 : p := hp lemma h2 : p := h1 }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("class instance parses");
        let Cmd::ClassInstance(CmdClassInstance {
            id: _,
            local_types: _,
            local_classes: _,
            target: _,
            fields,
        }) = cmd
        else {
            panic!("expected class instance command");
        };
        let ClassInstanceField::Lemma(ClassInstanceLemma {
            field_id: _,
            field_name,
            target: _,
            holes: _,
            expr,
            ..
        }) = &fields[1]
        else {
            panic!("expected second field to be a lemma");
        };
        assert_eq!(field_name, &Name::from_str("h2"));
        let Expr::Local(local) = expr else {
            panic!("expected second lemma expression to reference a local lemma");
        };
        let ExprLocal {
            metadata: _, id, ..
        } = &**local;
        let ClassInstanceField::Lemma(ClassInstanceLemma {
            field_id: first_field_id,
            ..
        }) = &fields[0]
        else {
            panic!("expected first field to be a lemma");
        };
        assert_eq!(*id, *first_field_id);
    }

    #[test]
    fn structure_const_field_keeps_id_for_later_axioms() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "structure foo := { const rep : Prop axiom ok : rep }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("structure parses");
        let Cmd::Structure(CmdStructure { abs_id, fields, .. }) = cmd else {
            panic!("expected structure command");
        };
        assert_eq!(abs_id, global_id("foo.abs"));
        let StructureField::Const(StructureConst {
            field_id,
            field_name,
            id,
            ty: _,
        }) = &fields[0]
        else {
            panic!("expected const field");
        };
        assert_eq!(field_name, &Name::from_str("rep"));
        assert_eq!(id, &global_id("foo.rep"));
        let StructureField::Axiom(StructureAxiom {
            field_name,
            id,
            target,
        }) = &fields[1]
        else {
            panic!("expected axiom field");
        };
        assert_eq!(field_name, &Name::from_str("ok"));
        assert_eq!(id, &global_id("foo.ok"));
        let Term::Local(local) = target else {
            panic!("expected axiom target to reference the const field id");
        };
        assert_eq!(local.id, *field_id);
    }

    #[test]
    fn class_structure_const_field_keeps_id_for_later_axioms() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "class structure foo := { const rep : Prop axiom ok : rep }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("class structure parses");
        let Cmd::ClassStructure(CmdClassStructure { fields, .. }) = cmd else {
            panic!("expected class structure command");
        };
        let ClassStructureField::Const(ClassStructureConst {
            field_id,
            field_name,
            id,
            ty: _,
        }) = &fields[0]
        else {
            panic!("expected const field");
        };
        assert_eq!(field_name, &Name::from_str("rep"));
        assert_eq!(id, &global_id("foo.rep"));
        let ClassStructureField::Axiom(ClassStructureAxiom {
            field_name,
            id,
            target,
        }) = &fields[1]
        else {
            panic!("expected axiom field");
        };
        assert_eq!(field_name, &Name::from_str("ok"));
        assert_eq!(id, &global_id("foo.ok"));
        let Term::Local(local) = target else {
            panic!("expected axiom target to reference the const field id");
        };
        assert_eq!(local.id, *field_id);
    }

    #[test]
    fn instance_lemma_self_reference_is_rejected() {
        let (tt, type_consts, consts, mut axioms, class_predicates) = setup_tables();
        axioms.insert(
            global_id("hp"),
            Axiom {
                local_types: vec![],
                local_classes: vec![],
                target: mk_const(global_id("p"), vec![], vec![]),
            },
        );
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_cmd_with_tables(
            "instance inst : Prop := { lemma h1 : p := h1 }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("self-referencing lemma should fail to parse");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "unknown variable");
    }

    #[test]
    fn class_instance_lemma_self_reference_is_rejected() {
        let (tt, type_consts, consts, mut axioms, mut class_predicates) = setup_tables();
        axioms.insert(
            global_id("hp"),
            Axiom {
                local_types: vec![],
                local_classes: vec![],
                target: mk_const(global_id("p"), vec![], vec![]),
            },
        );
        class_predicates.insert(global_id("C"), ClassType { arity: 0 });
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_cmd_with_tables(
            "class instance inst : C := { lemma h1 : p := h1 }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("self-referencing lemma should fail to parse");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "unknown variable");
    }

    #[test]
    fn use_scoped_group_expands_to_leaf_decls() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "prod.fst");
        insert_prop_const(&mut consts, "prod.snd");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        assert_eq!(decls[0].target, path("prod.fst"));
        assert_eq!(decls[1].alias, Name::from_str("snd"));
        assert_eq!(decls[1].target, path("prod.snd"));
    }

    #[test]
    fn use_absolute_group_expands_to_leaf_decls() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "foo");
        insert_prop_const(&mut consts, "bar");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "use .{foo, bar}",
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
        assert_eq!(decls[0].alias, Name::from_str("foo"));
        assert_eq!(decls[0].target, path("foo"));
        assert_eq!(decls[1].alias, Name::from_str("bar"));
        assert_eq!(decls[1].target, path("bar"));
    }

    #[test]
    fn use_absolute_group_in_namespace_is_resolved_from_root() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace local { use .{foo, bar.baz} }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace commands parse");
        let Cmd::Use(CmdUse { decls }) = &cmds[1] else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].alias, Name::from_str("foo"));
        assert_eq!(decls[0].target, path("foo"));
        assert_eq!(decls[1].alias, Name::from_str("baz"));
        assert_eq!(decls[1].target, path("bar.baz"));
    }

    #[test]
    fn use_absolute_group_supports_aliases_and_nested_groups() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "use .{foo as f, bar.{baz as q}}",
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
        assert_eq!(decls[0].target, path("foo"));
        assert_eq!(decls[1].alias, Name::from_str("q"));
        assert_eq!(decls[1].target, path("bar.baz"));
    }

    #[test]
    fn use_absolute_scoped_group_is_resolved_from_root() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace local { use .root.{leaf as l} }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace commands parse");
        let Cmd::Use(CmdUse { decls }) = &cmds[1] else {
            panic!("expected use command");
        };
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].alias, Name::from_str("l"));
        assert_eq!(decls[0].target, path("root.leaf"));
    }

    #[test]
    fn use_scoped_group_rejects_absolute_entry() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let inputs = ["use .field.{.bar}", "use field.{.bar}"];
        for input in inputs {
            let mut use_table: HashMap<Name, Path> = HashMap::new();
            let err = parse_cmd_with_tables(
                input,
                &tt,
                &mut use_table,
                &type_consts,
                &consts,
                &axioms,
                &class_predicates,
            )
            .expect_err("absolute entry in scoped use group should be rejected");
            let ParseError::Parse { message, span: _ } = err else {
                panic!("expected parse error");
            };
            assert_eq!(message, "absolute path is not allowed in use group");
        }
    }

    #[test]
    fn use_group_rejects_top_level_absolute_entries() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_cmd_with_tables(
            "use {.foo, .bar}",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("absolute entries in use group should be rejected");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "absolute path is not allowed in use group");
    }

    #[test]
    fn use_cmd_parse_does_not_mutate_current_namespace_use_table() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let type_defs = HashMap::new();
        let file = Arc::new(File::new("<test>", "use bar as baz"));
        let mut lex = Lex::new(file);
        let root_namespace = Path::root();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let mut top_entry = Namespace::default();
        top_entry.add(Name::from_str("bar"), path("foo"));
        namespace_table.insert(root_namespace.clone(), top_entry);
        seed_namespace_table_from_globals(
            &mut namespace_table,
            &type_consts,
            &type_defs,
            &consts,
            &axioms,
            &class_predicates,
        );
        let current_namespace = root_namespace.clone();
        let mut parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        );
        let _ = parser.cmd().expect("use command parses");
        assert_eq!(
            namespace_table[&root_namespace]
                .use_table
                .get(&Name::from_str("baz")),
            None
        );
    }

    #[test]
    fn use_chain_resolves_alias_target_during_parse() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "foo");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        use_table.insert(Name::from_str("bar"), path("foo"));
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
        assert_eq!(decls[0].target, path("foo"));
    }

    #[test]
    fn use_target_resolves_alias_head_without_target_validation() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        use_table.insert(Name::from_str("bar"), path("foo"));
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
        assert_eq!(decls[0].target, path("foo.baz"));
    }

    #[test]
    fn use_shadowing_rebinds_alias_to_new_target() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "foo");
        insert_prop_const(&mut consts, "bar");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        use_table.insert(Name::from_str("name"), path("foo"));
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
        assert_eq!(decls[0].target, path("bar"));
    }

    #[test]
    fn use_group_alias_chain_uses_command_start_snapshot() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "hoge");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        assert_eq!(decls[0].target, path("hoge"));
        assert_eq!(decls[1].alias, Name::from_str("piyo"));
        assert_eq!(decls[1].target, path("fuga"));
    }

    #[test]
    fn use_group_swap_targets_use_command_start_snapshot() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        use_table.insert(Name::from_str("a"), path("left"));
        use_table.insert(Name::from_str("b"), path("right"));
        let cmd = parse_cmd_with_tables(
            "use {a as b, b as a}",
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
        assert_eq!(decls[0].alias, Name::from_str("b"));
        assert_eq!(decls[0].target, path("left"));
        assert_eq!(decls[1].alias, Name::from_str("a"));
        assert_eq!(decls[1].target, path("right"));
    }

    #[test]
    fn use_unknown_target_is_accepted() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        assert_eq!(decls[0].target, path("future.symbol"));
    }

    #[test]
    fn use_unknown_target_chain_in_same_group() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        assert_eq!(decls[0].target, path("future"));
        assert_eq!(decls[1].alias, Name::from_str("g"));
        assert_eq!(decls[1].target, path("f"));
    }

    #[test]
    fn use_unknown_target_fails_when_referenced() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        use_table.insert(Name::from_str("fst"), path("prod.fst"));
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
        assert_eq!(inner.id, global_id("prod.fst.default"));
    }

    #[test]
    fn infix_entity_rewrites_alias_head_without_target_validation() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        assert_eq!(entity, global_id("foo.baz"));
    }

    #[test]
    fn prefix_entity_rewrites_alias_head_without_target_validation() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        assert_eq!(entity, global_id("foo.baz"));
    }

    #[test]
    fn nofix_entity_rewrites_alias_head_without_target_validation() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        assert_eq!(entity, global_id("foo.baz"));
    }

    #[test]
    fn infix_entity_resolves_aliases_left_to_right_across_namespaces() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { use qux as inner namespace qux { use real as leaf } infix * : 50 := inner.leaf.tail }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace commands parse");
        assert_eq!(cmds.len(), 7);
        let Cmd::Infix(CmdInfix {
            op: _,
            prec: _,
            entity,
        }) = &cmds[5]
        else {
            panic!("expected infix command");
        };
        assert_eq!(entity, &global_id("foo.qux.real.tail"));
    }

    #[test]
    fn declaration_name_resolution_rewrites_use_alias_head() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        use_table.insert(Name::from_str("alias"), path("prod"));
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
        let Cmd::TypeConst(CmdTypeConst { id, kind: _ }) = cmd else {
            panic!("expected type_const command");
        };
        assert_eq!(id, global_id("prod.elem"));
    }

    #[test]
    fn type_def_command_parses() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "type def sub u := u → Prop",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("type def command parses");
        assert_eq!(cmd.to_string(), "type def sub.{u} := $u → Prop");
    }

    #[test]
    fn type_fixity_commands_parse() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("prod"), Kind(2));
        type_consts.insert(global_id("sum"), Kind(2));
        type_consts.insert(global_id("maybe"), Kind(1));
        type_consts.insert(global_id("unit"), Kind(0));
        let scenarios = [
            ("type infixr × : 35 := prod", "type infixr"),
            ("type infixl ⊕ : 35 := sum", "type infixl"),
            ("type infix ~ : 35 := sum", "type infix"),
            ("type prefix ‽ : 90 := maybe", "type prefix"),
            ("type nofix One := unit", "type nofix"),
        ];

        for (input, label) in scenarios {
            let mut use_table: HashMap<Name, Path> = HashMap::new();
            let cmd = parse_cmd_with_tables(
                input,
                &tt,
                &mut use_table,
                &type_consts,
                &consts,
                &axioms,
                &class_predicates,
            )
            .expect("type fixity command parses");
            match cmd {
                Cmd::TypeInfixr(cmd) => {
                    assert_eq!(cmd.entity, global_id("prod"), "label = {label}");
                    assert_eq!(cmd.prec, 35, "label = {label}");
                }
                Cmd::TypeInfixl(cmd) => {
                    assert_eq!(cmd.entity, global_id("sum"), "label = {label}");
                    assert_eq!(cmd.prec, 35, "label = {label}");
                }
                Cmd::TypeInfix(cmd) => {
                    assert_eq!(cmd.entity, global_id("sum"), "label = {label}");
                    assert_eq!(cmd.prec, 35, "label = {label}");
                }
                Cmd::TypePrefix(cmd) => {
                    assert_eq!(cmd.entity, global_id("maybe"), "label = {label}");
                    assert_eq!(cmd.prec, 90, "label = {label}");
                }
                Cmd::TypeNofix(cmd) => {
                    assert_eq!(cmd.entity, global_id("unit"), "label = {label}");
                }
                _ => panic!("expected type fixity command for {label}"),
            }
        }
    }

    #[test]
    fn absolute_type_fixity_entities_are_resolved_from_root() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("prod"), Kind(2));
        type_consts.insert(global_id("sum"), Kind(2));
        type_consts.insert(global_id("maybe"), Kind(1));
        type_consts.insert(global_id("unit"), Kind(0));
        let scenarios = [
            (
                "type infixr × : 35 := .prod",
                "type infixr",
                global_id("prod"),
            ),
            (
                "type infixl ⊕ : 35 := .sum",
                "type infixl",
                global_id("sum"),
            ),
            ("type infix ~ : 35 := .sum", "type infix", global_id("sum")),
            (
                "type prefix ‽ : 90 := .maybe",
                "type prefix",
                global_id("maybe"),
            ),
            ("type nofix One := .unit", "type nofix", global_id("unit")),
        ];
        for (command, label, expected_entity) in scenarios {
            let input = format!("namespace foo {{ {command} }}");
            let mut use_table: HashMap<Name, Path> = HashMap::new();
            let cmds = parse_cmds_with_tables(
                &input,
                &tt,
                &mut use_table,
                &type_consts,
                &consts,
                &axioms,
                &class_predicates,
            )
            .expect("commands parse");
            let entity = match &cmds[1] {
                Cmd::TypeInfixr(cmd) => &cmd.entity,
                Cmd::TypeInfixl(cmd) => &cmd.entity,
                Cmd::TypeInfix(cmd) => &cmd.entity,
                Cmd::TypePrefix(cmd) => &cmd.entity,
                Cmd::TypeNofix(cmd) => &cmd.entity,
                _ => panic!("expected type fixity command"),
            };
            assert_eq!(entity, &expected_entity, "label = {label}");
        }
    }

    #[test]
    fn type_def_reference_is_expanded_during_parsing() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("U"), Kind(0));
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "type def sub u := u → Prop
             const s : sub U",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::Const(CmdConst {
            id: _,
            local_types: _,
            local_classes: _,
            ty,
        }) = &cmds[1]
        else {
            panic!("expected const command");
        };
        assert_eq!(
            ty,
            &mk_type_const(global_id("Prop")).arrow([mk_type_const(global_id("U"))])
        );
    }

    #[test]
    fn type_def_multi_argument_reference_is_expanded_left_associatively() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("U"), Kind(0));
        type_consts.insert(global_id("V"), Kind(0));
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "type def pairish u v := u → v → Prop
             const s : pairish U V",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::Const(CmdConst {
            id: _,
            local_types: _,
            local_classes: _,
            ty,
        }) = &cmds[1]
        else {
            panic!("expected const command");
        };
        assert_eq!(
            ty,
            &mk_type_const(global_id("Prop"))
                .arrow([mk_type_const(global_id("U")), mk_type_const(global_id("V"))])
        );
    }

    #[test]
    fn declared_type_infixr_has_higher_precedence_than_arrow() {
        let (mut tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("U"), Kind(0));
        type_consts.insert(global_id("V"), Kind(0));
        type_consts.insert(global_id("W"), Kind(0));
        type_consts.insert(global_id("prod"), Kind(2));
        tt.add_type(Operator {
            symbol: "×".to_owned(),
            fixity: Fixity::Infixr,
            prec: 35,
            entity: global_id("prod"),
        })
        .expect("register type infixr");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let ty = parse_type_with_tables(
            "U × V → W",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("type parses");
        assert_eq!(
            ty,
            mk_type_arrow(
                mk_type_const(global_id("prod"))
                    .apply([mk_type_const(global_id("U")), mk_type_const(global_id("V"))]),
                mk_type_const(global_id("W"))
            )
        );
    }

    #[test]
    fn declared_type_infixr_is_right_associative() {
        let (mut tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("U"), Kind(0));
        type_consts.insert(global_id("V"), Kind(0));
        type_consts.insert(global_id("W"), Kind(0));
        type_consts.insert(global_id("prod"), Kind(2));
        tt.add_type(Operator {
            symbol: "×".to_owned(),
            fixity: Fixity::Infixr,
            prec: 35,
            entity: global_id("prod"),
        })
        .expect("register type infixr");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let ty = parse_type_with_tables(
            "U × V × W",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("type parses");
        assert_eq!(
            ty,
            mk_type_const(global_id("prod")).apply([
                mk_type_const(global_id("U")),
                mk_type_const(global_id("prod"))
                    .apply([mk_type_const(global_id("V")), mk_type_const(global_id("W"))]),
            ])
        );
    }

    #[test]
    fn declared_type_prefix_binds_tighter_than_application() {
        let (mut tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("U"), Kind(0));
        type_consts.insert(global_id("F"), Kind(1));
        type_consts.insert(global_id("maybe"), Kind(1));
        tt.add_type(Operator {
            symbol: "◻".to_owned(),
            fixity: Fixity::Prefix,
            prec: 90,
            entity: global_id("maybe"),
        })
        .expect("register type prefix");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let ty = parse_type_with_tables(
            "F ◻U",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("type parses");
        assert_eq!(
            ty,
            mk_type_const(global_id("F"))
                .apply([mk_type_const(global_id("maybe")).apply([mk_type_const(global_id("U"))])])
        );
    }

    #[test]
    fn recursive_type_def_is_rejected() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_cmd_with_tables(
            "type def foo := foo",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("recursive type def should fail");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "unknown type constant");
    }

    #[test]
    fn type_def_rhs_and_reference_resolve_use_aliases() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("foo.U"), Kind(0));
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo {
                 use .foo as self
                 type def sub alias := alias → self.U
                 const s : sub U
             }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("commands parse");
        let Cmd::Const(CmdConst {
            id: _,
            local_types: _,
            local_classes: _,
            ty,
        }) = &cmds[3]
        else {
            panic!("expected const command");
        };
        assert_eq!(
            ty,
            &mk_type_const(global_id("foo.U")).arrow([mk_type_const(global_id("foo.U"))])
        );
    }

    #[test]
    fn type_inductive_constructor_rejects_dotted_name() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_cmd_with_tables(
            "type inductive foo | bar.baz : foo",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("dotted constructor name should be rejected");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "expected symbol ':'");
    }

    #[test]
    fn inductive_constructor_rejects_dotted_name() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_cmd_with_tables(
            "inductive foo : Prop | bar.baz : foo",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("dotted constructor name should be rejected");
        let ParseError::Parse { message, span: _ } = err else {
            panic!("expected parse error");
        };
        assert_eq!(message, "expected symbol ':'");
    }

    #[test]
    fn type_inductive_ctor_parse_does_not_mutate_top_level_use_table() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
            !use_table.contains_key(&Name::from_str("ctor")),
            "parsing must not mutate current namespace aliases"
        );
    }

    #[test]
    fn type_inductive_command_parses_with_this_and_type_inductive_constructor() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "type inductive foo u | mk : foo u",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("type inductive command parses");
        let Cmd::TypeInductive(CmdTypeInductive {
            id,
            this,
            this_name,
            local_types,
            ind_id,
            rec_id,
            ctors,
        }) = cmd
        else {
            panic!("expected type inductive command");
        };
        assert_eq!(this_name, Name::from_str("foo"));
        assert_eq!(id, global_id("foo"));
        assert_eq!(ind_id, global_id("foo.ind"));
        assert_eq!(rec_id, global_id("foo.rec"));
        assert_eq!(local_types.len(), 1);
        assert_ne!(this, local_types[0].id);
        let [
            TypeInductiveConstructor {
                ctor_id,
                name,
                ctor_spec_id,
                ty,
            },
        ] = ctors.as_slice()
        else {
            panic!("expected one type inductive constructor");
        };
        assert_eq!(name, &Name::from_str("mk"));
        assert_eq!(ctor_id, &global_id("foo.mk"));
        assert_eq!(ctor_spec_id, &global_id("foo.mk.spec"));
        assert_eq!(
            ty,
            &mk_type_local(this).apply([mk_type_local(local_types[0].id)])
        );
    }

    #[test]
    fn inductive_command_parses_with_this_and_inductive_constructor() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmd = parse_cmd_with_tables(
            "inductive foo : Prop | mk (h : Prop) : foo",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("inductive command parses");
        let Cmd::Inductive(CmdInductive {
            id,
            this,
            this_name,
            local_types,
            params,
            target_ty,
            ind_id,
            ctors,
        }) = cmd
        else {
            panic!("expected inductive command");
        };
        assert_eq!(this_name, Name::from_str("foo"));
        assert_eq!(id, global_id("foo"));
        assert_eq!(ind_id, global_id("foo.ind"));
        assert!(local_types.is_empty());
        assert!(params.is_empty());
        assert_eq!(target_ty, mk_type_prop());
        let [
            InductiveConstructor {
                ctor_id,
                name,
                target,
            },
        ] = ctors.as_slice()
        else {
            panic!("expected one inductive constructor");
        };
        assert_eq!(name, &Name::from_str("mk"));
        assert_eq!(ctor_id, &global_id("foo.mk"));
        let (ctor_params, ctor_body) = ungeneralize(target);
        assert_eq!(ctor_params.len(), 1);
        let (ctor_args, ctor_target) = unguard(&ctor_body);
        assert!(ctor_args.is_empty());
        assert!(ctor_target.head().alpha_eq(&mk_local(this)));
    }

    #[test]
    fn resolve_to_path_stops_after_first_missing_alias() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let root_namespace = Path::root();
        namespace_table.insert(root_namespace, Namespace::default());
        namespace_table.insert(path("foo"), Namespace::default());
        namespace_table.insert(path("foo.qux.real"), Namespace::default());
        let mut qux_namespace = Namespace::default();
        qux_namespace.add(Name::from_str("leaf"), path("foo.qux.real"));
        namespace_table.insert(path("foo.qux"), qux_namespace);
        let current_namespace = path("foo");
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("qux.leaf"));
        assert_eq!(resolved, path("foo.qux.leaf"));
        assert_eq!(
            parser.resolve(qualified("qux.leaf")).to_global_id(),
            global_id("foo.qux.leaf")
        );
    }

    #[test]
    fn resolve_stops_after_first_missing_alias() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let root_namespace = Path::root();
        namespace_table.insert(root_namespace, Namespace::default());
        namespace_table.insert(path("foo"), Namespace::default());
        namespace_table.insert(path("foo.qux.real"), Namespace::default());
        let mut qux_namespace = Namespace::default();
        qux_namespace.add(Name::from_str("leaf"), path("foo.qux.real"));
        namespace_table.insert(path("foo.qux"), qux_namespace);
        let current_namespace = path("foo");
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("qux.leaf"));
        assert_eq!(resolved, path("foo.qux.leaf"));
    }

    #[test]
    fn resolve_does_not_create_missing_namespaces_along_path() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let root_namespace = Path::root();
        namespace_table.insert(root_namespace.clone(), Namespace::default());
        let current_namespace = root_namespace;
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("qux.quux"));
        assert_eq!(resolved, path("qux.quux"));
        assert!(
            !parser.namespace_table.contains_key(&path("qux")),
            "resolve should not create intermediate namespace entries"
        );
        assert!(
            !parser.namespace_table.contains_key(&path("qux.quux")),
            "resolve should not create terminal namespace entries"
        );
        assert_eq!(
            parser.namespace_table[&Path::root()]
                .use_table
                .get(&Name::from_str("qux")),
            None
        );
    }

    #[test]
    fn resolve_preserves_remaining_tail_after_first_missing_alias() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let root_namespace = Path::root();
        namespace_table.insert(root_namespace, Namespace::default());
        namespace_table.insert(path("foo"), Namespace::default());
        namespace_table.insert(path("foo.qux.real"), Namespace::default());
        let mut qux_namespace = Namespace::default();
        qux_namespace.add(Name::from_str("leaf"), path("foo.qux.real"));
        namespace_table.insert(path("foo.qux"), qux_namespace);
        let current_namespace = path("foo");
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("qux.leaf.tail"));
        assert_eq!(resolved, path("foo.qux.leaf.tail"));
    }

    #[test]
    fn resolve_alias_tail_without_namespace_entry_for_alias_target() {
        let file = Arc::new(File::new("<test>", ""));
        let mut lex = Lex::new(file);
        let tt = TokenTable::default();
        let mut namespace_table: HashMap<Path, Namespace> = HashMap::new();
        let root_namespace = Path::root();
        namespace_table.insert(root_namespace.clone(), Namespace::default());
        let current_namespace = path("subset");
        let mut subset_namespace = Namespace::default();
        subset_namespace.add(Name::from_str("iff"), path("iff"));
        namespace_table.insert(current_namespace.clone(), subset_namespace);
        let type_const_table = HashMap::new();
        let const_table = HashMap::new();
        let axiom_table = HashMap::new();
        let class_predicate_table = HashMap::new();
        let parser = new_parser_without_type_defs(
            &mut lex,
            &tt,
            &namespace_table,
            &current_namespace,
            &type_const_table,
            &const_table,
            &axiom_table,
            &class_predicate_table,
        );

        let resolved = parser.resolve(qualified("iff.intro"));
        assert_eq!(resolved, path("iff.intro"));
        assert!(
            !parser.namespace_table.contains_key(&path("iff")),
            "resolve should not require or create namespace entries for alias target paths"
        );
    }

    #[test]
    fn let_term_expr_without_type_annotation_parses() {
        let expr = parse_expr("let c := p, assume c as h, h");
        let Expr::LetTerm(let_term) = expr else {
            panic!("expected let-term expression");
        };
        let ExprLetTerm {
            metadata: _,
            id,
            name,
            ty,
            value,
            body,
        } = *let_term;
        assert_eq!(name, Some(Name::from_str("c")));
        assert!(ty.is_none());
        let Term::Const(value_const) = value else {
            panic!("expected const term in let value");
        };
        assert_eq!(value_const.id, global_id("p"));
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
        assert_eq!(local_const.id, id);
    }

    #[test]
    fn let_term_expr_with_type_annotation_parses() {
        let expr = parse_expr("let c : Prop := p, assume c as h, h");
        let Expr::LetTerm(let_term) = expr else {
            panic!("expected let-term expression");
        };
        let ExprLetTerm {
            metadata: _,
            id: _,
            name: _,
            ty,
            value: _,
            body: _,
        } = *let_term;
        let Some(ty) = ty else {
            panic!("expected type annotation");
        };
        assert_eq!(ty, mk_type_const(global_id("Prop")));
    }

    #[test]
    fn let_term_expr_rejects_qualified_binder() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        use_table.insert(Name::from_str("c"), path("global.target"));
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
            id,
            name,
            ty: _,
            value: _,
            body,
        } = *let_term;
        assert_eq!(name, Some(Name::from_str("c")));
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
        assert_eq!(local_const.id, id);
    }

    #[test]
    fn shadowed_let_term_uses_distinct_ids() {
        let expr = parse_expr("let h := p, let h := h, assume h as hp, hp");
        let Expr::LetTerm(outer_let) = expr else {
            panic!("expected outer let");
        };

        let Expr::LetTerm(inner_let) = outer_let.body else {
            panic!("expected inner let");
        };
        let Term::Local(inner_value) = inner_let.value else {
            panic!("expected inner let value to reference outer binder");
        };

        let Expr::Assume(assume) = inner_let.body else {
            panic!("expected assume in inner let body");
        };
        let Term::Local(inner_target) = assume.local_axiom else {
            panic!("expected inner let body to reference inner binder");
        };

        assert_ne!(inner_value.id, inner_target.id);
    }

    #[test]
    fn let_structure_body_uses_local_term() {
        let expr = parse_expr("let structure foo := { const f : Prop }, assume foo.f as h, h");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Some(LocalStructureField::Const(field)) = let_structure.fields.first() else {
            panic!("expected local const field");
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
        assert_eq!(local_const.id, field.id);
    }

    #[test]
    fn let_structure_const_field_keeps_bare_and_qualified_ids() {
        let expr = parse_expr("let structure foo := { const f : Prop }, assume foo.f as h, h");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Some(LocalStructureField::Const(field)) = let_structure.fields.first() else {
            panic!("expected local const field");
        };
        assert_eq!(field.field_name, Name::from_str("f"));
        assert_eq!(field.name, Name::from_str("foo.f"));
        let Expr::Assume(assume) = let_structure.body else {
            panic!("expected assume expression in let structure body");
        };
        let Term::Local(local_const) = assume.local_axiom else {
            panic!("expected local term");
        };
        assert_eq!(local_const.id, field.id);
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
        let Some(LocalStructureField::Const(outer_field)) = outer.fields.first() else {
            panic!("expected outer local const field");
        };
        let Some(LocalStructureField::Const(inner_field)) = inner.fields.first() else {
            panic!("expected inner local const field");
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
        assert_eq!(local_const.id, inner_field.id);
        assert_ne!(local_const.id, outer_field.id);
    }

    #[test]
    fn let_structure_local_has_priority_over_global_const() {
        let (tt, type_consts, mut consts, axioms, class_predicates) = setup_tables();
        insert_prop_const(&mut consts, "foo.f");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        let Some(LocalStructureField::Const(field)) = let_structure.fields.first() else {
            panic!("expected local const field");
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
        assert_eq!(local_const.id, field.id);
    }

    #[test]
    fn let_structure_bare_field_name_does_not_bind_in_body() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_expr_with_tables(
            "let structure foo := { const x : Prop }, x",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("bare field name should not resolve in let structure body");
        assert!(err.to_string().contains("unknown variable"));
    }

    #[test]
    fn let_structure_rejects_duplicate_const_field_names() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_expr_with_tables(
            "let structure foo := { const f : Prop const f : Prop }, foo.f",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("duplicate const field should be rejected");
        assert!(err.to_string().contains("duplicate field"));
    }

    #[test]
    fn let_structure_rejects_duplicate_axiom_field_names() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_expr_with_tables(
            "let structure foo := { const f : Prop axiom a : f axiom a : f }, @foo.a",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("duplicate axiom field should be rejected");
        assert!(err.to_string().contains("duplicate field"));
    }

    #[test]
    fn let_structure_rejects_const_axiom_name_collision() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let err = parse_expr_with_tables(
            "let structure foo := { const f : Prop axiom f : f }, @foo.f",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect_err("const/axiom name collision should be rejected");
        assert!(err.to_string().contains("duplicate field"));
    }

    #[test]
    fn let_structure_local_axiom_is_parsed_as_local_expr() {
        let expr = parse_expr("let structure foo := { const f : Prop axiom a : f }, @foo.a");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Some(LocalStructureField::Axiom(field)) = let_structure.fields.get(1) else {
            panic!("expected local axiom field");
        };
        let Expr::Local(local_axiom) = let_structure.body else {
            panic!("expected local expression in let structure body");
        };
        assert_eq!(local_axiom.id, field.id);
    }

    #[test]
    fn let_structure_axiom_field_keeps_bare_and_qualified_ids() {
        let expr = parse_expr("let structure foo := { const f : Prop axiom a : f }, @foo.a");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Some(LocalStructureField::Axiom(field)) = let_structure.fields.get(1) else {
            panic!("expected local axiom field");
        };
        assert_eq!(field.field_name, Name::from_str("a"));
        let Expr::Local(local_axiom) = let_structure.body else {
            panic!("expected local expression in let structure body");
        };
        assert_eq!(local_axiom.id, field.id);
    }

    #[test]
    fn let_structure_axiom_target_uses_bare_const_field_id() {
        let expr = parse_expr("let structure foo := { const x : Prop axiom a : x }, @foo.a");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Some(LocalStructureField::Const(const_field)) = let_structure.fields.first() else {
            panic!("expected local const field");
        };
        let Some(LocalStructureField::Axiom(axiom_field)) = let_structure.fields.get(1) else {
            panic!("expected local axiom field");
        };
        let Term::Local(local) = &axiom_field.target else {
            panic!("expected local structure axiom target to reference the const field");
        };
        assert_eq!(local.id, const_field.field_id);
        assert_ne!(const_field.field_id, const_field.id);
    }

    #[test]
    fn let_structure_local_axiom_ignores_whitespace_before_segment() {
        let expr = parse_expr("let structure foo := { const f : Prop axiom a : f }, @foo .a");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Some(LocalStructureField::Axiom(field)) = let_structure.fields.get(1) else {
            panic!("expected local axiom field");
        };
        let Expr::Local(local_axiom) = let_structure.body else {
            panic!("expected local expression in let structure body");
        };
        assert_eq!(local_axiom.id, field.id);
    }

    #[test]
    fn let_structure_local_axiom_without_at_is_parsed_as_local_expr() {
        let expr = parse_expr("let structure foo := { const f : Prop axiom a : f }, foo.a");
        let Expr::LetStructure(let_structure) = expr else {
            panic!("expected let structure expression");
        };
        let Some(LocalStructureField::Axiom(field)) = let_structure.fields.get(1) else {
            panic!("expected local axiom field");
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
        assert_eq!(local_axiom.id, field.id);
        assert!(arg.head().is_hole());
    }

    #[test]
    fn shadowed_let_structure_abs_keeps_outer_id_in_inner_field() {
        let expr = parse_expr(
            "let structure foo := { const f : Prop }, \
             let structure foo := { const f : Prop }, \
             assume foo.f as h, h",
        );
        let Expr::LetStructure(outer) = expr else {
            panic!("expected outer let structure");
        };
        let Expr::LetStructure(inner) = outer.body else {
            panic!("expected inner let structure");
        };
        let Some(LocalStructureField::Const(outer_field)) = outer.fields.first() else {
            panic!("expected outer field to be a const");
        };
        let Expr::Assume(inner_assume) = inner.body else {
            panic!("expected inner body assume");
        };
        let Term::Local(inner_field_ref) = inner_assume.local_axiom else {
            panic!("expected inner body to reference inner local const");
        };
        assert_ne!(outer_field.id, inner_field_ref.id);
    }

    #[test]
    fn obtain_instance_desugars_to_let_have_and_obtain() {
        let (tt, mut type_consts, consts, mut axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("foo"), Kind(0));
        axioms.insert(
            global_id("hp"),
            Axiom {
                local_types: vec![],
                local_classes: vec![],
                target: mk_const(global_id("p"), vec![], vec![]),
            },
        );
        let rep_field_id = Id::fresh();
        let structure_table = HashMap::from([(
            global_id("foo"),
            CmdStructure {
                id: global_id("foo"),
                local_types: vec![],
                abs_id: global_id("foo.abs"),
                fields: vec![
                    StructureField::Const(StructureConst {
                        field_id: rep_field_id,
                        field_name: Name::from_str("rep"),
                        id: global_id("foo.rep"),
                        ty: mk_type_const(global_id("Prop")),
                    }),
                    StructureField::Axiom(StructureAxiom {
                        field_name: Name::from_str("ok"),
                        id: global_id("foo.ok"),
                        target: mk_local(rep_field_id),
                    }),
                ],
            },
        )]);
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let expr = parse_expr_with_structure_tables(
            "obtain instance c : foo := { def rep : Prop := p lemma ok : rep := hp }, c.ok",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
            &structure_table,
        )
        .expect("expression parses");

        let Expr::LetTerm(let_term) = expr else {
            panic!("expected outer let-term");
        };
        assert_eq!(let_term.name, Some(Name::from_str("c.rep")));
        let Term::Const(value_const) = let_term.value else {
            panic!("expected let value to be a const");
        };
        assert_eq!(value_const.id, global_id("p"));

        let Expr::App(have_app) = let_term.body else {
            panic!("expected let body to be a have expansion");
        };
        let Expr::Assume(have_assume) = have_app.expr1 else {
            panic!("expected have expansion to start with assume");
        };
        let (ok_id, ok_name) = have_assume.alias.expect("expected c.ok alias");
        assert_eq!(ok_name, Name::from_str("c.ok"));
        let Term::Local(local_axiom) = have_assume.local_axiom else {
            panic!("expected have target to reference c.rep");
        };
        assert_eq!(local_axiom.id, let_term.id);
        let Expr::Const(proof) = have_app.expr2 else {
            panic!("expected have proof to be hp");
        };
        assert_eq!(proof.id, global_id("hp"));

        let Expr::App(obtain_app) = have_assume.expr else {
            panic!("expected have body to be an obtain expansion");
        };
        let Expr::Take(take) = obtain_app.expr2 else {
            panic!("expected obtain body to be a take");
        };
        assert_eq!(take.name, Some(Name::from_str("c")));
        let Expr::Assume(obtain_assume) = take.expr else {
            panic!("expected obtain take body to be an assume");
        };
        let Expr::Local(body_local) = obtain_assume.expr else {
            panic!("expected obtain body to use c.ok");
        };
        assert_eq!(body_local.id, ok_id);
    }

    #[test]
    fn obtain_instance_later_lemma_uses_prior_field_ids() {
        let (tt, mut type_consts, consts, mut axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("foo"), Kind(0));
        axioms.insert(
            global_id("hp"),
            Axiom {
                local_types: vec![],
                local_classes: vec![],
                target: mk_const(global_id("p"), vec![], vec![]),
            },
        );
        let structure_table = HashMap::from([(
            global_id("foo"),
            CmdStructure {
                id: global_id("foo"),
                local_types: vec![],
                abs_id: global_id("foo.abs"),
                fields: vec![
                    StructureField::Axiom(StructureAxiom {
                        field_name: Name::from_str("ok"),
                        id: global_id("foo.ok"),
                        target: mk_const(global_id("p"), vec![], vec![]),
                    }),
                    StructureField::Axiom(StructureAxiom {
                        field_name: Name::from_str("ok2"),
                        id: global_id("foo.ok2"),
                        target: mk_const(global_id("p"), vec![], vec![]),
                    }),
                ],
            },
        )]);
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let expr = parse_expr_with_structure_tables(
            "obtain instance c : foo := { lemma ok : p := hp lemma ok2 : p := ok }, c.ok2",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
            &structure_table,
        )
        .expect("expression parses");

        let Expr::App(first_have) = expr else {
            panic!("expected outer have expansion");
        };
        let Expr::Assume(first_assume) = first_have.expr1 else {
            panic!("expected outer assume");
        };
        let (first_alias, first_alias_name) = first_assume.alias.expect("expected first alias");
        assert_eq!(first_alias_name, Name::from_str("c.ok"));

        let Expr::App(second_have) = first_assume.expr else {
            panic!("expected inner have expansion");
        };
        let Expr::Assume(second_assume) = second_have.expr1 else {
            panic!("expected inner assume");
        };
        let (_second_alias, second_alias_name) =
            second_assume.alias.expect("expected second alias");
        assert_eq!(second_alias_name, Name::from_str("c.ok2"));
        let Expr::Local(second_proof) = second_have.expr2 else {
            panic!("expected second proof to reference prior lemma");
        };
        assert_eq!(second_proof.id, first_alias);
    }

    #[test]
    fn namespace_command_parses_const_with_prefixed_name() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("Type"), Kind(0));
        type_consts.insert(global_id("foo.Prop"), Kind(0));
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { const bar : Prop }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace commands parse");
        let Cmd::NamespaceStart(namespace_start) = &cmds[0] else {
            panic!("expected namespace start");
        };
        assert_eq!(namespace_start.path, path("foo"));
        let Cmd::Const(inner) = &cmds[1] else {
            panic!("expected const command");
        };
        assert_eq!(inner.id, global_id("foo.bar"));
        assert!(matches!(cmds[2], Cmd::BlockEnd));
    }

    #[test]
    fn namespace_block_is_parsed_incrementally() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace block parses");
        assert_eq!(cmds.len(), 2);
        assert_eq!(format!("{}", cmds[0]), "namespace foo {");
        assert_eq!(format!("{}", cmds[1]), "}");
    }

    #[test]
    fn namespace_qualified_declaration_creates_child_path() {
        let (tt, mut type_consts, consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("Type"), Kind(0));
        type_consts.insert(global_id("foo.bar.Prop"), Kind(0));
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo.bar { const qux.quux : Prop }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace commands parse");
        let Cmd::NamespaceStart(namespace_start) = &cmds[0] else {
            panic!("expected namespace start");
        };
        assert_eq!(namespace_start.path, path("foo.bar"));
        let Cmd::Const(inner) = &cmds[1] else {
            panic!("expected const command");
        };
        assert_eq!(inner.id, global_id("foo.bar.qux.quux"));
        assert!(matches!(cmds[2], Cmd::BlockEnd));
    }

    #[test]
    fn qualified_def_at_top_level_creates_missing_namespace() {
        let (tt, type_consts, consts, axioms, class_predicates) = setup_tables();
        let mut use_table: HashMap<Name, Path> = HashMap::new();
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
        assert_eq!(def_cmd.id, global_id("qux.quux"));
    }

    #[test]
    fn namespace_qualified_def_creates_missing_namespace_under_current() {
        let (tt, mut type_consts, mut consts, axioms, class_predicates) = setup_tables();
        type_consts.insert(global_id("foo.Prop"), Kind(0));
        insert_prop_const(&mut consts, "foo.p");
        let mut use_table: HashMap<Name, Path> = HashMap::new();
        let cmds = parse_cmds_with_tables(
            "namespace foo { def qux.quux : Prop := p }",
            &tt,
            &mut use_table,
            &type_consts,
            &consts,
            &axioms,
            &class_predicates,
        )
        .expect("namespace commands parse");
        let Cmd::NamespaceStart(namespace_start) = &cmds[0] else {
            panic!("expected namespace start");
        };
        assert_eq!(namespace_start.path, path("foo"));
        let Cmd::Def(def_cmd) = &cmds[1] else {
            panic!("expected def command");
        };
        assert_eq!(def_cmd.id, global_id("foo.qux.quux"));
        assert!(matches!(cmds[2], Cmd::BlockEnd));
    }
}
