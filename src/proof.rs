//! Prove by type synthesis.

use std::sync::LazyLock;
use std::{collections::HashMap, iter::zip, slice};

use crate::{
    lex::Span,
    tt::{
        self, Class, Id, Instance, Local, LocalDelta, Name, QualifiedName, Term, Type, mk_abs,
        mk_const, mk_local, mk_type_const, mk_type_local,
    },
};

pub fn mk_type_prop() -> Type {
    static T_PROP: LazyLock<Type> =
        LazyLock::new(|| mk_type_const(QualifiedName::from_str("Prop")));
    T_PROP.clone()
}

pub fn count_forall(term: &Term) -> usize {
    static FORALL: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("forall"));

    let mut count = 0;
    let mut current = term;
    loop {
        let Term::App(app) = current else {
            break;
        };
        let app = app.as_ref();
        let Term::Const(head) = &app.fun else {
            break;
        };
        if head.name != *FORALL {
            break;
        }
        let Term::Abs(abs) = &app.arg else {
            break;
        };
        let body = &abs.as_ref().body;
        count += 1;
        current = body;
    }

    count
}

pub fn generalize(term: &Term, xs: &[Local]) -> Term {
    static FORALL: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("forall"));

    let locals = xs.iter().map(|x| x.id).collect::<Vec<_>>();
    let mut result = term.close(&locals, 0);
    for x in xs.iter().rev() {
        result = mk_abs(x.id.name(), x.ty.clone(), result);
        let mut c = mk_const(FORALL.clone(), vec![x.ty.clone()], vec![]);
        c = c.apply([result]);
        result = c;
    }
    result
}

pub fn ungeneralize(term: &Term) -> (Vec<Local>, Term) {
    let mut acc = vec![];
    let mut current = term.clone();
    while let Some((binder, body)) = ungeneralize1(&current) {
        acc.push(binder);
        current = body;
    }
    (acc, current)
}

pub fn ungeneralize1(term: &Term) -> Option<(Local, Term)> {
    static FORALL: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("forall"));

    let Term::App(m) = term else {
        return None;
    };
    let Term::Const(head) = &m.fun else {
        return None;
    };
    if head.name != *FORALL {
        return None;
    }
    let Term::Abs(abs) = &m.arg else {
        return None;
    };
    let tt::TermAbs {
        metadata: _,
        binder_type,
        binder_name,
        body,
    } = &**abs;
    let id = match binder_name {
        Some(name) => Id::fresh_with_name(name.clone()),
        None => Id::fresh(),
    };
    let body = body.open(&[mk_local(id)], 0);
    let binder = Local {
        id,
        ty: binder_type.clone(),
    };
    Some((binder, body))
}

pub fn guard(term: &Term, guards: impl IntoIterator<Item = Term>) -> Term {
    guard_help(term.clone(), guards.into_iter())
}

fn guard_help(target: Term, mut guards: impl Iterator<Item = Term>) -> Term {
    static IMP: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("imp"));

    if let Some(guard_term) = guards.next() {
        let inner = guard_help(target, guards);
        let mut m = mk_const(IMP.clone(), vec![], vec![]);
        m = m.apply([guard_term, inner]);
        m
    } else {
        target
    }
}

pub fn unguard(term: &Term) -> (Vec<Term>, Term) {
    let mut acc = vec![];
    let mut current = term.clone();
    while let Some((lhs, rhs)) = unguard1(&current) {
        acc.push(lhs);
        current = rhs;
    }
    (acc, current)
}

pub fn unguard1(term: &Term) -> Option<(Term, Term)> {
    static IMP: LazyLock<QualifiedName> = LazyLock::new(|| QualifiedName::from_str("imp"));

    let Term::App(m) = term else {
        return None;
    };
    let Term::App(n) = &m.fun else {
        return None;
    };
    let Term::Const(head) = &n.fun else {
        return None;
    };
    if head.name != *IMP {
        return None;
    }
    Some((n.arg.clone(), m.arg.clone()))
}

/// p ::= «φ»
///     | assume φ, p
///     | p p
///     | take (x : τ), p
///     | p[m]
///     | c.{u₁, ⋯, uₙ}
///     | change φ, p
///
///
/// --------------- (φ ∈ Φ)
/// Γ | Φ ⊢ «φ» : φ
///
/// Γ | Φ, φ ⊢ h : ψ
/// ----------------------------
/// Γ | Φ ⊢ assume φ, h : φ → ψ
///
/// Γ | Φ ⊢ h₁ : ψ → ξ    Γ | Φ ⊢ h₂ : ψ
/// -------------------------------------
/// Γ | Φ ⊢ h₁ h₂ : ξ
///
/// Γ, x : u | Φ ⊢ h : φ
/// --------------------------------------- (x # Φ)
/// Γ | Φ ⊢ take (x : u), h : ∀ (x : u), φ
///
/// Γ | Φ ⊢ h : ∀ x, ψ
/// --------------------- (Γ ⊢ m : u)
/// Γ | Φ ⊢ h[m] : ψ[m/x]
///
/// -------------------------
/// Γ | Φ ⊢ c.{u₁, ⋯, uₙ} : φ
///
/// Γ | Φ ⊢ h : ψ     ψ ≈ φ
/// ------------------------
/// Γ | Φ ⊢ change φ, h : φ
///
#[derive(Debug, Clone, Default)]
pub struct ExprMetadata {
    pub span: Option<Span>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Assump(Box<ExprAssump>),
    Local(Box<ExprLocal>),
    Assume(Box<ExprAssume>),
    App(Box<ExprApp>),
    Take(Box<ExprTake>),
    Inst(Box<ExprInst>),
    Const(Box<ExprConst>),
    LetTerm(Box<ExprLetTerm>),
    LetStructure(Box<ExprLetStructure>),
    Change(Box<ExprChange>),
}

#[derive(Debug, Clone)]
pub struct ExprAssump {
    pub metadata: ExprMetadata,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct ExprLocal {
    pub metadata: ExprMetadata,
    pub id: Id,
}

#[derive(Debug, Clone)]
pub struct ExprAssume {
    pub metadata: ExprMetadata,
    pub local_axiom: Term,
    pub alias: Option<Id>,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprApp {
    pub metadata: ExprMetadata,
    pub expr1: Expr,
    pub expr2: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprTake {
    pub metadata: ExprMetadata,
    pub id: Id,
    pub ty: Type,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprInst {
    pub metadata: ExprMetadata,
    pub expr: Expr,
    pub arg: Term,
}

#[derive(Debug, Clone)]
pub struct ExprConst {
    pub metadata: ExprMetadata,
    pub name: QualifiedName,
    pub ty_args: Vec<Type>,
    pub instances: Vec<Instance>,
}

#[derive(Debug, Clone)]
pub struct ExprLetTerm {
    pub metadata: ExprMetadata,
    pub name: QualifiedName,
    pub ty: Option<Type>,
    pub value: Term,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprChange {
    pub metadata: ExprMetadata,
    pub target: Term,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprLetStructure {
    pub metadata: ExprMetadata,
    pub name: Name,
    pub fields: Vec<LocalStructureField>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub enum LocalStructureField {
    Const(LocalStructureConst),
    Axiom(LocalStructureAxiom),
}

#[derive(Debug, Clone)]
pub struct LocalStructureConst {
    pub name: Name,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct LocalStructureAxiom {
    pub name: Name,
    pub target: Term,
}

impl Default for Expr {
    fn default() -> Self {
        static DEFAULT: LazyLock<Expr> = LazyLock::new(|| mk_expr_assump(Default::default()));
        DEFAULT.clone()
    }
}

pub fn mk_expr_assump(m: Term) -> Expr {
    Expr::Assump(Box::new(ExprAssump {
        metadata: ExprMetadata::default(),
        target: m,
    }))
}

pub fn mk_expr_local(id: Id) -> Expr {
    Expr::Local(Box::new(ExprLocal {
        metadata: ExprMetadata::default(),
        id,
    }))
}

pub fn mk_expr_assume(h: Term, alias: Option<Id>, e: Expr) -> Expr {
    Expr::Assume(Box::new(ExprAssume {
        metadata: ExprMetadata::default(),
        local_axiom: h,
        alias,
        expr: e,
    }))
}

pub fn mk_expr_app(e1: Expr, e2: Expr) -> Expr {
    Expr::App(Box::new(ExprApp {
        metadata: ExprMetadata::default(),
        expr1: e1,
        expr2: e2,
    }))
}

pub fn mk_expr_take(id: Id, ty: Type, e: Expr) -> Expr {
    Expr::Take(Box::new(ExprTake {
        metadata: ExprMetadata::default(),
        id,
        ty,
        expr: e,
    }))
}

pub fn mk_expr_inst(e: Expr, m: Term) -> Expr {
    Expr::Inst(Box::new(ExprInst {
        metadata: ExprMetadata::default(),
        expr: e,
        arg: m,
    }))
}

pub fn mk_expr_const(name: QualifiedName, ty_args: Vec<Type>, instances: Vec<Instance>) -> Expr {
    Expr::Const(Box::new(ExprConst {
        metadata: ExprMetadata::default(),
        name,
        ty_args,
        instances,
    }))
}

pub fn mk_expr_let_term(name: QualifiedName, ty: Option<Type>, value: Term, body: Expr) -> Expr {
    Expr::LetTerm(Box::new(ExprLetTerm {
        metadata: ExprMetadata::default(),
        name,
        ty,
        value,
        body,
    }))
}

pub fn mk_expr_let_structure(name: Name, fields: Vec<LocalStructureField>, body: Expr) -> Expr {
    Expr::LetStructure(Box::new(ExprLetStructure {
        metadata: ExprMetadata::default(),
        name,
        fields,
        body,
    }))
}

pub fn mk_expr_change(target: Term, expr: Expr) -> Expr {
    Expr::Change(Box::new(ExprChange {
        metadata: ExprMetadata::default(),
        target,
        expr,
    }))
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const PREC_LOWEST: u8 = 0;
        const PREC_PREFIX: u8 = 1;
        const PREC_APP: u8 = 2;
        const PREC_INST: u8 = 3;
        const PREC_ATOM: u8 = 4;

        fn precedence(expr: &Expr) -> u8 {
            match expr {
                Expr::Assump(_) | Expr::Local(_) | Expr::Const(_) => PREC_ATOM,
                Expr::Inst(_) => PREC_INST,
                Expr::App(_) => PREC_APP,
                Expr::Assume(_)
                | Expr::Take(_)
                | Expr::LetTerm(_)
                | Expr::LetStructure(_)
                | Expr::Change(_) => PREC_PREFIX,
            }
        }

        fn collect_inst_chain<'a>(expr: &'a Expr, args: &mut Vec<&'a Term>) -> &'a Expr {
            match expr {
                Expr::Inst(inner) => {
                    args.push(&inner.arg);
                    collect_inst_chain(&inner.expr, args)
                }
                _ => expr,
            }
        }

        fn fmt_expr(
            expr: &Expr,
            f: &mut std::fmt::Formatter<'_>,
            parent_prec: u8,
        ) -> std::fmt::Result {
            let my_prec = precedence(expr);
            let needs_paren = my_prec < parent_prec;
            if needs_paren {
                write!(f, "(")?;
            }

            match expr {
                Expr::Assump(e) => {
                    write!(f, "«{}»", e.target)?;
                }
                Expr::Local(e) => {
                    write!(f, "{}", e.id)?;
                }
                Expr::Assume(e) => {
                    write!(f, "assume {}", e.local_axiom)?;
                    if let Some(alias) = e.alias {
                        write!(f, " as {}", alias)?;
                    }
                    write!(f, ", ")?;
                    fmt_expr(&e.expr, f, PREC_LOWEST)?;
                }
                Expr::App(e) => {
                    fmt_expr(&e.expr1, f, PREC_APP)?;
                    write!(f, " ")?;
                    fmt_expr(&e.expr2, f, PREC_INST)?;
                }
                Expr::Take(e) => {
                    write!(f, "take ({} : {}), ", e.id, e.ty)?;
                    fmt_expr(&e.expr, f, PREC_LOWEST)?;
                }
                Expr::Inst(_) => {
                    let mut args = Vec::new();
                    let base = collect_inst_chain(expr, &mut args);
                    args.reverse();
                    fmt_expr(base, f, PREC_INST)?;
                    write!(f, "[")?;
                    for (idx, arg) in args.iter().enumerate() {
                        if idx > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, "]")?;
                }
                Expr::Const(e) => {
                    write!(f, "{}", e.name)?;
                    if !e.ty_args.is_empty() {
                        write!(f, ".{{")?;
                        for (idx, t) in e.ty_args.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{t}")?;
                        }
                        write!(f, "}}")?;
                    }
                    if !e.instances.is_empty() {
                        write!(f, ".[")?;
                        for (idx, i) in e.instances.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{i}")?;
                        }
                        write!(f, "]")?;
                    }
                }
                Expr::LetTerm(e) => {
                    write!(f, "let {}", e.name)?;
                    if let Some(ty) = &e.ty {
                        write!(f, " : {}", ty)?;
                    }
                    write!(f, " := {}, ", e.value)?;
                    fmt_expr(&e.body, f, PREC_LOWEST)?;
                }
                Expr::LetStructure(e) => {
                    write!(f, "let structure {} := {{", e.name)?;
                    for (idx, field) in e.fields.iter().enumerate() {
                        if idx > 0 {
                            write!(f, "; ")?;
                        } else {
                            write!(f, " ")?;
                        }
                        match field {
                            LocalStructureField::Const(LocalStructureConst { name, ty }) => {
                                write!(f, "const {name} : {ty}")?;
                            }
                            LocalStructureField::Axiom(LocalStructureAxiom { name, target }) => {
                                write!(f, "axiom {name} : {target}")?;
                            }
                        }
                    }
                    if !e.fields.is_empty() {
                        write!(f, " ")?;
                    }
                    write!(f, "}}, ")?;
                    fmt_expr(&e.body, f, PREC_LOWEST)?;
                }
                Expr::Change(e) => {
                    write!(f, "change {}, ", e.target)?;
                    fmt_expr(&e.expr, f, PREC_LOWEST)?;
                }
            }

            if needs_paren {
                write!(f, ")")?;
            }

            Ok(())
        }

        fmt_expr(self, f, PREC_LOWEST)
    }
}

impl Expr {
    pub fn metadata(&self) -> &ExprMetadata {
        match self {
            Expr::Assump(inner) => &inner.metadata,
            Expr::Local(inner) => &inner.metadata,
            Expr::Assume(inner) => &inner.metadata,
            Expr::App(inner) => &inner.metadata,
            Expr::Take(inner) => &inner.metadata,
            Expr::Inst(inner) => &inner.metadata,
            Expr::Const(inner) => &inner.metadata,
            Expr::LetTerm(inner) => &inner.metadata,
            Expr::LetStructure(inner) => &inner.metadata,
            Expr::Change(inner) => &inner.metadata,
        }
    }

    pub fn span(&self) -> Option<&Span> {
        self.metadata().span.as_ref()
    }

    pub fn with_span(self, span: Option<Span>) -> Expr {
        match self {
            Expr::Assump(mut inner) => {
                inner.metadata.span = span;
                Expr::Assump(inner)
            }
            Expr::Local(mut inner) => {
                inner.metadata.span = span;
                Expr::Local(inner)
            }
            Expr::Assume(mut inner) => {
                inner.metadata.span = span;
                Expr::Assume(inner)
            }
            Expr::App(mut inner) => {
                inner.metadata.span = span;
                Expr::App(inner)
            }
            Expr::Take(mut inner) => {
                inner.metadata.span = span;
                Expr::Take(inner)
            }
            Expr::Inst(mut inner) => {
                inner.metadata.span = span;
                Expr::Inst(inner)
            }
            Expr::Const(mut inner) => {
                inner.metadata.span = span;
                Expr::Const(inner)
            }
            Expr::LetTerm(mut inner) => {
                inner.metadata.span = span;
                Expr::LetTerm(inner)
            }
            Expr::LetStructure(mut inner) => {
                inner.metadata.span = span;
                Expr::LetStructure(inner)
            }
            Expr::Change(mut inner) => {
                inner.metadata.span = span;
                Expr::Change(inner)
            }
        }
    }

    pub fn is_ground(&self) -> bool {
        match self {
            Expr::Assump(e) => {
                let ExprAssump {
                    metadata: _,
                    target,
                } = &**e;
                target.is_ground()
            }
            Expr::Local(_) => true,
            Expr::Assume(e) => {
                let ExprAssume {
                    metadata: _,
                    local_axiom,
                    alias: _,
                    expr,
                } = &**e;
                local_axiom.is_ground() && expr.is_ground()
            }
            Expr::App(e) => {
                let ExprApp {
                    metadata: _,
                    expr1,
                    expr2,
                } = &**e;
                expr1.is_ground() && expr2.is_ground()
            }
            Expr::Take(e) => {
                let ExprTake {
                    metadata: _,
                    id: _,
                    ty: _,
                    expr,
                } = &**e;
                expr.is_ground()
            }
            Expr::Inst(e) => {
                let ExprInst {
                    metadata: _,
                    expr,
                    arg,
                } = &**e;
                expr.is_ground() && arg.is_ground()
            }
            Expr::Const(_) => true,
            Expr::LetTerm(e) => {
                let ExprLetTerm {
                    metadata: _,
                    name: _,
                    ty,
                    value,
                    body,
                } = &**e;
                ty.as_ref().is_none_or(Type::is_ground) && value.is_ground() && body.is_ground()
            }
            Expr::LetStructure(e) => {
                let ExprLetStructure {
                    metadata: _,
                    name: _,
                    fields,
                    body,
                } = &**e;
                fields.iter().all(|field| match field {
                    LocalStructureField::Const(LocalStructureConst { name: _, ty }) => {
                        ty.is_ground()
                    }
                    LocalStructureField::Axiom(LocalStructureAxiom { name: _, target }) => {
                        target.is_ground()
                    }
                }) && body.is_ground()
            }
            Expr::Change(e) => {
                let ExprChange {
                    metadata: _,
                    target,
                    expr,
                } = &**e;
                target.is_ground() && expr.is_ground()
            }
        }
    }

    pub fn is_type_ground(&self) -> bool {
        match self {
            Expr::Assump(e) => {
                let ExprAssump {
                    metadata: _,
                    target,
                } = &**e;
                target.is_type_ground()
            }
            Expr::Local(_) => true,
            Expr::Assume(e) => {
                let ExprAssume {
                    metadata: _,
                    local_axiom,
                    alias: _,
                    expr,
                } = &**e;
                local_axiom.is_type_ground() && expr.is_type_ground()
            }
            Expr::App(e) => {
                let ExprApp {
                    metadata: _,
                    expr1,
                    expr2,
                } = &**e;
                expr1.is_type_ground() && expr2.is_type_ground()
            }
            Expr::Take(e) => {
                let ExprTake {
                    metadata: _,
                    id: _,
                    ty,
                    expr,
                } = &**e;
                ty.is_ground() && expr.is_type_ground()
            }
            Expr::Inst(e) => {
                let ExprInst {
                    metadata: _,
                    expr,
                    arg,
                } = &**e;
                expr.is_type_ground() && arg.is_ground()
            }
            Expr::Const(e) => {
                let ExprConst {
                    metadata: _,
                    name: _,
                    ty_args,
                    instances,
                } = &**e;
                ty_args.iter().all(|t| t.is_ground())
                    && instances.iter().all(|i| i.is_type_ground())
            }
            Expr::LetTerm(e) => {
                let ExprLetTerm {
                    metadata: _,
                    name: _,
                    ty,
                    value,
                    body,
                } = &**e;
                ty.as_ref().is_none_or(Type::is_ground)
                    && value.is_type_ground()
                    && body.is_type_ground()
            }
            Expr::LetStructure(e) => {
                let ExprLetStructure {
                    metadata: _,
                    name: _,
                    fields,
                    body,
                } = &**e;
                fields.iter().all(|field| match field {
                    LocalStructureField::Const(LocalStructureConst { name: _, ty }) => {
                        ty.is_ground()
                    }
                    LocalStructureField::Axiom(LocalStructureAxiom { name: _, target }) => {
                        target.is_type_ground()
                    }
                }) && body.is_type_ground()
            }
            Expr::Change(e) => {
                let ExprChange {
                    metadata: _,
                    target,
                    expr,
                } = &**e;
                target.is_type_ground() && expr.is_type_ground()
            }
        }
    }

    pub fn is_instance_ground(&self) -> bool {
        match self {
            Expr::Assump(inner) => inner.target.is_instance_ground(),
            Expr::Local(_) => true,
            Expr::Assume(inner) => {
                inner.local_axiom.is_instance_ground() && inner.expr.is_instance_ground()
            }
            Expr::App(inner) => {
                inner.expr1.is_instance_ground() && inner.expr2.is_instance_ground()
            }
            Expr::Take(inner) => inner.expr.is_instance_ground(),
            Expr::Inst(inner) => inner.expr.is_instance_ground() && inner.arg.is_instance_ground(),
            Expr::Const(inner) => inner.instances.iter().all(Instance::is_instance_ground),
            Expr::LetTerm(inner) => {
                inner.ty.as_ref().is_none_or(Type::is_ground)
                    && inner.value.is_instance_ground()
                    && inner.body.is_instance_ground()
            }
            Expr::LetStructure(inner) => {
                inner.fields.iter().all(|field| match field {
                    LocalStructureField::Const(_) => true,
                    LocalStructureField::Axiom(axiom) => axiom.target.is_instance_ground(),
                }) && inner.body.is_instance_ground()
            }
            Expr::Change(inner) => {
                inner.target.is_instance_ground() && inner.expr.is_instance_ground()
            }
        }
    }

    pub fn subst(&mut self, subst: &[(Id, Term)]) {
        match self {
            Expr::Assump(e) => {
                let ExprAssump {
                    metadata: _,
                    target,
                } = e.as_mut();
                let new_target = target.subst(subst);
                *target = new_target;
            }
            Expr::Local(_) => {}
            Expr::Assume(e) => {
                let ExprAssume {
                    metadata: _,
                    local_axiom,
                    alias: _,
                    expr,
                } = e.as_mut();
                let new_local_axiom = local_axiom.subst(subst);
                *local_axiom = new_local_axiom;
                expr.subst(subst);
            }
            Expr::App(e) => {
                let ExprApp {
                    metadata: _,
                    expr1,
                    expr2,
                } = e.as_mut();
                expr1.subst(subst);
                expr2.subst(subst);
            }
            Expr::Take(e) => {
                let ExprTake {
                    metadata: _,
                    id: _,
                    ty: _,
                    expr,
                } = e.as_mut();
                expr.subst(subst);
            }
            Expr::Inst(e) => {
                let ExprInst {
                    metadata: _,
                    expr,
                    arg,
                } = e.as_mut();
                expr.subst(subst);
                let new_arg = arg.subst(subst);
                *arg = new_arg;
            }
            Expr::Const(_) => {}
            Expr::LetTerm(e) => {
                let ExprLetTerm {
                    metadata: _,
                    name: _,
                    ty: _,
                    value,
                    body,
                } = e.as_mut();
                *value = value.subst(subst);
                body.subst(subst);
            }
            Expr::LetStructure(e) => {
                let ExprLetStructure {
                    metadata: _,
                    name: _,
                    fields,
                    body,
                } = e.as_mut();
                for field in fields {
                    if let LocalStructureField::Axiom(LocalStructureAxiom { target, .. }) = field {
                        *target = target.subst(subst);
                    }
                }
                body.subst(subst);
            }
            Expr::Change(e) => {
                let ExprChange {
                    metadata: _,
                    target,
                    expr,
                } = e.as_mut();
                let new_target = target.subst(subst);
                *target = new_target;
                expr.subst(subst);
            }
        }
    }

    pub fn replace_hole<F>(&mut self, f: &F)
    where
        F: Fn(Id) -> Option<Term>,
    {
        match self {
            Expr::Assump(e) => {
                let ExprAssump {
                    metadata: _,
                    target,
                } = e.as_mut();
                *target = target.replace_hole(f);
            }
            Expr::Local(_) => {}
            Expr::Assume(e) => {
                let ExprAssume {
                    metadata: _,
                    local_axiom,
                    alias: _,
                    expr,
                } = e.as_mut();
                *local_axiom = local_axiom.replace_hole(f);
                expr.replace_hole(f);
            }
            Expr::App(e) => {
                let ExprApp {
                    metadata: _,
                    expr1,
                    expr2,
                } = e.as_mut();
                expr1.replace_hole(f);
                expr2.replace_hole(f);
            }
            Expr::Take(e) => {
                let ExprTake {
                    metadata: _,
                    id: _,
                    ty: _,
                    expr,
                } = e.as_mut();
                expr.replace_hole(f);
            }
            Expr::Inst(e) => {
                let ExprInst {
                    metadata: _,
                    expr,
                    arg,
                } = e.as_mut();
                expr.replace_hole(f);
                *arg = arg.replace_hole(f);
            }
            Expr::Const(_) => {}
            Expr::LetTerm(e) => {
                let ExprLetTerm {
                    metadata: _,
                    name: _,
                    ty: _,
                    value,
                    body,
                } = e.as_mut();
                *value = value.replace_hole(f);
                body.replace_hole(f);
            }
            Expr::LetStructure(e) => {
                let ExprLetStructure {
                    metadata: _,
                    name: _,
                    fields,
                    body,
                } = e.as_mut();
                for field in fields {
                    if let LocalStructureField::Axiom(LocalStructureAxiom { target, .. }) = field {
                        *target = target.replace_hole(f);
                    }
                }
                body.replace_hole(f);
            }
            Expr::Change(e) => {
                let ExprChange {
                    metadata: _,
                    target,
                    expr,
                } = e.as_mut();
                *target = target.replace_hole(f);
                expr.replace_hole(f);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Axiom {
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct Env<'a> {
    pub tt_env: tt::Env<'a>,
    // Proved or postulated facts
    pub axiom_table: &'a HashMap<QualifiedName, Axiom>,
}

#[derive(Debug, Clone)]
pub struct LocalAxiom {
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct Assume {
    pub alias: Option<Id>,
    pub prop: Term,
}

#[derive(Debug, Clone, Default)]
pub struct LocalEnv {
    pub local_axioms: Vec<(QualifiedName, LocalAxiom)>,
    pub assumes: Vec<Assume>,
}

impl Env<'_> {
    // prop is trusted
    pub fn check_prop(
        &self,
        tt_local_env: &mut tt::LocalEnv,
        local_env: &mut LocalEnv,
        expr: &Expr,
        prop: &Term,
    ) {
        let p = self.infer_prop(tt_local_env, local_env, expr);
        if !p.alpha_eq(prop) {
            panic!("proposition mismatch: expected {}, got {}", prop, p);
        }
    }

    pub fn infer_prop(
        &self,
        tt_local_env: &mut tt::LocalEnv,
        local_env: &mut LocalEnv,
        expr: &Expr,
    ) -> Term {
        match expr {
            Expr::Assump(e) => {
                let ExprAssump {
                    metadata: _,
                    target,
                } = &**e;
                for assume in &local_env.assumes {
                    if target.alpha_eq(&assume.prop) {
                        return target.clone();
                    }
                }
                panic!("unknown assumption: {}", target);
            }
            Expr::Local(e) => {
                let ExprLocal { metadata: _, id } = &**e;
                for assume in local_env.assumes.iter().rev() {
                    if assume.alias == Some(*id) {
                        return assume.prop.clone();
                    }
                }
                for (local_name, local_axiom) in local_env.local_axioms.iter().rev() {
                    if *id == Id::from_qualified_name(local_name) {
                        return local_axiom.target.clone();
                    }
                }
                panic!("unknown assumption alias: {}", id);
            }
            Expr::Assume(e) => {
                let ExprAssume {
                    metadata: _,
                    local_axiom,
                    alias,
                    expr,
                } = &**e;
                self.tt_env.check_wff(tt_local_env, local_axiom);
                local_env.assumes.push(Assume {
                    alias: *alias,
                    prop: local_axiom.clone(),
                });
                let target = self.infer_prop(tt_local_env, local_env, expr);
                let p = local_env.assumes.pop().unwrap();
                guard(&target, [p.prop])
            }
            Expr::App(e) => {
                let ExprApp {
                    metadata: _,
                    expr1,
                    expr2,
                } = &**e;
                let target = self.infer_prop(tt_local_env, local_env, expr1);
                let Some((lhs, rhs)) = unguard1(&target) else {
                    panic!("implication expected, got {}", target);
                };
                self.check_prop(tt_local_env, local_env, expr2, &lhs);
                rhs
            }
            Expr::Take(e) => {
                let ExprTake {
                    metadata: _,
                    id,
                    ty,
                    expr,
                } = &**e;
                self.tt_env.check_wft(tt_local_env, ty);
                for assume in &local_env.assumes {
                    if !assume.prop.is_fresh(std::slice::from_ref(id)) {
                        // eigenvariable condition fails
                        panic!("eigenvariable condition violated by {}", assume.prop);
                    }
                }
                let param = Local {
                    id: *id,
                    ty: ty.clone(),
                };
                tt_local_env.locals.push(param);
                let target = self.infer_prop(tt_local_env, local_env, expr);
                let x = tt_local_env.locals.pop().unwrap();
                generalize(&target, &[x])
            }
            Expr::Inst(e) => {
                let ExprInst {
                    metadata: _,
                    expr,
                    arg,
                } = &**e;
                let target = self.infer_prop(tt_local_env, local_env, expr);
                let Some((Local { id, ty }, mut body)) = ungeneralize1(&target) else {
                    panic!("∀ expected, got {}", target);
                };
                self.tt_env.check_type(tt_local_env, arg, &ty);
                body = body.subst(&[(id, arg.clone())]);
                body
            }
            Expr::Const(e) => {
                let ExprConst {
                    metadata: _,
                    name,
                    ty_args,
                    instances,
                } = &**e;
                let Axiom {
                    local_types,
                    local_classes,
                    target,
                } = self
                    .axiom_table
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown axiom: {:?}", name));
                if ty_args.len() != local_types.len() {
                    panic!(
                        "axiom {:?} expects {} type arguments but got {}",
                        name,
                        local_types.len(),
                        ty_args.len()
                    );
                }
                for ty_arg in ty_args {
                    self.tt_env.check_wft(tt_local_env, ty_arg);
                }
                let mut type_subst = Vec::with_capacity(local_types.len());
                for (x, t) in zip(local_types, ty_args) {
                    type_subst.push((*x, t.clone()))
                }
                if local_classes.len() != instances.len() {
                    panic!(
                        "axiom {:?} expects {} class arguments but got {}",
                        name,
                        local_classes.len(),
                        instances.len()
                    );
                }
                let mut instance_subst = vec![];
                for (local_class, instance) in zip(local_classes, instances) {
                    let local_class = local_class.subst(&type_subst);
                    self.tt_env
                        .check_class(tt_local_env, instance, &local_class);
                    instance_subst.push((local_class, instance.clone()));
                }
                let mut target = target.clone();
                target = target.subst_type(&type_subst);
                target = target.subst_instance(&instance_subst);
                target
            }
            Expr::LetTerm(e) => {
                let ExprLetTerm {
                    metadata: _,
                    name,
                    ty,
                    value,
                    body,
                } = &**e;

                let value_ty = self.tt_env.infer_type(tt_local_env, value);
                let binder_ty = if let Some(ty) = ty {
                    self.tt_env.check_wft(tt_local_env, ty);
                    self.tt_env.check_type(tt_local_env, value, ty);
                    ty.clone()
                } else {
                    value_ty
                };

                let local_len = tt_local_env.locals.len();
                let local_delta_len = tt_local_env.local_deltas.len();
                let id = Id::from_qualified_name(name);
                tt_local_env.locals.push(Local { id, ty: binder_ty });
                tt_local_env.local_deltas.push(LocalDelta {
                    id,
                    target: value.clone(),
                    height: self.tt_env.height(tt_local_env, value),
                });
                let target = self.infer_prop(tt_local_env, local_env, body);
                tt_local_env.local_deltas.truncate(local_delta_len);
                tt_local_env.locals.truncate(local_len);
                self.tt_env.check_wff(tt_local_env, &target);
                target
            }
            Expr::LetStructure(e) => {
                let ExprLetStructure {
                    metadata: _,
                    name,
                    fields,
                    body,
                } = &**e;

                let structure_id = Id::from_name(name);
                let structure_name = QualifiedName::from_str(name.as_str());
                let mut const_field_names: Vec<Name> = vec![];
                let mut axiom_field_names: Vec<Name> = vec![];
                let mut num_consts = 0;
                for field in fields {
                    match field {
                        LocalStructureField::Const(LocalStructureConst {
                            name: field_name,
                            ty: field_ty,
                        }) => {
                            for existing in &const_field_names {
                                if existing == field_name {
                                    panic!("duplicate const field");
                                }
                            }
                            const_field_names.push(field_name.clone());
                            self.tt_env.check_wft(tt_local_env, field_ty);
                            tt_local_env.locals.push(Local {
                                id: Id::from_name(field_name),
                                ty: field_ty.clone(),
                            });
                            num_consts += 1;
                        }
                        LocalStructureField::Axiom(LocalStructureAxiom {
                            name: field_name,
                            target,
                        }) => {
                            for existing in &axiom_field_names {
                                if existing == field_name {
                                    panic!("duplicate axiom field");
                                }
                            }
                            axiom_field_names.push(field_name.clone());
                            self.tt_env.check_wff(tt_local_env, target);
                        }
                    }
                }
                tt_local_env
                    .locals
                    .truncate(tt_local_env.locals.len() - num_consts);

                let this_ty = mk_type_local(structure_id);
                let this = Local {
                    id: Id::fresh_with_name(Name::from_str("this")),
                    ty: this_ty.clone(),
                };
                let mut locals: Vec<Local> = vec![];
                let mut local_axioms: Vec<(QualifiedName, LocalAxiom)> = vec![];
                let mut subst = vec![];

                for field in fields {
                    match field {
                        LocalStructureField::Const(LocalStructureConst {
                            name: field_name,
                            ty,
                        }) => {
                            let fullname = structure_name.extend(field_name.as_str());
                            let id = Id::from_qualified_name(&fullname);
                            let ty = ty.arrow([this_ty.clone()]);
                            locals.push(Local { id, ty });

                            let mut target = mk_local(id);
                            target = target.apply([mk_local(this.id)]);
                            subst.push((Id::from_name(field_name), target));
                        }
                        LocalStructureField::Axiom(LocalStructureAxiom {
                            name: field_name,
                            target,
                        }) => {
                            let fullname = structure_name.extend(field_name.as_str());
                            let mut target = target.clone();
                            target = target.subst(&subst);
                            target = generalize(&target, slice::from_ref(&this));
                            local_axioms.push((fullname, LocalAxiom { target }));
                        }
                    }
                }

                let abs_name = structure_name.extend("abs");
                let mut params = vec![];
                let mut guards = vec![];
                let mut chars = vec![];
                let mut abs_subst = vec![];
                for field in fields {
                    match field {
                        LocalStructureField::Const(LocalStructureConst {
                            name: field_name,
                            ty,
                        }) => {
                            let param = Local {
                                id: Id::fresh_with_name(field_name.clone()),
                                ty: ty.clone(),
                            };

                            let fullname = structure_name.extend(field_name.as_str());
                            let id = Id::from_qualified_name(&fullname);
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
                        .unwrap_or_else(|| {
                            mk_const(QualifiedName::from_str("true"), vec![], vec![])
                        });
                    char = char.abs(slice::from_ref(&this));
                    char
                }]);
                abs = guard(&abs, guards);
                abs = generalize(&abs, &params);
                local_axioms.push((abs_name, LocalAxiom { target: abs }));

                let local_type_len = tt_local_env.local_types.len();
                let local_len = tt_local_env.locals.len();
                let local_axiom_len = local_env.local_axioms.len();
                tt_local_env.local_types.push(structure_id);
                tt_local_env.locals.extend(locals);
                local_env.local_axioms.extend(local_axioms);
                for i in local_len..tt_local_env.locals.len() {
                    let local = &tt_local_env.locals[i];
                    self.tt_env.check_wft(tt_local_env, &local.ty);
                }
                let target = self.infer_prop(tt_local_env, local_env, body);
                local_env.local_axioms.truncate(local_axiom_len);
                tt_local_env.locals.truncate(local_len);
                tt_local_env.local_types.truncate(local_type_len);
                self.tt_env.check_wff(tt_local_env, &target);
                target
            }
            Expr::Change(e) => {
                let ExprChange {
                    metadata: _,
                    target,
                    expr,
                } = &**e;
                self.tt_env.check_wff(tt_local_env, target);
                let source = self.infer_prop(tt_local_env, local_env, expr);
                if !self.tt_env.equiv(tt_local_env, &source, target) {
                    panic!(
                        "conversion failed: expected {} but proof showed {}",
                        target, source
                    );
                }
                target.clone()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tt::{ClassInstance, ClassType, Const, Delta, Kappa, Kind};

    use std::collections::HashMap;

    #[test]
    #[should_panic(expected = "unknown axiom")]
    fn const_expr_does_not_resolve_local_axiom_from_local_table() {
        let mut tt_local_env = tt::LocalEnv::default();
        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::new();
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, Axiom> = HashMap::new();

        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let env = Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let mut local_env = LocalEnv::default();
        let local_axiom_name = QualifiedName::from_str("foo.a");
        local_env.local_axioms.push((
            local_axiom_name.clone(),
            LocalAxiom {
                target: mk_const(QualifiedName::from_str("p"), vec![], vec![]),
            },
        ));
        let expr = mk_expr_const(local_axiom_name, vec![], vec![]);
        let _ = env.infer_prop(&mut tt_local_env, &mut local_env, &expr);
    }
}
