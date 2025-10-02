//! Prove by type synthesis.

use std::sync::LazyLock;
use std::{collections::HashMap, iter::zip, mem, sync::Arc};

use crate::tt::{
    self, Class, Instance, Name, Parameter, Term, Type, mk_abs, mk_const, mk_local, mk_type_const,
};

pub fn mk_type_prop() -> Type {
    static T_PROP: LazyLock<Type> = LazyLock::new(|| mk_type_const(Name::intern("Prop")));
    T_PROP.clone()
}

pub fn count_forall(term: &Term) -> usize {
    static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall"));

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

pub fn generalize(term: &mut Term, xs: &[Parameter]) {
    static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall"));

    let locals = xs.iter().map(|x| x.name).collect::<Vec<_>>();
    let mut result = term.pclose(&locals, 0);
    for x in xs.iter().rev() {
        result = mk_abs(x.name, x.ty.clone(), result);
        let mut c = mk_const(*FORALL, vec![x.ty.clone()], vec![]);
        c.apply([result]);
        result = c;
    }
    *term = result;
}

pub fn ungeneralize(term: &mut Term) -> Vec<Parameter> {
    let mut target = mem::take(term);
    let mut acc = vec![];
    while let Some((binder, body)) = ungeneralize1(&target) {
        acc.push(binder);
        target = body;
    }
    *term = target;
    acc
}

pub fn ungeneralize1(term: &Term) -> Option<(Parameter, Term)> {
    static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall"));

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
        binder_type,
        binder_name,
        body,
    } = &**abs;
    let name = Name::fresh_from(*binder_name);
    let mut body = body.clone();
    body.open(&mk_local(name));
    let binder = Parameter {
        name,
        ty: binder_type.clone(),
    };
    Some((binder, body))
}

pub fn guard(term: &mut Term, guards: impl IntoIterator<Item = Term>) {
    guard_help(term, guards.into_iter());
}

fn guard_help(target: &mut Term, mut guards: impl Iterator<Item = Term>) {
    static IMP: LazyLock<Name> = LazyLock::new(|| Name::intern("imp"));

    if let Some(guard_term) = guards.next() {
        guard_help(target, guards);
        let inner = mem::take(target);
        let mut m = mk_const(*IMP, vec![], vec![]);
        m.apply([guard_term, inner]);
        *target = m;
    }
}

pub fn unguard(term: &mut Term) -> Vec<Term> {
    let mut target = mem::take(term);
    let mut acc = vec![];
    while let Some((lhs, rhs)) = unguard1(&target) {
        acc.push(lhs);
        target = rhs;
    }
    *term = target;
    acc
}

pub fn unguard1(term: &Term) -> Option<(Term, Term)> {
    static IMP: LazyLock<Name> = LazyLock::new(|| Name::intern("imp"));

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
#[derive(Debug, Clone)]
pub enum Expr {
    Assump(Arc<ExprAssump>),
    Assume(Arc<ExprAssume>),
    App(Arc<ExprApp>),
    Take(Arc<ExprTake>),
    Inst(Arc<ExprInst>),
    Const(Arc<ExprConst>),
    Change(Arc<ExprChange>),
}

#[derive(Debug, Clone)]
pub struct ExprAssump {
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct ExprAssume {
    pub local_axiom: Term,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprApp {
    pub expr1: Expr,
    pub expr2: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprTake {
    pub name: Name,
    pub ty: Type,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprInst {
    pub expr: Expr,
    pub arg: Term,
}

#[derive(Debug, Clone)]
pub struct ExprConst {
    pub name: Name,
    pub ty_args: Vec<Type>,
    pub instances: Vec<Instance>,
}

#[derive(Debug, Clone)]
pub struct ExprChange {
    pub target: Term,
    pub expr: Expr,
}

impl Default for Expr {
    fn default() -> Self {
        static DEFAULT: LazyLock<Expr> = LazyLock::new(|| mk_expr_assump(Default::default()));
        DEFAULT.clone()
    }
}

pub fn mk_expr_assump(m: Term) -> Expr {
    Expr::Assump(Arc::new(ExprAssump { target: m }))
}

pub fn mk_expr_assume(h: Term, e: Expr) -> Expr {
    Expr::Assume(Arc::new(ExprAssume {
        local_axiom: h,
        expr: e,
    }))
}

pub fn mk_expr_app(e1: Expr, e2: Expr) -> Expr {
    Expr::App(Arc::new(ExprApp {
        expr1: e1,
        expr2: e2,
    }))
}

pub fn mk_expr_take(name: Name, ty: Type, e: Expr) -> Expr {
    Expr::Take(Arc::new(ExprTake { name, ty, expr: e }))
}

pub fn mk_expr_inst(e: Expr, m: Term) -> Expr {
    Expr::Inst(Arc::new(ExprInst { expr: e, arg: m }))
}

pub fn mk_expr_const(name: Name, ty_args: Vec<Type>, instances: Vec<Instance>) -> Expr {
    Expr::Const(Arc::new(ExprConst {
        name,
        ty_args,
        instances,
    }))
}

pub fn mk_expr_change(target: Term, expr: Expr) -> Expr {
    Expr::Change(Arc::new(ExprChange { target, expr }))
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
                Expr::Assump(_) | Expr::Const(_) => PREC_ATOM,
                Expr::Inst(_) => PREC_INST,
                Expr::App(_) => PREC_APP,
                Expr::Assume(_) | Expr::Take(_) | Expr::Change(_) => PREC_PREFIX,
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
                Expr::Assume(e) => {
                    write!(f, "assume {}, ", e.local_axiom)?;
                    fmt_expr(&e.expr, f, PREC_LOWEST)?;
                }
                Expr::App(e) => {
                    fmt_expr(&e.expr1, f, PREC_APP)?;
                    write!(f, " ")?;
                    fmt_expr(&e.expr2, f, PREC_INST)?;
                }
                Expr::Take(e) => {
                    write!(f, "take ({} : {}), ", e.name, e.ty)?;
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
    pub fn is_ground(&self) -> bool {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = &**e;
                target.is_ground()
            }
            Expr::Assume(e) => {
                let ExprAssume { local_axiom, expr } = &**e;
                local_axiom.is_ground() && expr.is_ground()
            }
            Expr::App(e) => {
                let ExprApp { expr1, expr2 } = &**e;
                expr1.is_ground() && expr2.is_ground()
            }
            Expr::Take(e) => {
                let ExprTake { expr, .. } = &**e;
                expr.is_ground()
            }
            Expr::Inst(e) => {
                let ExprInst { expr, arg } = &**e;
                expr.is_ground() && arg.is_ground()
            }
            Expr::Const(_) => true,
            Expr::Change(e) => {
                let ExprChange { target, expr } = &**e;
                target.is_ground() && expr.is_ground()
            }
        }
    }

    pub fn is_type_ground(&self) -> bool {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = &**e;
                target.is_type_ground()
            }
            Expr::Assume(e) => {
                let ExprAssume { local_axiom, expr } = &**e;
                local_axiom.is_type_ground() && expr.is_type_ground()
            }
            Expr::App(e) => {
                let ExprApp { expr1, expr2 } = &**e;
                expr1.is_type_ground() && expr2.is_type_ground()
            }
            Expr::Take(e) => {
                let ExprTake { ty, expr, .. } = &**e;
                ty.is_ground() && expr.is_type_ground()
            }
            Expr::Inst(e) => {
                let ExprInst { expr, arg } = &**e;
                expr.is_type_ground() && arg.is_ground()
            }
            Expr::Const(e) => {
                let ExprConst {
                    ty_args, instances, ..
                } = &**e;
                ty_args.iter().all(|t| t.is_ground())
                    && instances.iter().all(|i| i.is_type_ground())
            }
            Expr::Change(e) => {
                let ExprChange { target, expr } = &**e;
                target.is_type_ground() && expr.is_type_ground()
            }
        }
    }

    pub fn subst(&mut self, subst: &[(Name, Term)]) {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = Arc::make_mut(e);
                target.subst(subst);
            }
            Expr::Assume(e) => {
                let ExprAssume { local_axiom, expr } = Arc::make_mut(e);
                local_axiom.subst(subst);
                expr.subst(subst);
            }
            Expr::App(e) => {
                let ExprApp { expr1, expr2 } = Arc::make_mut(e);
                expr1.subst(subst);
                expr2.subst(subst);
            }
            Expr::Take(e) => {
                let ExprTake { expr, .. } = Arc::make_mut(e);
                expr.subst(subst);
            }
            Expr::Inst(e) => {
                let ExprInst { expr, arg } = Arc::make_mut(e);
                expr.subst(subst);
                arg.subst(subst);
            }
            Expr::Const(_) => {}
            Expr::Change(e) => {
                let ExprChange { target, expr } = Arc::make_mut(e);
                target.subst(subst);
                expr.subst(subst);
            }
        }
    }

    pub fn replace_hole<F>(&mut self, f: &F)
    where
        F: Fn(Name) -> Option<Term>,
    {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = Arc::make_mut(e);
                target.replace_hole(f);
            }
            Expr::Assume(e) => {
                let ExprAssume { local_axiom, expr } = Arc::make_mut(e);
                local_axiom.replace_hole(f);
                expr.replace_hole(f);
            }
            Expr::App(e) => {
                let ExprApp { expr1, expr2 } = Arc::make_mut(e);
                expr1.replace_hole(f);
                expr2.replace_hole(f);
            }
            Expr::Take(e) => {
                let ExprTake { expr, .. } = Arc::make_mut(e);
                expr.replace_hole(f);
            }
            Expr::Inst(e) => {
                let ExprInst { expr, arg } = Arc::make_mut(e);
                expr.replace_hole(f);
                arg.replace_hole(f);
            }
            Expr::Const(_) => {}
            Expr::Change(e) => {
                let ExprChange { target, expr } = Arc::make_mut(e);
                target.replace_hole(f);
                expr.replace_hole(f);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Axiom {
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct Env<'a> {
    pub tt_env: tt::Env<'a>,
    // Proved or postulated facts
    pub axiom_table: &'a HashMap<Name, Axiom>,
}

#[derive(Debug, Clone, Default)]
pub struct LocalEnv {
    pub local_axioms: Vec<Term>,
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
                let ExprAssump { target } = &**e;
                for local_axiom in &local_env.local_axioms {
                    if target.alpha_eq(local_axiom) {
                        return target.clone();
                    }
                }
                panic!("unknown assumption: {}", target);
            }
            Expr::Assume(e) => {
                let ExprAssume { local_axiom, expr } = &**e;
                self.tt_env.check_wff(tt_local_env, local_axiom);
                local_env.local_axioms.push(local_axiom.clone());
                let mut target = self.infer_prop(tt_local_env, local_env, expr);
                let p = local_env.local_axioms.pop().unwrap();
                guard(&mut target, [p]);
                target
            }
            Expr::App(e) => {
                let ExprApp { expr1, expr2 } = &**e;
                let target = self.infer_prop(tt_local_env, local_env, expr1);
                let Some((lhs, rhs)) = unguard1(&target) else {
                    panic!("implication expected, got {}", target);
                };
                self.check_prop(tt_local_env, local_env, expr2, &lhs);
                rhs
            }
            Expr::Take(e) => {
                let ExprTake { name, ty, expr } = &**e;
                self.tt_env.check_wft(tt_local_env, ty);
                for c in &local_env.local_axioms {
                    if !c.is_fresh(&[name.clone()]) {
                        // eigenvariable condition fails
                        panic!("eigenvariable condition violated by {}", c);
                    }
                }
                let param = Parameter {
                    name: name.clone(),
                    ty: ty.clone(),
                };
                tt_local_env.locals.push(param);
                let mut target = self.infer_prop(tt_local_env, local_env, expr);
                let x = tt_local_env.locals.pop().unwrap();
                generalize(&mut target, &[x]);
                target
            }
            Expr::Inst(e) => {
                let ExprInst { expr, arg } = &**e;
                let target = self.infer_prop(tt_local_env, local_env, expr);
                let Some((Parameter { name, ty }, mut body)) = ungeneralize1(&target) else {
                    panic!("∀ expected, got {}", target);
                };
                self.tt_env.check_type(tt_local_env, arg, &ty);
                body.subst(&[(name, arg.clone())]);
                body
            }
            Expr::Const(e) => {
                let ExprConst {
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
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, ty_args) {
                    type_subst.push((x, t.clone()))
                }
                if local_classes.len() != instances.len() {
                    panic!(
                        "axiom {:?} expects {} class arguments but got {}",
                        name,
                        local_classes.len(),
                        instances.len()
                    );
                }
                for (local_class, instance) in zip(local_classes, instances) {
                    let local_class = local_class.subst(&type_subst);
                    self.tt_env
                        .check_class(tt_local_env, instance, &local_class);
                }
                let mut target = target.clone();
                target.subst_type(&type_subst);
                target
            }
            Expr::Change(e) => {
                let ExprChange { target, expr } = &**e;
                self.tt_env.check_wff(tt_local_env, target);
                let source = self.infer_prop(tt_local_env, local_env, expr);
                if !self.tt_env.equiv(&source, target) {
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
