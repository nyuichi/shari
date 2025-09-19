use std::iter::zip;
use std::sync::Arc;
use std::sync::LazyLock;

use crate::proof::{
    self, Axiom, Forall, Imp, Proof, mk_proof_assump, mk_proof_conv, mk_proof_forall_elim,
    mk_proof_forall_intro, mk_proof_imp_elim, mk_proof_imp_intro, mk_proof_ref,
};
use crate::tt::Instance;
use crate::tt::{self, Name, Parameter, Term, Type};

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
/// Γ | Φ ⊢ h : ∀ ψ
/// ------------------- (Γ ⊢ m : u)
/// Γ | Φ ⊢ h[m] : ψ m
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
        match self {
            Expr::Assump(e) => {
                write!(f, "«{}»", e.target)
            }
            Expr::Assume(e) => {
                write!(f, "assume {}, {}", e.local_axiom, e.expr)
            }
            Expr::App(e) => {
                write!(f, "({}) {}", e.expr1, e.expr2)
            }
            Expr::Take(e) => {
                write!(f, "take ({} : {}), {}", e.name, e.ty, e.expr)
            }
            Expr::Inst(e) => {
                write!(f, "({})[{}]", e.expr, e.arg)
            }
            Expr::Const(e) => {
                write!(f, "{}", e.name)?;
                if !e.ty_args.is_empty() {
                    let mut first = true;
                    for t in &e.ty_args {
                        if !first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", t)?;
                        first = false;
                    }
                    write!(f, "}}")?
                }
                if !e.instances.is_empty() {
                    write!(f, ".[")?;
                    let mut first = true;
                    for i in &e.instances {
                        if !first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", i)?;
                        first = false;
                    }
                    write!(f, "]")?
                }
                Ok(())
            }
            Expr::Change(e) => {
                write!(f, "change {}, {}", e.target, e.expr)
            }
        }
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
                let ExprTake {
                    name: _,
                    ty: _,
                    expr,
                } = &**e;
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
                let ExprTake { name: _, ty, expr } = &**e;
                ty.is_ground() && expr.is_type_ground()
            }
            Expr::Inst(e) => {
                let ExprInst { expr, arg } = &**e;
                expr.is_type_ground() && arg.is_ground()
            }
            Expr::Const(e) => {
                let ExprConst {
                    name: _,
                    ty_args,
                    instances,
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
                let ExprTake {
                    name: _,
                    ty: _,
                    expr,
                } = Arc::make_mut(e);
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
}

#[derive(Debug)]
pub struct Env<'a> {
    pub proof_env: proof::Env<'a>,
    pub tt_local_env: &'a mut tt::LocalEnv,
}

impl Env<'_> {
    fn run_help(&mut self, expr: &Expr) -> (Proof, Term) {
        match expr {
            Expr::Assump(expr) => {
                let ExprAssump { target } = &**expr;
                let h = mk_proof_assump(target.clone());
                (h, target.clone())
            }
            Expr::Assume(expr) => {
                let ExprAssume { local_axiom, expr } = &**expr;
                let (h, mut target) = self.run_help(expr);
                let h = mk_proof_imp_intro(local_axiom.clone(), h);
                target.guard([local_axiom.clone()]);
                (h, target)
            }
            Expr::App(expr) => {
                let ExprApp { expr1, expr2 } = &**expr;
                let (h1, p1) = self.run_help(expr1);
                let (h2, _) = self.run_help(expr2);
                let h = mk_proof_imp_elim(h1, h2);
                let Imp { lhs: _lhs, rhs } = p1.try_into().unwrap();
                (h, rhs)
            }
            Expr::Take(expr) => {
                let &ExprTake {
                    name,
                    ref ty,
                    ref expr,
                } = &**expr;
                let x = Parameter {
                    name,
                    ty: ty.clone(),
                };
                self.tt_local_env.locals.push(x);
                let (h, mut p) = self.run_help(expr);
                let x = self.tt_local_env.locals.pop().unwrap();
                let h = mk_proof_forall_intro(name, ty.clone(), h);
                p.generalize(&[x]);
                (h, p)
            }
            Expr::Inst(expr) => {
                let ExprInst { expr, arg } = &**expr;
                let (h, p) = self.run_help(expr);
                let h = mk_proof_forall_elim(arg.clone(), h);
                let Forall { domain: _, pred } = p.try_into().unwrap();
                let mut target = pred;
                target.apply([arg.clone()]);
                (h, target)
            }
            Expr::Const(expr) => {
                let &ExprConst {
                    name,
                    ref ty_args,
                    ref instances,
                } = &**expr;
                let h = mk_proof_ref(name, ty_args.clone(), instances.clone());
                let Axiom {
                    local_types,
                    local_classes,
                    target,
                } = self.proof_env.axiom_table.get(&name).cloned().unwrap();
                let mut type_subst = vec![];
                for (&x, t) in zip(&local_types, ty_args) {
                    type_subst.push((x, t.clone()));
                }
                let mut instance_subst = vec![];
                for (local_class, instance) in zip(&local_classes, instances) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    instance_subst.push((local_class, instance.clone()));
                }
                let mut target = target.clone();
                target.subst_type(&type_subst);
                target.subst_instance(&instance_subst);
                (h, target)
            }
            Expr::Change(expr) => {
                let ExprChange { target, expr } = &**expr;
                let (h, p) = self.run_help(expr);
                let path = self.proof_env.tt_env.equiv(&p, target).unwrap();
                (mk_proof_conv(path, h), target.clone())
            }
        }
    }

    pub fn run(&mut self, e: &Expr) -> Proof {
        self.run_help(e).0
    }
}
