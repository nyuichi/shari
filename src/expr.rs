use std::iter::zip;
use std::sync::LazyLock;
use std::{collections::HashMap, sync::Arc};

use crate::proof::{
    mk_proof_assump, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro, mk_proof_imp_elim,
    mk_proof_imp_intro, mk_proof_ref, Forall, Imp, Proof,
};
use crate::tt::{self, Name, Parameter, Term, Type};

/// p ::= ⟪φ⟫
///     | assume φ, p
///     | p p
///     | take (x : τ), p
///     | p[m]
///     | c.{u₁, ⋯, uₙ}
///     | change φ, p
///
///
/// --------------- (φ ∈ Φ)
/// Γ | Φ ⊢ ⟪φ⟫ : φ
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

pub fn mk_expr_const(name: Name, ty_args: Vec<Type>) -> Expr {
    Expr::Const(Arc::new(ExprConst { name, ty_args }))
}

pub fn mk_expr_change(target: Term, expr: Expr) -> Expr {
    Expr::Change(Arc::new(ExprChange { target, expr }))
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Assump(e) => {
                write!(f, "⟪{}⟫", e.target)
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
                write!(f, "{}.{{", e.name)?;
                let mut first = true;
                for t in &e.ty_args {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", t)?;
                    first = false;
                }
                write!(f, "}}")
            }
            Expr::Change(e) => {
                write!(f, "change {}, {}", e.target, e.expr)
            }
        }
    }
}

impl Expr {
    pub fn inst_type_hole(&mut self, subst: &[(Name, Type)]) {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = Arc::make_mut(e);
                target.inst_type_hole(subst)
            }
            Expr::Assume(e) => {
                let ExprAssume { local_axiom, expr } = Arc::make_mut(e);
                local_axiom.inst_type_hole(subst);
                expr.inst_type_hole(subst);
            }
            Expr::App(e) => {
                let ExprApp { expr1, expr2 } = Arc::make_mut(e);
                expr1.inst_type_hole(subst);
                expr2.inst_type_hole(subst);
            }
            Expr::Take(e) => {
                let ExprTake { name: _, ty, expr } = Arc::make_mut(e);
                ty.inst_hole(subst);
                expr.inst_type_hole(subst);
            }
            Expr::Inst(e) => {
                let ExprInst { expr, arg } = Arc::make_mut(e);
                expr.inst_type_hole(subst);
                arg.inst_type_hole(subst);
            }
            Expr::Const(e) => {
                let ExprConst { name: _, ty_args } = Arc::make_mut(e);
                for ty_arg in ty_args {
                    ty_arg.inst_hole(subst);
                }
            }
            Expr::Change(e) => {
                let ExprChange { target, expr } = Arc::make_mut(e);
                target.inst_type_hole(subst);
                expr.inst_type_hole(subst);
            }
        }
    }

    pub fn inst_hole(&mut self, subst: &[(Name, Term)]) {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = Arc::make_mut(e);
                target.inst_hole(subst)
            }
            Expr::Assume(e) => {
                let ExprAssume { local_axiom, expr } = Arc::make_mut(e);
                local_axiom.inst_hole(subst);
                expr.inst_hole(subst);
            }
            Expr::App(e) => {
                let ExprApp { expr1, expr2 } = Arc::make_mut(e);
                expr1.inst_hole(subst);
                expr2.inst_hole(subst);
            }
            Expr::Take(e) => {
                let ExprTake {
                    name: _,
                    ty: _,
                    expr,
                } = Arc::make_mut(e);
                expr.inst_hole(subst);
            }
            Expr::Inst(e) => {
                let ExprInst { expr, arg } = Arc::make_mut(e);
                expr.inst_hole(subst);
                arg.inst_hole(subst);
            }
            Expr::Const(_) => {}
            Expr::Change(e) => {
                let ExprChange { target, expr } = Arc::make_mut(e);
                target.inst_hole(subst);
                expr.inst_hole(subst);
            }
        }
    }

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
                let ExprConst { name: _, ty_args } = &**e;
                ty_args.iter().all(|t| t.is_ground())
            }
            Expr::Change(e) => {
                let ExprChange { target, expr } = &**e;
                target.is_type_ground() && expr.is_type_ground()
            }
        }
    }
}

#[derive(Debug)]
pub struct Env<'a> {
    pub axioms: &'a HashMap<Name, (Vec<Name>, Term)>,
    pub tt_env: &'a tt::Env,
    pub tt_local_env: &'a mut tt::LocalEnv,
}

impl<'a> Env<'a> {
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
                let &ExprConst { name, ref ty_args } = &**expr;
                let h = mk_proof_ref(name, ty_args.clone());
                let (tv, mut target) = self.axioms.get(&name).cloned().unwrap();
                let mut subst = vec![];
                for (&x, t) in zip(&tv, ty_args) {
                    subst.push((x, t.clone()));
                }
                target.subst_type(&subst);
                (h, target)
            }
            Expr::Change(expr) => {
                let ExprChange { target, expr } = &**expr;
                let (h, p) = self.run_help(expr);
                let path = self.tt_env.equiv(&p, target).unwrap();
                (mk_proof_conv(path, h), target.clone())
            }
        }
    }

    pub fn run(&mut self, e: &Expr) -> Proof {
        self.run_help(e).0
    }
}
