use std::iter::zip;
use std::{collections::HashMap, sync::Arc};

use crate::proof::{
    mk_proof_assump, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro, mk_proof_imp_elim,
    mk_proof_imp_intro, mk_proof_ref, Forall, Imp, Proof,
};
use crate::tt::{self, mk_local, Name, Term, Type};

/// p ::= ⟪φ⟫
///     | assume φ, p
///     | p p
///     | take (x : τ), p
///     | p[m]
///     | c.{u₁, ⋯, uₙ}
///
///
/// --------------- (φ ∈ Φ)
/// Γ | Φ ⊢ ⟪φ⟫ : φ
///
/// Γ | Φ, φ ⊢ h : ψ
/// ----------------------------
/// Γ | Φ ⊢ assume φ, h : φ → ψ
///
/// Γ | Φ ⊢ h₁ : φ    Γ | Φ ⊢ h₂ : ψ    φ ≈ ψ → ξ
/// ----------------------------------------------
/// Γ | Φ ⊢ h₁ h₂ : ξ
///
/// Γ, x : u | Φ ⊢ h : φ
/// --------------------------------------- (x # Φ)
/// Γ | Φ ⊢ take (x : u), h : ∀ (x : u), φ
///
/// Γ | Φ ⊢ h : φ    φ ≈ ∀ (x : u), ψ x
/// ------------------------------------ (Γ ⊢ m : u)
/// Γ | Φ ⊢ h[m] : ψ m
///
/// -------------------------
/// Γ | Φ ⊢ c.{u₁, ⋯, uₙ} : φ
///
#[derive(Debug, Clone)]
pub enum Expr {
    Assump(Arc<ExprAssump>),
    Assume(Arc<ExprAssume>),
    App(Arc<ExprApp>),
    Take(Arc<ExprTake>),
    Inst(Arc<ExprInst>),
    Const(Arc<ExprConst>),
}

#[derive(Debug, Clone)]
pub struct ExprAssump {
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct ExprAssume {
    pub target: Term,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprApp {
    pub expr1: Expr,
    pub expr2: Expr,
    // ξ : Prop
    pub target: Term,
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
    // P : u → Prop
    pub predicate: Term,
}

#[derive(Debug, Clone)]
pub struct ExprConst {
    pub name: Name,
    pub ty_args: Vec<Type>,
}

pub fn mk_expr_assump(m: Term) -> Expr {
    Expr::Assump(Arc::new(ExprAssump { target: m }))
}

pub fn mk_expr_assume(h: Term, e: Expr) -> Expr {
    Expr::Assume(Arc::new(ExprAssume { target: h, expr: e }))
}

pub fn mk_expr_app(e1: Expr, e2: Expr, target: Term) -> Expr {
    Expr::App(Arc::new(ExprApp {
        expr1: e1,
        expr2: e2,
        target,
    }))
}

pub fn mk_expr_take(name: Name, ty: Type, e: Expr) -> Expr {
    Expr::Take(Arc::new(ExprTake { name, ty, expr: e }))
}

pub fn mk_expr_inst(e: Expr, m: Term, p: Term) -> Expr {
    Expr::Inst(Arc::new(ExprInst {
        expr: e,
        arg: m,
        predicate: p,
    }))
}

pub fn mk_expr_const(name: Name, ty_args: Vec<Type>) -> Expr {
    Expr::Const(Arc::new(ExprConst { name, ty_args }))
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Assump(e) => {
                write!(f, "⟪{}⟫", e.target)
            }
            Expr::Assume(e) => {
                write!(f, "assume {}, {}", e.target, e.expr)
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
                let ExprAssume { target, expr } = Arc::make_mut(e);
                target.inst_type_hole(subst);
                expr.inst_type_hole(subst);
            }
            Expr::App(e) => {
                let ExprApp {
                    expr1,
                    expr2,
                    target,
                } = Arc::make_mut(e);
                expr1.inst_type_hole(subst);
                expr2.inst_type_hole(subst);
                target.inst_type_hole(subst);
            }
            Expr::Take(e) => {
                let ExprTake { name: _, ty, expr } = Arc::make_mut(e);
                ty.inst_hole(subst);
                expr.inst_type_hole(subst);
            }
            Expr::Inst(e) => {
                let ExprInst {
                    expr,
                    arg,
                    predicate,
                } = Arc::make_mut(e);
                expr.inst_type_hole(subst);
                arg.inst_type_hole(subst);
                predicate.inst_type_hole(subst);
            }
            Expr::Const(e) => {
                let ExprConst { name: _, ty_args } = Arc::make_mut(e);
                for ty_arg in ty_args {
                    ty_arg.inst_hole(subst);
                }
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
                let ExprAssume { target, expr } = Arc::make_mut(e);
                target.inst_hole(subst);
                expr.inst_hole(subst);
            }
            Expr::App(e) => {
                let ExprApp {
                    expr1,
                    expr2,
                    target,
                } = Arc::make_mut(e);
                expr1.inst_hole(subst);
                expr2.inst_hole(subst);
                target.inst_hole(subst);
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
                let ExprInst {
                    expr,
                    arg,
                    predicate,
                } = Arc::make_mut(e);
                expr.inst_hole(subst);
                arg.inst_hole(subst);
                predicate.inst_hole(subst);
            }
            Expr::Const(_) => {}
        }
    }

    pub fn normalize(&mut self) {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = Arc::make_mut(e);
                target.normalize();
            }
            Expr::Assume(e) => {
                let ExprAssume { target, expr } = Arc::make_mut(e);
                target.normalize();
                expr.normalize();
            }
            Expr::App(e) => {
                let ExprApp {
                    expr1,
                    expr2,
                    target,
                } = Arc::make_mut(e);
                expr1.normalize();
                expr2.normalize();
                target.normalize();
            }
            Expr::Take(e) => {
                let ExprTake {
                    name: _,
                    ty: _,
                    expr,
                } = Arc::make_mut(e);
                expr.normalize();
            }
            Expr::Inst(e) => {
                let ExprInst {
                    expr,
                    arg,
                    predicate,
                } = Arc::make_mut(e);
                expr.normalize();
                arg.normalize();
                predicate.normalize();
            }
            Expr::Const(_) => {}
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
                let h = mk_proof_assump(expr.target.clone());
                (h, expr.target.clone())
            }
            Expr::Assume(inner) => {
                let (h, p) = self.run_help(&inner.expr);
                let h = mk_proof_imp_intro(inner.target.clone(), h);
                (
                    h,
                    Imp {
                        lhs: inner.target.clone(),
                        rhs: p,
                    }
                    .into(),
                )
            }
            Expr::App(inner) => {
                let (h1, p1) = self.run_help(&inner.expr1);
                let (h2, p2) = self.run_help(&inner.expr2);

                let pat: Term = Imp {
                    lhs: p2,
                    rhs: inner.target.clone(),
                }
                .into();

                let path = self.tt_env.equiv(&p1, &pat).unwrap();
                let h = mk_proof_imp_elim(mk_proof_conv(path, h1), h2);

                let Imp { lhs: _lhs, rhs } = pat.try_into().unwrap();
                (h, rhs)
            }
            Expr::Take(inner) => {
                self.tt_local_env
                    .locals
                    .push((inner.name, inner.ty.clone()));
                let (h, mut p) = self.run_help(&inner.expr);
                self.tt_local_env.locals.pop();

                let h = mk_proof_forall_intro(inner.name, inner.ty.clone(), h);

                p.generalize(&[(inner.name, inner.ty.clone())]);

                (h, p)
            }
            Expr::Inst(inner) => {
                let (h, p) = self.run_help(&inner.expr);

                let mut arg = inner.arg.clone();
                let ty = self.tt_env.infer_type(self.tt_local_env, &mut arg).unwrap();

                let mut pat = inner.predicate.clone();
                let tmp = Name::fresh_with_name("x");
                pat.apply([mk_local(tmp)]);
                pat.generalize(&[(tmp, ty.clone())]);

                let path = self.tt_env.equiv(&p, &pat).unwrap();
                let h = mk_proof_forall_elim(arg.clone(), mk_proof_conv(path, h));

                let Forall {
                    name: _name,
                    ty: _ty,
                    body,
                } = pat.try_into().unwrap();
                let mut target = body;
                target.open(&arg);

                (h, target)
            }
            Expr::Const(inner) => {
                let h = mk_proof_ref(inner.name, inner.ty_args.clone());
                let (tv, mut target) = self.axioms.get(&inner.name).cloned().unwrap();
                let mut subst = vec![];
                for (&x, t) in zip(&tv, &inner.ty_args) {
                    subst.push((x, t.clone()));
                }
                target.subst_type(&subst);
                (h, target)
            }
        }
    }

    pub fn run(&mut self, e: &Expr) -> Proof {
        self.run_help(e).0
    }
}
