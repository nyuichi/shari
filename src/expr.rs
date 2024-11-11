use std::sync::Arc;

use anyhow::bail;

use crate::kernel::{
    proof::{
        self, mk_proof_assump, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro,
        mk_proof_imp_elim, mk_proof_imp_intro, mk_proof_ref, mk_type_prop, Forall, Imp, Proof,
        Prop,
    },
    tt::{self, Name, Term, Type},
};

/// p ::= ⟪φ⟫
///     | assume φ, p
///     | p p
///     | take (x : τ), p
///     | p[m]
///     | change φ, p
///     | c.{u₁, ⋯, uₙ}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Assump(Arc<ExprAssump>),
    Assume(Arc<ExprAssume>),
    App(Arc<ExprApp>),
    Take(Arc<ExprTake>),
    Inst(Arc<ExprInst>),
    Change(Arc<ExprChange>),
    Const(Arc<ExprConst>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprAssump {
    pub target: Term,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprAssume {
    pub target: Term,
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprApp {
    pub expr1: Expr,
    pub expr2: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprTake {
    pub name: Name,
    pub ty: Type,
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprInst {
    pub expr: Expr,
    pub arg: Term,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprChange {
    pub target: Term,
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

pub fn mk_expr_change(h: Term, e: Expr) -> Expr {
    Expr::Change(Arc::new(ExprChange { target: h, expr: e }))
}

pub fn mk_expr_const(name: Name, ty_args: Vec<Type>) -> Expr {
    Expr::Const(Arc::new(ExprConst { name, ty_args }))
}

#[derive(Debug)]
pub struct Eval<'a> {
    proof_env: &'a proof::Env,
    local_env: &'a mut tt::LocalEnv,
}

impl<'a> Eval<'a> {
    pub fn new(proof_env: &'a proof::Env, local_env: &'a mut tt::LocalEnv) -> Self {
        Self {
            proof_env,
            local_env,
        }
    }

    fn certify_formula(&mut self, m: &Term) -> anyhow::Result<Term> {
        let mut m = m.clone();
        self.proof_env
            .tt_env
            .check_type(self.local_env, &mut m, &mut mk_type_prop())?;
        Ok(m)
    }

    pub fn run_expr(&mut self, expr: &Expr) -> anyhow::Result<(Proof, Term)> {
        match expr {
            Expr::Assump(inner) => {
                let prop = self.certify_formula(&inner.target)?;
                let h = mk_proof_assump(Prop {
                    target: prop.clone(),
                });
                Ok((h, prop))
            }
            Expr::Assume(inner) => {
                let prop = self.certify_formula(&inner.target)?;
                let (h, p) = self.run_expr(&inner.expr)?;
                let h = mk_proof_imp_intro(
                    Prop {
                        target: prop.clone(),
                    },
                    h,
                );
                Ok((h, Imp { lhs: prop, rhs: p }.into()))
            }
            Expr::App(inner) => {
                let (h1, p1) = self.run_expr(&inner.expr1)?;
                let (h2, _) = self.run_expr(&inner.expr2)?;
                let h = mk_proof_imp_elim(h1, h2);

                // destruct φ ⇒ ψ as ψ
                let target = {
                    let Ok(Imp { lhs: _, rhs }) = p1.clone().try_into() else {
                        bail!("not an implication: {}", p1);
                    };
                    rhs
                };

                Ok((h, target))
            }
            Expr::Take(inner) => {
                self.local_env.locals.push((inner.name, inner.ty.clone()));
                let (h, p) = self.run_expr(&inner.expr)?;
                self.local_env.locals.pop();
                let h = mk_proof_forall_intro(inner.name, inner.ty.clone(), h);

                let mut body = p;
                body.close(inner.name);

                Ok((
                    h,
                    Forall {
                        name: inner.name,
                        ty: inner.ty.clone(),
                        body,
                    }
                    .into(),
                ))
            }
            Expr::Inst(inner) => {
                let (h, p) = self.run_expr(&inner.expr)?;
                let mut arg = inner.arg.clone();
                self.proof_env.tt_env.infer_type(self.local_env, &mut arg)?;
                let h = mk_proof_forall_elim(arg.clone(), h);

                // destruct ∀ (x : τ), φ as [0/x]φ
                let Ok(Forall {
                    name: _,
                    ty: _,
                    body,
                }) = p.clone().try_into()
                else {
                    bail!("not a forall: {}", p);
                };

                let mut target = body;
                target.open(&arg);

                Ok((h, target))
            }
            Expr::Change(inner) => {
                let prop = self.certify_formula(&inner.target)?;
                let (h, p) = self.run_expr(&inner.expr)?;
                let Some(path) = self.proof_env.tt_env.equiv(&p, &prop) else {
                    bail!("terms not convertible: {} ≢ {}", p, prop);
                };
                let h = mk_proof_conv(path, h);
                Ok((h, prop))
            }
            Expr::Const(inner) => {
                let h = mk_proof_ref(inner.name, inner.ty_args.clone());
                let Some((tv, mut target)) = self.proof_env.facts.get(&inner.name).cloned() else {
                    bail!("proposition not found");
                };
                let subst: Vec<_> = std::iter::zip(tv, inner.ty_args.iter()).collect();
                target.target.instantiate(&subst);
                Ok((h, target.target))
            }
        }
    }
}
