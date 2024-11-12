use std::{collections::VecDeque, sync::Arc};

use anyhow::bail;

use crate::kernel::{
    proof::{
        self, mk_proof_assump, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro,
        mk_proof_imp_elim, mk_proof_imp_intro, mk_proof_ref, mk_type_prop, Forall, Imp, Proof,
        Prop,
    },
    tt::{self, mk_abs, mk_const, mk_local, mk_var, Name, Term, Type},
};

/// p ::= ⟪φ⟫
///     | assume φ, p
///     | p p
///     | take (x : τ), p
///     | p[m]
///     | change φ, p
///     | c.{u₁, ⋯, uₙ}
///     | obtain (x : τ), p := e, e
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Assump(Arc<ExprAssump>),
    Assume(Arc<ExprAssume>),
    App(Arc<ExprApp>),
    Take(Arc<ExprTake>),
    Inst(Arc<ExprInst>),
    Change(Arc<ExprChange>),
    Const(Arc<ExprConst>),
    Obtain(Arc<ExprObtain>),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprObtain {
    pub name: Name,
    pub ty: Type,
    pub prop: Term,
    pub expr: Expr,
    pub body: Expr,
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

pub fn mk_expr_obtain(name: Name, ty: Type, prop: Term, expr: Expr, body: Expr) -> Expr {
    Expr::Obtain(Arc::new(ExprObtain {
        name,
        ty,
        prop,
        expr,
        body,
    }))
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

                // destruct φ ⇒ ψ as ψ
                let Ok(Imp { lhs, rhs }) = p1.clone().try_into() else {
                    bail!("not an implication: {}", p1);
                };

                // automatic insertion of change
                let (h2, _) = self.run_expr(&mk_expr_change(lhs, inner.expr2.clone()))?;
                let h = mk_proof_imp_elim(h1, h2);

                Ok((h, rhs))
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
                    bail!("proposition not found: {}", inner.name);
                };
                let subst: Vec<_> = std::iter::zip(tv, inner.ty_args.iter()).collect();
                target.target.instantiate(&subst);
                Ok((h, target.target))
            }
            Expr::Obtain(inner) => {
                let (h1, p1) = self.run_expr(&inner.expr)?;

                let expr2 = mk_expr_take(
                    inner.name,
                    inner.ty.clone(),
                    mk_expr_assume(inner.prop.clone(), inner.body.clone()),
                );
                let (h2, p2) = self.run_expr(&expr2)?;

                let Forall {
                    name: _,
                    ty: _,
                    body,
                } = p2.clone().try_into().unwrap();
                let Imp {
                    lhs: prop,
                    rhs: target,
                } = body.try_into().unwrap();

                if !target.is_lclosed() {
                    bail!("eigenvariable condition failed");
                }

                let pred = mk_abs(inner.name, inner.ty.clone(), prop.clone());

                let mut exists_p =
                    mk_const(Name::intern("exists").unwrap(), vec![inner.ty.clone()]);
                exists_p.apply([pred.clone()]);
                let Some(path1) = self.proof_env.tt_env.equiv(&p1, &exists_p) else {
                    bail!("terms not convertible: {} ≢ {}", p1, exists_p);
                };

                let mut p_x = pred.clone();
                p_x.apply([mk_var(0)]);
                let q: Term = Forall {
                    name: inner.name,
                    ty: inner.ty.clone(),
                    body: Imp {
                        lhs: p_x,
                        rhs: target.clone(),
                    }
                    .into(),
                }
                .into();
                let Some(path2) = self.proof_env.tt_env.equiv(&p2, &q) else {
                    bail!("terms not convertible: {} ≢ {}", p2, q);
                };

                let exists_elim =
                    mk_proof_ref(Name::intern("exists.elim").unwrap(), vec![inner.ty.clone()]);
                let h = mk_proof_forall_elim(pred.clone(), exists_elim);
                let h = mk_proof_forall_elim(target.clone(), h);
                let h = mk_proof_imp_elim(h, mk_proof_conv(path1, h1));
                let h = mk_proof_imp_elim(h, mk_proof_conv(path2, h2));
                Ok((h, target))
            }
        }
    }
}

// /// A convenient representation of head normal form.
// /// Recall that every (normal) term has form `λv*. m n*`.
// #[derive(Clone)]
// struct Triple {
//     /// Outermost-first
//     binder: Vec<(Name, Type)>,
//     /// may be locally open.
//     head: Term,
//     /// may be locally open.
//     /// Huch calls these parts "arguments" [Huch, 2020](https://www21.in.tum.de/teaching/sar/SS20/5.pdf).
//     /// See also Notation 2.29 in The Clausal Theory of Types [Wolfram, 2009].
//     args: Vec<Term>,
// }

// impl From<Term> for Triple {
//     /// m must be canonical
//     fn from(mut m: Term) -> Self {
//         let binder = m.undischarge();
//         let args = m.unapply();
//         let head = m;
//         Self { binder, head, args }
//     }
// }

// impl From<Triple> for Term {
//     fn from(m: Triple) -> Self {
//         let Triple { binder, head, args } = m;
//         let mut m = head;
//         m.apply(args);
//         m.discharge(binder);
//         m
//     }
// }

// impl Triple {
//     /// See [Vukmirović+, 2020].
//     pub fn is_flex(&self, free_list: &[Name]) -> bool {
//         match self.head {
//             Term::Local(local) => free_list.contains(&local),
//             Term::Var(_) | Term::Const(_) => false,
//             Term::Abs(_) | Term::App(_) => unreachable!(),
//         }
//     }

//     /// See [Vukmirović+, 2020].
//     pub fn is_rigid(&self, free_list: &[Name]) -> bool {
//         !self.is_flex(free_list)
//     }

//     /// Suppose `f ≡ λx*. X t*` and `r ≡ λy*. x u*`.
//     /// Imitation: X ↦ λz*. x (Y z*)* (when x = c)
//     /// Projection: X ↦ λz*. zᵢ (Y z*)* (when τ(zᵢ) is compatible with τ(x))
//     fn r#match(&self, other: &Triple) -> Vec<(Name, Term)> {
//         assert!(self.is_flex());
//         assert!(self.is_rigid());
//         let (t, mid) = if let Term::Mvar(t, mid) = &self.head {
//             (t, *mid)
//         } else {
//             panic!("self is not flex")
//         };
//         let binder: Vec<_> = t
//             .components()
//             .into_iter()
//             .map(|t| (Name::fresh(), t.clone()))
//             .collect();
//         let mut heads = vec![];
//         // projection
//         for (x, u) in &binder {
//             if t.target() == u.target() {
//                 heads.push(Term::Fvar((*u).clone(), x.to_owned()));
//             }
//         }
//         // imitation
//         match other.head {
//             Term::Fvar(_, _) | Term::Const(_, _) => {
//                 heads.push(other.head.clone());
//             }
//             _ => {}
//         };
//         let mut subst = vec![];
//         for mut head in heads {
//             head.curry(
//                 head.r#type()
//                     .components()
//                     .into_iter()
//                     .map(|t| {
//                         let mut t = t.clone();
//                         t.curry(binder.iter().map(|(_, t)| (*t).clone()).collect());
//                         let mut m = Term::Mvar(t, MvarId::fresh());
//                         m.curry(
//                             binder
//                                 .iter()
//                                 .map(|(x, t)| Term::Fvar(t.clone(), x.to_owned()))
//                                 .collect(),
//                         );
//                         m
//                     })
//                     .collect(),
//             );
//             head.r#abstract(binder.clone());
//             subst.push((mid, head));
//         }
//         subst
//     }
// }

// /// In Huet's original paper a disagreement set is just a finite set of pairs of terms.
// /// For performance improvement, we classify pairs into rigid/rigid, flex/rigid, and flex/flex
// /// at the preprocessing phase.
// #[derive(Default)]
// struct DisagreementSet {
//     // rigid-rigid
//     rr: Vec<(Triple, Triple)>,
//     // flex-rigid
//     fr: Vec<(Triple, Triple)>,
//     // flex-flex
//     ff: Vec<(Triple, Triple)>,
// }

// impl DisagreementSet {
//     fn add(&mut self, m1: Triple, m2: Triple, free_list: &[Name]) {
//         match (m1.is_rigid(free_list), m2.is_rigid(free_list)) {
//             (true, true) => self.rr.push((m1, m2)),
//             (true, false) => self.fr.push((m2, m1)),
//             (false, true) => self.fr.push((m1, m2)),
//             (false, false) => self.ff.push((m1, m2)),
//         }
//     }

//     /// decompose rigid-rigid pairs by chopping into smaller ones
//     fn simplify(&mut self, free_list: &[Name]) -> bool {
//         while let Some((h1, h2)) = self.rr.pop() {
//             assert_eq!(h1.binder.len(), h2.binder.len());
//             for ((_, t1), (_, t2)) in h1.binder.iter().zip(h2.binder.iter()) {
//                 assert_eq!(t1, t2);
//             }
//             if h1.head != h2.head {
//                 return false;
//             }
//             assert_eq!(h1.args.len(), h2.args.len());
//             for (mut a1, mut a2) in h1.args.into_iter().zip(h2.args.into_iter()) {
//                 a1.discharge(h1.binder.clone());
//                 a2.discharge(h2.binder.clone());
//                 self.add(Triple::from(a1), Triple::from(a2), free_list);
//             }
//         }
//         true
//     }

//     fn solve(self, free_list: &[Name]) -> Vec<(Name, Term)> {
//         let mut queue = VecDeque::new();
//         queue.push_back((self, vec![]));
//         while let Some((mut set, subst)) = queue.pop_front() {
//             if !set.simplify(free_list) {
//                 continue;
//             }
//             if set.fr.is_empty() {
//                 return subst;
//             }
//             let (h1, h2) = &set.fr[0];
//             for (name, m) in h1.r#match(h2) {
//                 let mut new_set = DisagreementSet::default();
//                 for (m1, m2) in set.fr.iter().chain(set.ff.iter()) {
//                     let mut m1 = Term::from(m1.clone());
//                     m1.subst(name, &m);
//                     m1.normalize();
//                     let mut m2 = Term::from(m2.clone());
//                     m2.subst(name, &m);
//                     m2.normalize();
//                     new_set.add(Triple::from(m1), Triple::from(m2), free_list);
//                 }
//                 let mut new_subst = subst.clone();
//                 new_subst.push((name, m));
//                 queue.push_back((new_set, new_subst));
//             }
//         }
//         todo!("no solution found");
//     }
// }

// impl Term {
//     /// `self` and `other` must be type-correct and type-equal under the same environment.
//     pub fn unify(&mut self, other: &mut Term, free_list: &[Name]) {
//         let mut set = DisagreementSet::default();
//         self.normalize();
//         let h1 = Triple::from(self.clone());
//         other.normalize();
//         let h2 = Triple::from(std::mem::take(other));
//         set.add(h1, h2, free_list);
//         let subst = set.solve(free_list);
//         for (name, m) in subst {
//             self.subst(name, &m);
//         }
//         *other = self.clone();
//     }
// }
