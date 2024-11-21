use std::{collections::VecDeque, sync::Arc};

use anyhow::bail;

use crate::kernel::{
    proof::{
        self, mk_proof_assump, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro,
        mk_proof_imp_elim, mk_proof_imp_intro, mk_proof_ref, mk_type_prop, Forall, Imp, Proof,
        Prop,
    },
    tt::{
        self, mk_abs, mk_const, mk_fresh_mvar, mk_fresh_type_mvar, mk_local, mk_var, LocalEnv,
        Name, Term, Type,
    },
};

/// p ::= ⟪φ⟫
///     | assume φ, p
///     | p p
///     | take (x : τ), p
///     | p[m]
///     | change φ, p
///     | c.{u₁, ⋯, uₙ}
///     | obtain (x : τ), p := e, e
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
/// Γ | Φ ⊢ h : φ    φ ≈ ∀ (x : u), ψ
/// ---------------------------------- (Γ ⊢ m : u)
/// Γ | Φ ⊢ h[m] : [m/x]ψ
///
/// Γ | Φ ⊢ h : φ
/// ----------------------- (φ ≡ ψ)
/// Γ | Φ ⊢ change ψ, h : ψ
///
/// -------------------------
/// Γ | Φ ⊢ c.{u₁, ⋯, uₙ} : φ
///
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
                let (h2, p2) = self.run_expr(&inner.expr2)?;

                let mut rhs = mk_fresh_mvar();
                rhs.apply(
                    self.local_env
                        .locals
                        .iter()
                        .map(|(name, _)| mk_local(*name)),
                );
                let mut pat: Term = Imp { lhs: p2, rhs }.into();
                unify(&mut p1.clone(), &mut pat, &self.proof_env.tt_env);
                pat.normalize();
                self.proof_env.tt_env.infer_type(self.local_env, &mut pat)?;

                let Some(path) = self.proof_env.tt_env.equiv(&p1, &pat) else {
                    bail!("terms not convertible: {} ≢ {}", p1, pat);
                };
                let h = mk_proof_imp_elim(mk_proof_conv(path, h1), h2);

                let Imp { lhs: _lhs, rhs } = pat.try_into().unwrap();
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
                let ty = self.proof_env.tt_env.infer_type(self.local_env, &mut arg)?;

                let mut body = mk_fresh_mvar();
                body.apply([mk_var(0)]);
                body.apply(
                    self.local_env
                        .locals
                        .iter()
                        .map(|(name, _)| mk_local(*name)),
                );
                let mut pat: Term = Forall {
                    name: Name::fresh(),
                    ty: ty.clone(),
                    body,
                }
                .into();
                unify(&mut p.clone(), &mut pat, &self.proof_env.tt_env);
                pat.normalize();
                self.proof_env.tt_env.infer_type(self.local_env, &mut pat)?;

                let Some(path) = self.proof_env.tt_env.equiv(&p, &pat) else {
                    bail!("terms not convertible: {} ≢ {}", p, pat);
                };
                let h = mk_proof_forall_elim(arg.clone(), mk_proof_conv(path, h));

                let Forall {
                    name: _name,
                    ty: _ty,
                    body,
                } = pat.try_into().unwrap();
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
                target.target.inst_type_mvar(&subst);
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

/// A convenient representation of head normal form.
/// Recall that every (normal) term has form `λv*. m n*`.
#[derive(Debug, Clone)]
struct Triple {
    /// Outermost-first
    /// The second element is the display name of the binder.
    binder: Vec<(Name, Name, Type)>,
    /// must be locally closed.
    head: Term,
    /// must be locally closed.
    /// Huch calls these parts "arguments" [Huch, 2020](https://www21.in.tum.de/teaching/sar/SS20/5.pdf).
    /// See also Notation 2.29 in The Clausal Theory of Types [Wolfram, 2009].
    args: Vec<Term>,
}

impl From<Term> for Triple {
    /// m must be canonical
    fn from(mut m: Term) -> Self {
        let binder = m.unabs();
        let args = m.unapply();
        let head = m;
        Self { binder, head, args }
    }
}

impl From<Triple> for Term {
    fn from(m: Triple) -> Self {
        let Triple { binder, head, args } = m;
        let mut m = head;
        m.apply(args);
        m.abs(binder);
        m
    }
}

impl Triple {
    /// See [Vukmirović+, 2020].
    pub fn is_flex(&self) -> bool {
        match self.head {
            Term::Mvar(_) => true,
            Term::Local(_) | Term::Const(_) => false,
            Term::Var(_) | Term::Abs(_) | Term::App(_) => unreachable!(),
        }
    }

    /// See [Vukmirović+, 2020].
    pub fn is_rigid(&self) -> bool {
        !self.is_flex()
    }

    /// Suppose `f ≡ λx*. X t*` and `r ≡ λy*. @ u*`.
    /// Imitation: X ↦ λz*. @ (Y z*)* (when @ = c)
    /// Projection: X ↦ λz*. zᵢ (Y z*)*
    ///
    /// Currently this method is type-agnostic.
    fn r#match(&self, other: &Triple) -> Vec<(Name, Term)> {
        assert!(self.is_flex());
        assert!(other.is_rigid());
        let mut subst = vec![];
        let Term::Mvar(mid) = self.head else {
            unreachable!()
        };
        match self.binder.len().cmp(&other.binder.len()) {
            std::cmp::Ordering::Greater => {
                return vec![];
            }
            std::cmp::Ordering::Equal => {
                // f ≡ λ x[1] .. x[n], X t[1] .. t[p]
                // r ≡ λ x[1] .. x[n], @ u[1] .. u[q]
                for k in 0..=self.args.len().min(other.args.len()) {
                    // Yield solutions in the form of:
                    //
                    // X ↦ λ z[1] .. z[p-k], ? (Y[1] z[1] .. z[p-k]) .. (Y[q-k] z[1] .. z[p-k])
                    //
                    // which means:
                    //
                    // f ≡ λ x[1] .. x[n], ?? (Y[1] t[1] .. t[p-k]) .. (Y[q-k] t[1] .. t[p-k]) t[p-k+1] .. t[p].

                    // TODO: check if types are equal for t[-k]..t[-1] and u[-k]..u[-1]
                    // TODO: report types of Y[1]..Y[q-k]

                    // z[1] .. z[p-k]
                    let new_binders = (0..self.args.len() - k)
                        .map(|_| {
                            let name = Name::fresh();
                            // TODO: determine the types of new binders from t[1]..t[p].
                            (name, name, mk_fresh_type_mvar())
                        })
                        .collect::<Vec<_>>();

                    // (Y[1] z[1] .. z[p-k]) .. (Y[q-k] z[1] .. z[p-k])
                    let new_args = (0..other.args.len() - k)
                        .map(|_| {
                            let mut arg = mk_fresh_mvar();
                            for i in 0..self.args.len() - k {
                                arg.apply([mk_local(new_binders[i].0)]);
                            }
                            arg
                        })
                        .collect::<Vec<_>>();

                    // projection
                    for (x, _, _) in &new_binders {
                        // TODO: yeild a candidate only if the target type is correct
                        let mut cand = mk_local(*x);
                        cand.apply(new_args.clone());
                        cand.abs(new_binders.clone());
                        subst.push((mid, cand));
                    }

                    // imitation
                    match other.head {
                        Term::Const(_) => {
                            let mut cand = other.head.clone();
                            cand.apply(new_args.clone());
                            cand.abs(new_binders.clone());
                            subst.push((mid, cand));
                        }
                        Term::Local(_) => {}
                        _ => unreachable!(),
                    };
                }
            }
            std::cmp::Ordering::Less => {
                // f ≡ λ x[1] .. x[n],                X t[1] .. t[p]
                // r ≡ λ x[1] .. x[n] x[n+1] .. x[m], @ u[1] .. u[q]
                //
                // Yield solutions in the form of:
                //
                // X ↦ λ z[1] .. z[p] x[n+1] .. x[m], ? (Y[1] z[1] .. z[p] x[n+1] .. x[m]) .. (Y[q] z[1] .. z[p] x[n+1] .. x[m])

                // z[1] .. z[p] x[n+1] .. x[m]
                let new_binders = (0..self.args.len())
                    .map(|_| {
                        let name = Name::fresh();
                        // TODO: determine the types of new binders from t[1]..t[p].
                        (name, name, mk_fresh_type_mvar())
                    })
                    .chain(
                        other.binder[self.binder.len()..other.binder.len()]
                            .iter()
                            .cloned(),
                    )
                    .collect::<Vec<_>>();

                // (Y[1] z[1] .. z[p] x[n+1] .. x[m]) .. (Y[q] z[1] .. z[p] x[n+1] .. x[m])
                let new_args = (0..other.args.len())
                    .map(|_| {
                        let mut arg = mk_fresh_mvar();
                        for &(name, _, _) in &new_binders {
                            arg.apply([mk_local(name)]);
                        }
                        arg
                    })
                    .collect::<Vec<_>>();

                // projection
                for (x, _, _) in new_binders.iter().take(self.args.len()) {
                    // TODO: yeild a candidate only if the target type is correct
                    let mut cand = mk_local(*x);
                    cand.apply(new_args.clone());
                    cand.abs(new_binders.clone());
                    subst.push((mid, cand));
                }

                // imitation
                match other.head {
                    Term::Const(_) => {
                        let mut cand = other.head.clone();
                        cand.apply(new_args.clone());
                        cand.abs(new_binders.clone());
                        subst.push((mid, cand));
                    }
                    Term::Local(name) => {
                        // @ ∈ { x[n+1], .., x[m] }
                        if other
                            .binder
                            .iter()
                            .skip(self.args.len())
                            .any(|(x, _, _)| x == &name)
                        {
                            let mut cand = other.head.clone();
                            cand.apply(new_args.clone());
                            cand.abs(new_binders.clone());
                            subst.push((mid, cand));
                        }
                    }
                    _ => unreachable!(),
                };
            }
        }
        subst
    }
}

/// In Huet's original paper a disagreement set is just a finite set of pairs of terms.
/// For performance improvement, we classify pairs into rigid/rigid, flex/rigid, and flex/flex
/// at the preprocessing phase.
struct DisagreementSet<'a> {
    // rigid-rigid
    rr: Vec<(Triple, Triple)>,
    // flex-rigid
    fr: Vec<(Triple, Triple)>,
    // flex-flex
    ff: Vec<(Triple, Triple)>,
    tt_env: &'a tt::Env,
}

impl<'a> DisagreementSet<'a> {
    fn new(tt_env: &'a tt::Env) -> Self {
        Self {
            rr: vec![],
            fr: vec![],
            ff: vec![],
            tt_env,
        }
    }

    fn add(&mut self, mut m1: Term, mut m2: Term) {
        m1.hnf();
        m2.hnf();
        let m1 = Triple::from(m1);
        let m2 = Triple::from(m2);
        match (m1.is_rigid(), m2.is_rigid()) {
            (true, true) => self.rr.push((m1, m2)),
            (true, false) => self.fr.push((m2, m1)),
            (false, true) => self.fr.push((m1, m2)),
            (false, false) => self.ff.push((m1, m2)),
        }
    }

    /// decompose rigid-rigid pairs by chopping into smaller ones
    fn simplify(&mut self) -> bool {
        while let Some((mut h1, mut h2)) = self.rr.pop() {
            match (&h1.head, &h2.head) {
                (Term::Local(name1), Term::Local(name2)) => {
                    let mut name2 = *name2;
                    for (i, (x, _, _)) in h2.binder.iter().enumerate() {
                        if i == h1.binder.len() {
                            break;
                        }
                        if x == &name2 {
                            name2 = h1.binder[i].0;
                            break;
                        }
                    }
                    if name1 != &name2 {
                        return false;
                    }
                }
                (Term::Local(_), Term::Const(_)) => {
                    if h1.binder.len() < h2.binder.len() {
                        return false;
                    }
                    // TODO: check if name occurs in h2.args
                    if self.tt_env.delta_reduce(&mut h2.head).is_none() {
                        return false;
                    }
                    self.add(Term::from(h1), Term::from(h2));
                    continue;
                }
                (Term::Const(_), Term::Local(_)) => {
                    if h1.binder.len() > h2.binder.len() {
                        return false;
                    }
                    // TODO: check if name occurs in h1.args
                    if self.tt_env.delta_reduce(&mut h1.head).is_none() {
                        return false;
                    }
                    self.add(Term::from(h1), Term::from(h2));
                    continue;
                }
                (Term::Const(head1), Term::Const(head2)) => {
                    if head1.name != head2.name {
                        let def1 = self.tt_env.def_hint(head1.name);
                        let def2 = self.tt_env.def_hint(head2.name);
                        match (def1, def2) {
                            (None, None) => {
                                return false;
                            }
                            (Some(_), None) => {
                                self.tt_env.delta_reduce(&mut h1.head).unwrap();
                                self.add(Term::from(h1), Term::from(h2));
                                continue;
                            }
                            (None, Some(_)) => {
                                self.tt_env.delta_reduce(&mut h2.head).unwrap();
                                self.add(Term::from(h1), Term::from(h2));
                                continue;
                            }
                            (Some(hint1), Some(hint2)) => match hint1.cmp(&hint2) {
                                std::cmp::Ordering::Greater => {
                                    self.tt_env.delta_reduce(&mut h1.head).unwrap();
                                    self.add(Term::from(h1), Term::from(h2));
                                    continue;
                                }
                                std::cmp::Ordering::Less => {
                                    self.tt_env.delta_reduce(&mut h2.head).unwrap();
                                    self.add(Term::from(h1), Term::from(h2));
                                    continue;
                                }
                                std::cmp::Ordering::Equal => {
                                    self.tt_env.delta_reduce(&mut h1.head).unwrap();
                                    self.tt_env.delta_reduce(&mut h2.head).unwrap();
                                    self.add(Term::from(h1), Term::from(h2));
                                    continue;
                                }
                            },
                        }
                    } else {
                        if h1.binder.len() != h2.binder.len() {
                            return false;
                        }
                        if h1.args.len() != h2.args.len() {
                            return false;
                        }
                        let mut arg_match = true;
                        for (a1, a2) in h1.args.iter().zip(h2.args.iter()) {
                            if self.tt_env.equiv(a1, a2).is_none() {
                                arg_match = false;
                                break;
                            }
                        }
                        if arg_match {
                            continue;
                        }
                        if self.tt_env.delta_reduce(&mut h1.head).is_some() {
                            self.tt_env.delta_reduce(&mut h2.head).unwrap();
                            self.add(Term::from(h1), Term::from(h2));
                            continue;
                        }
                    }
                }
                _ => {}
            }
            // if heads are equal and neither of them can be delta-reduced.

            if h1.binder.len() != h2.binder.len() {
                return false;
            }
            if h1.args.len() != h2.args.len() {
                return false;
            }
            for (mut a1, mut a2) in h1.args.into_iter().zip(h2.args.into_iter()) {
                a1.abs(h1.binder.clone());
                a2.abs(h2.binder.clone());
                self.add(a1, a2);
            }
        }
        true
    }

    fn solve(self) -> Option<Vec<(Name, Term)>> {
        let tt_env = self.tt_env;
        let mut queue = VecDeque::new();
        queue.push_back((self, vec![]));
        while let Some((mut set, subst)) = queue.pop_front() {
            if !set.simplify() {
                continue;
            }
            if set.fr.is_empty() {
                return Some(subst);
            }
            let (h1, h2) = &set.fr[0];
            for (name, m) in h1.r#match(h2) {
                let mut new_set = DisagreementSet::<'a>::new(tt_env);
                for (m1, m2) in set.fr.iter().chain(set.ff.iter()) {
                    let mut m1 = Term::from(m1.clone());
                    m1.inst_mvar(&[(name, &m)]);
                    let mut m2 = Term::from(m2.clone());
                    m2.inst_mvar(&[(name, &m)]);
                    new_set.add(m1, m2);
                }
                let mut new_subst = subst.clone();
                new_subst.push((name, m));
                queue.push_back((new_set, new_subst));
            }
        }
        None
    }
}

fn unify(x: &mut Term, y: &mut Term, tt_env: &tt::Env) -> Vec<(Name, Term)> {
    let mut set = DisagreementSet::new(tt_env);
    set.add(x.clone(), y.clone());
    let Some(subst) = set.solve() else {
        panic!("unification failed:\n{x}\n{y}");
    };
    for (name, m) in &subst {
        x.inst_mvar(&[(*name, m)]);
        y.inst_mvar(&[(*name, m)]);
    }
    x.normalize();
    y.normalize();
    if !x.is_ground() || !y.is_ground() {
        panic!("flex-flex remains\n{x}\n{y}");
    }
    subst
}
