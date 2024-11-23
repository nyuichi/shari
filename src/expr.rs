use std::{
    collections::{HashMap, VecDeque},
    mem,
    rc::Rc,
    sync::Arc,
};

use anyhow::bail;

use crate::kernel::{
    proof::{
        self, mk_proof_assump, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro,
        mk_proof_imp_elim, mk_proof_imp_intro, mk_proof_ref, mk_type_prop, Forall, Imp, Proof,
        Prop,
    },
    tt::{
        self, mk_abs, mk_const, mk_fresh_mvar, mk_fresh_type_mvar, mk_local, mk_var, Name, Term,
        Type,
    },
};

/// p ::= ⟪φ⟫
///     | assume φ, p
///     | p p
///     | take (x : τ), p
///     | p[m]
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
                let Some(subst) = unify(&p1.clone(), &pat, &self.proof_env.tt_env) else {
                    bail!("not an implication");
                };
                for (name, m) in &subst {
                    pat.inst_mvar(&[(*name, m)]);
                }
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
                let Some(subst) = unify(&p, &pat, &self.proof_env.tt_env) else {
                    bail!("not an implication");
                };
                for (name, m) in &subst {
                    pat.inst_mvar(&[(*name, m)]);
                }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintKind {
    Delta,
    QuasiPattern,
    FlexRigid,
    FlexFlex,
}

#[derive(Debug, Clone)]
struct Constraint {
    left: Term,
    right: Term,
    justification: Justification,
    kind: ConstraintKind,
}

#[derive(Debug, Clone)]
struct Justification {
    decision_level: usize,
}

impl Justification {
    fn join(&self, other: &Self) -> Self {
        Justification {
            decision_level: self.decision_level.max(other.decision_level),
        }
    }
}

#[derive(Debug, Clone)]
struct Snapshot {
    subst_len: usize,
    history_len: usize,
}

struct Branch<'a> {
    snapshot: Snapshot,
    constraint: Rc<Constraint>,
    choice: Box<dyn Iterator<Item = Vec<(Term, Term, Justification)>> + 'a>,
}

struct Unifier<'a> {
    tt_env: &'a tt::Env,
    queue_delta: VecDeque<Rc<Constraint>>,
    queue_qpat: VecDeque<Rc<Constraint>>,
    queue_fr: VecDeque<Rc<Constraint>>,
    queue_ff: VecDeque<Rc<Constraint>>,
    watch_list: HashMap<Name, Vec<Rc<Constraint>>>,
    subst: Vec<(Name, Term)>,
    subst_map: HashMap<Name, Term>,
    trail: Vec<Branch<'a>>,
    // for backjumping
    history: Vec<Rc<Constraint>>,
    // only used in find_conflict
    stack: Vec<(Term, Term, Justification)>,
}

impl<'a> Unifier<'a> {
    fn new(tt_env: &'a tt::Env, constraints: Vec<(Term, Term)>) -> Self {
        let mut solver = Self {
            tt_env,
            queue_delta: Default::default(),
            queue_qpat: Default::default(),
            queue_fr: Default::default(),
            queue_ff: Default::default(),
            watch_list: Default::default(),
            subst: Default::default(),
            subst_map: Default::default(),
            trail: Default::default(),
            history: Default::default(),
            stack: Default::default(),
        };
        for (left, right) in constraints.into_iter().rev() {
            solver
                .stack
                .push((left, right, Justification { decision_level: 0 }));
        }
        solver
    }

    fn inst_head(&self, left: &mut Term, right: &mut Term) -> bool {
        if let &Term::Mvar(left_head) = left.head() {
            if let Some(m) = self.subst_map.get(&left_head) {
                let subst = [(left_head, m)];
                left.inst_mvar(&subst);
                right.inst_mvar(&subst);
                return true;
            }
        }
        if let &Term::Mvar(right_head) = right.head() {
            if let Some(m) = self.subst_map.get(&right_head) {
                let subst = [(right_head, m)];
                left.inst_mvar(&subst);
                right.inst_mvar(&subst);
                return true;
            }
        }
        false
    }

    fn add_derived_constraint(
        &mut self,
        mut left: Term,
        mut right: Term,
        is_delta: bool,
        justification: Justification,
    ) {
        let kind;
        if is_delta {
            kind = ConstraintKind::Delta;
        } else if left.is_quasi_pattern() {
            kind = ConstraintKind::QuasiPattern;
        } else if right.is_quasi_pattern() {
            mem::swap(&mut left, &mut right);
            kind = ConstraintKind::QuasiPattern;
        } else if left.head().is_mvar() && right.head().is_mvar() {
            kind = ConstraintKind::FlexFlex;
        } else if left.head().is_mvar() {
            kind = ConstraintKind::FlexRigid;
        } else {
            mem::swap(&mut left, &mut right);
            kind = ConstraintKind::FlexRigid;
        }

        let c = Rc::new(Constraint {
            left: left.clone(),
            right: right.clone(),
            justification,
            kind,
        });

        self.history.push(c.clone());

        match kind {
            ConstraintKind::Delta => {
                self.queue_delta.push_back(c.clone());
            }
            ConstraintKind::QuasiPattern => {
                self.queue_qpat.push_back(c.clone());
            }
            ConstraintKind::FlexRigid => {
                self.queue_fr.push_back(c.clone());
            }
            ConstraintKind::FlexFlex => {
                self.queue_ff.push_back(c.clone());
            }
        }

        if !is_delta {
            if let &Term::Mvar(left_head) = left.head() {
                match self.watch_list.get_mut(&left_head) {
                    Some(constraints) => {
                        constraints.push(c.clone());
                    }
                    None => {
                        self.watch_list.insert(left_head, vec![c.clone()]);
                    }
                }
            }
            if let &Term::Mvar(right_head) = right.head() {
                match self.watch_list.get_mut(&right_head) {
                    Some(constraints) => {
                        constraints.push(c);
                    }
                    None => {
                        self.watch_list.insert(right_head, vec![c]);
                    }
                }
            }
        }
    }

    fn add_subst(&mut self, name: Name, m: Term) {
        self.subst.push((name, m.clone()));
        self.subst_map.insert(name, m);
    }

    fn find_conflict(&mut self) -> Option<Justification> {
        while let Some((mut left, mut right, justification)) = self.stack.pop() {
            if left.untyped_eq(&right) {
                continue;
            }
            if let (Term::Abs(l), Term::Abs(r)) = (&mut left, &mut right) {
                let x = Name::fresh();
                Arc::make_mut(l).body.open(&mk_local(x));
                Arc::make_mut(r).body.open(&mk_local(x));
                let left = mem::take(&mut Arc::make_mut(l).body);
                let right = mem::take(&mut Arc::make_mut(r).body);
                self.stack.push((left, right, justification));
                continue;
            }
            if left.whnf().is_some() || right.whnf().is_some() {
                self.stack.push((left, right, justification));
                continue;
            }
            if left.is_abs() {
                mem::swap(&mut left, &mut right);
            }
            if right.is_abs() {
                // L ≡ (?M t₁ ⋯ tₙ)
                if left.head().is_mvar() {
                    // this case is handled later.
                } else if self.tt_env.unfold_head(&mut left).is_some() {
                    self.stack.push((left, right, justification));
                    continue;
                } else {
                    return Some(justification);
                }
            }
            if self.inst_head(&mut left, &mut right) {
                self.stack.push((left, right, justification));
                continue;
            }
            // then each of the heads can be a local, a const, or an mvar
            if let &Term::Mvar(right_head) = right.head() {
                if let Some(args) = right.is_pattern() {
                    let args = args
                        .into_iter()
                        .map(|n| (n, n, mk_fresh_type_mvar()))
                        .collect::<Vec<_>>();
                    if left.abs(&args, false) {
                        self.add_subst(right_head, left.clone());
                        if let Some(constraints) = self.watch_list.get(&right_head) {
                            for c in constraints.iter().rev() {
                                if c.left.head() == &Term::Mvar(right_head) {
                                    if let Term::Mvar(right_head) = c.right.head() {
                                        if self.subst_map.contains_key(right_head) {
                                            continue;
                                        }
                                    }
                                } else if let Term::Mvar(left_head) = c.left.head() {
                                    if self.subst_map.contains_key(left_head) {
                                        continue;
                                    }
                                }
                                let mut c = (**c).clone();
                                let subst = [(right_head, &left)];
                                c.left.inst_mvar(&subst);
                                c.right.inst_mvar(&subst);
                                self.stack.push((
                                    c.left,
                                    c.right,
                                    c.justification.join(&justification),
                                ));
                            }
                        }
                        continue;
                    }
                }
            }
            if let &Term::Mvar(left_head) = left.head() {
                if let Some(args) = left.is_pattern() {
                    let args = args
                        .into_iter()
                        .map(|n| (n, n, mk_fresh_type_mvar()))
                        .collect::<Vec<_>>();
                    if right.abs(&args, false) {
                        self.add_subst(left_head, right.clone());
                        if let Some(constraints) = self.watch_list.get(&left_head) {
                            for c in constraints.iter().rev() {
                                if c.left.head() == &Term::Mvar(left_head) {
                                    if let Term::Mvar(right_head) = c.right.head() {
                                        if self.subst_map.contains_key(right_head) {
                                            continue;
                                        }
                                    }
                                } else if let Term::Mvar(left_head) = c.left.head() {
                                    if self.subst_map.contains_key(left_head) {
                                        continue;
                                    }
                                }
                                let mut c = (**c).clone();
                                let subst = [(left_head, &right)];
                                c.left.inst_mvar(&subst);
                                c.right.inst_mvar(&subst);
                                self.stack.push((
                                    c.left,
                                    c.right,
                                    c.justification.join(&justification),
                                ));
                            }
                        }
                        continue;
                    }
                }
            }
            if right.head().is_mvar() || left.head().is_mvar() {
                self.add_derived_constraint(left, right, false, justification);
                continue;
            }
            // then each of the heads can be a local or a const.
            if right.head().is_const() {
                mem::swap(&mut left, &mut right);
            }
            match (left.head(), right.head()) {
                (Term::Const(left_head), Term::Const(right_head)) => {
                    if left_head.name != right_head.name {
                        let left_hint = self.tt_env.def_hint(left_head.name).unwrap_or(0);
                        let right_hint = self.tt_env.def_hint(right_head.name).unwrap_or(0);
                        match left_hint.cmp(&right_hint) {
                            std::cmp::Ordering::Greater => {
                                self.tt_env.unfold_head(&mut left).unwrap();
                                self.stack.push((left, right, justification));
                                continue;
                            }
                            std::cmp::Ordering::Less => {
                                self.tt_env.unfold_head(&mut right).unwrap();
                                self.stack.push((left, right, justification));
                                continue;
                            }
                            std::cmp::Ordering::Equal => {
                                if left_hint == 0 {
                                    // (f t₁ ⋯ tₙ) ≈ (g s₁ ⋯ sₘ) where f and g are both irreducible.
                                    return Some(justification);
                                }
                                self.tt_env.unfold_head(&mut left).unwrap();
                                self.tt_env.unfold_head(&mut right).unwrap();
                                self.stack.push((left, right, justification));
                                continue;
                            }
                        }
                    }
                    // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ)
                    if self.tt_env.def_hint(left_head.name).is_none() {
                        let left_args = left.unapply();
                        let right_args = right.unapply();
                        if left_args.len() != right_args.len() {
                            return Some(justification);
                        }
                        for (left_arg, right_arg) in
                            left_args.into_iter().zip(right_args.into_iter()).rev()
                        {
                            self.stack
                                .push((left_arg, right_arg, justification.clone()));
                        }
                        continue;
                    }
                    // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ) where any of t or s contains an mvar.
                    self.add_derived_constraint(left, right, true, justification);
                    continue;
                }
                (Term::Const(left_head), Term::Local(right_head)) => {
                    // yuichi: perhaps we can simply give up on this case, when completeness is not important.
                    if self.tt_env.def_hint(left_head.name).is_none() {
                        return Some(justification);
                    }
                    left.close(*right_head);
                    if left.is_lclosed() {
                        return Some(justification);
                    }
                    left.open(&mk_local(*right_head));
                    self.tt_env.unfold_head(&mut left).unwrap();
                    self.stack.push((left, right, justification));
                    continue;
                }
                (Term::Local(left_head), Term::Local(right_head)) => {
                    if left_head != right_head {
                        return Some(justification);
                    }
                    let left_args = left.unapply();
                    let right_args = right.unapply();
                    if left_args.len() != right_args.len() {
                        return Some(justification);
                    }
                    for (left_arg, right_arg) in
                        left_args.into_iter().zip(right_args.into_iter()).rev()
                    {
                        self.stack
                            .push((left_arg, right_arg, justification.clone()));
                    }
                    continue;
                }
                _ => unreachable!(),
            }
        }
        None
    }

    fn is_resolved_constraint(&self, c: &Constraint) -> bool {
        if let &Term::Mvar(right_head) = c.right.head() {
            if self.subst_map.contains_key(&right_head) {
                return true;
            }
        }
        if let &Term::Mvar(left_head) = c.left.head() {
            if self.subst_map.contains_key(&left_head) {
                return true;
            }
        }
        false
    }

    fn save(&self) -> Snapshot {
        Snapshot {
            subst_len: self.subst.len(),
            history_len: self.history.len(),
        }
    }

    fn restore(&mut self, snapshot: &Snapshot) {
        for i in snapshot.subst_len..self.subst.len() {
            let name = self.subst[i].0;
            self.subst_map.remove(&name);
        }
        self.subst.truncate(snapshot.subst_len);
        for i in 0..self.history.len() - snapshot.history_len {
            let i = self.history.len() - i - 1;
            let c = &self.history[i];
            match c.kind {
                ConstraintKind::Delta => {
                    self.queue_delta.pop_back();
                }
                ConstraintKind::QuasiPattern => {
                    self.queue_qpat.pop_back();
                }
                ConstraintKind::FlexRigid => {
                    self.queue_fr.pop_back();
                }
                ConstraintKind::FlexFlex => {
                    self.queue_ff.pop_back();
                }
            }
            if let &Term::Mvar(left_head) = c.left.head() {
                let constraints = self.watch_list.get_mut(&left_head).unwrap();
                constraints.pop();
            }
            if let &Term::Mvar(right_head) = c.right.head() {
                let constraints = self.watch_list.get_mut(&right_head).unwrap();
                constraints.pop();
            }
        }
        self.history.truncate(snapshot.history_len);
    }

    fn push_branch(
        &mut self,
        snapshot: Snapshot,
        c: Rc<Constraint>,
        choice: Box<dyn Iterator<Item = Vec<(Term, Term, Justification)>> + 'a>,
    ) {
        self.trail.push(Branch {
            snapshot,
            constraint: c,
            choice,
        });
    }

    fn pop_branch(&mut self) -> bool {
        let Some(br) = self.trail.pop() else {
            return false;
        };
        if br.constraint.kind == ConstraintKind::Delta {
            self.queue_delta.push_front(br.constraint);
        }
        true
    }

    fn next(&mut self) -> bool {
        let Some(br) = self.trail.last_mut() else {
            return false;
        };
        let Some(constraints) = br.choice.next() else {
            return false;
        };
        let snapshot = br.snapshot.clone();
        self.restore(&snapshot);
        self.stack.clear();
        for (left, right, justification) in constraints.into_iter().rev() {
            self.stack.push((
                left,
                right,
                justification.join(&Justification {
                    decision_level: self.stack.len() + 1,
                }),
            ));
        }
        true
    }

    fn choice_delta(&self, c: &Constraint) -> Vec<Vec<(Term, Term, Justification)>> {
        // suppose (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₙ)
        let left_args = c.left.args();
        let right_args = c.right.args();
        // Try first (t₁ ≈ s₁) ∧ ⋯ ∧ (tₙ ≈ sₙ)
        let mut a1 = vec![];
        for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
            a1.push((left_arg.clone(), right_arg.clone(), c.justification.clone()));
        }
        // Try second ((unfold f) t₁ ⋯ tₙ ≈ (unfold f) s₁ ⋯ sₙ)
        let mut a2 = vec![];
        {
            let mut left = c.left.clone();
            let mut right = c.right.clone();
            self.tt_env.unfold_head(&mut left).unwrap();
            self.tt_env.unfold_head(&mut right).unwrap();
            a2.push((left, right, c.justification.clone()));
        }
        vec![a1, a2]
    }

    fn choice_fr(&self, c: &Constraint) -> Vec<Vec<(Term, Term, Justification)>> {
        let left = &c.left;
        let mut right = c.right.clone();

        let mut choice = vec![];

        if right.is_abs() {
            // f ≡                 ?M t[1] .. t[p]
            // r ≡ λ x[1] .. x[m],  @ u[1] .. u[q]
            //
            // Yield solutions in the form of:
            //
            // X ↦ λ z[1] .. z[p] x[1] .. x[m], ? (Y[1] z[1] .. z[p] x[1] .. x[m]) .. (Y[q] z[1] .. z[p] x[1] .. x[m])

            let left_head = left.head();
            let left_args = left.args();
            let right_binders = right.unabs();
            let right_args = right.args();
            let right_head = right.head();

            // z[1] .. z[p] x[1] .. x[m]
            let new_binders = (0..left_args.len())
                .map(|_| {
                    let name = Name::fresh();
                    // TODO: determine the types of new binders from t[1]..t[p].
                    (name, name, mk_fresh_type_mvar())
                })
                .chain(right_binders.iter().cloned())
                .collect::<Vec<_>>();

            // (Y[1] z[1] .. z[p] x[1] .. x[m]) .. (Y[q] z[1] .. z[p] x[1] .. x[m])
            let new_args = (0..right_args.len())
                .map(|_| {
                    let mut arg = mk_fresh_mvar();
                    for &(name, _, _) in &new_binders {
                        arg.apply([mk_local(name)]);
                    }
                    arg
                })
                .collect::<Vec<_>>();

            // projection
            for (x, _, _) in new_binders.iter().take(left_args.len()) {
                // TODO: yeild a candidate only if the target type is correct
                let mut cand = mk_local(*x);
                cand.apply(new_args.clone());
                cand.abs(&new_binders, true);
                choice.push(vec![(left_head.clone(), cand, c.justification.clone())]);
            }

            // imitation
            match right_head {
                Term::Const(_) => {
                    let mut cand = right_head.clone();
                    cand.apply(new_args.clone());
                    cand.abs(&new_binders, true);
                    choice.push(vec![(left_head.clone(), cand, c.justification.clone())]);
                }
                Term::Local(name) => {
                    // @ ∈ { x[1], .., x[m] }
                    if right_binders.iter().any(|(x, _, _)| x == name) {
                        let mut cand = right_head.clone();
                        cand.apply(new_args.clone());
                        cand.abs(&new_binders, true);
                        choice.push(vec![(left_head.clone(), cand, c.justification.clone())]);
                    }
                }
                _ => unreachable!(),
            };
        } else {
            // left  ≡ ?M t[1] .. t[p]
            // right ≡  @ u[1] .. u[q]

            let left_head = left.head();
            let left_args = left.args();
            let right_args = right.args();
            let right_head = right.head();

            for k in 0..=left_args.len().min(right_args.len()) {
                // Yield solutions in the form of:
                //
                // X ↦ λ z[1] .. z[p-k], ? (Y[1] z[1] .. z[p-k]) .. (Y[q-k] z[1] .. z[p-k])

                // TODO: check if types are equal for t[-k]..t[-1] and u[-k]..u[-1]
                // TODO: report types of Y[1]..Y[q-k]

                // z[1] .. z[p-k]
                let new_binders = (0..left_args.len() - k)
                    .map(|_| {
                        let name = Name::fresh();
                        // TODO: determine the types of new binders from t[1]..t[p].
                        (name, name, mk_fresh_type_mvar())
                    })
                    .collect::<Vec<_>>();

                // (Y[1] z[1] .. z[p-k]) .. (Y[q-k] z[1] .. z[p-k])
                let new_args = (0..right_args.len() - k)
                    .map(|_| {
                        let mut arg = mk_fresh_mvar();
                        for i in 0..left_args.len() - k {
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
                    cand.abs(&new_binders, true);
                    choice.push(vec![(left_head.clone(), cand, c.justification.clone())]);
                }

                // imitation
                match right_head {
                    Term::Const(_) => {
                        let mut cand = right_head.clone();
                        cand.apply(new_args.clone());
                        cand.abs(&new_binders, true);
                        choice.push(vec![(left_head.clone(), cand, c.justification.clone())]);
                    }
                    Term::Local(_) => {}
                    _ => unreachable!(),
                };
            }
        }
        choice
    }

    // Returns false if the constraints are pre-unified.
    fn decide(&mut self) -> bool {
        let snapshot = self.save();
        if let Some(c) = self.queue_delta.pop_front() {
            let choice = self.choice_delta(&c);
            self.push_branch(snapshot, c, Box::new(choice.into_iter()));
            self.next();
            return true;
        }
        if let Some(c) = self.queue_qpat.front() {
            if !self.is_resolved_constraint(c) {
                let choice = self.choice_fr(c);
                self.push_branch(snapshot, c.clone(), Box::new(choice.into_iter()));
                self.next();
                return true;
            }
        }
        if let Some(c) = self.queue_fr.front() {
            if !self.is_resolved_constraint(c) {
                let choice = self.choice_fr(c);
                self.push_branch(snapshot, c.clone(), Box::new(choice.into_iter()));
                self.next();
                return true;
            }
        }
        false
    }

    fn backjump(&mut self, justification: &Justification) -> bool {
        if justification.decision_level == 0 {
            return false;
        }
        while justification.decision_level < self.trail.len() {
            self.pop_branch();
        }
        while !self.next() {
            if !self.pop_branch() {
                return false;
            }
        }
        true
    }

    fn solve(mut self) -> Option<Vec<(Name, Term)>> {
        loop {
            while let Some(justification) = self.find_conflict() {
                if !self.backjump(&justification) {
                    return None;
                }
            }
            if !self.decide() {
                return Some(self.subst);
            }
        }
    }
}

fn unify(x: &Term, y: &Term, tt_env: &tt::Env) -> Option<Vec<(Name, Term)>> {
    let solver = Unifier::new(tt_env, vec![(x.clone(), y.clone())]);
    solver.solve()
}
