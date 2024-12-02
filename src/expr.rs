use std::{
    collections::{HashMap, VecDeque},
    iter::repeat_n,
    mem,
    rc::Rc,
    sync::Arc,
};

use anyhow::{bail, Context};

use crate::kernel::{
    proof::{
        mk_proof_assump, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro,
        mk_proof_imp_elim, mk_proof_imp_intro, mk_proof_ref, mk_type_prop, Forall, Imp, Proof,
    },
    tt::{
        self, mk_fresh_hole, mk_fresh_type_hole, mk_local, mk_type_arrow, mk_var, Kind, Name, Term,
        TermAbs, TermApp, Type, TypeApp, TypeArrow,
    },
};

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
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Assump(Arc<ExprAssump>),
    Assume(Arc<ExprAssume>),
    App(Arc<ExprApp>),
    Take(Arc<ExprTake>),
    Inst(Arc<ExprInst>),
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
    // ξ : Prop
    pub target: Term,
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
    // P : u → Prop
    pub predicate: Term,
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
    fn inst_type_hole(&mut self, subst: &[(Name, &Type)]) {
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

    fn inst_hole(&mut self, subst: &[(Name, &Term)]) {
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
                let ExprTake { name: _, ty, expr } = Arc::make_mut(e);
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

    fn normalize(&mut self) {
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
    tt_env: &'a tt::Env,
    tt_local_env: &'a mut tt::LocalEnv,
    // Proved or postulated facts
    facts: &'a HashMap<Name, (Vec<Name>, Term)>,
    locals: Vec<Term>,
    type_constraints: Vec<(Type, Type)>,
    term_constraints: Vec<(Term, Term)>,
}

impl<'a> Env<'a> {
    pub fn new(
        tt_env: &'a tt::Env,
        tt_local_env: &'a mut tt::LocalEnv,
        facts: &'a HashMap<Name, (Vec<Name>, Term)>,
    ) -> Self {
        Env {
            tt_env,
            tt_local_env,
            facts,
            locals: vec![],
            type_constraints: vec![],
            term_constraints: vec![],
        }
    }

    fn add_type_constraint(&mut self, t1: Type, t2: Type) {
        self.type_constraints.push((t1, t2));
    }

    fn add_term_constraint(&mut self, m1: Term, m2: Term) {
        self.term_constraints.push((m1, m2));
    }

    fn visit_type(&self, t: Type) -> anyhow::Result<Kind> {
        match t {
            Type::Const(t) => {
                let Some(kind) = self.tt_env.type_consts.get(&t) else {
                    bail!("constant type not found");
                };
                Ok(kind.clone())
            }
            Type::Arrow(t) => {
                let TypeArrow { dom, cod } = Arc::unwrap_or_clone(t);
                let dom_kind = self.visit_type(dom)?;
                if !dom_kind.is_base() {
                    bail!("expected Type, but got {dom_kind}");
                }
                let cod_kind = self.visit_type(cod)?;
                if !cod_kind.is_base() {
                    bail!("expected Type, but got {cod_kind}");
                }
                Ok(Kind::base())
            }
            Type::App(t) => {
                let TypeApp { fun, arg } = Arc::unwrap_or_clone(t);
                let fun_kind = self.visit_type(fun.clone())?;
                if fun_kind.is_base() {
                    bail!("too many type arguments: {fun} {arg}");
                }
                let arg_kind = self.visit_type(arg)?;
                if !arg_kind.is_base() {
                    bail!("expected Type, but got {arg_kind}");
                }
                Ok(Kind(fun_kind.0 - 1))
            }
            Type::Local(t) => {
                for local_type in self.tt_local_env.local_types.iter().rev() {
                    if *local_type == t {
                        return Ok(Kind::base());
                    }
                }
                bail!("unbound local type: {t}");
            }
            Type::Hole(_) => Ok(Kind::base()),
        }
    }

    fn visit_term(&mut self, m: Term) -> anyhow::Result<Type> {
        match m {
            Term::Local(m) => {
                for (local, ty) in &self.tt_local_env.locals {
                    if *local == m {
                        return Ok(ty.clone());
                    }
                }
                bail!("unknown local variable: {m}");
            }
            Term::Hole(m) => {
                for (local, ty) in &self.tt_local_env.holes {
                    if *local == m {
                        return Ok(ty.clone());
                    }
                }
                bail!("unknown meta variable");
            }
            Term::Var(_) => {
                bail!("term not locally closed");
            }
            Term::Abs(m) => {
                let TermAbs {
                    binder_type: arg_ty,
                    binder_name: _,
                    mut body,
                } = Arc::unwrap_or_clone(m);

                let arg_ty_kind = self.visit_type(arg_ty.clone())?;
                if !arg_ty_kind.is_base() {
                    bail!("expected Type, but got {arg_ty_kind}");
                }

                let x = Name::fresh();
                self.tt_local_env.locals.push((x, arg_ty.clone()));
                body.open(&mk_local(x));
                let body_ty = self.visit_term(body)?;
                self.tt_local_env.locals.pop();

                Ok(mk_type_arrow(arg_ty, body_ty))
            }
            Term::App(m) => {
                let TermApp { fun, arg } = Arc::unwrap_or_clone(m);

                let fun_ty = self.visit_term(fun)?;
                let arg_ty = self.visit_term(arg)?;
                let ret_ty = mk_fresh_type_hole();

                self.add_type_constraint(fun_ty, mk_type_arrow(arg_ty, ret_ty.clone()));

                Ok(ret_ty)
            }
            Term::Const(m) => {
                let Some((tv, ty)) = self.tt_env.consts.get(&m.name) else {
                    bail!("constant not found");
                };
                if tv.len() != m.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                for ty_arg in &m.ty_args {
                    let ty_arg_kind = self.visit_type(ty_arg.clone())?;
                    if !ty_arg_kind.is_base() {
                        bail!("expected Type, but got {ty_arg_kind}");
                    }
                }
                let mut ty = ty.clone();
                ty.subst(&std::iter::zip(tv.iter().copied(), &m.ty_args).collect::<Vec<_>>());
                Ok(ty)
            }
        }
    }

    fn visit_expr(&mut self, e: &Expr) -> anyhow::Result<Term> {
        match e {
            Expr::Assump(e) => {
                let ExprAssump { target } = &**e;

                let target_ty = self.visit_term(target.clone())?;
                self.add_type_constraint(target_ty, mk_type_prop());

                let mut found = false;
                for local in &self.locals {
                    // use literal equality by intention
                    if local.untyped_eq(target) {
                        found = true;
                        break;
                    }
                }
                if !found {
                    bail!("assumption not found: {target}");
                }

                Ok(target.clone())
            }
            Expr::Assume(e) => {
                let ExprAssume { target, expr } = &**e;

                let target_ty = self.visit_term(target.clone())?;
                self.add_type_constraint(target_ty, mk_type_prop());

                self.locals.push(target.clone());
                let rhs = self.visit_expr(expr)?;
                self.locals.pop();

                Ok(Imp {
                    lhs: target.clone(),
                    rhs,
                }
                .into())
            }
            Expr::App(e) => {
                let ExprApp {
                    expr1,
                    expr2,
                    target,
                } = &**e;

                let fun_prop = self.visit_expr(expr1)?;
                let arg_prop = self.visit_expr(expr2)?;
                let target_ty = self.visit_term(target.clone())?;
                self.add_type_constraint(target_ty, mk_type_prop());

                let pat: Term = Imp {
                    lhs: arg_prop,
                    rhs: target.clone(),
                }
                .into();
                self.add_term_constraint(pat, fun_prop);

                Ok(target.clone())
            }
            Expr::Take(e) => {
                let ExprTake { name, ty, expr } = &**e;

                let ty_kind = self.visit_type(ty.clone())?;
                if !ty_kind.is_base() {
                    bail!("expected Type, but got {ty_kind}");
                }

                self.tt_local_env.locals.push((*name, ty.clone()));
                let body_prop = self.visit_expr(expr)?;
                self.tt_local_env.locals.pop();

                let mut body = body_prop;
                body.close(*name);

                Ok(Forall {
                    name: *name,
                    ty: ty.clone(),
                    body,
                }
                .into())
            }
            Expr::Inst(e) => {
                let ExprInst {
                    expr,
                    arg,
                    predicate,
                } = &**e;

                let arg_ty = self.visit_term(arg.clone())?;
                let predicate_ty = self.visit_term(predicate.clone())?;
                self.add_type_constraint(
                    predicate_ty,
                    mk_type_arrow(arg_ty.clone(), mk_type_prop()),
                );

                let expr_prop = self.visit_expr(expr)?;

                let mut body = predicate.clone();
                body.apply([mk_var(0)]);
                let pat: Term = Forall {
                    name: Name::fresh(),
                    ty: arg_ty.clone(),
                    body,
                }
                .into();
                self.add_term_constraint(pat, expr_prop);

                let mut target = predicate.clone();
                target.apply([arg.clone()]);
                Ok(target)
            }
            Expr::Const(e) => {
                let Some((tv, target)) = self.facts.get(&e.name) else {
                    bail!("proposition not found: {}", e.name);
                };
                if tv.len() != e.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                for ty_arg in &e.ty_args {
                    let ty_arg_kind = self.visit_type(ty_arg.clone())?;
                    if !ty_arg_kind.is_base() {
                        bail!("expected Type, but got {ty_arg_kind}");
                    }
                }
                let mut target = target.clone();
                target.subst_type(
                    &std::iter::zip(tv.iter().copied(), &e.ty_args).collect::<Vec<_>>(),
                );
                Ok(target)
            }
        }
    }

    pub fn elaborate(mut self, e: &mut Expr) -> anyhow::Result<Proof> {
        self.visit_expr(e)?;

        let (mut subst, mut type_subst) =
            Unifier::new(self.tt_env, self.term_constraints, self.type_constraints)
                .solve()
                .context("unification failed")?;
        // Because subst is not topologically sorted, make it sorted by applying subst to subst in order.
        for i in 1..subst.len() {
            let (first, last) = subst.split_at_mut(i);
            let (name, m) = first.last().unwrap();
            for (_, n) in last {
                n.inst_hole(&[(*name, m)]);
            }
        }
        for i in 1..type_subst.len() {
            let (first, last) = type_subst.split_at_mut(i);
            let (name, m) = first.last().unwrap();
            for (_, n) in last {
                n.inst_hole(&[(*name, m)]);
            }
        }

        for (name, m) in subst {
            let subst = [(name, &m)];
            e.inst_hole(&subst);
        }
        e.normalize();

        for (name, ty) in type_subst {
            let subst = [(name, &ty)];
            e.inst_type_hole(&subst);
        }

        #[cfg(debug_assertions)]
        {
            println!("elaborated:\n{e}");
        }

        let h = Eval {
            facts: self.facts,
            tt_env: self.tt_env,
            tt_local_env: self.tt_local_env,
        }
        .run(e);

        Ok(h)
    }
}

#[derive(Debug)]
struct Eval<'a> {
    facts: &'a HashMap<Name, (Vec<Name>, Term)>,
    tt_env: &'a tt::Env,
    tt_local_env: &'a mut tt::LocalEnv,
}

impl<'a> Eval<'a> {
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
                let (h, p) = self.run_help(&inner.expr);
                self.tt_local_env.locals.pop();

                let h = mk_proof_forall_intro(inner.name, inner.ty.clone(), h);

                let mut body = p;
                body.close(inner.name);

                (
                    h,
                    Forall {
                        name: inner.name,
                        ty: inner.ty.clone(),
                        body,
                    }
                    .into(),
                )
            }
            Expr::Inst(inner) => {
                let (h, p) = self.run_help(&inner.expr);

                let mut arg = inner.arg.clone();
                let ty = self.tt_env.infer_type(self.tt_local_env, &mut arg).unwrap();

                let mut body = inner.predicate.clone();
                body.apply([mk_var(0)]);
                let pat: Term = Forall {
                    name: Name::fresh(),
                    ty: ty.clone(),
                    body,
                }
                .into();

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
                let (tv, mut target) = self.facts.get(&inner.name).cloned().unwrap();
                let subst: Vec<_> = std::iter::zip(tv, inner.ty_args.iter()).collect();
                target.subst_type(&subst);
                (h, target)
            }
        }
    }

    fn run(&mut self, e: &Expr) -> Proof {
        self.run_help(e).0
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
    kind: ConstraintKind,
}

#[derive(Debug, Clone)]
struct Snapshot {
    subst_len: usize,
    trail_len: usize,
    type_constraints_len: usize,
    type_subst_len: usize,
}

struct Branch<'a> {
    trail_len: usize,
    snapshot: Snapshot,
    choice: Box<dyn Iterator<Item = Vec<(Term, Term)>> + 'a>,
}

struct Unifier<'a> {
    tt_env: &'a tt::Env,
    queue_delta: VecDeque<Rc<Constraint>>,
    queue_qp: VecDeque<Rc<Constraint>>,
    queue_fr: VecDeque<Rc<Constraint>>,
    queue_ff: VecDeque<Rc<Constraint>>,
    watch_list: HashMap<Name, Vec<Rc<Constraint>>>,
    subst: Vec<(Name, Term)>,
    // this map is always sync'd to subst.
    subst_map: HashMap<Name, Term>,
    decisions: Vec<Branch<'a>>,
    // for backjumping
    trail: Vec<Rc<Constraint>>,
    // only used in find_conflict
    stack: Vec<(Term, Term)>,
    type_constraints_index: usize,
    type_constraints: Vec<(Type, Type)>,
    type_subst: Vec<(Name, Type)>,
    type_subst_map: HashMap<Name, Type>,
}

impl<'a> Unifier<'a> {
    fn new(
        tt_env: &'a tt::Env,
        constraints: Vec<(Term, Term)>,
        type_constraints: Vec<(Type, Type)>,
    ) -> Self {
        let mut solver = Self {
            tt_env,
            queue_delta: Default::default(),
            queue_qp: Default::default(),
            queue_fr: Default::default(),
            queue_ff: Default::default(),
            watch_list: Default::default(),
            subst: Default::default(),
            subst_map: Default::default(),
            decisions: Default::default(),
            trail: Default::default(),
            stack: Default::default(),
            type_constraints_index: 0,
            type_constraints,
            type_subst: vec![],
            type_subst_map: Default::default(),
        };
        for (left, right) in constraints.into_iter().rev() {
            solver.stack.push((left, right));
        }
        solver
    }

    #[cfg(debug_assertions)]
    fn print_state(&self) {
        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
        println!("{sp}+current state");
        if !self.stack.is_empty() {
            println!("{sp}| stack:");
            for (left, right) in &self.stack {
                println!("{sp}| - {}\n{sp}|   {}", left, right);
            }
            println!();
        }
        if !self.queue_delta.is_empty() {
            println!("{sp}| delta ({}):", self.queue_delta.len());
            for c in &self.queue_delta {
                println!("{sp}| - {}\n{sp}|   {}", c.left, c.right);
            }
            println!();
        }
        if !self.queue_qp.is_empty() {
            println!("{sp}| qp:");
            for c in &self.queue_qp {
                println!("{sp}| - {}\n{sp}|   {}", c.left, c.right);
            }
            println!();
        }
        if !self.queue_fr.is_empty() {
            println!("{sp}| fr:");
            for c in &self.queue_fr {
                println!("{sp}| - {}\n{sp}|   {}", c.left, c.right);
            }
            println!();
        }
        if !self.queue_ff.is_empty() {
            println!("{sp}| qp:");
            for c in &self.queue_ff {
                println!("{sp}| - {}\n{sp}|   {}", c.left, c.right);
            }
            println!();
        }
        println!();
    }

    fn watch(&mut self, c: Rc<Constraint>) {
        if c.kind != ConstraintKind::Delta {
            if let &Term::Hole(left_head) = c.left.head() {
                match self.watch_list.get_mut(&left_head) {
                    Some(watch_list) => {
                        watch_list.push(c.clone());
                    }
                    None => {
                        self.watch_list.insert(left_head, vec![c.clone()]);
                    }
                }
            }
            if let &Term::Hole(right_head) = c.right.head() {
                match self.watch_list.get_mut(&right_head) {
                    Some(watch_list) => {
                        watch_list.push(c);
                    }
                    None => {
                        self.watch_list.insert(right_head, vec![c]);
                    }
                }
            }
        }
    }

    fn unwatch(&mut self, c: &Rc<Constraint>) {
        if c.kind != ConstraintKind::Delta {
            if let &Term::Hole(left_head) = c.left.head() {
                let watch_list = self.watch_list.get_mut(&left_head).unwrap();
                let mut index = 0;
                for i in (0..watch_list.len()).rev() {
                    if Rc::ptr_eq(&watch_list[i], c) {
                        index = i;
                        break;
                    }
                }
                watch_list.swap_remove(index);
            }
            if let &Term::Hole(right_head) = c.right.head() {
                let watch_list = self.watch_list.get_mut(&right_head).unwrap();
                let mut index = 0;
                for i in (0..watch_list.len()).rev() {
                    if Rc::ptr_eq(&watch_list[i], c) {
                        index = i;
                        break;
                    }
                }
                watch_list.swap_remove(index);
            }
        }
    }

    // Note that the result term may contain redex in head
    fn inst_head(&self, m: &mut Term) -> bool {
        if let &Term::Hole(m_head) = m.head() {
            if let Some(a) = self.subst_map.get(&m_head) {
                let subst = [(m_head, a)];
                m.head_mut().inst_hole(&subst);
                return true;
            }
        }
        false
    }

    fn inst_arg_heads(&self, m: &mut Term) {
        for arg in &mut m.args_mut() {
            arg.whnf();
            while self.inst_head(arg) {
                if arg.whnf().is_none() {
                    break;
                }
            }
        }
    }

    fn inst(&self, m: &mut Term, occur_check: Name) -> bool {
        match m {
            Term::Var(_) => true,
            Term::Abs(m) => {
                let TermAbs {
                    binder_type: _,
                    binder_name: _,
                    body,
                } = Arc::make_mut(m);
                self.inst(body, occur_check)
            }
            Term::App(m) => {
                let TermApp { fun, arg } = Arc::make_mut(m);
                self.inst(fun, occur_check) && self.inst(arg, occur_check)
            }
            Term::Local(_) => true,
            Term::Const(_) => true,
            Term::Hole(name) => {
                if *name == occur_check {
                    return false;
                }
                let Some(a) = self.subst_map.get(name).cloned() else {
                    return true;
                };
                *m = a;
                self.inst(m, occur_check)
            }
        }
    }

    fn is_fully_inst(&self, m: &Term) -> bool {
        match m {
            Term::Var(_) => true,
            Term::Abs(m) => self.is_fully_inst(&m.body),
            Term::App(m) => self.is_fully_inst(&m.fun) && self.is_fully_inst(&m.arg),
            Term::Local(_) => true,
            Term::Const(_) => true,
            Term::Hole(name) => !self.subst_map.contains_key(name),
        }
    }

    fn add_derived_constraint(&mut self, mut left: Term, mut right: Term, is_delta: bool) {
        let kind;
        if is_delta {
            kind = ConstraintKind::Delta;
        } else {
            self.inst_arg_heads(&mut left);
            self.inst_arg_heads(&mut right);
            if left.is_quasi_pattern() {
                kind = ConstraintKind::QuasiPattern;
            } else if right.is_quasi_pattern() {
                mem::swap(&mut left, &mut right);
                kind = ConstraintKind::QuasiPattern;
            } else if left.head().is_hole() && right.head().is_hole() {
                kind = ConstraintKind::FlexFlex;
            } else if left.head().is_hole() {
                kind = ConstraintKind::FlexRigid;
            } else {
                mem::swap(&mut left, &mut right);
                kind = ConstraintKind::FlexRigid;
            }
        }

        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!(
                "{sp}new constraint ({kind:#?}):\n{sp}- {}\n{sp}  {}",
                left, right
            );
        }

        let c = Rc::new(Constraint {
            left: left.clone(),
            right: right.clone(),
            kind,
        });

        self.trail.push(c.clone());

        assert!(!self.is_resolved_constraint(&c));

        match kind {
            ConstraintKind::Delta => {
                self.queue_delta.push_back(c.clone());
            }
            ConstraintKind::QuasiPattern => {
                self.queue_qp.push_back(c.clone());
            }
            ConstraintKind::FlexRigid => {
                self.queue_fr.push_back(c.clone());
            }
            ConstraintKind::FlexFlex => {
                self.queue_ff.push_back(c.clone());
            }
        }

        self.watch(c);
    }

    fn add_subst(&mut self, name: Name, m: Term) {
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}new subst {name} := {m}");
        }

        self.subst.push((name, m.clone()));
        self.subst_map.insert(name, m);
    }

    fn add_type_constraint(&mut self, t1: Type, t2: Type) {
        self.type_constraints.push((t1, t2));
    }

    fn add_type_subst(&mut self, name: Name, ty: Type) {
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}new type subst {name} := {ty}");
        }

        self.type_subst.push((name, ty.clone()));
        self.type_subst_map.insert(name, ty);
    }

    fn inst_type_head(&mut self, ty: Type) -> Type {
        let Type::Hole(name) = ty else {
            return ty;
        };
        let Some(ty) = self.type_subst_map.get(&name).cloned() else {
            return ty;
        };
        self.inst_type_head(ty)
    }

    fn find_conflict_in_types(&mut self, t1: Type, t2: Type) -> Option<()> {
        let t1 = self.inst_type_head(t1);
        let t2 = self.inst_type_head(t2);
        if t1 == t2 {
            return None;
        }
        match (t1, t2) {
            (Type::Arrow(inner1), Type::Arrow(inner2)) => {
                let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                self.add_type_constraint(inner1.dom, inner2.dom);
                self.add_type_constraint(inner1.cod, inner2.cod);
            }
            (Type::App(inner1), Type::App(inner2)) => {
                // Since we have no higher-kinded polymorphism, holes will only be typed as `Type`,
                // it is illegal to match the following two types:
                //  ?M₁ t =?= ?M₂ t₁ t₂
                // But such a case is checked and ruled out in the kind checking phase that runs before
                // this unificaiton phase.
                let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                self.add_type_constraint(inner1.fun, inner2.fun);
                self.add_type_constraint(inner1.arg, inner2.arg);
            }
            (Type::Hole(name), t) | (t, Type::Hole(name)) => {
                self.add_type_subst(name, t);
            }
            (_, _) => {
                return Some(());
            }
        }
        None
    }

    fn find_conflict_in_terms(&mut self, mut left: Term, mut right: Term) -> Option<()> {
        if left == right {
            return None;
        }
        if let (Term::Abs(l), Term::Abs(r)) = (&mut left, &mut right) {
            let x = Name::fresh();
            Arc::make_mut(l).body.open(&mk_local(x));
            Arc::make_mut(r).body.open(&mk_local(x));
            // TODO: I think this line is not necessary...
            self.add_type_constraint(l.binder_type.clone(), r.binder_type.clone());
            let left = mem::take(&mut Arc::make_mut(l).body);
            let right = mem::take(&mut Arc::make_mut(r).body);
            self.stack.push((left, right));
            return None;
        }
        if left.whnf().is_some() || right.whnf().is_some() {
            self.stack.push((left, right));
            return None;
        }
        if left.is_abs() {
            mem::swap(&mut left, &mut right);
        }
        if right.is_abs() {
            // L ≡ (?M t₁ ⋯ tₙ)
            if left.head().is_hole() {
                // this case is handled later.
            } else if self.tt_env.unfold_head(&mut left).is_some() {
                self.stack.push((left, right));
                return None;
            } else {
                return Some(());
            }
        }
        if self.inst_head(&mut left) || self.inst_head(&mut right) {
            self.stack.push((left, right));
            return None;
        }
        // then each of the heads can be a local, a const, or a hole
        if let Term::Hole(right_head) = right.head() {
            let right_head = *right_head;
            self.inst_arg_heads(&mut right);
            if let Some(args) = right.is_pattern() {
                // TODO: avoid full instantiation
                if self.inst(&mut left, right_head) {
                    let args = args
                        .into_iter()
                        // TODO determine types from local_env
                        .map(|n| (n, n, mk_fresh_type_hole()))
                        .collect::<Vec<_>>();
                    if left.abs(&args, false) {
                        self.add_subst(right_head, left.clone());
                        if let Some(constraints) = self.watch_list.get(&right_head) {
                            for c in constraints.iter().rev() {
                                if c.left.head() == &Term::Hole(right_head) {
                                    if let Term::Hole(right_head) = c.right.head() {
                                        if self.subst_map.contains_key(right_head) {
                                            continue;
                                        }
                                    }
                                } else if let Term::Hole(left_head) = c.left.head() {
                                    if self.subst_map.contains_key(left_head) {
                                        continue;
                                    }
                                }
                                let mut c = (**c).clone();
                                let subst = [(right_head, &left)];
                                c.left.inst_hole(&subst);
                                c.right.inst_hole(&subst);
                                self.stack.push((c.left, c.right));
                            }
                        }
                        return None;
                    }
                }
            }
        }
        if let Term::Hole(left_head) = left.head() {
            let left_head = *left_head;
            self.inst_arg_heads(&mut left);
            if let Some(args) = left.is_pattern() {
                if self.inst(&mut right, left_head) {
                    let args = args
                        .into_iter()
                        // TODO determine types from local_env
                        .map(|n| (n, n, mk_fresh_type_hole()))
                        .collect::<Vec<_>>();
                    if right.abs(&args, false) {
                        self.add_subst(left_head, right.clone());
                        if let Some(constraints) = self.watch_list.get(&left_head) {
                            for c in constraints.iter().rev() {
                                if c.left.head() == &Term::Hole(left_head) {
                                    if let Term::Hole(right_head) = c.right.head() {
                                        if self.subst_map.contains_key(right_head) {
                                            continue;
                                        }
                                    }
                                } else if let Term::Hole(left_head) = c.left.head() {
                                    if self.subst_map.contains_key(left_head) {
                                        continue;
                                    }
                                }
                                let mut c = (**c).clone();
                                let subst = [(left_head, &right)];
                                c.left.inst_hole(&subst);
                                c.right.inst_hole(&subst);
                                self.stack.push((c.left, c.right));
                            }
                        }
                        return None;
                    }
                }
            }
        }
        if right.head().is_hole() || left.head().is_hole() {
            self.add_derived_constraint(left, right, false);
            return None;
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
                            self.stack.push((left, right));
                            return None;
                        }
                        std::cmp::Ordering::Less => {
                            self.tt_env.unfold_head(&mut right).unwrap();
                            self.stack.push((left, right));
                            return None;
                        }
                        std::cmp::Ordering::Equal => {
                            if left_hint == 0 {
                                // (f t₁ ⋯ tₙ) ≈ (g s₁ ⋯ sₘ) where f and g are both irreducible.
                                return Some(());
                            }
                            self.tt_env.unfold_head(&mut left).unwrap();
                            self.tt_env.unfold_head(&mut right).unwrap();
                            self.stack.push((left, right));
                            return None;
                        }
                    }
                }
                // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ)
                for (t1, t2) in left_head.ty_args.iter().zip(right_head.ty_args.iter()) {
                    self.add_type_constraint(t1.clone(), t2.clone());
                }
                if self.tt_env.def_hint(left_head.name).is_none() {
                    let left_args = left.unapply();
                    let right_args = right.unapply();
                    if left_args.len() != right_args.len() {
                        return Some(());
                    }
                    for (left_arg, right_arg) in
                        left_args.into_iter().zip(right_args.into_iter()).rev()
                    {
                        self.stack.push((left_arg, right_arg));
                    }
                    return None;
                }
                // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ) where any of t or s contains a hole.
                self.add_derived_constraint(left, right, true);
                return None;
            }
            (Term::Const(left_head), Term::Local(right_head)) => {
                // yuichi: perhaps we can simply give up on this case, when completeness is not important.
                if self.tt_env.def_hint(left_head.name).is_none() {
                    return Some(());
                }
                left.close(*right_head);
                if left.is_lclosed() {
                    return Some(());
                }
                left.open(&mk_local(*right_head));
                self.tt_env.unfold_head(&mut left).unwrap();
                self.stack.push((left, right));
                return None;
            }
            (Term::Local(left_head), Term::Local(right_head)) => {
                if left_head != right_head {
                    return Some(());
                }
                let left_args = left.unapply();
                let right_args = right.unapply();
                if left_args.len() != right_args.len() {
                    return Some(());
                }
                for (left_arg, right_arg) in left_args.into_iter().zip(right_args.into_iter()).rev()
                {
                    self.stack.push((left_arg, right_arg));
                }
                return None;
            }
            _ => unreachable!(),
        }
    }

    fn find_conflict(&mut self) -> Option<()> {
        #[cfg(debug_assertions)]
        {
            self.print_state();
        }
        while !self.type_constraints.is_empty() || !self.stack.is_empty() {
            if let Some((t1, t2)) = self.type_constraints.pop() {
                if self.find_conflict_in_types(t1, t2).is_some() {
                    return Some(());
                }
            }
            if let Some((m1, m2)) = self.stack.pop() {
                if self.find_conflict_in_terms(m1, m2).is_some() {
                    return Some(());
                }
            }
        }
        None
    }

    fn save(&self) -> Snapshot {
        Snapshot {
            subst_len: self.subst.len(),
            trail_len: self.trail.len(),
            type_constraints_len: self.type_constraints.len(),
            type_subst_len: self.type_subst.len(),
        }
    }

    fn restore(&mut self, snapshot: &Snapshot) {
        for i in snapshot.subst_len..self.subst.len() {
            let name = self.subst[i].0;
            self.subst_map.remove(&name);
        }
        self.subst.truncate(snapshot.subst_len);
        for i in 0..self.trail.len() - snapshot.trail_len {
            let i = self.trail.len() - i - 1;
            let c = &self.trail[i];
            match c.kind {
                ConstraintKind::Delta => {
                    self.queue_delta.pop_back();
                }
                ConstraintKind::QuasiPattern => {
                    self.queue_qp.pop_back();
                }
                ConstraintKind::FlexRigid => {
                    self.queue_fr.pop_back();
                }
                ConstraintKind::FlexFlex => {
                    self.queue_ff.pop_back();
                }
            }
            self.unwatch(&c.clone());
        }
        self.trail.truncate(snapshot.trail_len);
        for i in snapshot.type_subst_len..self.type_subst.len() {
            let name = self.type_subst[i].0;
            self.type_subst_map.remove(&name);
        }
        self.type_subst.truncate(snapshot.type_subst_len);
        self.type_constraints
            .truncate(snapshot.type_constraints_len);
        self.type_constraints_index = snapshot.type_constraints_len;
    }

    fn push_branch(
        &mut self,
        trail_len: usize,
        choice: Box<dyn Iterator<Item = Vec<(Term, Term)>> + 'a>,
    ) {
        let snapshot = self.save();
        self.decisions.push(Branch {
            trail_len,
            snapshot,
            choice,
        });
    }

    fn pop_branch(&mut self) -> bool {
        let Some(br) = self.decisions.pop() else {
            return false;
        };
        self.restore(&br.snapshot);
        for _ in 0..self.trail.len() - br.trail_len {
            let c = self.trail.pop().unwrap();
            assert_eq!(c.kind, ConstraintKind::Delta);
            self.queue_delta.push_front(c);
        }
        true
    }

    fn next(&mut self) -> bool {
        let Some(br) = self.decisions.last_mut() else {
            return false;
        };
        let Some(constraints) = br.choice.next() else {
            return false;
        };
        let snapshot = br.snapshot.clone();
        self.restore(&snapshot);
        for (left, right) in constraints.into_iter().rev() {
            self.stack.push((left, right));
        }
        true
    }

    fn choice_delta(&self, c: &Constraint) -> Vec<Vec<(Term, Term)>> {
        // suppose (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₙ)
        let left_args = c.left.args();
        let right_args = c.right.args();
        // Try first (t₁ ≈ s₁) ∧ ⋯ ∧ (tₙ ≈ sₙ)
        let mut a1 = vec![];
        for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
            a1.push((left_arg.clone(), right_arg.clone()));
        }
        // Try second ((unfold f) t₁ ⋯ tₙ ≈ (unfold f) s₁ ⋯ sₙ)
        let mut a2 = vec![];
        {
            let mut left = c.left.clone();
            let mut right = c.right.clone();
            self.tt_env.unfold_head(&mut left).unwrap();
            self.tt_env.unfold_head(&mut right).unwrap();
            a2.push((left, right));
        }
        vec![a1, a2]
    }

    fn choice_fr(&self, c: &Constraint) -> Vec<Vec<(Term, Term)>> {
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
                    (name, name, mk_fresh_type_hole())
                })
                .chain(right_binders.iter().cloned())
                .collect::<Vec<_>>();

            // (Y[1] z[1] .. z[p] x[1] .. x[m]) .. (Y[q] z[1] .. z[p] x[1] .. x[m])
            let new_args = (0..right_args.len())
                .map(|_| {
                    let mut arg = mk_fresh_hole();
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
                choice.push(vec![(left_head.clone(), cand)]);
            }

            // imitation
            match right_head {
                Term::Const(_) => {
                    let mut cand = right_head.clone();
                    cand.apply(new_args.clone());
                    cand.abs(&new_binders, true);
                    choice.push(vec![(left_head.clone(), cand)]);
                }
                Term::Local(name) => {
                    // @ ∈ { x[1], .., x[m] }
                    if right_binders.iter().any(|(x, _, _)| x == name) {
                        let mut cand = right_head.clone();
                        cand.apply(new_args.clone());
                        cand.abs(&new_binders, true);
                        choice.push(vec![(left_head.clone(), cand)]);
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
                        (name, name, mk_fresh_type_hole())
                    })
                    .collect::<Vec<_>>();

                // (Y[1] z[1] .. z[p-k]) .. (Y[q-k] z[1] .. z[p-k])
                let new_args = (0..right_args.len() - k)
                    .map(|_| {
                        let mut arg = mk_fresh_hole();
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
                    choice.push(vec![(left_head.clone(), cand)]);
                }

                // imitation
                match right_head {
                    Term::Const(_) => {
                        let mut cand = right_head.clone();
                        cand.apply(new_args.clone());
                        cand.abs(&new_binders, true);
                        choice.push(vec![(left_head.clone(), cand)]);
                    }
                    Term::Local(_) => {}
                    _ => unreachable!(),
                };
            }
        }
        choice
    }

    fn is_resolved_constraint(&self, c: &Constraint) -> bool {
        if let &Term::Hole(right_head) = c.right.head() {
            if self.subst_map.contains_key(&right_head) {
                return true;
            }
        }
        if let &Term::Hole(left_head) = c.left.head() {
            if self.subst_map.contains_key(&left_head) {
                return true;
            }
        }
        false
    }

    // Returns false if the constraints are pre-unified.
    fn decide(&mut self) -> bool {
        let trail_len = self.trail.len();
        let c = 'next: {
            if let Some(c) = self.queue_delta.pop_front() {
                self.trail.push(c.clone());
                break 'next c;
            }
            for c in &self.queue_qp {
                if !self.is_resolved_constraint(c) {
                    break 'next c.clone();
                }
            }
            for c in &self.queue_fr {
                if !self.is_resolved_constraint(c) {
                    break 'next c.clone();
                }
            }
            return false;
        };
        let choice = match c.kind {
            ConstraintKind::Delta => self.choice_delta(&c),
            ConstraintKind::QuasiPattern => self.choice_fr(&c),
            ConstraintKind::FlexRigid => self.choice_fr(&c),
            ConstraintKind::FlexFlex => unreachable!(),
        };

        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!(
                "{sp}decision is made for ({:?}):\n{sp}- {}\n{sp}  {}",
                c.kind, c.left, c.right
            );
        }

        self.push_branch(trail_len, Box::new(choice.into_iter()));
        self.next();
        true
    }

    fn backjump(&mut self) -> bool {
        self.stack.clear();
        while !self.next() {
            if !self.pop_branch() {
                return false;
            }
        }
        true
    }

    fn solve(mut self) -> Option<(Vec<(Name, Term)>, Vec<(Name, Type)>)> {
        loop {
            while let Some(()) = self.find_conflict() {
                #[cfg(debug_assertions)]
                {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}conflict found!");
                }
                if !self.backjump() {
                    return None;
                }
            }
            if !self.decide() {
                return Some((self.subst, self.type_subst));
            }
        }
    }
}
