use std::{
    collections::{HashMap, VecDeque},
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
        self, mk_fresh_mvar, mk_fresh_type_mvar, mk_local, mk_type_arrow, mk_var, Kind, Name, Term,
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
    fn inst_type_mvar(&mut self, subst: &[(Name, &Type)]) {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = Arc::make_mut(e);
                target.inst_type_mvar(subst)
            }
            Expr::Assume(e) => {
                let ExprAssume { target, expr } = Arc::make_mut(e);
                target.inst_type_mvar(subst);
                expr.inst_type_mvar(subst);
            }
            Expr::App(e) => {
                let ExprApp {
                    expr1,
                    expr2,
                    target,
                } = Arc::make_mut(e);
                expr1.inst_type_mvar(subst);
                expr2.inst_type_mvar(subst);
                target.inst_type_mvar(subst);
            }
            Expr::Take(e) => {
                let ExprTake { name: _, ty, expr } = Arc::make_mut(e);
                ty.inst_mvar(subst);
                expr.inst_type_mvar(subst);
            }
            Expr::Inst(e) => {
                let ExprInst {
                    expr,
                    arg,
                    predicate,
                } = Arc::make_mut(e);
                expr.inst_type_mvar(subst);
                arg.inst_type_mvar(subst);
                predicate.inst_type_mvar(subst);
            }
            Expr::Const(e) => {
                let ExprConst { name: _, ty_args } = Arc::make_mut(e);
                for ty_arg in ty_args {
                    ty_arg.inst_mvar(subst);
                }
            }
        }
    }

    fn inst_mvar(&mut self, subst: &[(Name, &Term)]) {
        match self {
            Expr::Assump(e) => {
                let ExprAssump { target } = Arc::make_mut(e);
                target.inst_mvar(subst)
            }
            Expr::Assume(e) => {
                let ExprAssume { target, expr } = Arc::make_mut(e);
                target.inst_mvar(subst);
                expr.inst_mvar(subst);
            }
            Expr::App(e) => {
                let ExprApp {
                    expr1,
                    expr2,
                    target,
                } = Arc::make_mut(e);
                expr1.inst_mvar(subst);
                expr2.inst_mvar(subst);
                target.inst_mvar(subst);
            }
            Expr::Take(e) => {
                let ExprTake { name: _, ty, expr } = Arc::make_mut(e);
                expr.inst_mvar(subst);
            }
            Expr::Inst(e) => {
                let ExprInst {
                    expr,
                    arg,
                    predicate,
                } = Arc::make_mut(e);
                expr.inst_mvar(subst);
                arg.inst_mvar(subst);
                predicate.inst_mvar(subst);
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
            Type::Mvar(_) => Ok(Kind::base()),
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
            Term::Mvar(m) => {
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
                let ret_ty = mk_fresh_type_mvar();

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

        let type_subst = TypeUnifier::new(self.type_constraints).solve()?;

        // we defer type instantiation because our unifier does not touch types.
        let mut subst = Unifier::new(self.tt_env, self.term_constraints)
            .solve()
            .context("unification failed")?;
        // Because subst is not topologically sorted, make it sorted by applying subst to subst in order.
        for i in 1..subst.len() {
            let (first, last) = subst.split_at_mut(i);
            let (name, m) = first.last().unwrap();
            for (_, n) in last {
                n.inst_mvar(&[(*name, m)]);
            }
        }
        for (name, m) in subst {
            let subst = [(name, &m)];
            e.inst_mvar(&subst);
        }
        e.normalize();

        for (name, ty) in type_subst {
            let subst = [(name, &ty)];
            e.inst_type_mvar(&subst);
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

#[derive(Clone, Debug, Default)]
struct TypeUnifier {
    constraints: Vec<(Type, Type)>,
    subst: Vec<(Name, Type)>,
    subst_map: HashMap<Name, Type>,
}

impl TypeUnifier {
    fn new(constraints: Vec<(Type, Type)>) -> Self {
        TypeUnifier {
            constraints,
            subst: vec![],
            subst_map: Default::default(),
        }
    }

    fn add_constraint(&mut self, t1: Type, t2: Type) {
        self.constraints.push((t1, t2));
    }

    fn add_subst(&mut self, name: Name, ty: Type) {
        self.subst.push((name, ty.clone()));
        self.subst_map.insert(name, ty);
    }

    fn find(&mut self, ty: Type) -> Type {
        let Type::Mvar(name) = ty else {
            return ty;
        };
        let Some(ty) = self.subst_map.get(&name).cloned() else {
            return ty;
        };
        // During calling `find` parents[name] will NOT be updated
        // because a unification solution is not cyclic.
        let ty = self.find(ty);
        self.subst_map.insert(name, ty.clone());
        ty
    }

    fn solve(mut self) -> anyhow::Result<Vec<(Name, Type)>> {
        while let Some((t1, t2)) = self.constraints.pop() {
            let t1 = self.find(t1);
            let t2 = self.find(t2);
            if t1 == t2 {
                continue;
            }
            match (t1, t2) {
                (Type::Arrow(inner1), Type::Arrow(inner2)) => {
                    let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                    let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                    self.add_constraint(inner1.dom, inner2.dom);
                    self.add_constraint(inner1.cod, inner2.cod);
                }
                (Type::App(inner1), Type::App(inner2)) => {
                    // Since we have no higher-kinded polymorphism, mvars will only be typed as `Type`,
                    // it is illegal to match the following two types:
                    //  ?M₁ t =?= ?M₂ t₁ t₂
                    // But such a case is checked and ruled out in the kind checking phase that runs before
                    // this unificaiton phase.
                    let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                    let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                    self.add_constraint(inner1.fun, inner2.fun);
                    self.add_constraint(inner1.arg, inner2.arg);
                }
                (Type::Mvar(name), t) | (t, Type::Mvar(name)) => {
                    self.add_subst(name, t);
                }
                (t1, t2) => {
                    bail!("type mismatch: {t1} =/= {t2}");
                }
            }
        }
        Ok(self.subst)
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
}

struct Branch<'a> {
    snapshot: Snapshot,
    constraint: Rc<Constraint>,
    choice: Box<dyn Iterator<Item = Vec<(Term, Term)>> + 'a>,
}

struct Unifier<'a> {
    tt_env: &'a tt::Env,
    queue_delta: VecDeque<Rc<Constraint>>,
    queue_qpat: VecDeque<Rc<Constraint>>,
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
            decisions: Default::default(),
            trail: Default::default(),
            stack: Default::default(),
        };
        for (left, right) in constraints.into_iter().rev() {
            solver.stack.push((left, right));
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

    fn add_derived_constraint(&mut self, mut left: Term, mut right: Term, is_delta: bool) {
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
            kind,
        });

        self.trail.push(c.clone());

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

    fn find_conflict(&mut self) -> Option<()> {
        while let Some((mut left, mut right)) = self.stack.pop() {
            if left.untyped_eq(&right) {
                continue;
            }
            if let (Term::Abs(l), Term::Abs(r)) = (&mut left, &mut right) {
                let x = Name::fresh();
                Arc::make_mut(l).body.open(&mk_local(x));
                Arc::make_mut(r).body.open(&mk_local(x));
                let left = mem::take(&mut Arc::make_mut(l).body);
                let right = mem::take(&mut Arc::make_mut(r).body);
                self.stack.push((left, right));
                continue;
            }
            if left.whnf().is_some() || right.whnf().is_some() {
                self.stack.push((left, right));
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
                    self.stack.push((left, right));
                    continue;
                } else {
                    return Some(());
                }
            }
            if self.inst_head(&mut left, &mut right) {
                self.stack.push((left, right));
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
                                self.stack.push((c.left, c.right));
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
                                self.stack.push((c.left, c.right));
                            }
                        }
                        continue;
                    }
                }
            }
            if right.head().is_mvar() || left.head().is_mvar() {
                self.add_derived_constraint(left, right, false);
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
                                self.stack.push((left, right));
                                continue;
                            }
                            std::cmp::Ordering::Less => {
                                self.tt_env.unfold_head(&mut right).unwrap();
                                self.stack.push((left, right));
                                continue;
                            }
                            std::cmp::Ordering::Equal => {
                                if left_hint == 0 {
                                    // (f t₁ ⋯ tₙ) ≈ (g s₁ ⋯ sₘ) where f and g are both irreducible.
                                    return Some(());
                                }
                                self.tt_env.unfold_head(&mut left).unwrap();
                                self.tt_env.unfold_head(&mut right).unwrap();
                                self.stack.push((left, right));
                                continue;
                            }
                        }
                    }
                    // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ)
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
                        continue;
                    }
                    // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ) where any of t or s contains an mvar.
                    self.add_derived_constraint(left, right, true);
                    continue;
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
                    continue;
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
                    for (left_arg, right_arg) in
                        left_args.into_iter().zip(right_args.into_iter()).rev()
                    {
                        self.stack.push((left_arg, right_arg));
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
            trail_len: self.trail.len(),
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
        self.trail.truncate(snapshot.trail_len);
    }

    fn push_branch(
        &mut self,
        snapshot: Snapshot,
        c: Rc<Constraint>,
        choice: Box<dyn Iterator<Item = Vec<(Term, Term)>> + 'a>,
    ) {
        self.decisions.push(Branch {
            snapshot,
            constraint: c,
            choice,
        });
    }

    fn pop_branch(&mut self) -> bool {
        let Some(br) = self.decisions.pop() else {
            return false;
        };
        if br.constraint.kind == ConstraintKind::Delta {
            self.queue_delta.push_front(br.constraint);
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
        self.stack.clear();
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

    fn backjump(&mut self) -> bool {
        while !self.next() {
            if !self.pop_branch() {
                return false;
            }
        }
        true
    }

    fn solve(mut self) -> Option<Vec<(Name, Term)>> {
        loop {
            while let Some(()) = self.find_conflict() {
                if !self.backjump() {
                    return None;
                }
            }
            if !self.decide() {
                return Some(self.subst);
            }
        }
    }
}
