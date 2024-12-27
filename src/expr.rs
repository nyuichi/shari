use std::{
    collections::{HashMap, VecDeque},
    iter::{repeat_n, zip},
    mem,
    rc::Rc,
    sync::Arc,
};

use anyhow::{bail, Context};

use crate::{
    cmd::{CmdStructure, StructureField},
    tt::{
        self, mk_const, mk_fresh_type_hole, mk_local, mk_type_arrow, Kind, Name, Term, TermAbs,
        TermApp, Type, TypeApp, TypeArrow,
    },
};
use crate::{
    proof::{
        mk_proof_assump, mk_proof_conv, mk_proof_forall_elim, mk_proof_forall_intro,
        mk_proof_imp_elim, mk_proof_imp_intro, mk_proof_ref, mk_type_prop, Forall, Imp, Proof,
    },
    tt::LocalEnv,
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
    structure_table: &'a HashMap<Name, CmdStructure>,
    // Proved or postulated facts
    axioms: &'a HashMap<Name, (Vec<Name>, Term)>,
    locals: Vec<Term>,
    type_constraints: Vec<(Type, Type)>,
    term_constraints: Vec<(LocalEnv, Term, Term)>,
}

impl<'a> Env<'a> {
    pub fn new(
        tt_env: &'a tt::Env,
        tt_local_env: &'a mut tt::LocalEnv,
        axioms: &'a HashMap<Name, (Vec<Name>, Term)>,
        structure_table: &'a HashMap<Name, CmdStructure>,
    ) -> Self {
        Env {
            tt_env,
            tt_local_env,
            structure_table,
            axioms,
            locals: vec![],
            type_constraints: vec![],
            term_constraints: vec![],
        }
    }

    fn add_type_constraint(&mut self, t1: Type, t2: Type) {
        self.type_constraints.push((t1, t2));
    }

    fn add_term_constraint(&mut self, local_env: LocalEnv, m1: Term, m2: Term) {
        self.term_constraints.push((local_env, m1, m2));
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
                    binder_name,
                    mut body,
                } = Arc::unwrap_or_clone(m);

                let arg_ty_kind = self.visit_type(arg_ty.clone())?;
                if !arg_ty_kind.is_base() {
                    bail!("expected Type, but got {arg_ty_kind}");
                }

                let x = Name::fresh_from(binder_name);
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
                self.add_term_constraint(self.tt_local_env.clone(), pat, fun_prop);

                Ok(target.clone())
            }
            Expr::Take(e) => {
                let ExprTake { name, ty, expr } = &**e;

                let ty_kind = self.visit_type(ty.clone())?;
                if !ty_kind.is_base() {
                    bail!("expected Type, but got {ty_kind}");
                }

                self.tt_local_env.locals.push((*name, ty.clone()));
                let mut target = self.visit_expr(expr)?;
                self.tt_local_env.locals.pop();

                target.generalize(&[(*name, ty.clone())]);

                Ok(target)
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

                let mut pat = predicate.clone();
                let tmp = Name::fresh();
                pat.apply([mk_local(tmp)]);
                pat.generalize(&[(tmp, arg_ty.clone())]);
                self.add_term_constraint(self.tt_local_env.clone(), pat, expr_prop);

                let mut target = predicate.clone();
                target.apply([arg.clone()]);
                Ok(target)
            }
            Expr::Const(e) => {
                let Some((tv, target)) = self.axioms.get(&e.name) else {
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
        #[cfg(debug_assertions)]
        {
            println!("elaborating:\n{e}");
        }

        self.visit_expr(e)?;

        let (mut subst, mut type_subst) = Unifier::new(
            self.tt_env,
            self.structure_table,
            self.tt_local_env.holes.clone(),
            self.term_constraints,
            self.type_constraints,
        )
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
            axioms: self.axioms,
            tt_env: self.tt_env,
            tt_local_env: self.tt_local_env,
        }
        .run(e);

        Ok(h)
    }
}

#[derive(Debug)]
struct Eval<'a> {
    axioms: &'a HashMap<Name, (Vec<Name>, Term)>,
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
    // TODO: only the locals field is used. Use a more efficient data structure.
    local_env: LocalEnv,
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

#[derive(Debug, Default)]
struct Node {
    type_constraints: Vec<(Type, Type)>,
    term_constraints: Vec<(LocalEnv, Term, Term)>,
}

struct Branch<'a> {
    trail_len: usize,
    snapshot: Snapshot,
    nodes: Box<dyn Iterator<Item = Node> + 'a>,
}

struct Unifier<'a> {
    tt_env: &'a tt::Env,
    structure_table: &'a HashMap<Name, CmdStructure>,
    term_holes: Vec<(Name, Type)>,
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
    stack: Vec<(LocalEnv, Term, Term)>,
    type_constraints_index: usize,
    type_constraints: Vec<(Type, Type)>,
    type_subst: Vec<(Name, Type)>,
    type_subst_map: HashMap<Name, Type>,
}

impl<'a> Unifier<'a> {
    fn new(
        tt_env: &'a tt::Env,
        structure_table: &'a HashMap<Name, CmdStructure>,
        term_holes: Vec<(Name, Type)>,
        constraints: Vec<(LocalEnv, Term, Term)>,
        type_constraints: Vec<(Type, Type)>,
    ) -> Self {
        let mut solver = Self {
            tt_env,
            structure_table,
            term_holes,
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
        for (local_env, left, right) in constraints.into_iter().rev() {
            solver.stack.push((local_env, left, right));
        }
        solver
    }

    #[cfg(debug_assertions)]
    fn print_state(&self) {
        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
        println!("{sp}+current state");
        if !self.stack.is_empty() {
            println!("{sp}| stack:");
            for (_, left, right) in &self.stack {
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

    // Note that the result term may contain redex in head
    fn inst_stuck(&self, m: &mut Term) -> bool {
        if self.inst_head(m) {
            return true;
        }
        let Term::Const(m_head) = m.head() else {
            return false;
        };
        if self.tt_env.get_proj_rules(m_head.name).is_none() {
            return false;
        };
        let mut args = m.args_mut();
        if args.is_empty() {
            return false;
        }
        self.inst_stuck(&mut *args[0])
    }

    fn unfold_stuck(&self, m: &mut Term) -> bool {
        if self.tt_env.unfold_head(m).is_some() {
            return true;
        }
        let Term::Const(m_head) = m.head() else {
            return false;
        };
        if self.tt_env.get_proj_rules(m_head.name).is_none() {
            return false;
        };
        let mut args = m.args_mut();
        if args.is_empty() {
            return false;
        }
        self.unfold_stuck(&mut *args[0])
    }

    fn inst_arg_stuck(&self, m: &mut Term) {
        for arg in &mut m.args_mut() {
            self.tt_env.weak_reduce(arg);
            while self.inst_stuck(arg) {
                if self.tt_env.weak_reduce(arg).is_none() {
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

    fn inst_type(&self, t: &mut Type) {
        match t {
            Type::Const(_) => {}
            Type::Arrow(t) => {
                let TypeArrow { dom, cod } = Arc::make_mut(t);
                self.inst_type(dom);
                self.inst_type(cod);
            }
            Type::App(t) => {
                let TypeApp { fun, arg } = Arc::make_mut(t);
                self.inst_type(fun);
                self.inst_type(arg);
            }
            Type::Local(_) => {}
            Type::Hole(name) => {
                let Some(a) = self.type_subst_map.get(name).cloned() else {
                    return;
                };
                *t = a;
                self.inst_type(t);
            }
        }
    }

    fn add_derived_constraint(
        &mut self,
        local_env: LocalEnv,
        mut left: Term,
        mut right: Term,
        is_delta: bool,
    ) {
        let kind;
        if is_delta {
            kind = ConstraintKind::Delta;
        } else {
            self.inst_arg_stuck(&mut left);
            self.inst_arg_stuck(&mut right);
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
            local_env,
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
        self.subst_map.insert(name, m.clone());

        if let Some(constraints) = self.watch_list.get(&name) {
            for c in constraints.iter().rev() {
                // skip constraints already resolved anyway
                if c.left.head().typed_eq(&Term::Hole(name)) {
                    if let Term::Hole(name) = c.right.head() {
                        if self.subst_map.contains_key(name) {
                            continue;
                        }
                    }
                } else if let Term::Hole(name) = c.left.head() {
                    if self.subst_map.contains_key(name) {
                        continue;
                    }
                }
                let mut c = (**c).clone();
                let subst = [(name, &m)];
                c.left.inst_hole(&subst);
                c.right.inst_hole(&subst);
                self.stack.push((c.local_env, c.left, c.right));
            }
        }
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

    fn get_hole_type(&self, name: Name) -> Option<&Type> {
        self.term_holes
            .iter()
            .find(|&&(n, _)| n == name)
            .map(|(_, t)| t)
    }

    fn add_hole_type(&mut self, name: Name, ty: Type) {
        self.term_holes.push((name, ty));
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
                let mut t = t.clone();
                self.inst_type(&mut t); // TODO: avoid instantiation
                if t.contains_hole(&name) {
                    return Some(());
                }
                self.add_type_subst(name, t);
            }
            (_, _) => {
                return Some(());
            }
        }
        None
    }

    fn find_conflict_in_terms(
        &mut self,
        mut local_env: LocalEnv,
        mut left: Term,
        mut right: Term,
    ) -> Option<()> {
        if left.typed_eq(&right) {
            return None;
        }
        if let (Term::Abs(l), Term::Abs(r)) = (&mut left, &mut right) {
            let x = Name::fresh();
            Arc::make_mut(l).body.open(&mk_local(x));
            Arc::make_mut(r).body.open(&mk_local(x));
            self.add_type_constraint(l.binder_type.clone(), r.binder_type.clone());
            local_env
                .locals
                .push((x, mem::take(&mut Arc::make_mut(l).binder_type)));
            let left = mem::take(&mut Arc::make_mut(l).body);
            let right = mem::take(&mut Arc::make_mut(r).body);
            self.stack.push((local_env, left, right));
            return None;
        }
        if self.tt_env.weak_reduce(&mut left).is_some()
            || self.tt_env.weak_reduce(&mut right).is_some()
        {
            self.stack.push((local_env, left, right));
            return None;
        }
        if self.inst_stuck(&mut left) || self.inst_stuck(&mut right) {
            self.stack.push((local_env, left, right));
            return None;
        }
        if left.is_abs() {
            mem::swap(&mut left, &mut right);
        }
        if let Term::Abs(right) = right {
            // solvable only when
            // 1. L is stuck by an unfoldable constant
            // 2. L is stuck by an unassigned hole
            if self.unfold_stuck(&mut left) {
                // case 1
                self.stack.push((local_env, left, Term::Abs(right)));
                return None;
            } else if left.head().is_hole() {
                // ?M t₁ ⋯ tₙ =?= λ x, N
                // ----------------------
                // ?M t₁ ⋯ tₙ x =?= N
                //
                // Note that this rule in general allows us to reason eta equivalence like
                //
                // ?M =?= λ x, f x
                // ---------------
                // ?M x =?= f x
                // --------------- (1)  (possible in theory, but not implemented in our code!)
                // ?M := f
                //
                // but in our implementation (1) is solved by choice_fr which always solves it
                // by assigning ?M := λ x, f x, so we don't need to worry about that.
                let right = Arc::unwrap_or_clone(right);
                let x = Name::fresh_from(right.binder_name);
                local_env.locals.push((x, right.binder_type));
                let mut right = right.body;
                right.open(&mk_local(x));
                left.apply([mk_local(x)]);
                self.stack.push((local_env, left, right));
                return None;
            } else {
                // TODO: check the case where L = (π ?M t₁ ⋯ tₙ)
                // TODO: if we decide to land the kernel support for eta we need to add a clause here
                return Some(());
            }
        }
        // then each of the heads can be a local, a const, or a hole
        if let Term::Hole(right_head) = right.head() {
            let right_head = *right_head;
            self.inst_arg_stuck(&mut right);
            if let Some(args) = right.is_pattern() {
                // TODO: avoid full instantiation
                if self.inst(&mut left, right_head) {
                    let binders = args
                        .into_iter()
                        .map(|n| (n, local_env.get_local(n).unwrap().clone()))
                        .collect::<Vec<_>>();
                    if left.abs(&binders, false) {
                        self.add_subst(right_head, left.clone());
                        return None;
                    }
                }
            }
        }
        if let Term::Hole(left_head) = left.head() {
            let left_head = *left_head;
            self.inst_arg_stuck(&mut left);
            if let Some(args) = left.is_pattern() {
                if self.inst(&mut right, left_head) {
                    let binders = args
                        .into_iter()
                        .map(|n| (n, local_env.get_local(n).unwrap().clone()))
                        .collect::<Vec<_>>();
                    if right.abs(&binders, false) {
                        self.add_subst(left_head, right.clone());
                        return None;
                    }
                }
            }
        }
        if right.head().is_hole() || left.head().is_hole() {
            self.add_derived_constraint(local_env, left, right, false);
            return None;
        }
        // then each of the heads can be a local or a const.
        if right.head().is_const() {
            mem::swap(&mut left, &mut right);
        }
        match (left.head(), right.head()) {
            (Term::Const(left_head), Term::Const(right_head)) => {
                // Stucks can occur because its main premise is any of the following forms:
                // 1. f a₁ ⋯ aₙ    stuck can be resolved by δ-reduction
                // 2. ?M a₁ ⋯ aₙ   stuck can be resolved by instantiation
                // 3. l a₁ ⋯ aₙ
                if left_head.name != right_head.name {
                    let left_hint = self.tt_env.def_hint(left_head.name).unwrap_or(0);
                    let right_hint = self.tt_env.def_hint(right_head.name).unwrap_or(0);
                    match left_hint.cmp(&right_hint) {
                        std::cmp::Ordering::Greater => {
                            self.tt_env.unfold_head(&mut left).unwrap();
                            self.stack.push((local_env, left, right));
                            return None;
                        }
                        std::cmp::Ordering::Less => {
                            self.tt_env.unfold_head(&mut right).unwrap();
                            self.stack.push((local_env, left, right));
                            return None;
                        }
                        std::cmp::Ordering::Equal => {
                            if left_hint == 0 {
                                // Check whether either is a projection whose premise is unfoldable.
                                // No priority is given to each side.
                                if self.unfold_stuck(&mut left) || self.unfold_stuck(&mut right) {
                                    self.stack.push((local_env, left, right));
                                    return None;
                                }
                                // Two possibilities
                                // 1. (f t₁ ⋯ tₙ) ≈ (g s₁ ⋯ sₘ) where f and g are both irreducible.
                                // 2. (π₁ t₁ ⋯ tₙ) ≈ (π₂ s₁ ⋯ sₘ) where π₁ and π₂ are different projections and
                                //    both are stuck by possibly different holes.
                                // Case 2 can be possibly resolved by appropriate instantiation but in this implementation
                                // we simply give up. TODO: do something anyhow?
                                return Some(());
                            }
                            self.tt_env.unfold_head(&mut left).unwrap();
                            self.tt_env.unfold_head(&mut right).unwrap();
                            self.stack.push((local_env, left, right));
                            return None;
                        }
                    }
                }
                // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ)
                if self.tt_env.def_hint(left_head.name).is_none() {
                    // Check whether either is a projection whose premise is unfoldable.
                    // No priority is given to each side.
                    if self.unfold_stuck(&mut left) || self.unfold_stuck(&mut right) {
                        self.stack.push((local_env, left, right));
                        return None;
                    }
                    // rebind left_head and right_head because their lifetimes are over.
                    let (Term::Const(left_head), Term::Const(right_head)) =
                        (left.head(), right.head())
                    else {
                        unreachable!();
                    };
                    // Three possibilities
                    // 1. (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ) where f is irreducible
                    // 2. (π t₁ ⋯ tₙ) ≈ (π s₁ ⋯ sₘ) where both sides are stuck by some holes.
                    // 3. (π₁ t₁ ⋯ tₙ) ≈ (π₂ s₁ ⋯ sₘ) where rec₁ and rec₂ are different projections and both are stuck by some holes.
                    // We ignore case 3, and do only unify as if π is a regular opaque constant for case 2. TODO: do something anyhow?
                    for (t1, t2) in left_head.ty_args.iter().zip(right_head.ty_args.iter()) {
                        self.add_type_constraint(t1.clone(), t2.clone());
                    }
                    let left_args = left.unapply();
                    let right_args = right.unapply();
                    if left_args.len() != right_args.len() {
                        return Some(());
                    }
                    for (left_arg, right_arg) in
                        left_args.into_iter().zip(right_args.into_iter()).rev()
                    {
                        self.stack.push((local_env.clone(), left_arg, right_arg));
                    }
                    return None;
                }
                // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ) where any of t or s contains a hole.
                self.add_derived_constraint(local_env, left, right, true);
                None
            }
            (Term::Const(left_head), Term::Local(right_head)) => {
                // TODO: perhaps we can simply give up on this case, when completeness is not important.
                if self.tt_env.def_hint(left_head.name).is_none() {
                    if self.unfold_stuck(&mut left) {
                        self.stack.push((local_env, left, right));
                        return None;
                    }
                    // we give up in finding a solution for a stuck recursor. TODO: anything we can do?
                    return Some(());
                }
                left.close(*right_head);
                if left.is_lclosed() {
                    return Some(());
                }
                left.open(&mk_local(*right_head));
                self.tt_env.unfold_head(&mut left).unwrap();
                self.stack.push((local_env, left, right));
                None
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
                    self.stack.push((local_env.clone(), left_arg, right_arg));
                }
                None
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
                #[cfg(debug_assertions)]
                {
                    println!("find conflict in {t1} =?= {t2}");
                }
                if self.find_conflict_in_types(t1, t2).is_some() {
                    #[cfg(debug_assertions)]
                    {
                        println!("conflict in types");
                    }
                    return Some(());
                }
            }
            if let Some((local_env, m1, m2)) = self.stack.pop() {
                #[cfg(debug_assertions)]
                {
                    println!("find conflict in {m1} =?= {m2}");
                }
                if self.find_conflict_in_terms(local_env, m1, m2).is_some() {
                    #[cfg(debug_assertions)]
                    {
                        println!("conflict in terms");
                    }
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

    fn push_branch(&mut self, trail_len: usize, nodes: Box<dyn Iterator<Item = Node> + 'a>) {
        let snapshot = self.save();
        self.decisions.push(Branch {
            trail_len,
            snapshot,
            nodes,
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
        let Some(node) = br.nodes.next() else {
            return false;
        };
        let snapshot = br.snapshot.clone();
        self.restore(&snapshot);
        for (left, right) in node.type_constraints.into_iter().rev() {
            self.type_constraints.push((left, right));
        }
        for (local_env, left, right) in node.term_constraints.into_iter().rev() {
            self.stack.push((local_env, left, right));
        }
        true
    }

    fn choice_delta(&self, c: &Constraint) -> Vec<Node> {
        // suppose (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₙ)
        let Term::Const(left_head) = c.left.head() else {
            unreachable!();
        };
        let Term::Const(right_head) = c.right.head() else {
            unreachable!();
        };
        let left_args = c.left.args();
        let right_args = c.right.args();
        // Try first (t₁ ≈ s₁) ∧ ⋯ ∧ (tₙ ≈ sₙ)
        let mut node1 = Node::default();
        for (t1, t2) in zip(&left_head.ty_args, &right_head.ty_args) {
            node1.type_constraints.push((t1.clone(), t2.clone()));
        }
        for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
            node1
                .term_constraints
                .push((c.local_env.clone(), left_arg.clone(), right_arg.clone()));
        }
        // Try second ((unfold f) t₁ ⋯ tₙ ≈ (unfold f) s₁ ⋯ sₙ)
        let mut node2 = Node::default();
        {
            let mut left = c.left.clone();
            let mut right = c.right.clone();
            self.tt_env.unfold_head(&mut left).unwrap();
            self.tt_env.unfold_head(&mut right).unwrap();
            node2
                .term_constraints
                .push((c.local_env.clone(), left, right));
        }
        vec![node1, node2]
    }

    fn choice_fr(&mut self, c: &Constraint) -> Vec<Node> {
        // left  ≡ ?M t[1] .. t[p]
        // right ≡  @ u[1] .. u[q]
        let &Term::Hole(left_head) = c.left.head() else {
            panic!()
        };
        let left_args = c.left.args();
        let right_args = c.right.args();
        let right_head = c.right.head();

        let mut nodes = vec![];

        // τ(?M)
        let left_head_ty = {
            let mut t = self.get_hole_type(left_head).unwrap().clone();
            self.inst_type(&mut t); // TODO: avoid full instantiation
            t
        };

        // τ(?M t[1] .. t[p]) (= τ(@ u[1] .. u[q]))
        let left_ty = {
            let mut t = left_head_ty.target().clone();
            t.arrow(
                left_head_ty
                    .components()
                    .into_iter()
                    .skip(left_args.len())
                    .cloned(),
            );
            t
        };

        // z[1] .. z[p]
        let new_binders = left_head_ty
            .components()
            .iter()
            .take(left_args.len())
            .map(|&t| (Name::fresh(), t.clone()))
            .collect::<Vec<_>>();
        assert_eq!(new_binders.len(), left_args.len());

        // Projection step.
        //
        //   M ↦ λ z[1] .. z[p], z[i] (Y[1] z[1] .. z[p]) .. (Y[m] z[1] .. z[p])
        //
        // where τ(z[i]) = t₁ → ⋯ → tₘ → τ(@ u[1] .. u[q]).
        // We try projection first because projection yields more general solutions.
        for &(z, ref z_ty) in &new_binders {
            // TODO: this implementation is incompolete!
            //
            // When the target of the type of z[i] is a hole, we cannot determine the number m of Y[i]s.
            // This is critical because it appears often in the wild. Consider the following lemma.
            //
            //   lemma L : bool.rec tt true false = true := eq.ap bool.tt.spec
            //
            // where bool.tt.spec.{α} : bool.rec tt = (λ x y, x).
            // Then we will need to solve tt = C (λ x y, x), but C has an uninstantiated meta type variable α,
            // and it makes hard to proceed the projection step because we cannot determine the number of Y[i]s
            // which will be applied to z[1] of C := λ z[1], z[1] (..).
            //
            // More generally, when we solve the following constraint:
            //
            //  (?M : α → Prop) (t : α) =?= N
            //
            // We have infinitely many solutions produced by projection in combination with type instantiation:
            //
            //   ?M = λ x, x : Prop → Prop
            //      | λ x, x (Y x) : (β → Prop) → Prop
            //      | λ x, x (Y x) (Z x) : (β → γ → Prop) → Prop
            //      ...
            //
            // In our implementation we only check the first branch (i.e. assume instantiation of α happens only for base types).
            // (Maybe we can prove that only a finite subset of them matters using the subformula property?)
            //
            // See [1] for more detailed discussion, and [2] for a solution of this problem.
            //
            // - [1] Tobias Nipkow. Higher-Order Unification, Polymorphism and Subsort, 1990.
            // - [2] Ullrich Hustadt. A complete transformation system for polymorphic higher-order unification, 1991.

            if z_ty.components().len() < left_ty.components().len() {
                continue;
            }
            let m = z_ty.components().len() - left_ty.components().len();

            let mut t = z_ty.target().clone();
            t.arrow(z_ty.components().into_iter().skip(m).cloned());

            // Y[1] .. Y[m]
            let arg_holes = z_ty
                .components()
                .iter()
                .take(m)
                .map(|&arg_ty| {
                    let new_hole = Name::fresh();
                    let mut ty = arg_ty.clone();
                    ty.arrow(new_binders.iter().map(|(_, t)| t.clone()));
                    (new_hole, ty)
                })
                .collect::<Vec<_>>();

            for &(x, ref t) in &arg_holes {
                self.add_hole_type(x, t.clone());
            }

            // (Y[1] z[1] .. z[p]) .. (Y[m] z[1] .. z[p])
            let new_args = arg_holes
                .iter()
                .map(|&(hole, _)| {
                    let mut arg = Term::Hole(hole);
                    arg.apply(new_binders.iter().map(|&(x, _)| mk_local(x)));
                    arg
                })
                .collect::<Vec<_>>();

            // TODO: try eta equal condidates when the hole ?M is used twice or more among the whole set of constraints.
            let mut target = mk_local(z);
            target.apply(new_args);
            target.abs(&new_binders, false);
            nodes.push(Node {
                type_constraints: vec![(t, left_ty.clone())],
                term_constraints: vec![(c.local_env.clone(), Term::Hole(left_head), target)],
            });
        }

        // Imitation step.
        //
        //   M ↦ λ z[1] .. z[p], C (Y[1] z[1] .. z[p]) .. (Y[q] z[1] .. z[p])
        //
        // when @ = C.
        if let Term::Const(right_head) = right_head {
            // τ(C)
            let right_head_ty = {
                let (args, t) = self.tt_env.consts.get(&right_head.name).unwrap();
                let subst = zip(args.iter().copied(), &right_head.ty_args).collect::<Vec<_>>();
                let mut t = t.clone();
                t.subst(&subst);
                self.inst_type(&mut t); // TODO: avoid full instantiation
                t
            };

            // τ(u[1]) ⋯ τ(u[q])
            let new_arg_tys = right_head_ty
                .components()
                .iter()
                .take(right_args.len())
                .map(|&t| t.clone())
                .collect::<Vec<_>>();

            // Y[1] .. Y[q]
            let new_arg_holes = new_arg_tys
                .iter()
                .map(|arg_ty| {
                    let new_hole = Name::fresh();
                    let mut ty = arg_ty.clone();
                    ty.arrow(new_binders.iter().map(|(_, t)| t.clone()));
                    (new_hole, ty)
                })
                .collect::<Vec<_>>();

            for &(x, ref t) in &new_arg_holes {
                self.add_hole_type(x, t.clone());
            }

            // (Y[1] z[1] .. z[p]) .. (Y[q] z[1] .. z[p])
            let new_args = new_arg_holes
                .iter()
                .map(|&(hole, _)| {
                    let mut arg = Term::Hole(hole);
                    arg.apply(new_binders.iter().map(|&(x, _)| mk_local(x)));
                    arg
                })
                .collect::<Vec<_>>();

            // TODO: try eta equal condidates when the hole ?M is used twice or more among the whole set of constraints.
            let mut target = Term::Const(right_head.clone());
            target.apply(new_args);
            target.abs(&new_binders, false);
            nodes.push(Node {
                type_constraints: vec![],
                term_constraints: vec![(c.local_env.clone(), Term::Hole(left_head), target)],
            });
        }

        // Field accessor step.
        //
        //   M ↦ λ z[1] .. z[p], π (z[i] (Y[1] z[1] .. z[p]) .. (Y[m] z[1] .. z[p])) (W[1] z[1] .. z[p]) (W[k] z[1] .. z[p])
        //
        // where τ(z[i]) = t₁ → ⋯ → tₘ → (S σ₁ ⋯ σₙ) and target(τ(π)) = τ(@ u[1] .. u[q]).
        for &(z, ref z_ty) in &new_binders {
            // Note that z_ty is already instantiated.
            let mut z_ty_target = z_ty.target().clone();
            let ty_args = z_ty_target.unapply();
            // We assume type variables will never be instantiated with structure types or arrow types.
            // In the most general situation z[i] : (τᵢ) → α is instantiated into (τᵢ) → (σⱼ) → S,
            // in which case we need j more variables for Ys.
            // TODO: if z_ty_target is a type hole, it may be instantiated with a type with a sturcutre type as its target.
            // TODO: if z_ty_target is a type hole, it may be instantiated with an arrow type, which means we need increase
            // the number m of the count of Ys.
            let Type::Const(head) = z_ty_target else {
                continue;
            };
            let Some(structure) = self.structure_table.get(&head) else {
                continue;
            };
            let ty_subst = zip(structure.local_types.iter().copied(), &ty_args).collect::<Vec<_>>();
            for field in &structure.fields {
                let StructureField::Const(field) = field else {
                    continue;
                };
                let mut proj_ty = field.ty.clone();
                proj_ty.subst(&ty_subst);
                if proj_ty.components().len() < left_ty.components().len() {
                    continue;
                }

                let struct_obj = {
                    // Y[1] .. Y[m]
                    let arg_holes = z_ty
                        .components()
                        .iter()
                        .map(|&arg_ty| {
                            let new_hole = Name::fresh();
                            let mut ty = arg_ty.clone();
                            ty.arrow(new_binders.iter().map(|(_, t)| t.clone()));
                            (new_hole, ty)
                        })
                        .collect::<Vec<_>>();

                    for &(x, ref t) in &arg_holes {
                        self.add_hole_type(x, t.clone());
                    }

                    // (Y[1] z[1] .. z[p]) .. (Y[m] z[1] .. z[p])
                    let new_args = arg_holes
                        .iter()
                        .map(|&(hole, _)| {
                            let mut arg = Term::Hole(hole);
                            arg.apply(new_binders.iter().map(|&(x, _)| mk_local(x)));
                            arg
                        })
                        .collect::<Vec<_>>();

                    // z[i] (Y[1] z[1] .. z[p]) .. (Y[m] z[1] .. z[p])
                    let mut struct_obj = mk_local(z);
                    struct_obj.apply(new_args);
                    struct_obj.abs(&new_binders, false);
                    struct_obj
                };

                let k = proj_ty.components().len() - left_ty.components().len();

                // TODO: if the target of proj_ty is a type hole, it may be instantiated with an arrow type,
                // which means we need increase the number k of the count of Ws.
                let mut t = proj_ty.target().clone();
                t.arrow(proj_ty.components().into_iter().skip(k).cloned());

                // W[1] .. W[k]
                let arg_holes = proj_ty
                    .components()
                    .iter()
                    .take(k)
                    .map(|&arg_ty| {
                        let new_hole = Name::fresh();
                        let mut ty = arg_ty.clone();
                        ty.arrow(new_binders.iter().map(|(_, t)| t.clone()));
                        (new_hole, ty)
                    })
                    .collect::<Vec<_>>();

                for &(x, ref t) in &arg_holes {
                    self.add_hole_type(x, t.clone());
                }

                // (W[1] z[1] .. z[p]) .. (W[k] z[1] .. z[p])
                let new_args = arg_holes
                    .iter()
                    .map(|&(hole, _)| {
                        let mut arg = Term::Hole(hole);
                        arg.apply(new_binders.iter().map(|&(x, _)| mk_local(x)));
                        arg
                    })
                    .collect::<Vec<_>>();

                // TODO: try eta equal condidates when the hole ?M is used twice or more among the whole set of constraints.
                let proj_name =
                    Name::intern(&format!("{}.{}", structure.name, field.name)).unwrap();
                let mut target = mk_const(proj_name, ty_args.clone());
                target.apply([struct_obj]);
                target.apply(new_args);
                target.abs(&new_binders, false);
                nodes.push(Node {
                    type_constraints: vec![(t, left_ty.clone())],
                    term_constraints: vec![(c.local_env.clone(), Term::Hole(left_head), target)],
                });
            }
        }

        nodes
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
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!(
                "{sp}making a decision ({:?}):\n{sp}- {}\n{sp}  {}",
                c.kind, c.left, c.right
            );
        }
        let nodes = match c.kind {
            ConstraintKind::Delta => self.choice_delta(&c),
            ConstraintKind::QuasiPattern => self.choice_fr(&c),
            ConstraintKind::FlexRigid => self.choice_fr(&c),
            ConstraintKind::FlexFlex => unreachable!(),
        };

        self.push_branch(trail_len, Box::new(nodes.into_iter()));
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
