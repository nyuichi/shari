use std::{
    collections::{HashMap, VecDeque},
    iter::{repeat_n, zip},
    mem,
    rc::Rc,
    sync::Arc,
};

use anyhow::{bail, Context};

use crate::{
    cmd::{Axiom, CmdClass, CmdStructure, Const, StructureField},
    expr::{
        mk_expr_change, mk_expr_inst, Expr, ExprApp, ExprAssume, ExprAssump, ExprChange, ExprInst,
        ExprTake,
    },
    tt::{
        self, mk_const, mk_fresh_type_hole, mk_local, mk_type_arrow, Kind, Name, Term, TermAbs,
        TermApp, Type, TypeApp, TypeArrow,
    },
};
use crate::{
    proof::{mk_type_prop, Imp},
    tt::LocalEnv,
};

#[derive(Debug)]
pub struct Elaborator<'a> {
    tt_env: &'a tt::Env,
    tt_local_env: &'a mut tt::LocalEnv,
    structure_table: &'a HashMap<Name, CmdStructure>,
    const_table: &'a HashMap<Name, Const>,
    axiom_table: &'a HashMap<Name, Axiom>,
    database: &'a Vec<CmdClass>,
    locals: Vec<Term>,
    type_constraints: Vec<(Type, Type)>,
    term_constraints: Vec<(LocalEnv, Term, Term)>,
    class_constraints: Vec<Term>,
}

impl<'a> Elaborator<'a> {
    pub fn new(
        tt_env: &'a tt::Env,
        tt_local_env: &'a mut tt::LocalEnv,
        const_table: &'a HashMap<Name, Const>,
        axiom_table: &'a HashMap<Name, Axiom>,
        structure_table: &'a HashMap<Name, CmdStructure>,
        database: &'a Vec<CmdClass>,
    ) -> Self {
        Elaborator {
            tt_env,
            tt_local_env,
            const_table,
            axiom_table,
            structure_table,
            database,
            locals: vec![],
            type_constraints: vec![],
            term_constraints: vec![],
            class_constraints: vec![],
        }
    }

    fn add_type_constraint(&mut self, t1: Type, t2: Type) {
        self.type_constraints.push((t1, t2));
    }

    fn add_term_constraint(&mut self, local_env: LocalEnv, m1: Term, m2: Term) {
        self.term_constraints.push((local_env, m1, m2));
    }

    fn add_class_constraint(&mut self, m: Term) {
        self.class_constraints.push(m);
    }

    fn visit_type(&self, t: &Type) -> anyhow::Result<Kind> {
        match t {
            Type::Const(t) => {
                let Some(kind) = self.tt_env.type_consts.get(t) else {
                    bail!("constant type not found");
                };
                Ok(kind.clone())
            }
            Type::Arrow(t) => {
                let TypeArrow { dom, cod } = &**t;
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
                let TypeApp { fun, arg } = &**t;
                let fun_kind = self.visit_type(fun)?;
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
                    if local_type == t {
                        return Ok(Kind::base());
                    }
                }
                bail!("unbound local type: {t}");
            }
            Type::Hole(_) => Ok(Kind::base()),
        }
    }

    fn mk_term_hole(&mut self, ty: Type) -> Term {
        let mut hole_ty = ty;
        hole_ty.arrow(self.tt_local_env.locals.iter().map(|(_, ty)| ty.clone()));
        let hole = self.tt_local_env.add_new_hole(None, hole_ty);
        // ?M l₁ ⋯ lₙ
        let mut target = Term::Hole(hole);
        target.apply(
            self.tt_local_env
                .locals
                .iter()
                .map(|&(name, _)| mk_local(name)),
        );
        target
    }

    fn visit_term(&mut self, m: &mut Term) -> anyhow::Result<Type> {
        match m {
            Term::Local(m) => {
                for (local, ty) in &self.tt_local_env.locals {
                    if local == m {
                        return Ok(ty.clone());
                    }
                }
                bail!("unknown local variable: {m}");
            }
            Term::Hole(m) => {
                for (local, ty) in &self.tt_local_env.holes {
                    if local == m {
                        return Ok(ty.clone());
                    }
                }
                bail!("unknown meta variable");
            }
            Term::Var(_) => {
                bail!("term not locally closed");
            }
            Term::Abs(m) => {
                let &mut TermAbs {
                    binder_type: ref arg_ty,
                    binder_name,
                    ref mut body,
                } = Arc::make_mut(m);

                let arg_ty_kind = self.visit_type(arg_ty)?;
                if !arg_ty_kind.is_base() {
                    bail!("expected Type, but got {arg_ty_kind}");
                }

                let x = Name::fresh_from(binder_name);
                self.tt_local_env.locals.push((x, arg_ty.clone()));
                body.open(&mk_local(x));
                let body_ty = self.visit_term(body)?;
                body.close(x);
                self.tt_local_env.locals.pop();

                Ok(mk_type_arrow(arg_ty.clone(), body_ty))
            }
            Term::App(m) => {
                let TermApp { fun, arg } = Arc::make_mut(m);

                let fun_ty = self.visit_term(fun)?;
                let arg_ty = self.visit_term(arg)?;
                let ret_ty = mk_fresh_type_hole();

                self.add_type_constraint(fun_ty, mk_type_arrow(arg_ty, ret_ty.clone()));

                Ok(ret_ty)
            }
            Term::Const(n) => {
                let Some(Const {
                    local_types,
                    local_classes,
                    ty,
                }) = self.const_table.get(&n.name)
                else {
                    bail!("constant not found");
                };
                if local_types.len() != n.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                for ty_arg in &n.ty_args {
                    let ty_arg_kind = self.visit_type(ty_arg)?;
                    if !ty_arg_kind.is_base() {
                        bail!("expected Type, but got {ty_arg_kind}");
                    }
                }
                let mut subst = vec![];
                for (&x, t) in zip(local_types, &n.ty_args) {
                    subst.push((x, t.clone()));
                }
                let mut ty = ty.clone();
                ty.subst(&subst);

                let mut class_args = vec![];
                for (_, class_ty) in local_classes {
                    let mut ty = class_ty.clone();
                    ty.subst(&subst);
                    let hole = self.tt_local_env.add_new_hole(Some("d"), ty);
                    self.add_class_constraint(Term::Hole(hole));
                    class_args.push(Term::Hole(hole));
                }
                // C ↦ C d₁ ⋯ dₙ
                m.apply(class_args);

                Ok(ty)
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) -> anyhow::Result<Term> {
        match expr {
            Expr::Assump(expr) => {
                let ExprAssump { target } = Arc::make_mut(expr);

                let target_ty = self.visit_term(target)?;
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
            Expr::Assume(expr) => {
                let ExprAssume { target, expr } = Arc::make_mut(expr);

                let target_ty = self.visit_term(target)?;
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
            Expr::App(expr) => {
                let ExprApp { expr1, expr2 } = Arc::make_mut(expr);

                let fun = self.visit_expr(expr1)?;
                let arg = self.visit_expr(expr2)?;

                let ret = self.mk_term_hole(mk_type_prop());

                let mut target = ret.clone();
                target.guard([arg]);
                self.add_term_constraint(self.tt_local_env.clone(), fun, target.clone());

                *expr1 = mk_expr_change(target, mem::take(expr1));

                Ok(ret)
            }
            Expr::Take(expr) => {
                let ExprTake { name, ty, expr } = Arc::make_mut(expr);

                let ty_kind = self.visit_type(ty)?;
                if !ty_kind.is_base() {
                    bail!("expected Type, but got {ty_kind}");
                }

                self.tt_local_env.locals.push((*name, ty.clone()));
                let mut target = self.visit_expr(expr)?;
                self.tt_local_env.locals.pop();

                target.generalize(&[(*name, ty.clone())]);

                Ok(target)
            }
            Expr::Inst(expr) => {
                let ExprInst { expr, arg } = Arc::make_mut(expr);

                let forall = self.visit_expr(expr)?;
                let arg_ty = self.visit_term(arg)?;

                let pred = self.mk_term_hole(mk_type_arrow(arg_ty.clone(), mk_type_prop()));

                let mut target = pred.clone();
                let x = Name::fresh();
                target.apply([mk_local(x)]);
                target.generalize(&[(x, arg_ty.clone())]);
                self.add_term_constraint(self.tt_local_env.clone(), forall, target.clone());

                *expr = mk_expr_change(target, mem::take(expr));

                let mut ret = pred;
                ret.apply([arg.clone()]);
                Ok(ret)
            }
            Expr::Const(e) => {
                let Some(Axiom {
                    local_types,
                    local_classes,
                    target,
                }) = self.axiom_table.get(&e.name)
                else {
                    bail!("proposition not found: {}", e.name);
                };
                if local_types.len() != e.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                for ty_arg in &e.ty_args {
                    let ty_arg_kind = self.visit_type(ty_arg)?;
                    if !ty_arg_kind.is_base() {
                        bail!("expected Type, but got {ty_arg_kind}");
                    }
                }
                let mut subst = vec![];
                for (&x, t) in zip(local_types, &e.ty_args) {
                    subst.push((x, t.clone()));
                }
                let mut target = target.clone();
                target.subst_type(&subst);

                let mut class_args = vec![];
                for (_, class_ty) in local_classes {
                    let mut ty = class_ty.clone();
                    ty.subst(&subst);
                    let hole = self.tt_local_env.add_new_hole(Some("d"), ty);
                    self.add_class_constraint(Term::Hole(hole));
                    class_args.push(Term::Hole(hole));
                }
                for class_arg in &class_args {
                    *expr = mk_expr_inst(mem::take(expr), class_arg.clone());
                }
                target.subst(
                    &zip(local_classes, class_args)
                        .map(|(&(x, _), a)| (x, a))
                        .collect::<Vec<_>>(),
                );
                Ok(target)
            }
            Expr::Change(expr) => {
                let ExprChange { target, expr } = Arc::make_mut(expr);

                let target_ty = self.visit_term(target)?;
                self.add_type_constraint(target_ty, mk_type_prop());
                let expr_prop = self.visit_expr(expr)?;
                self.add_term_constraint(
                    self.tt_local_env.clone(),
                    expr_prop.clone(),
                    target.clone(),
                );

                Ok(target.clone())
            }
        }
    }

    // ty is trusted
    pub fn elaborate_term(mut self, target: &mut Term, ty: &Type) -> anyhow::Result<()> {
        let t = self.visit_term(target)?;
        self.add_type_constraint(t, ty.clone());

        let (subst, type_subst) = Unifier::new(
            self.tt_env,
            self.structure_table,
            self.tt_local_env.holes.clone(),
            self.term_constraints,
            self.type_constraints,
            self.class_constraints,
            self.database,
        )
        .solve()
        .context("unification failed")?;

        target.inst_type_hole(&type_subst);
        target.inst_hole(&subst);

        Ok(())
    }

    // prop is trusted
    pub fn elaborate_expr(mut self, e: &mut Expr, prop: &Term) -> anyhow::Result<()> {
        #[cfg(debug_assertions)]
        {
            println!("elaborating:\n{e}");
        }

        *e = mk_expr_change(prop.clone(), mem::take(e));
        self.visit_expr(e)?;

        let (subst, type_subst) = Unifier::new(
            self.tt_env,
            self.structure_table,
            self.tt_local_env.holes.clone(),
            self.term_constraints,
            self.type_constraints,
            self.class_constraints,
            self.database,
        )
        .solve()
        .context("unification failed")?;

        e.inst_type_hole(&type_subst);
        e.inst_hole(&subst);

        #[cfg(debug_assertions)]
        {
            println!("elaborated:\n{e}");
        }

        Ok(())
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
struct EqConstraint {
    // TODO: only the locals field is used. Use a more efficient data structure.
    local_env: LocalEnv,
    left: Term,
    right: Term,
}

#[derive(Debug, Clone)]
struct ClassConstraint {
    target: Term,
}

#[derive(Debug, Clone)]
struct Snapshot {
    subst_len: usize,
    trail_len: usize,
    type_subst_len: usize,
}

#[derive(Debug, Default)]
struct Node {
    subst: Vec<(Name, Term)>,
    type_constraints: Vec<(Type, Type)>,
    term_constraints: Vec<(LocalEnv, Term, Term)>,
}

struct Branch<'a> {
    trail_len: usize,
    snapshot: Snapshot,
    nodes: Box<dyn Iterator<Item = Node> + 'a>,
}

enum TrailElement {
    EqConstraint(Rc<EqConstraint>, ConstraintKind),
    ClassConstraint(Rc<ClassConstraint>),
}

struct Unifier<'a> {
    tt_env: &'a tt::Env,
    structure_table: &'a HashMap<Name, CmdStructure>,
    term_holes: Vec<(Name, Type)>,
    database: &'a [CmdClass],
    queue_delta: VecDeque<Rc<EqConstraint>>,
    queue_qp: VecDeque<Rc<EqConstraint>>,
    queue_fr: VecDeque<Rc<EqConstraint>>,
    queue_ff: VecDeque<Rc<EqConstraint>>,
    queue_class: VecDeque<Rc<ClassConstraint>>,
    watch_list: HashMap<Name, Vec<Rc<EqConstraint>>>,
    subst: Vec<(Name, Term)>,
    subst_map: HashMap<Name, Term>,
    type_subst: Vec<(Name, Type)>,
    type_subst_map: HashMap<Name, Type>,
    decisions: Vec<Branch<'a>>,
    // for backjumping.
    // It extends when a new constraint is queued or a decision is made.
    trail: Vec<TrailElement>,
    // only used in find_conflict
    stack: Vec<(LocalEnv, Term, Term)>,
    type_stack: Vec<(Type, Type)>,
}

impl<'a> Unifier<'a> {
    fn new(
        tt_env: &'a tt::Env,
        structure_table: &'a HashMap<Name, CmdStructure>,
        term_holes: Vec<(Name, Type)>,
        constraints: Vec<(LocalEnv, Term, Term)>,
        type_constraints: Vec<(Type, Type)>,
        class_constraints: Vec<Term>,
        database: &'a [CmdClass],
    ) -> Self {
        Self {
            tt_env,
            structure_table,
            term_holes,
            database,
            queue_delta: Default::default(),
            queue_qp: Default::default(),
            queue_fr: Default::default(),
            queue_ff: Default::default(),
            queue_class: class_constraints
                .into_iter()
                .map(|target| Rc::new(ClassConstraint { target }))
                .collect(),
            watch_list: Default::default(),
            subst: Default::default(),
            subst_map: Default::default(),
            type_subst: vec![],
            type_subst_map: Default::default(),
            decisions: Default::default(),
            trail: Default::default(),
            stack: constraints,
            type_stack: type_constraints,
        }
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

    fn watch(&mut self, c: Rc<EqConstraint>) {
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

    fn unwatch(&mut self, c: &Rc<EqConstraint>) {
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

    // Note that the result term may contain redex in head
    fn inst_head(&self, m: &mut Term) -> bool {
        if let &Term::Hole(m_head) = m.head() {
            if let Some(a) = self.subst_map.get(&m_head) {
                let subst = [(m_head, a.clone())];
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

        let c = Rc::new(EqConstraint {
            local_env,
            left: left.clone(),
            right: right.clone(),
        });

        self.trail.push(TrailElement::EqConstraint(c.clone(), kind));

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
                let subst = [(name, m.clone())];
                c.left.inst_hole(&subst);
                c.right.inst_hole(&subst);
                self.stack.push((c.local_env, c.left, c.right));
            }
        }
    }

    fn add_type_constraint(&mut self, t1: Type, t2: Type) {
        self.type_stack.push((t1, t2));
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

    fn get_type(&self, local_env: &mut LocalEnv, target: &Term) -> Type {
        match target {
            Term::Var(_) => unreachable!(),
            Term::Abs(target) => {
                let x = Name::fresh();
                let mut dom = target.binder_type.clone();
                self.inst_type(&mut dom);
                local_env.locals.push((x, dom.clone()));
                let mut body = target.body.clone();
                body.open(&mk_local(x));
                let mut cod = self.get_type(local_env, &body);
                local_env.locals.pop();
                cod.arrow([dom]);
                cod
            }
            Term::App(target) => {
                let mut t = self.get_type(local_env, &target.fun);
                let mut doms = t.unarrow();
                doms.remove(0);
                t.arrow(doms);
                t
            }
            Term::Const(target) => {
                let (args, t) = self.tt_env.consts.get(&target.name).unwrap();
                let mut subst = vec![];
                for (&x, t) in zip(args, &target.ty_args) {
                    subst.push((x, t.clone()));
                }
                let mut t = t.clone();
                t.subst(&subst);
                self.inst_type(&mut t);
                t
            }
            &Term::Local(name) => local_env.get_local(name).unwrap().clone(),
            &Term::Hole(name) => self.get_hole_type(name).unwrap().clone(),
        }
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
        while !self.type_stack.is_empty() || !self.stack.is_empty() {
            if let Some((t1, t2)) = self.type_stack.pop() {
                #[cfg(debug_assertions)]
                {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}find conflict in {t1} =?= {t2}");
                }
                if self.find_conflict_in_types(t1, t2).is_some() {
                    #[cfg(debug_assertions)]
                    {
                        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                        println!("{sp}conflict in types");
                    }
                    return Some(());
                }
            }
            if let Some((local_env, m1, m2)) = self.stack.pop() {
                #[cfg(debug_assertions)]
                {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}find conflict in {m1} =?= {m2}");
                }
                if self.find_conflict_in_terms(local_env, m1, m2).is_some() {
                    #[cfg(debug_assertions)]
                    {
                        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                        println!("{sp}conflict in terms");
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
            let TrailElement::EqConstraint(c, kind) = &self.trail[i] else {
                unreachable!()
            };
            match kind {
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
            match self.trail.pop().unwrap() {
                TrailElement::EqConstraint(c, kind) => match kind {
                    ConstraintKind::Delta => {
                        self.queue_delta.push_front(c);
                    }
                    ConstraintKind::QuasiPattern => {
                        self.queue_qp.push_front(c);
                    }
                    ConstraintKind::FlexRigid => {
                        self.queue_fr.push_front(c);
                    }
                    ConstraintKind::FlexFlex => {
                        self.queue_ff.push_front(c);
                    }
                },
                TrailElement::ClassConstraint(c) => {
                    self.queue_class.push_front(c);
                }
            }
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
        for (x, m) in node.subst.into_iter().rev() {
            self.add_subst(x, m);
        }
        for (left, right) in node.type_constraints.into_iter().rev() {
            self.type_stack.push((left, right));
        }
        for (local_env, left, right) in node.term_constraints.into_iter().rev() {
            self.stack.push((local_env, left, right));
        }
        true
    }

    fn choice_delta(&self, c: &EqConstraint) -> Vec<Node> {
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
        let node1 = {
            let mut node = Node::default();
            for (t1, t2) in zip(&left_head.ty_args, &right_head.ty_args) {
                node.type_constraints.push((t1.clone(), t2.clone()));
            }
            for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
                node.term_constraints.push((
                    c.local_env.clone(),
                    left_arg.clone(),
                    right_arg.clone(),
                ));
            }
            node
        };
        // Try second ((unfold f) t₁ ⋯ tₙ ≈ (unfold f) s₁ ⋯ sₙ)
        let node2 = {
            let mut node = Node::default();
            let mut left = c.left.clone();
            let mut right = c.right.clone();
            self.tt_env.unfold_head(&mut left).unwrap();
            self.tt_env.unfold_head(&mut right).unwrap();
            node.term_constraints
                .push((c.local_env.clone(), left, right));
            node
        };
        vec![node1, node2]
    }

    fn choice_fr(&mut self, c: &EqConstraint) -> Vec<Node> {
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
                subst: vec![(left_head, target)],
                type_constraints: vec![(t, left_ty.clone())],
                term_constraints: vec![(c.local_env.clone(), c.left.clone(), c.right.clone())], // TODO: optimize
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
                let mut subst = vec![];
                for (&x, t) in zip(args, &right_head.ty_args) {
                    subst.push((x, t.clone()));
                }
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
                subst: vec![(left_head, target)],
                type_constraints: vec![],
                term_constraints: vec![(c.local_env.clone(), c.left.clone(), c.right.clone())], // TODO: optimize
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
            let mut ty_subst = vec![];
            for (&x, t) in zip(&structure.local_types, &ty_args) {
                ty_subst.push((x, t.clone()));
            }
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
                    subst: vec![(left_head, target)],
                    type_constraints: vec![(t, left_ty.clone())],
                    term_constraints: vec![(c.local_env.clone(), c.left.clone(), c.right.clone())], // TODO: optimize me!
                });
            }
        }

        nodes
    }

    fn synthesize_instance(&self, goal: &Type) -> Option<Term> {
        // TODO(typeclass): support local class constraints
        for clause in self.database {
            let CmdClass {
                local_types,
                params,
                ty,
                target,
            } = clause;
            let pattern = {
                let mut subst = vec![];
                for &name in local_types {
                    subst.push((name, mk_fresh_type_hole()));
                }
                let mut ty = ty.clone();
                ty.subst(&subst);
                ty
            };
            let Some(type_subst) = goal.matches(&pattern) else {
                continue;
            };
            // TODO(typeclass): allow the params to contain its own local types.
            assert!(local_types
                .iter()
                .all(|local| type_subst.iter().any(|(x, _)| x == local)));
            let mut subst = vec![];
            let mut success = true;
            for &(x, ref t) in params {
                let mut subgoal = t.clone();
                subgoal.subst(&type_subst);
                let Some(arg) = self.synthesize_instance(&subgoal) else {
                    success = false;
                    break;
                };
                subst.push((x, arg));
            }
            if !success {
                continue;
            }
            let mut target = target.clone();
            target.subst_type(&type_subst);
            target.subst(&subst);
            // TODO(typeclass):
            // Our language does not support overlapping instances so we generally don't need to check other instances.
            // However, if we try to synthesize for a non-ground goal like `H a ?b`, we will possibly find more than one solutions,
            // and we may want to report an error to tell the user so.
            return Some(target);
        }
        None
    }

    fn choice_class(&mut self, c: &ClassConstraint) -> Vec<Node> {
        // TODO(typeclass): if hole is already assigned, check if the synthesized term is an instance.
        // TODO(typeclass): solve c early when the type of c is known.
        let mut t = self.get_type(&mut LocalEnv::default(), &c.target);
        self.inst_type(&mut t);
        assert!(t.is_ground());
        let Some(instance) = self.synthesize_instance(&t) else {
            return vec![];
        };
        let node = Node {
            subst: vec![],
            type_constraints: vec![],
            term_constraints: vec![(LocalEnv::default(), c.target.clone(), instance)],
        };
        vec![node]
    }

    fn is_resolved_constraint(&self, c: &EqConstraint) -> bool {
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
        let nodes = 'next: {
            if let Some(c) = self.queue_delta.pop_front() {
                self.trail
                    .push(TrailElement::EqConstraint(c.clone(), ConstraintKind::Delta));
                #[cfg(debug_assertions)]
                {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!(
                        "{sp}making a decision (delta):\n{sp}- {}\n{sp}  {}",
                        c.left, c.right
                    );
                }
                break 'next self.choice_delta(&c);
            }
            while let Some(c) = self.queue_qp.pop_front() {
                self.trail.push(TrailElement::EqConstraint(
                    c.clone(),
                    ConstraintKind::QuasiPattern,
                ));
                if !self.is_resolved_constraint(&c) {
                    #[cfg(debug_assertions)]
                    {
                        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                        println!(
                            "{sp}making a decision (qp):\n{sp}- {}\n{sp}  {}",
                            c.left, c.right
                        );
                    }
                    break 'next self.choice_fr(&c);
                }
            }
            while let Some(c) = self.queue_fr.pop_front() {
                self.trail.push(TrailElement::EqConstraint(
                    c.clone(),
                    ConstraintKind::FlexRigid,
                ));
                if !self.is_resolved_constraint(&c) {
                    #[cfg(debug_assertions)]
                    {
                        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                        println!(
                            "{sp}making a decision (fr):\n{sp}- {}\n{sp}  {}",
                            c.left, c.right
                        );
                    }
                    break 'next self.choice_fr(&c);
                }
            }
            for i in 0..self.queue_class.len() {
                let mut t = self.get_type(&mut LocalEnv::default(), &self.queue_class[i].target);
                self.inst_type(&mut t);
                // TODO(typeclass): synthesize instances for constraints with type holes (e.g. ?M : C a ?b)
                if t.is_ground() {
                    let c = self.queue_class.swap_remove_back(i).unwrap();
                    self.trail.push(TrailElement::ClassConstraint(c.clone()));
                    break 'next self.choice_class(&c);
                }
            }
            return false;
        };

        self.push_branch(trail_len, Box::new(nodes.into_iter()));
        self.next();
        true
    }

    fn backjump(&mut self) -> bool {
        self.stack.clear();
        self.type_stack.clear();
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
            #[cfg(debug_assertions)]
            {
                let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                println!("{sp}simplification done");
                self.print_state();
            }
            if !self.decide() {
                break;
            }
        }
        // TODO: optimize
        for i in 0..self.type_subst.len() {
            let mut t = self.type_subst[i].1.clone();
            while !t.is_ground() {
                t.inst_hole(&self.type_subst);
            }
            self.type_subst[i].1 = t;
        }
        for i in 0..self.subst.len() {
            let mut m = self.subst[i].1.clone();
            while !m.is_ground() {
                m.inst_hole(&self.subst);
            }
            while !m.is_type_ground() {
                m.inst_type_hole(&self.type_subst);
            }
            self.subst[i].1 = m;
        }
        Some((self.subst, self.type_subst))
    }
}
