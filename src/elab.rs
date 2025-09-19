use std::{
    collections::{HashMap, VecDeque},
    iter::{repeat_n, zip},
    mem,
    rc::Rc,
    sync::Arc,
};

use anyhow::{bail, ensure};

use crate::{
    expr::{
        Expr, ExprApp, ExprAssume, ExprAssump, ExprChange, ExprConst, ExprInst, ExprTake,
        mk_expr_change,
    },
    proof::{self, Axiom},
    tt::{
        self, Class, ClassInstance, ClassType, Const, Instance, InstanceGlobal, Kind, LocalEnv,
        Name, Parameter, Term, TermAbs, TermApp, TermConst, Type, TypeApp, TypeArrow, mk_const,
        mk_fresh_type_hole, mk_instance_global, mk_local, mk_type_arrow, mk_type_prop,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintKind {
    Postponed,
    Delta,
    QuasiPattern,
    FlexRigid,
    FlexFlex,
}

#[derive(Debug, Clone)]
enum Error {
    Visit(String),
    Join(Arc<(Error, Error)>),
}

fn mk_error_join(e1: Error, e2: Error) -> Error {
    Error::Join(Arc::new((e1, e2)))
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Visit(s) => write!(f, "{}", s),
            Error::Join(inner) => write!(f, "{}", inner.0),
        }
    }
}

#[derive(Debug, Clone)]
struct EqConstraint {
    // TODO: only the locals field is used. Use a more efficient data structure.
    local_env: LocalEnv,
    left: Term,
    right: Term,
    error: Error,
}

#[derive(Debug, Clone)]
struct ClassConstraint {
    // TODO: only the local_classes field is used. Use a more efficient data structure.
    local_env: LocalEnv,
    hole: Name,
    class: Class,
    error: Error,
}

#[derive(Debug, Clone)]
struct Snapshot {
    subst_len: usize,
    trail_len: usize,
    type_subst_len: usize,
    instance_subst_len: usize,
}

#[derive(Debug, Default)]
struct Node {
    subst: Vec<(Name, Term, Error)>,
    type_constraints: Vec<(Type, Type, Error)>,
    term_constraints: Vec<(LocalEnv, Term, Term, Error)>,
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

struct Elaborator<'a> {
    proof_env: proof::Env<'a>,
    term_holes: Vec<(Name, Type)>,
    // only used in visit
    tt_local_env: &'a mut tt::LocalEnv,
    // only used in visit
    instance_holes: Vec<(Name, Class)>,
    // only used in visit
    local_axioms: Vec<Term>,
    queue_delta: VecDeque<Rc<EqConstraint>>,
    queue_qp: VecDeque<Rc<EqConstraint>>,
    queue_fr: VecDeque<Rc<EqConstraint>>,
    queue_ff: VecDeque<Rc<EqConstraint>>,
    queue_class: VecDeque<Rc<ClassConstraint>>,
    queue_postponed: VecDeque<Rc<EqConstraint>>,
    watch_list: HashMap<Name, Vec<Rc<EqConstraint>>>,
    type_watch_list: HashMap<Name, Vec<Rc<ClassConstraint>>>,
    instance_watch_list: HashMap<Name, Vec<Rc<EqConstraint>>>,
    // remove after adding TrailElement::Subst
    subst: Vec<(Name, Term)>,
    subst_map: HashMap<Name, Term>,
    // remove after adding TrailElement::TypeSubst
    type_subst: Vec<(Name, Type)>,
    type_subst_map: HashMap<Name, Type>,
    // remove after adding TrailElement::InstanceSubst
    instance_subst: Vec<(Name, Instance)>,
    instance_subst_map: HashMap<Name, Instance>,
    decisions: Vec<Branch<'a>>,
    // for backjumping.
    // It extends when a new constraint is queued or a decision is made.
    trail: Vec<TrailElement>,
    // only used in find_conflict
    term_constraints: Vec<(LocalEnv, Term, Term, Error)>,
    // only used in find_conflict
    type_constraints: Vec<(Type, Type, Error)>,
    // only used in find_conflict
    class_constraints: Vec<(LocalEnv, Name, Class, Error)>,
}

impl<'a> Elaborator<'a> {
    pub fn new(
        proof_env: proof::Env<'a>,
        tt_local_env: &'a mut tt::LocalEnv,
        term_holes: Vec<(Name, Type)>,
    ) -> Self {
        Elaborator {
            proof_env,
            tt_local_env,
            term_holes,
            instance_holes: Default::default(),
            local_axioms: Default::default(),
            type_constraints: Default::default(),
            term_constraints: Default::default(),
            class_constraints: Default::default(),
            queue_delta: Default::default(),
            queue_qp: Default::default(),
            queue_fr: Default::default(),
            queue_ff: Default::default(),
            queue_class: Default::default(),
            queue_postponed: Default::default(),
            watch_list: Default::default(),
            type_watch_list: Default::default(),
            instance_watch_list: Default::default(),
            subst: Default::default(),
            subst_map: Default::default(),
            type_subst: Default::default(),
            type_subst_map: Default::default(),
            instance_subst: Default::default(),
            instance_subst_map: Default::default(),
            decisions: Default::default(),
            trail: Default::default(),
        }
    }

    fn visit_type(&self, t: &Type) -> anyhow::Result<Kind> {
        match t {
            Type::Const(t) => {
                let Some(kind) = self.proof_env.tt_env.type_const_table.get(t) else {
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
            // no higher-kinded polymorphism
            Type::Hole(_) => Ok(Kind::base()),
        }
    }

    // generate a fresh hole of form `?M l₁ ⋯ lₙ` where l₁ ⋯ lₙ are the local variables
    fn mk_term_hole(&mut self, ty: Type) -> Term {
        let mut hole_ty = ty;
        hole_ty.arrow(
            self.tt_local_env
                .locals
                .iter()
                .map(|local| local.ty.clone()),
        );
        let hole = Name::fresh();
        self.term_holes.push((hole, hole_ty));
        let mut target = Term::Hole(hole);
        target.apply(
            self.tt_local_env
                .locals
                .iter()
                .map(|local| mk_local(local.name)),
        );
        target
    }

    fn visit_term(&mut self, m: &mut Term) -> anyhow::Result<Type> {
        match m {
            &mut Term::Local(m) => {
                for local in &self.tt_local_env.locals {
                    if local.name == m {
                        return Ok(local.ty.clone());
                    }
                }
                bail!("unknown local variable: {m}");
            }
            Term::Hole(m) => {
                for (local, ty) in &self.term_holes {
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

                let x = Parameter {
                    name: Name::fresh_from(binder_name),
                    ty: arg_ty.clone(),
                };
                body.open(&mk_local(x.name));
                self.tt_local_env.locals.push(x);
                let body_ty = self.visit_term(body)?;
                let x = self.tt_local_env.locals.pop().unwrap();
                body.close(x.name);

                Ok(mk_type_arrow(arg_ty.clone(), body_ty))
            }
            Term::App(m) => {
                let TermApp { fun, arg } = Arc::make_mut(m);

                let fun_ty = self.visit_term(fun)?;
                let arg_ty = self.visit_term(arg)?;
                let ret_ty = mk_fresh_type_hole();

                let error = Error::Visit(format!("not an arrow: {}", fun_ty));
                self.type_constraints
                    .push((fun_ty, mk_type_arrow(arg_ty, ret_ty.clone()), error));

                Ok(ret_ty)
            }
            Term::Const(n) => {
                let Some(Const {
                    local_types,
                    local_classes,
                    ty,
                }) = self.proof_env.tt_env.const_table.get(&n.name)
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
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, &n.ty_args) {
                    type_subst.push((x, t.clone()));
                }
                if local_classes.len() != n.instances.len() {
                    bail!("number of class instances mismatch");
                }
                for (instance, local_class) in zip(&n.instances, local_classes) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    self.visit_instance(instance, &local_class)?;
                }
                let mut ty = ty.clone();
                ty.subst(&type_subst);
                Ok(ty)
            }
        }
    }

    // class is trusted
    fn visit_instance(&mut self, instance: &Instance, class: &Class) -> anyhow::Result<()> {
        match instance {
            Instance::Local(instance) => {
                if !self.tt_local_env.local_classes.contains(instance) {
                    bail!("local class not found");
                }
                if instance != class {
                    bail!("class mismatch");
                }
                Ok(())
            }
            Instance::Global(instance) => {
                let InstanceGlobal {
                    name,
                    ty_args,
                    args,
                } = &**instance;
                let Some(ClassInstance {
                    local_types,
                    local_classes,
                    target,
                    method_table: _,
                }) = self.proof_env.tt_env.class_instance_table.get(name)
                else {
                    bail!("class rule not found");
                };
                if ty_args.len() != local_types.len() {
                    bail!("number of type variables mismatch");
                }
                for ty_arg in ty_args {
                    let ty_arg_kind = self.visit_type(ty_arg)?;
                    if !ty_arg_kind.is_base() {
                        bail!("expected Type, but got {ty_arg_kind}");
                    }
                }
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, ty_args) {
                    type_subst.push((x, t.clone()));
                }
                if args.len() != local_classes.len() {
                    bail!("number of class instances mismatch");
                }
                for (instance, local_class) in zip(args, local_classes) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    self.visit_instance(instance, &local_class)?;
                }
                let mut target = target.clone();
                target.subst(&type_subst);
                if target != *class {
                    bail!("class mismatch");
                }
                Ok(())
            }
            &Instance::Hole(instance) => {
                if let Some((_, c)) = self
                    .instance_holes
                    .iter()
                    .find(|&&(hole, _)| hole == instance)
                {
                    if c != class {
                        bail!("class mismatch");
                    }
                    return Ok(());
                }
                self.instance_holes.push((instance, class.clone()));
                let error = Error::Visit(format!("could not synthesize instance: {}", instance));
                self.class_constraints.push((
                    self.tt_local_env.clone(),
                    instance,
                    class.clone(),
                    error,
                ));
                Ok(())
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) -> anyhow::Result<Term> {
        match expr {
            Expr::Assump(expr) => {
                let ExprAssump { target } = Arc::make_mut(expr);

                let target_ty = self.visit_term(target)?;
                let error = Error::Visit(format!("not a proposition: {}", target_ty));
                self.type_constraints
                    .push((target_ty, mk_type_prop(), error));

                let mut found = false;
                for local in &self.local_axioms {
                    // don't need strict check here
                    if local.maybe_alpha_eq(target) {
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
                let ExprAssume { local_axiom, expr } = Arc::make_mut(expr);

                let local_axiom_ty = self.visit_term(local_axiom)?;
                let error = Error::Visit(format!("not a proposition: {}", local_axiom_ty));
                self.type_constraints
                    .push((local_axiom_ty, mk_type_prop(), error));

                self.local_axioms.push(local_axiom.clone());
                let mut target = self.visit_expr(expr)?;
                let p = self.local_axioms.pop().unwrap();
                target.guard([p]);

                Ok(target)
            }
            Expr::App(expr) => {
                let ExprApp { expr1, expr2 } = Arc::make_mut(expr);

                let fun = self.visit_expr(expr1)?;
                let arg = self.visit_expr(expr2)?;

                let ret = self.mk_term_hole(mk_type_prop());

                let mut target = ret.clone();
                target.guard([arg]);
                self.term_constraints.push((
                    self.tt_local_env.clone(),
                    fun,
                    target.clone(),
                    Error::Visit(format!("not an implication: {}", expr1)),
                ));

                *expr1 = mk_expr_change(target, mem::take(expr1));

                Ok(ret)
            }
            Expr::Take(expr) => {
                let &mut ExprTake {
                    name,
                    ref mut ty,
                    ref mut expr,
                } = Arc::make_mut(expr);

                let ty_kind = self.visit_type(ty)?;
                if !ty_kind.is_base() {
                    bail!("expected Type, but got {ty_kind}");
                }

                let x = Parameter {
                    name,
                    ty: ty.clone(),
                };
                self.tt_local_env.locals.push(x);
                let mut target = self.visit_expr(expr)?;
                let x = self.tt_local_env.locals.pop().unwrap();

                target.generalize(&[x]);

                Ok(target)
            }
            Expr::Inst(expr) => {
                let ExprInst { expr, arg } = Arc::make_mut(expr);

                let forall = self.visit_expr(expr)?;
                let arg_ty = self.visit_term(arg)?;

                let pred = self.mk_term_hole(mk_type_arrow(arg_ty.clone(), mk_type_prop()));

                let mut target = mk_const(
                    Name::intern("forall").unwrap(),
                    vec![arg_ty.clone()],
                    vec![],
                );
                target.apply([pred.clone()]);
                self.term_constraints.push((
                    self.tt_local_env.clone(),
                    forall,
                    target.clone(),
                    Error::Visit(format!("not a forall: {}", expr)),
                ));

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
                }) = self.proof_env.axiom_table.get(&e.name)
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
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, &e.ty_args) {
                    type_subst.push((x, t.clone()));
                }
                if local_classes.len() != e.instances.len() {
                    bail!("number of class instances mismatch");
                }
                let mut instance_subst = vec![];
                for (instance, local_class) in zip(&e.instances, local_classes) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    self.visit_instance(instance, &local_class)?;
                    instance_subst.push((local_class, instance.clone()));
                }
                let mut target = target.clone();
                target.subst_type(&type_subst);
                target.subst_instance(&instance_subst);
                Ok(target)
            }
            Expr::Change(expr) => {
                let ExprChange { target, expr } = Arc::make_mut(expr);

                let target_ty = self.visit_term(target)?;
                let error = Error::Visit(format!("not a proposition: {}", target_ty));
                self.type_constraints
                    .push((target_ty, mk_type_prop(), error));
                let expr_prop = self.visit_expr(expr)?;
                self.term_constraints.push((
                    self.tt_local_env.clone(),
                    expr_prop.clone(),
                    target.clone(),
                    Error::Visit(format!("propositions mismatch in change: {}", expr)),
                ));

                Ok(target.clone())
            }
        }
    }

    #[cfg(debug_assertions)]
    fn print_state(&self) {
        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
        println!("{sp}+current state");
        if !self.term_constraints.is_empty() {
            println!("{sp}| term_constraints:");
            for (_, left, right, _) in &self.term_constraints {
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
            self.watch_list
                .entry(left_head)
                .or_default()
                .push(c.clone());
        }
        if let &Term::Hole(right_head) = c.right.head() {
            self.watch_list
                .entry(right_head)
                .or_default()
                .push(c.clone());
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

    fn watch_type(&mut self, c: &Rc<ClassConstraint>) {
        let &hole = c.class.holes().first().unwrap();
        self.type_watch_list
            .entry(hole)
            .or_default()
            .push(c.clone());
    }

    fn unwatch_type(&mut self, c: &Rc<ClassConstraint>) {
        let &hole = c.class.holes().first().unwrap();
        let type_watch_list = self.type_watch_list.get_mut(&hole).unwrap();
        let mut index = 0;
        for i in (0..type_watch_list.len()).rev() {
            if Rc::ptr_eq(&type_watch_list[i], c) {
                index = i;
                break;
            }
        }
        type_watch_list.swap_remove(index);
    }

    fn watch_instance(&mut self, c: Rc<EqConstraint>) {
        if let Term::Const(left_head) = c.left.head() {
            if self.proof_env.tt_env.has_kappa(left_head.name) {
                if let &Instance::Hole(hole) = &left_head.instances[0] {
                    self.instance_watch_list
                        .entry(hole)
                        .or_default()
                        .push(c.clone());
                    // we don't need to watch the right head.
                    return;
                }
            }
        }
        if let Term::Const(right_head) = c.right.head() {
            if self.proof_env.tt_env.has_kappa(right_head.name) {
                if let &Instance::Hole(hole) = &right_head.instances[0] {
                    self.instance_watch_list
                        .entry(hole)
                        .or_default()
                        .push(c.clone());
                }
            }
        }
    }

    fn unwatch_instance(&mut self, c: &Rc<EqConstraint>) {
        if let Term::Const(left_head) = c.left.head() {
            if self.proof_env.tt_env.has_kappa(left_head.name) {
                if let Instance::Hole(hole) = &left_head.instances[0] {
                    let instance_watch_list = self.instance_watch_list.get_mut(hole).unwrap();
                    let mut index = 0;
                    for i in (0..instance_watch_list.len()).rev() {
                        if Rc::ptr_eq(&instance_watch_list[i], c) {
                            index = i;
                            break;
                        }
                    }
                    instance_watch_list.swap_remove(index);
                    return;
                }
            }
        }
        if let Term::Const(right_head) = c.right.head() {
            if self.proof_env.tt_env.has_kappa(right_head.name) {
                if let Instance::Hole(hole) = &right_head.instances[0] {
                    let instance_watch_list = self.instance_watch_list.get_mut(hole).unwrap();
                    let mut index = 0;
                    for i in (0..instance_watch_list.len()).rev() {
                        if Rc::ptr_eq(&instance_watch_list[i], c) {
                            index = i;
                            break;
                        }
                    }
                    instance_watch_list.swap_remove(index);
                }
            }
        }
    }

    fn occur_check(&self, m: &Term, hole: Name) -> bool {
        match m {
            Term::Var(_) => true,
            Term::Abs(m) => self.occur_check(&m.body, hole),
            Term::App(m) => self.occur_check(&m.fun, hole) && self.occur_check(&m.arg, hole),
            Term::Local(_) => true,
            Term::Const(_) => true,
            &Term::Hole(name) => {
                if name == hole {
                    return false;
                }
                let Some(target) = self.subst_map.get(&name) else {
                    return true;
                };
                self.occur_check(target, hole)
            }
        }
    }

    // Performs instantiation one step.
    // Note that the result term may contain redex in head
    fn inst_head(&self, m: &mut Term) -> bool {
        if let &Term::Hole(m_head) = m.head() {
            if let Some(target) = self.subst_map.get(&m_head) {
                *m.head_mut() = target.clone();
                return true;
            }
        }
        false
    }

    fn inst_type_head(&self, ty: &mut Type) -> bool {
        let Type::Hole(name) = ty else {
            return false;
        };
        let Some(target) = self.type_subst_map.get(name).cloned() else {
            return false;
        };
        *ty = target;
        true
    }

    fn inst_recv(&self, m: &mut TermConst) {
        assert!(self.proof_env.tt_env.has_kappa(m.name));
        let Instance::Hole(hole) = &mut m.instances[0] else {
            return;
        };
        let Some(instance) = self.instance_subst_map.get(hole).cloned() else {
            return;
        };
        m.instances[0] = instance;
    }

    // TODO: rename to try_reduce_to_pattern or something.
    fn inst_arg_head(&self, m: &mut Term) {
        for arg in &mut m.args_mut() {
            arg.whnf();
            while self.inst_head(arg) {
                if arg.whnf().is_none() {
                    break;
                }
            }
        }
    }

    fn fully_inst(&self, m: &mut Term) {
        match m {
            Term::Var(_) => {}
            Term::Abs(m) => {
                let TermAbs {
                    binder_name: _,
                    binder_type,
                    body,
                } = Arc::make_mut(m);
                self.fully_inst_type(binder_type);
                self.fully_inst(body);
            }
            Term::App(m) => {
                let TermApp { fun, arg } = Arc::make_mut(m);
                self.fully_inst(fun);
                self.fully_inst(arg);
            }
            Term::Local(_) => {}
            Term::Const(m) => {
                let TermConst {
                    name: _,
                    ty_args,
                    instances,
                } = Arc::make_mut(m);
                for ty in ty_args {
                    self.fully_inst_type(ty);
                }
                for instance in instances {
                    self.fully_inst_instance(instance);
                }
            }
            Term::Hole(name) => {
                let Some(target) = self.subst_map.get(name) else {
                    return;
                };
                *m = target.clone();
                self.fully_inst(m);
            }
        }
    }

    fn fully_inst_type(&self, t: &mut Type) {
        match t {
            Type::Const(_) => {}
            Type::Arrow(t) => {
                let TypeArrow { dom, cod } = Arc::make_mut(t);
                self.fully_inst_type(dom);
                self.fully_inst_type(cod);
            }
            Type::App(t) => {
                let TypeApp { fun, arg } = Arc::make_mut(t);
                self.fully_inst_type(fun);
                self.fully_inst_type(arg);
            }
            Type::Local(_) => {}
            Type::Hole(name) => {
                let Some(a) = self.type_subst_map.get(name).cloned() else {
                    return;
                };
                *t = a;
                self.fully_inst_type(t);
            }
        }
    }

    fn fully_inst_class(&self, class: &mut Class) {
        for arg in &mut class.args {
            self.fully_inst_type(arg);
        }
    }

    fn fully_inst_instance(&self, instance: &mut Instance) {
        match instance {
            Instance::Local(class) => {
                self.fully_inst_class(class);
            }
            Instance::Global(instance) => {
                let InstanceGlobal {
                    name: _,
                    ty_args,
                    args,
                } = Arc::make_mut(instance);
                for ty_arg in ty_args {
                    self.fully_inst_type(ty_arg);
                }
                for arg in args {
                    self.fully_inst_instance(arg);
                }
            }
            Instance::Hole(name) => {
                let Some(target) = self.instance_subst_map.get(name) else {
                    return;
                };
                *instance = target.clone();
                self.fully_inst_instance(instance);
            }
        }
    }

    fn fully_inst_expr(&self, expr: &mut Expr) {
        match expr {
            Expr::Assump(expr) => {
                let ExprAssump { target } = Arc::make_mut(expr);
                self.fully_inst(target);
            }
            Expr::Assume(expr) => {
                let ExprAssume { local_axiom, expr } = Arc::make_mut(expr);
                self.fully_inst(local_axiom);
                self.fully_inst_expr(expr);
            }
            Expr::App(expr) => {
                let ExprApp { expr1, expr2 } = Arc::make_mut(expr);
                self.fully_inst_expr(expr1);
                self.fully_inst_expr(expr2);
            }
            Expr::Take(expr) => {
                let ExprTake { name: _, ty, expr } = Arc::make_mut(expr);
                self.fully_inst_type(ty);
                self.fully_inst_expr(expr);
            }
            Expr::Inst(expr) => {
                let ExprInst { expr, arg } = Arc::make_mut(expr);
                self.fully_inst_expr(expr);
                self.fully_inst(arg);
            }
            Expr::Const(expr) => {
                let ExprConst {
                    name: _,
                    ty_args,
                    instances,
                } = Arc::make_mut(expr);
                for ty in ty_args {
                    self.fully_inst_type(ty);
                }
                for instance in instances {
                    self.fully_inst_instance(instance);
                }
            }
            Expr::Change(expr) => {
                let ExprChange { target, expr } = Arc::make_mut(expr);
                self.fully_inst(target);
                self.fully_inst_expr(expr);
            }
        }
    }

    fn add_type_constraint(&mut self, t1: Type, t2: Type, error: Error) {
        self.type_constraints.push((t1, t2, error));
    }

    fn add_delta_constraint(&mut self, local_env: LocalEnv, left: Term, right: Term, error: Error) {
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!(
                "{sp}new constraint (delta):\n{sp}- {}\n{sp}  {}",
                left, right
            );
        }

        let c = Rc::new(EqConstraint {
            local_env,
            left,
            right,
            error,
        });
        self.trail
            .push(TrailElement::EqConstraint(c.clone(), ConstraintKind::Delta));
        self.queue_delta.push_back(c.clone());
    }

    fn add_flex_constraint(
        &mut self,
        local_env: LocalEnv,
        mut left: Term,
        mut right: Term,
        error: Error,
    ) {
        self.inst_arg_head(&mut left);
        self.inst_arg_head(&mut right);
        let kind;
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
            left,
            right,
            error,
        });

        self.trail.push(TrailElement::EqConstraint(c.clone(), kind));

        assert!(!self.is_resolved_constraint(&c));

        match kind {
            ConstraintKind::QuasiPattern => {
                self.queue_qp.push_back(c.clone());
            }
            ConstraintKind::FlexRigid => {
                self.queue_fr.push_back(c.clone());
            }
            ConstraintKind::FlexFlex => {
                self.queue_ff.push_back(c.clone());
            }
            ConstraintKind::Delta | ConstraintKind::Postponed => unreachable!(),
        }

        self.watch(c);
    }

    fn add_postponed_constraint(
        &mut self,
        local_env: LocalEnv,
        left: Term,
        right: Term,
        error: Error,
    ) {
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!(
                "{sp}new constraint (postponed):\n{sp}- {}\n{sp}  {}",
                left, right
            );
        }

        let c = Rc::new(EqConstraint {
            local_env,
            left,
            right,
            error,
        });
        self.trail.push(TrailElement::EqConstraint(
            c.clone(),
            ConstraintKind::Postponed,
        ));
        self.queue_postponed.push_back(c.clone());
        self.watch_instance(c);
    }

    fn add_class_constraint(
        &mut self,
        local_env: LocalEnv,
        hole: Name,
        class: Class,
        error: Error,
    ) {
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!(
                "{sp}new constraint (class):\n{sp}- {}\n{sp}  {}",
                hole, class
            );
        }

        let c = Rc::new(ClassConstraint {
            local_env,
            hole,
            class,
            error,
        });
        self.trail.push(TrailElement::ClassConstraint(c.clone()));
        self.queue_class.push_back(c.clone());
        self.watch_type(&c);
    }

    fn add_subst(&mut self, name: Name, m: Term, error: Error) {
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}new subst {name} := {m}");
        }

        self.subst.push((name, m.clone()));
        self.subst_map.insert(name, m.clone());

        if let Some(constraints) = self.watch_list.get(&name) {
            for c in constraints {
                // skip constraints already resolved anyway
                if c.left.head().alpha_eq(&Term::Hole(name)) {
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
                let c = (**c).clone();
                self.term_constraints.push((
                    c.local_env,
                    c.left,
                    c.right,
                    mk_error_join(c.error, error.clone()),
                ));
            }
        }
    }

    fn add_type_subst(&mut self, name: Name, ty: Type, error: Error) {
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}new type subst {name} := {ty}");
        }

        self.type_subst.push((name, ty.clone()));
        self.type_subst_map.insert(name, ty.clone());

        if let Some(constraints) = self.type_watch_list.get(&name) {
            for c in constraints {
                let c = (**c).clone();
                self.class_constraints.push((
                    c.local_env,
                    c.hole,
                    c.class,
                    mk_error_join(c.error, error.clone()),
                ));
            }
        }
    }

    fn add_instance_subst(&mut self, name: Name, instance: Instance, error: Error) {
        #[cfg(debug_assertions)]
        {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}new instance subst {name} := {instance}");
        }

        self.instance_subst.push((name, instance.clone()));
        self.instance_subst_map.insert(name, instance.clone());

        if let Some(constraints) = self.instance_watch_list.get(&name) {
            for c in constraints {
                let c = (**c).clone();
                self.term_constraints.push((
                    c.local_env,
                    c.left,
                    c.right,
                    mk_error_join(c.error, error.clone()),
                ));
            }
        }
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

    fn find_conflict_in_types(
        &mut self,
        mut t1: Type,
        mut t2: Type,
        error: Error,
    ) -> Option<Error> {
        if t1 == t2 {
            return None;
        }
        if self.inst_type_head(&mut t1) || self.inst_type_head(&mut t2) {
            self.add_type_constraint(t1, t2, error);
            return None;
        }
        match (t1, t2) {
            (Type::Arrow(inner1), Type::Arrow(inner2)) => {
                let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                self.add_type_constraint(inner1.dom, inner2.dom, error.clone());
                self.add_type_constraint(inner1.cod, inner2.cod, error);
            }
            (Type::App(inner1), Type::App(inner2)) => {
                // Since we have no higher-kinded polymorphism, it is impossible to match the following two types:
                //  ?M₁ t =?= ?M₂ t₁ t₂
                // But such a case is checked and ruled out in the kind checking phase that runs before
                // this unificaiton phase.
                let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                self.add_type_constraint(inner1.fun, inner2.fun, error.clone());
                self.add_type_constraint(inner1.arg, inner2.arg, error);
            }
            (Type::Hole(name), t) | (t, Type::Hole(name)) => {
                let mut t = t.clone();
                self.fully_inst_type(&mut t); // TODO: avoid instantiation
                if t.contains_hole(name) {
                    return Some(error);
                }
                self.add_type_subst(name, t, error);
            }
            (_, _) => {
                return Some(error);
            }
        }
        None
    }

    fn find_conflict_in_terms(
        &mut self,
        mut local_env: LocalEnv,
        mut left: Term,
        mut right: Term,
        error: Error,
    ) -> Option<Error> {
        if left.alpha_eq(&right) {
            return None;
        }
        if let (Term::Abs(l), Term::Abs(r)) = (&mut left, &mut right) {
            self.add_type_constraint(l.binder_type.clone(), r.binder_type.clone(), error.clone());
            let x = Parameter {
                name: Name::fresh(),
                ty: mem::take(&mut Arc::make_mut(l).binder_type),
            };
            Arc::make_mut(l).body.open(&mk_local(x.name));
            Arc::make_mut(r).body.open(&mk_local(x.name));
            local_env.locals.push(x);
            let left = mem::take(&mut Arc::make_mut(l).body);
            let right = mem::take(&mut Arc::make_mut(r).body);
            self.term_constraints.push((local_env, left, right, error));
            return None;
        }
        if left.whnf().is_some() || right.whnf().is_some() {
            self.term_constraints.push((local_env, left, right, error));
            return None;
        }
        if self.inst_head(&mut left) || self.inst_head(&mut right) {
            self.term_constraints.push((local_env, left, right, error));
            return None;
        }
        if left.is_abs() {
            mem::swap(&mut left, &mut right);
        }
        if let Term::Abs(right) = right {
            // solvable only when
            // 1. L is stuck by an unfoldable constant
            // 2. L is stuck by an unassigned hole
            if let Term::Const(left_head) = left.head_mut() {
                if self.proof_env.tt_env.has_kappa(left_head.name) {
                    self.inst_recv(Arc::make_mut(left_head));
                    if left_head.instances[0].is_hole() {
                        self.add_postponed_constraint(local_env, left, Term::Abs(right), error);
                        return None;
                    }
                }
                if self.proof_env.tt_env.unfold_head(&mut left).is_some() {
                    self.term_constraints
                        .push((local_env, left, Term::Abs(right), error));
                    return None;
                } else {
                    return Some(error);
                }
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
                let x = Parameter {
                    name: Name::fresh_from(right.binder_name),
                    ty: right.binder_type,
                };
                let mut right = right.body;
                right.open(&mk_local(x.name));
                left.apply([mk_local(x.name)]);
                local_env.locals.push(x);
                self.term_constraints.push((local_env, left, right, error));
                return None;
            } else {
                return Some(error);
            }
        }
        // then each of the heads can be a local, a const, or a hole
        if let Term::Hole(right_head) = right.head() {
            let right_head = *right_head;
            self.inst_arg_head(&mut right);
            if let Some(args) = right.is_pattern() {
                if self.occur_check(&left, right_head) && left.is_supported_by(&args) {
                    let binders = args
                        .into_iter()
                        .map(|arg| Parameter {
                            name: arg,
                            ty: local_env.get_local(arg).unwrap().clone(),
                        })
                        .collect::<Vec<_>>();
                    left.abs(&binders);
                    self.add_subst(right_head, left, error);
                    return None;
                }
            }
        }
        if let Term::Hole(left_head) = left.head() {
            let left_head = *left_head;
            self.inst_arg_head(&mut left);
            if let Some(args) = left.is_pattern() {
                if self.occur_check(&right, left_head) && right.is_supported_by(&args) {
                    let binders = args
                        .into_iter()
                        .map(|arg| Parameter {
                            name: arg,
                            ty: local_env.get_local(arg).unwrap().clone(),
                        })
                        .collect::<Vec<_>>();
                    right.abs(&binders);
                    self.add_subst(left_head, right, error);
                    return None;
                }
            }
        }
        if right.head().is_hole() || left.head().is_hole() {
            self.add_flex_constraint(local_env, left, right, error);
            return None;
        }
        // then each of the heads can be a local or a const.
        if let (Term::Local(left_head), Term::Local(right_head)) = (left.head(), right.head()) {
            if left_head != right_head {
                return Some(error);
            }
            let left_args = left.unapply();
            let right_args = right.unapply();
            if left_args.len() != right_args.len() {
                return Some(error);
            }
            for (left_arg, right_arg) in left_args.into_iter().zip(right_args.into_iter()).rev() {
                self.term_constraints
                    .push((local_env.clone(), left_arg, right_arg, error.clone()));
            }
            return None;
        }
        if right.head().is_local() {
            mem::swap(&mut left, &mut right);
        }
        if let (&Term::Local(left_head), Term::Const(right_head)) = (left.head(), right.head_mut())
        {
            if self.proof_env.tt_env.has_kappa(right_head.name) {
                self.inst_recv(Arc::make_mut(right_head));
                if right_head.instances[0].is_hole() {
                    self.add_postponed_constraint(local_env, left, right, error);
                    return None;
                }
            }
            if !right.contains_local(left_head) {
                return Some(error);
            }
            if self.proof_env.tt_env.unfold_head(&mut right).is_some() {
                self.term_constraints.push((local_env, left, right, error));
                return None;
            }
            return Some(error);
        }
        let (Term::Const(left_head), Term::Const(right_head)) = (left.head_mut(), right.head_mut())
        else {
            unreachable!()
        };
        if self.proof_env.tt_env.has_kappa(left_head.name) {
            self.inst_recv(Arc::make_mut(left_head));
            if left_head.instances[0].is_hole() {
                self.add_postponed_constraint(local_env, left, right, error);
                return None;
            }
            if self.proof_env.tt_env.unfold_head(&mut left).is_some() {
                self.term_constraints
                    .push((local_env.clone(), left, right, error));
                return None;
            }
        }
        if self.proof_env.tt_env.has_kappa(right_head.name) {
            self.inst_recv(Arc::make_mut(right_head));
            if right_head.instances[0].is_hole() {
                self.add_postponed_constraint(local_env, left, right, error);
                return None;
            }
            if self.proof_env.tt_env.unfold_head(&mut right).is_some() {
                self.term_constraints
                    .push((local_env.clone(), left, right, error));
                return None;
            }
        }
        let (Term::Const(left_head), Term::Const(right_head)) = (left.head(), right.head()) else {
            unreachable!()
        };
        if left_head.name == right_head.name {
            if self.proof_env.tt_env.has_delta(left_head.name) {
                // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ) where f is unfoldable
                self.add_delta_constraint(local_env, left, right, error);
                return None;
            }
            // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ) where f is not unfoldable.
            for (t1, t2) in left_head.ty_args.iter().zip(right_head.ty_args.iter()) {
                self.add_type_constraint(t1.clone(), t2.clone(), error.clone());
            }
            let left_args = left.unapply();
            let right_args = right.unapply();
            if left_args.len() != right_args.len() {
                return Some(error);
            }
            for (left_arg, right_arg) in left_args.into_iter().zip(right_args.into_iter()).rev() {
                self.term_constraints
                    .push((local_env.clone(), left_arg, right_arg, error.clone()));
            }
            return None;
        }
        let left_height = self.proof_env.tt_env.delta_height(left_head.name);
        let right_height = self.proof_env.tt_env.delta_height(right_head.name);
        if left_height == 0 && right_height == 0 {
            // (f t₁ ⋯ tₙ) ≈ (g s₁ ⋯ sₘ) where f and g are both irreducible.
            return Some(error);
        }
        match left_height.cmp(&right_height) {
            std::cmp::Ordering::Greater => {
                self.proof_env.tt_env.unfold_head(&mut left).unwrap();
            }
            std::cmp::Ordering::Less => {
                self.proof_env.tt_env.unfold_head(&mut right).unwrap();
            }
            std::cmp::Ordering::Equal => {
                self.proof_env.tt_env.unfold_head(&mut left).unwrap();
                self.proof_env.tt_env.unfold_head(&mut right).unwrap();
            }
        }
        self.term_constraints.push((local_env, left, right, error));
        None
    }

    fn resolve_class(&self, local_env: &LocalEnv, class: &Class) -> Option<Instance> {
        for local_class in &local_env.local_classes {
            if local_class == class {
                return Some(Instance::Local(local_class.clone()));
            }
        }
        'next_instance: for (&name, instance) in self.proof_env.tt_env.class_instance_table {
            let ClassInstance {
                local_types,
                local_classes,
                target,
                method_table: _,
            } = instance;
            let mut type_subst = vec![];
            for &local_type in local_types {
                type_subst.push((local_type, mk_fresh_type_hole()));
            }
            let mut target = target.clone();
            target.subst(&type_subst);
            // TODO: C a ?b ⇒ C ?b c ⇒ C a c
            let Some(subst) = class.matches(&target) else {
                continue;
            };
            let ty_args = type_subst
                .into_iter()
                .map(|(_, ty)| {
                    let mut ty = ty.clone();
                    ty.inst(&subst);
                    ty
                })
                .collect::<Vec<_>>();
            let subst = zip(local_types, &ty_args)
                .map(|(&name, ty)| (name, ty.clone()))
                .collect::<Vec<_>>();
            let mut args = vec![];
            for local_class in local_classes {
                let mut local_class = local_class.clone();
                local_class.subst(&subst);
                let Some(instance) = self.resolve_class(local_env, &local_class) else {
                    continue 'next_instance;
                };
                args.push(instance);
            }
            return Some(mk_instance_global(name, ty_args, args));
        }
        None
    }

    fn find_conflict_in_class(
        &mut self,
        local_env: LocalEnv,
        hole: Name,
        mut class: Class,
        error: Error,
    ) -> Option<Error> {
        self.fully_inst_class(&mut class);
        // TODO: infer a type class instance for a class like (C a ?b).
        if !class.is_ground() {
            self.add_class_constraint(local_env, hole, class, error);
            return None;
        }
        let Some(instance) = self.resolve_class(&local_env, &class) else {
            return Some(error);
        };
        self.add_instance_subst(hole, instance, error);
        None
    }

    fn find_conflict(&mut self) -> Option<Error> {
        #[cfg(debug_assertions)]
        {
            self.print_state();
        }
        while !self.type_constraints.is_empty()
            || !self.class_constraints.is_empty()
            || !self.term_constraints.is_empty()
        {
            if let Some((t1, t2, error)) = self.type_constraints.pop() {
                #[cfg(debug_assertions)]
                {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}find conflict in {t1} =?= {t2}");
                }
                if let Some(error) = self.find_conflict_in_types(t1, t2, error) {
                    #[cfg(debug_assertions)]
                    {
                        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                        println!("{sp}conflict in types");
                    }
                    return Some(error);
                }
                continue;
            }
            if let Some((local_env, hole, ty, error)) = self.class_constraints.pop() {
                if let Some(error) = self.find_conflict_in_class(local_env, hole, ty, error) {
                    return Some(error);
                }
                continue;
            }
            if let Some((local_env, m1, m2, error)) = self.term_constraints.pop() {
                #[cfg(debug_assertions)]
                {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}find conflict in {m1} =?= {m2}");
                }
                if let Some(error) = self.find_conflict_in_terms(local_env, m1, m2, error) {
                    #[cfg(debug_assertions)]
                    {
                        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                        println!("{sp}conflict in terms");
                    }
                    return Some(error);
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
            instance_subst_len: self.instance_subst.len(),
        }
    }

    fn restore(&mut self, snapshot: &Snapshot) {
        for _ in 0..self.trail.len() - snapshot.trail_len {
            match self.trail.pop().unwrap() {
                TrailElement::EqConstraint(c, kind) => match kind {
                    ConstraintKind::Postponed => {
                        self.queue_postponed.pop_back();
                        self.unwatch_instance(&c);
                    }
                    ConstraintKind::Delta => {
                        self.queue_delta.pop_back();
                    }
                    ConstraintKind::QuasiPattern => {
                        self.queue_qp.pop_back();
                        self.unwatch(&c);
                    }
                    ConstraintKind::FlexRigid => {
                        self.queue_fr.pop_back();
                        self.unwatch(&c);
                    }
                    ConstraintKind::FlexFlex => {
                        self.queue_ff.pop_back();
                        self.unwatch(&c);
                    }
                },
                TrailElement::ClassConstraint(c) => {
                    self.queue_class.pop_back();
                    self.unwatch_type(&c);
                }
            }
        }
        for _ in 0..self.subst.len() - snapshot.subst_len {
            let name = self.subst.pop().unwrap().0;
            self.subst_map.remove(&name);
        }
        for _ in 0..self.type_subst.len() - snapshot.type_subst_len {
            let name = self.type_subst.pop().unwrap().0;
            self.type_subst_map.remove(&name);
        }
        for _ in 0..self.instance_subst.len() - snapshot.instance_subst_len {
            let name = self.instance_subst.pop().unwrap().0;
            self.instance_subst_map.remove(&name);
        }
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
                    ConstraintKind::Postponed => {
                        self.queue_postponed.push_front(c);
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
        for (x, m, error) in node.subst.into_iter().rev() {
            self.add_subst(x, m, error);
        }
        for (left, right, error) in node.type_constraints.into_iter().rev() {
            self.type_constraints.push((left, right, error));
        }
        for (local_env, left, right, error) in node.term_constraints.into_iter().rev() {
            self.term_constraints.push((local_env, left, right, error));
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
                node.type_constraints
                    .push((t1.clone(), t2.clone(), c.error.clone()));
            }
            for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
                node.term_constraints.push((
                    c.local_env.clone(),
                    left_arg.clone(),
                    right_arg.clone(),
                    c.error.clone(),
                ));
            }
            node
        };
        // Try second ((unfold f) t₁ ⋯ tₙ ≈ (unfold f) s₁ ⋯ sₙ)
        let node2 = {
            let mut node = Node::default();
            let mut left = c.left.clone();
            let mut right = c.right.clone();
            self.proof_env.tt_env.unfold_head(&mut left).unwrap();
            self.proof_env.tt_env.unfold_head(&mut right).unwrap();
            node.term_constraints
                .push((c.local_env.clone(), left, right, c.error.clone()));
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
            self.fully_inst_type(&mut t); // TODO: avoid full instantiation
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
            .map(|&t| Parameter {
                name: Name::fresh(),
                ty: t.clone(),
            })
            .collect::<Vec<_>>();
        assert_eq!(new_binders.len(), left_args.len());

        // Projection step.
        //
        //   M ↦ λ z[1] .. z[p], z[i] (Y[1] z[1] .. z[p]) .. (Y[m] z[1] .. z[p])
        //
        // where τ(z[i]) = t₁ → ⋯ → tₘ → τ(@ u[1] .. u[q]).
        // We try projection first because projection yields more general solutions.
        for z in &new_binders {
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

            if z.ty.components().len() < left_ty.components().len() {
                continue;
            }
            let m = z.ty.components().len() - left_ty.components().len();

            let mut t = z.ty.target().clone();
            t.arrow(z.ty.components().into_iter().skip(m).cloned());

            // Y[1] .. Y[m]
            let arg_holes =
                z.ty.components()
                    .iter()
                    .take(m)
                    .map(|&arg_ty| {
                        let new_hole = Name::fresh();
                        let mut ty = arg_ty.clone();
                        ty.arrow(new_binders.iter().map(|z| z.ty.clone()));
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
                    arg.apply(new_binders.iter().map(|z| mk_local(z.name)));
                    arg
                })
                .collect::<Vec<_>>();

            // TODO: try eta equal condidates when the hole ?M is used twice or more among the whole set of constraints.
            let mut target = mk_local(z.name);
            target.apply(new_args);
            target.abs(&new_binders);
            nodes.push(Node {
                subst: vec![(left_head, target, c.error.clone())],
                type_constraints: vec![(t, left_ty.clone(), c.error.clone())],
                term_constraints: vec![(
                    c.local_env.clone(),
                    c.left.clone(),
                    c.right.clone(),
                    c.error.clone(),
                )], // TODO: optimize
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
                let Const {
                    local_types,
                    local_classes: _,
                    ty,
                } = self
                    .proof_env
                    .tt_env
                    .const_table
                    .get(&right_head.name)
                    .unwrap();
                let mut subst = vec![];
                for (&x, t) in zip(local_types, &right_head.ty_args) {
                    subst.push((x, t.clone()));
                }
                let mut ty = ty.clone();
                ty.subst(&subst);
                self.fully_inst_type(&mut ty); // TODO: avoid full instantiation
                ty
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
                    ty.arrow(new_binders.iter().map(|z| z.ty.clone()));
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
                    arg.apply(new_binders.iter().map(|z| mk_local(z.name)));
                    arg
                })
                .collect::<Vec<_>>();

            // TODO: try eta equal condidates when the hole ?M is used twice or more among the whole set of constraints.
            let mut target = Term::Const(right_head.clone());
            target.apply(new_args);
            target.abs(&new_binders);
            nodes.push(Node {
                subst: vec![(left_head, target, c.error.clone())],
                type_constraints: vec![],
                term_constraints: vec![(
                    c.local_env.clone(),
                    c.left.clone(),
                    c.right.clone(),
                    c.error.clone(),
                )], // TODO: optimize
            });
        }

        nodes
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
            return false;
        };

        self.push_branch(trail_len, Box::new(nodes.into_iter()));
        self.next();
        true
    }

    fn backjump(&mut self) -> bool {
        self.term_constraints.clear();
        self.type_constraints.clear();
        self.class_constraints.clear();
        while !self.next() {
            if !self.pop_branch() {
                return false;
            }
        }
        true
    }

    fn solve(&mut self) -> Result<(), Error> {
        loop {
            while let Some(error) = self.find_conflict() {
                #[cfg(debug_assertions)]
                {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}conflict found!");
                }
                if !self.backjump() {
                    return Err(error);
                }
            }
            #[cfg(debug_assertions)]
            {
                let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                println!("{sp}simplification done");
                self.print_state();
            }
            if !self.decide() {
                return Ok(());
            }
        }
    }
}

pub fn elaborate_type(
    proof_env: proof::Env,
    local_env: &mut LocalEnv,
    target: &Type,
    kind: Kind,
) -> anyhow::Result<()> {
    let elab = Elaborator::new(proof_env, local_env, vec![]);
    let k = elab.visit_type(target)?;
    ensure!(k == kind);
    ensure!(target.is_ground());
    Ok(())
}

// ty is trusted
pub fn elaborate_term(
    proof_env: proof::Env,
    local_env: &mut LocalEnv,
    target: &mut Term,
    ty: &Type,
) -> anyhow::Result<()> {
    #[cfg(debug_assertions)]
    {
        println!("elaborating:\n{target}");
    }

    let mut elab = Elaborator::new(proof_env, local_env, vec![]);

    let t = elab.visit_term(target)?;
    let error = Error::Visit("type mismatch".to_string());
    elab.type_constraints.push((t, ty.clone(), error));

    if let Err(error) = elab.solve() {
        bail!("unification failed: {error}");
    }

    elab.fully_inst(target);

    ensure!(target.is_ground());
    ensure!(target.is_type_ground());

    #[cfg(debug_assertions)]
    {
        println!("elaborated:\n{target}");
    }

    Ok(())
}

// prop is trusted
pub fn elaborate_expr(
    proof_env: proof::Env,
    local_env: &mut LocalEnv,
    term_holes: Vec<(Name, Type)>,
    e: &mut Expr,
    prop: &Term,
) -> anyhow::Result<()> {
    #[cfg(debug_assertions)]
    {
        println!("elaborating:\n{e}");
    }

    let mut elab = Elaborator::new(proof_env, local_env, term_holes);

    *e = mk_expr_change(prop.clone(), mem::take(e));
    elab.visit_expr(e)?;

    if let Err(error) = elab.solve() {
        bail!("unification failed: {error}");
    }

    elab.fully_inst_expr(e);

    ensure!(e.is_ground());
    ensure!(e.is_type_ground());

    #[cfg(debug_assertions)]
    {
        println!("elaborated:\n{e}");
    }

    Ok(())
}

pub fn elaborate_class(
    proof_env: proof::Env,
    local_env: &mut LocalEnv,
    class: &Class,
) -> anyhow::Result<()> {
    let Some(&ClassType { arity }) = proof_env.tt_env.class_predicate_table.get(&class.name) else {
        bail!("class not found");
    };
    if class.args.len() != arity {
        bail!("number of arguments mismatch");
    }
    for arg in &class.args {
        elaborate_type(proof_env.clone(), local_env, arg, Kind::base())?;
    }
    Ok(())
}
