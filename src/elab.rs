use std::{
    collections::{HashMap, VecDeque},
    iter::{repeat_n, zip},
    mem,
    rc::Rc,
    slice,
    sync::Arc,
};

use anyhow::{bail, ensure};

use crate::{
    lex::Span,
    proof::{
        self, Assume, Axiom, Expr, ExprApp, ExprAssume, ExprAssump, ExprChange, ExprConst,
        ExprInst, ExprLetStructure, ExprLetTerm, ExprLocal, ExprTake, LocalAxiom,
        LocalStructureAxiom, LocalStructureConst, LocalStructureField, generalize, guard,
        mk_expr_change, mk_type_prop, ungeneralize1, unguard1,
    },
    tt::{
        self, Class, ClassInstance, ClassType, Const, Id, Instance, InstanceGlobal, Kind, Local,
        LocalDelta, LocalEnv, Name, QualifiedName, Term, TermAbs, TermApp, Type, TypeApp,
        TypeArrow, mk_const, mk_fresh_type_hole, mk_hole, mk_instance_global, mk_instance_local,
        mk_local, mk_type_arrow, mk_type_local,
    },
};

#[derive(Debug, Clone)]
enum Error {
    Visit { message: String, span: Option<Span> },
    Join(Arc<(Error, Error)>),
}

fn visit_error(message: impl Into<String>, span: Option<Span>) -> Error {
    Error::Visit {
        message: message.into(),
        span,
    }
}

fn mk_error_join(e1: Error, e2: Error) -> Error {
    Error::Join(Arc::new((e1, e2)))
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Visit { message, span } => {
                if let Some(span) = span {
                    write!(f, "{}\n{}", message, span)
                } else {
                    write!(f, "{}", message)
                }
            }
            Error::Join(inner) => write!(f, "{}", inner.0),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintKind {
    Unfold,
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
    kind: ConstraintKind,
    error: Error,
}

// m l₁ ⋯ lₙ =?= t, where m is a method of an unresolved instance.
#[derive(Debug, Clone)]
struct MethodConstraint {
    // TODO: only the locals field is used. Use a more efficient data structure.
    local_env: LocalEnv,
    left: Term,
    right: Term,
    error: Error,
}

// ?I : C t₁ ⋯ tₙ
#[derive(Debug, Clone)]
struct ClassConstraint {
    // TODO: only the local_classes field is used. Use a more efficient data structure.
    local_env: LocalEnv,
    hole: Id,
    class: Class,
    error: Error,
}

#[derive(Debug, Clone)]
struct Snapshot {
    trail_len: usize,
}

#[derive(Debug, Default)]
struct Node {
    subst: Vec<(Id, Term, Error)>,
    type_constraints: Vec<(Type, Type, Error)>,
    term_constraints: Vec<(LocalEnv, Term, Term, Error)>,
}

struct Branch<'a> {
    snapshot: Snapshot,
    nodes: Box<dyn Iterator<Item = Node> + 'a>,
}

enum Record {
    AddEqConstraint(Rc<EqConstraint>),
    AddMethodConstraint(Rc<MethodConstraint>),
    AddClassConstraint(Rc<ClassConstraint>),
    AddSubst { id: Id },
    AddTypeSubst { id: Id },
    AddInstanceSubst { id: Id },
    RemoveEqConstraint(Rc<EqConstraint>),
}

struct Elaborator<'a> {
    proof_env: proof::Env<'a>,
    term_holes: Vec<(Id, Type)>,
    // only used in visit
    tt_local_env: &'a mut tt::LocalEnv,
    // only used in visit
    instance_holes: Vec<(Id, Class)>,
    // only used in visit
    local_axioms: Vec<(QualifiedName, LocalAxiom)>,
    // only used in visit
    assumes: Vec<Assume>,

    // only used in find_conflict
    term_constraints: Vec<(LocalEnv, Term, Term, Error)>,
    // only used in find_conflict
    type_constraints: Vec<(Type, Type, Error)>,
    // only used in find_conflict
    class_constraints: Vec<(LocalEnv, Id, Class, Error)>,

    // TODO: resolveされた制約はその場で消したい
    queue_unfold: VecDeque<Rc<EqConstraint>>,
    queue_qp: VecDeque<Rc<EqConstraint>>,
    queue_fr: VecDeque<Rc<EqConstraint>>,
    queue_ff: VecDeque<Rc<EqConstraint>>,
    queue_class: VecDeque<Rc<ClassConstraint>>,
    queue_method: VecDeque<Rc<MethodConstraint>>,

    watch_list: HashMap<Id, Vec<Rc<EqConstraint>>>,
    type_watch_list: HashMap<Id, Vec<Rc<ClassConstraint>>>,
    instance_watch_list: HashMap<Id, Vec<Rc<MethodConstraint>>>,

    // current solution
    subst_map: HashMap<Id, Term>,
    type_subst_map: HashMap<Id, Type>,
    instance_subst_map: HashMap<Id, Instance>,

    decisions: Vec<Branch<'a>>,
    // for backjumping.
    // It extends when a new constraint is queued or a decision is made.
    trail: Vec<Record>,
}

impl<'a> Elaborator<'a> {
    pub fn new(
        proof_env: proof::Env<'a>,
        tt_local_env: &'a mut tt::LocalEnv,
        term_holes: Vec<(Id, Type)>,
    ) -> Self {
        Elaborator {
            proof_env,
            tt_local_env,
            term_holes,
            instance_holes: Default::default(),
            local_axioms: Default::default(),
            assumes: Default::default(),
            type_constraints: Default::default(),
            term_constraints: Default::default(),
            class_constraints: Default::default(),
            queue_unfold: Default::default(),
            queue_qp: Default::default(),
            queue_fr: Default::default(),
            queue_ff: Default::default(),
            queue_class: Default::default(),
            queue_method: Default::default(),
            watch_list: Default::default(),
            type_watch_list: Default::default(),
            instance_watch_list: Default::default(),
            subst_map: Default::default(),
            type_subst_map: Default::default(),
            instance_subst_map: Default::default(),
            decisions: Default::default(),
            trail: Default::default(),
        }
    }

    fn visit_type(&self, t: &Type) -> anyhow::Result<Kind> {
        match t {
            Type::Const(t) => {
                let Some(kind) = self.proof_env.tt_env.type_const_table.get(&t.name) else {
                    bail!("constant type not found");
                };
                Ok(kind.clone())
            }
            Type::Arrow(t) => {
                let TypeArrow {
                    metadata: _,
                    dom,
                    cod,
                } = &**t;
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
                let TypeApp {
                    metadata: _,
                    fun,
                    arg,
                } = &**t;
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
                    if *local_type == t.id {
                        return Ok(Kind::base());
                    }
                }
                bail!("unbound local type: {}", t.id);
            }
            // no higher-kinded polymorphism
            Type::Hole(_) => Ok(Kind::base()),
        }
    }

    // generate a fresh hole of form `?M l₁ ⋯ lₙ` where l₁ ⋯ lₙ are the local variables
    fn mk_term_hole(&mut self, ty: Type) -> Term {
        let locals = self
            .tt_local_env
            .locals
            .iter()
            .filter(|local| self.tt_local_env.get_local_delta(local.id).is_none())
            .collect::<Vec<_>>();
        let hole_ty = ty.arrow(locals.iter().map(|local| local.ty.clone()));
        let hole = Id::fresh();
        self.term_holes.push((hole, hole_ty));
        let mut target = mk_hole(hole);
        target = target.apply(locals.iter().map(|local| mk_local(local.id)));
        target
    }

    fn visit_term(&mut self, m: &Term) -> anyhow::Result<Type> {
        match m {
            Term::Local(inner) => {
                let id = inner.id;
                for local in &self.tt_local_env.locals {
                    if local.id == id {
                        return Ok(local.ty.clone());
                    }
                }
                bail!("unknown local variable: {id}");
            }
            Term::Hole(inner) => {
                for (local, ty) in &self.term_holes {
                    if *local == inner.id {
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
                    metadata: _,
                    binder_type,
                    binder_name: _,
                    body,
                } = &**m;

                let binder_type_kind = self.visit_type(binder_type)?;
                if !binder_type_kind.is_base() {
                    bail!("expected Type, but got {binder_type_kind}");
                }

                let x = Local {
                    id: Id::fresh(),
                    ty: binder_type.clone(),
                };
                let body = body.open(&[mk_local(x.id)], 0);
                self.tt_local_env.locals.push(x);
                let body_ty = self.visit_term(&body)?;
                self.tt_local_env.locals.pop();

                Ok(mk_type_arrow(binder_type.clone(), body_ty))
            }
            Term::App(m) => {
                let TermApp {
                    metadata: _,
                    fun,
                    arg,
                } = &**m;

                let fun_ty = self.visit_term(fun)?;
                let arg_ty = self.visit_term(arg)?;
                let ret_ty = mk_fresh_type_hole();

                let error =
                    visit_error(format!("not an arrow: {}", fun_ty), fun_ty.span().cloned());
                self.push_type_constraint(fun_ty, mk_type_arrow(arg_ty, ret_ty.clone()), error);

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
                let mut type_subst = Vec::with_capacity(local_types.len());
                for (x, t) in zip(local_types, &n.ty_args) {
                    type_subst.push((*x, t.clone()));
                }
                if local_classes.len() != n.instances.len() {
                    bail!("number of class instances mismatch");
                }
                for (instance, local_class) in zip(&n.instances, local_classes) {
                    let local_class = local_class.subst(&type_subst);
                    self.visit_instance(instance, &local_class)?;
                }
                Ok(ty.subst(&type_subst))
            }
        }
    }

    // class is trusted
    fn visit_instance(&mut self, instance: &Instance, class: &Class) -> anyhow::Result<()> {
        match instance {
            Instance::Local(instance) => {
                if !self.tt_local_env.local_classes.contains(&instance.class) {
                    bail!("local class not found");
                }
                if instance.class != *class {
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
                let mut type_subst = Vec::with_capacity(local_types.len());
                for (x, t) in zip(local_types, ty_args) {
                    type_subst.push((*x, t.clone()));
                }
                if args.len() != local_classes.len() {
                    bail!("number of class instances mismatch");
                }
                for (instance, local_class) in zip(args, local_classes) {
                    let local_class = local_class.subst(&type_subst);
                    self.visit_instance(instance, &local_class)?;
                }
                let instantiated_target = target.subst(&type_subst);
                if instantiated_target != *class {
                    bail!("class mismatch");
                }
                Ok(())
            }
            Instance::Hole(instance) => {
                if let Some((_, c)) = self
                    .instance_holes
                    .iter()
                    .find(|&&(hole, _)| hole == instance.id)
                {
                    if c != class {
                        bail!("class mismatch");
                    }
                    return Ok(());
                }
                self.instance_holes.push((instance.id, class.clone()));
                let error = visit_error("could not synthesize instance", None);
                self.class_constraints.push((
                    self.tt_local_env.clone(),
                    instance.id,
                    class.clone(),
                    error,
                ));
                Ok(())
            }
        }
    }

    // TODO: take expr as &Expr
    fn visit_expr(&mut self, expr: &mut Expr) -> anyhow::Result<Term> {
        match expr {
            Expr::Assump(expr) => {
                let ExprAssump {
                    metadata: _,
                    target,
                } = expr.as_mut();

                let target_ty = self.visit_term(target)?;
                let error = visit_error(
                    format!("not a proposition: {}", target_ty),
                    target_ty.span().cloned(),
                );
                self.push_type_constraint(target_ty, mk_type_prop(), error);

                // don't need strict check here
                if !self
                    .assumes
                    .iter()
                    .any(|assume| assume.prop.maybe_alpha_eq(target))
                {
                    bail!("assumption not found: {target}");
                }

                Ok(target.clone())
            }
            Expr::Local(expr) => {
                let ExprLocal { metadata: _, id } = expr.as_ref();

                for assume in self.assumes.iter().rev() {
                    if assume.alias == Some(*id) {
                        return Ok(assume.prop.clone());
                    }
                }
                for (local_name, local_axiom) in self.local_axioms.iter().rev() {
                    if *id == Id::from_qualified_name(local_name) {
                        return Ok(local_axiom.target.clone());
                    }
                }

                bail!("assumption alias not found: {id}");
            }
            Expr::Assume(expr) => {
                let ExprAssume {
                    metadata: _,
                    local_axiom,
                    alias,
                    expr: inner,
                } = expr.as_mut();

                let local_axiom_ty = self.visit_term(local_axiom)?;
                let error = visit_error(
                    format!("not a proposition: {}", local_axiom_ty),
                    local_axiom_ty.span().cloned(),
                );
                self.push_type_constraint(local_axiom_ty, mk_type_prop(), error);

                self.assumes.push(Assume {
                    alias: *alias,
                    prop: local_axiom.clone(),
                });
                let mut target = self.visit_expr(inner)?;
                let p = self.assumes.pop().unwrap();
                target = guard(&target, [p.prop]);

                Ok(target)
            }
            Expr::App(expr) => {
                let ExprApp {
                    metadata: _,
                    expr1,
                    expr2,
                } = expr.as_mut();

                let fun = self.visit_expr(expr1)?;
                let arg = self.visit_expr(expr2)?;

                if let Some((lhs, rhs)) = unguard1(&fun) {
                    let error = visit_error(
                        format!(
                            "argument proposition mismatch: expected {}, but got {}",
                            lhs, arg
                        ),
                        expr2.span().cloned(),
                    );
                    self.push_term_constraint(self.tt_local_env.clone(), lhs.clone(), arg, error);

                    *expr2 = mk_expr_change(lhs, mem::take(expr2));

                    return Ok(rhs);
                }

                let ret = self.mk_term_hole(mk_type_prop());

                let mut target = ret.clone();
                target = guard(&target, [arg]);
                self.push_term_constraint(
                    self.tt_local_env.clone(),
                    fun,
                    target.clone(),
                    visit_error(
                        format!("not an implication: {}", expr1),
                        expr1.span().cloned(),
                    ),
                );

                *expr1 = mk_expr_change(target, mem::take(expr1));

                Ok(ret)
            }
            Expr::Take(expr) => {
                let ExprTake {
                    metadata: _,
                    id,
                    ty,
                    expr: inner,
                } = expr.as_mut();
                let id = *id;

                let ty_kind = self.visit_type(ty)?;
                if !ty_kind.is_base() {
                    bail!("expected Type, but got {ty_kind}");
                }

                let x = Local { id, ty: ty.clone() };
                self.tt_local_env.locals.push(x);
                let mut target = self.visit_expr(inner)?;
                let x = self.tt_local_env.locals.pop().unwrap();

                target = generalize(&target, &[x]);

                Ok(target)
            }
            Expr::Inst(expr) => {
                let ExprInst {
                    metadata: _,
                    expr: inner,
                    arg,
                } = expr.as_mut();

                let forall = self.visit_expr(inner)?;
                let arg_ty = self.visit_term(arg)?;

                if let Some((binder, mut body)) = ungeneralize1(&forall) {
                    let error = visit_error(
                        format!(
                            "type argument mismatch: expected {}, but got {}",
                            binder.ty, arg_ty
                        ),
                        arg.span().cloned(),
                    );
                    self.push_type_constraint(binder.ty, arg_ty, error);
                    body = body.subst(&[(binder.id, arg.clone())]);
                    return Ok(body);
                }

                let hole = self.mk_term_hole(mk_type_arrow(arg_ty.clone(), mk_type_prop()));

                let x = Local {
                    id: Id::fresh(),
                    ty: arg_ty.clone(),
                };
                let mut pred = hole.clone();
                pred = pred.apply([mk_local(x.id)]);
                pred = pred.abs(&[x]);

                let mut target = mk_const(
                    QualifiedName::from_str("forall"),
                    vec![arg_ty.clone()],
                    vec![],
                );
                target = target.apply([pred]);
                self.push_term_constraint(
                    self.tt_local_env.clone(),
                    forall,
                    target.clone(),
                    visit_error(format!("not a forall: {}", inner), inner.span().cloned()),
                );

                *inner = mk_expr_change(target, mem::take(inner));

                let mut ret = hole;
                ret = ret.apply([arg.clone()]);
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
                let mut type_subst = Vec::with_capacity(local_types.len());
                for (x, t) in zip(local_types, &e.ty_args) {
                    type_subst.push((*x, t.clone()));
                }
                if local_classes.len() != e.instances.len() {
                    bail!("number of class instances mismatch");
                }
                let mut instance_subst = vec![];
                for (instance, local_class) in zip(&e.instances, local_classes) {
                    let local_class = local_class.subst(&type_subst);
                    self.visit_instance(instance, &local_class)?;
                    instance_subst.push((local_class, instance.clone()));
                }
                let mut target = target.clone();
                target = target.subst_type(&type_subst);
                target = target.subst_instance(&instance_subst);
                Ok(target)
            }
            Expr::LetTerm(expr) => {
                let ExprLetTerm {
                    metadata: _,
                    name,
                    ty,
                    value,
                    body,
                } = expr.as_mut();

                let value_ty = self.visit_term(value)?;
                let binder_ty = if let Some(ty) = ty {
                    let kind = self.visit_type(ty)?;
                    if !kind.is_base() {
                        bail!("expected Type, but got {kind}");
                    }
                    self.push_type_constraint(
                        ty.clone(),
                        value_ty,
                        visit_error(
                            format!("type mismatch in let binding `{name}`"),
                            value.span().cloned(),
                        ),
                    );
                    ty.clone()
                } else {
                    value_ty
                };

                let local_len = self.tt_local_env.locals.len();
                let local_delta_len = self.tt_local_env.local_deltas.len();
                let id = Id::from_qualified_name(name);
                self.tt_local_env.locals.push(Local { id, ty: binder_ty });
                self.tt_local_env.local_deltas.push(LocalDelta {
                    id,
                    target: value.clone(),
                    height: self.proof_env.tt_env.height(self.tt_local_env, value),
                });
                let result = self.visit_expr(body);
                self.tt_local_env.local_deltas.truncate(local_delta_len);
                self.tt_local_env.locals.truncate(local_len);
                result
            }
            Expr::LetStructure(expr) => {
                let ExprLetStructure {
                    metadata: _,
                    name,
                    fields,
                    body,
                } = expr.as_mut();

                let structure_id = Id::from_name(name);
                let structure_name = QualifiedName::from_str(name.as_str());
                let locals_len = self.tt_local_env.locals.len();
                let mut const_field_names: Vec<Name> = vec![];
                let mut axiom_field_names: Vec<Name> = vec![];

                for field in &*fields {
                    match field {
                        LocalStructureField::Const(LocalStructureConst {
                            name: field_name,
                            ty: field_ty,
                        }) => {
                            for existing in &const_field_names {
                                if existing == field_name {
                                    self.tt_local_env.locals.truncate(locals_len);
                                    bail!("duplicate const field");
                                }
                            }
                            const_field_names.push(field_name.clone());
                            let kind = match self.visit_type(field_ty) {
                                Ok(kind) => kind,
                                Err(err) => {
                                    self.tt_local_env.locals.truncate(locals_len);
                                    return Err(err);
                                }
                            };
                            if !kind.is_base() {
                                self.tt_local_env.locals.truncate(locals_len);
                                bail!("expected Type, but got {kind}");
                            }
                            self.tt_local_env.locals.push(Local {
                                id: Id::from_name(field_name),
                                ty: field_ty.clone(),
                            });
                        }
                        LocalStructureField::Axiom(LocalStructureAxiom {
                            name: field_name,
                            target,
                        }) => {
                            for existing in &axiom_field_names {
                                if existing == field_name {
                                    self.tt_local_env.locals.truncate(locals_len);
                                    bail!("duplicate axiom field");
                                }
                            }
                            axiom_field_names.push(field_name.clone());
                            let target_ty = match self.visit_term(target) {
                                Ok(target_ty) => target_ty,
                                Err(err) => {
                                    self.tt_local_env.locals.truncate(locals_len);
                                    return Err(err);
                                }
                            };
                            let error = visit_error(
                                format!("not a proposition: {}", target_ty),
                                target_ty.span().cloned(),
                            );
                            self.push_type_constraint(target_ty, mk_type_prop(), error);
                        }
                    }
                }
                self.tt_local_env.locals.truncate(locals_len);

                let this_ty = mk_type_local(structure_id);
                let this = Local {
                    id: Id::fresh_with_name(Name::from_str("this")),
                    ty: this_ty.clone(),
                };
                let mut locals: Vec<Local> = vec![];
                let mut local_axioms: Vec<(QualifiedName, LocalAxiom)> = vec![];
                let mut subst = vec![];

                for field in &*fields {
                    match field {
                        LocalStructureField::Const(LocalStructureConst {
                            name: field_name,
                            ty,
                        }) => {
                            let fullname = structure_name.extend(field_name.as_str());
                            let id = Id::from_qualified_name(&fullname);
                            let ty = ty.arrow([this_ty.clone()]);
                            locals.push(Local { id, ty });

                            let mut target = mk_local(id);
                            target = target.apply([mk_local(this.id)]);
                            subst.push((Id::from_name(field_name), target));
                        }
                        LocalStructureField::Axiom(LocalStructureAxiom {
                            name: field_name,
                            target,
                        }) => {
                            let fullname = structure_name.extend(field_name.as_str());
                            let mut target = target.clone();
                            target = target.subst(&subst);
                            target = generalize(&target, slice::from_ref(&this));
                            local_axioms.push((fullname, LocalAxiom { target }));
                        }
                    }
                }

                let abs_name = structure_name.extend("abs");
                let mut params = vec![];
                let mut guards = vec![];
                let mut chars = vec![];
                let mut abs_subst = vec![];
                for field in &*fields {
                    match field {
                        LocalStructureField::Const(LocalStructureConst {
                            name: field_name,
                            ty,
                        }) => {
                            let param = Local {
                                id: Id::fresh_with_name(field_name.clone()),
                                ty: ty.clone(),
                            };

                            let fullname = structure_name.extend(field_name.as_str());
                            let id = Id::from_qualified_name(&fullname);
                            let mut rhs = mk_local(id);
                            rhs = rhs.apply([mk_local(this.id)]);

                            let mut char =
                                mk_const(QualifiedName::from_str("eq"), vec![ty.clone()], vec![]);
                            char = char.apply([mk_local(param.id), rhs]);
                            chars.push(char);

                            abs_subst.push((Id::from_name(field_name), mk_local(param.id)));
                            params.push(param);
                        }
                        LocalStructureField::Axiom(LocalStructureAxiom { target, .. }) => {
                            let mut target = target.clone();
                            target = target.subst(&abs_subst);
                            guards.push(target);
                        }
                    }
                }

                let mut abs = mk_const(
                    QualifiedName::from_str("uexists"),
                    vec![this_ty.clone()],
                    vec![],
                );
                abs = abs.apply([{
                    let mut char = chars
                        .into_iter()
                        .reduce(|left, right| {
                            let mut conj = mk_const(QualifiedName::from_str("and"), vec![], vec![]);
                            conj = conj.apply([left, right]);
                            conj
                        })
                        .unwrap_or_else(|| {
                            mk_const(QualifiedName::from_str("true"), vec![], vec![])
                        });
                    char = char.abs(slice::from_ref(&this));
                    char
                }]);
                abs = guard(&abs, guards);
                abs = generalize(&abs, &params);
                local_axioms.push((abs_name, LocalAxiom { target: abs }));

                let local_type_len = self.tt_local_env.local_types.len();
                let local_len = self.tt_local_env.locals.len();
                let local_axiom_len = self.local_axioms.len();
                self.tt_local_env.local_types.push(structure_id);
                self.tt_local_env.locals.extend(locals);
                self.local_axioms.extend(local_axioms);
                let result = match self.visit_expr(body) {
                    Ok(target) => {
                        if target.contains_type_local(structure_id) {
                            Err(anyhow::anyhow!(
                                "eigenvariable condition violated: local structure type `{}` escapes",
                                structure_name
                            ))
                        } else {
                            Ok(target)
                        }
                    }
                    Err(err) => Err(err),
                };
                self.local_axioms.truncate(local_axiom_len);
                self.tt_local_env.locals.truncate(local_len);
                self.tt_local_env.local_types.truncate(local_type_len);
                result
            }
            Expr::Change(expr) => {
                let ExprChange {
                    metadata: _,
                    target,
                    expr: inner,
                } = expr.as_mut();

                let target_ty = self.visit_term(target)?;
                let error = visit_error(
                    format!("not a proposition: {}", target_ty),
                    target_ty.span().cloned(),
                );
                self.push_type_constraint(target_ty, mk_type_prop(), error);
                let expr_prop = self.visit_expr(inner)?;
                self.push_term_constraint(
                    self.tt_local_env.clone(),
                    expr_prop.clone(),
                    target.clone(),
                    visit_error(
                        format!(
                            "propositions mismatch in change: {}\ntarget = {}\nexpr_prop = {}",
                            inner, target, expr_prop
                        ),
                        inner.span().cloned(),
                    ),
                );

                Ok(target.clone())
            }
        }
    }

    fn print_state(&self) {
        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
        println!("{sp}+current state");
        if !self.term_constraints.is_empty() {
            println!("{sp}| term_constraints:");
            for (_, left, right, _) in &self.term_constraints {
                let left = self.fully_inst(left);
                let right = self.fully_inst(right);
                println!("{sp}| - {}\n{sp}|   {}", left, right);
            }
            println!();
        }
        if !self.queue_unfold.is_empty() {
            println!("{sp}| unfold ({}):", self.queue_unfold.len());
            for c in &self.queue_unfold {
                let left = self.fully_inst(&c.left);
                let right = self.fully_inst(&c.right);
                println!("{sp}| - {}\n{sp}|   {}", left, right);
            }
            println!();
        }
        let mut queue_qp = vec![];
        for c in &self.queue_qp {
            if self.is_resolved_constraint(c) {
                continue;
            }
            queue_qp.push(c);
        }
        if !queue_qp.is_empty() {
            println!("{sp}| qp:");
            for c in &queue_qp {
                let left = self.fully_inst(&c.left);
                let right = self.fully_inst(&c.right);
                println!("{sp}| - {}\n{sp}|   {}", left, right);
            }
            println!();
        }
        let mut queue_fr = vec![];
        for c in &self.queue_fr {
            if self.is_resolved_constraint(c) {
                continue;
            }
            queue_fr.push(c);
        }
        if !queue_fr.is_empty() {
            println!("{sp}| fr:");
            for c in &queue_fr {
                let left = self.fully_inst(&c.left);
                let right = self.fully_inst(&c.right);
                println!("{sp}| - {}\n{sp}|   {}", left, right);
            }
            println!();
        }
        let mut queue_ff = vec![];
        for c in &self.queue_ff {
            if self.is_resolved_constraint(c) {
                continue;
            }
            queue_ff.push(c);
        }
        if !queue_ff.is_empty() {
            println!("{sp}| qp:");
            for c in &queue_ff {
                let left = self.fully_inst(&c.left);
                let right = self.fully_inst(&c.right);
                println!("{sp}| - {}\n{sp}|   {}", left, right);
            }
            println!();
        }
        println!();
    }

    fn push_term_constraint(&mut self, local_env: LocalEnv, left: Term, right: Term, error: Error) {
        if log::log_enabled!(log::Level::Debug) {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}→pushing constraint: {} =?= {}", left, right);
        }
        self.term_constraints.push((local_env, left, right, error));
    }

    fn push_type_constraint(&mut self, left: Type, right: Type, error: Error) {
        if log::log_enabled!(log::Level::Debug) {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}→pushing type constraint: {} =?= {}", left, right);
        }
        self.type_constraints.push((left, right, error));
    }

    fn watch(&mut self, c: Rc<EqConstraint>) {
        if let Term::Hole(left_head) = c.left.head() {
            let hole = left_head.id;
            self.watch_list.entry(hole).or_default().push(c.clone());
        }
        if let Term::Hole(right_head) = c.right.head() {
            let hole = right_head.id;
            self.watch_list.entry(hole).or_default().push(c.clone());
        }
    }

    fn unwatch(&mut self, c: &Rc<EqConstraint>) {
        if let Term::Hole(left_head) = c.left.head() {
            let hole = left_head.id;
            let watch_list = self.watch_list.get_mut(&hole).unwrap();
            let mut index = 0;
            for i in (0..watch_list.len()).rev() {
                if Rc::ptr_eq(&watch_list[i], c) {
                    index = i;
                    break;
                }
            }
            watch_list.swap_remove(index);
        }
        if let Term::Hole(right_head) = c.right.head() {
            let hole = right_head.id;
            let watch_list = self.watch_list.get_mut(&hole).unwrap();
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

    fn watch_instance(&mut self, c: Rc<MethodConstraint>) {
        if let Term::Const(left_head) = c.left.head()
            && self.proof_env.tt_env.has_kappa(&left_head.name)
            && let Instance::Hole(hole) = &left_head.instances[0]
        {
            self.instance_watch_list
                .entry(hole.id)
                .or_default()
                .push(c.clone());
            // we don't need to watch the right head.
            return;
        }
        if let Term::Const(right_head) = c.right.head()
            && self.proof_env.tt_env.has_kappa(&right_head.name)
            && let Instance::Hole(hole) = &right_head.instances[0]
        {
            self.instance_watch_list
                .entry(hole.id)
                .or_default()
                .push(c.clone());
        }
    }

    fn unwatch_instance(&mut self, c: &Rc<MethodConstraint>) {
        if let Term::Const(left_head) = c.left.head()
            && self.proof_env.tt_env.has_kappa(&left_head.name)
            && let Instance::Hole(hole) = &left_head.instances[0]
        {
            let hole_id = hole.id;
            let instance_watch_list = self.instance_watch_list.get_mut(&hole_id).unwrap();
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
        if let Term::Const(right_head) = c.right.head()
            && self.proof_env.tt_env.has_kappa(&right_head.name)
            && let Instance::Hole(hole) = &right_head.instances[0]
        {
            let hole_id = hole.id;
            let instance_watch_list = self.instance_watch_list.get_mut(&hole_id).unwrap();
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

    fn occur_check(&self, m: &Term, hole: Id) -> bool {
        match m {
            Term::Var(_) => true,
            Term::Abs(m) => self.occur_check(&m.body, hole),
            Term::App(m) => self.occur_check(&m.fun, hole) && self.occur_check(&m.arg, hole),
            Term::Local(_) => true,
            Term::Const(_) => true,
            Term::Hole(inner) => {
                if inner.id == hole {
                    return false;
                }
                let Some(target) = self.subst_map.get(&inner.id) else {
                    return true;
                };
                self.occur_check(target, hole)
            }
        }
    }

    // Performs instantiation one step.
    // Note that the result term may contain redex in head
    fn inst_head(&self, m: &Term) -> Option<Term> {
        m.replace_head(&|head| {
            let Term::Hole(head) = head else {
                return None;
            };
            let target = self.subst_map.get(&head.id)?;
            Some(target.clone())
        })
    }

    fn inst_type_head(&self, ty: &Type) -> Option<Type> {
        let Type::Hole(hole) = ty else {
            return None;
        };
        self.type_subst_map.get(&hole.id).cloned()
    }

    fn inst_recv(&self, m: &Term) -> Option<Term> {
        m.replace_head(&|head| {
            let Term::Const(head_const) = head else {
                return None;
            };
            if !self.proof_env.tt_env.has_kappa(&head_const.name) {
                return None;
            }
            if head_const.instances.is_empty() {
                return None;
            }
            let Instance::Hole(hole) = &head_const.instances[0] else {
                return None;
            };
            let instance = self.instance_subst_map.get(&hole.id).cloned()?;
            let mut instances = head_const.instances.clone();
            instances[0] = instance;
            Some(mk_const(
                head_const.name.clone(),
                head_const.ty_args.clone(),
                instances,
            ))
        })
    }

    // TODO: rename to try_reduce_to_pattern or something.
    fn inst_arg_head(&self, m: &Term) -> Term {
        m.replace_args(&|arg| {
            let mut new_arg = arg.whnf().unwrap_or_else(|| arg.clone());
            loop {
                let Some(inst) = self.inst_head(&new_arg) else {
                    break;
                };
                new_arg = inst;
                let Some(red) = new_arg.whnf() else {
                    break;
                };
                new_arg = red;
            }
            new_arg
        })
    }

    fn fully_inst(&self, m: &Term) -> Term {
        m.replace_hole(&|id| self.subst_map.get(&id).map(|m| self.fully_inst(m)))
            .replace_type(&|ty| self.fully_inst_type(ty))
            .replace_instance(&|instance| self.fully_inst_instance(instance))
    }

    fn fully_inst_type(&self, t: &Type) -> Type {
        t.replace_hole(&|id| {
            self.type_subst_map
                .get(&id)
                .map(|ty| self.fully_inst_type(ty))
        })
    }

    fn fully_inst_class(&self, class: &Class) -> Class {
        let args = class
            .args
            .iter()
            .map(|arg| self.fully_inst_type(arg))
            .collect::<Vec<_>>();
        if class.args.iter().zip(&args).all(|(lhs, rhs)| lhs == rhs) {
            class.clone()
        } else {
            Class {
                name: class.name.clone(),
                args,
            }
        }
    }

    fn fully_inst_instance(&self, instance: &Instance) -> Instance {
        match instance {
            Instance::Local(class) => {
                let new_class = self.fully_inst_class(&class.class);
                if new_class == class.class {
                    instance.clone()
                } else {
                    mk_instance_local(new_class)
                }
            }
            Instance::Global(instance) => {
                let InstanceGlobal {
                    name,
                    ty_args,
                    args,
                } = &**instance;
                let new_ty_args = ty_args
                    .iter()
                    .map(|ty_arg| self.fully_inst_type(ty_arg))
                    .collect::<Vec<_>>();
                let new_args = args
                    .iter()
                    .map(|arg| self.fully_inst_instance(arg))
                    .collect::<Vec<_>>();
                if ty_args
                    .iter()
                    .zip(&new_ty_args)
                    .all(|(lhs, rhs)| lhs == rhs)
                    && args.iter().zip(&new_args).all(|(lhs, rhs)| lhs == rhs)
                {
                    Instance::Global(instance.clone())
                } else {
                    Instance::Global(Arc::new(InstanceGlobal {
                        name: name.clone(),
                        ty_args: new_ty_args,
                        args: new_args,
                    }))
                }
            }
            Instance::Hole(hole) => {
                let Some(target) = self.instance_subst_map.get(&hole.id) else {
                    return instance.clone();
                };
                self.fully_inst_instance(target)
            }
        }
    }

    fn fully_inst_expr(&self, expr: &mut Expr) {
        match expr {
            Expr::Assump(expr) => {
                let ExprAssump {
                    metadata: _,
                    target,
                } = expr.as_mut();
                *target = self.fully_inst(target);
            }
            Expr::Local(_) => {}
            Expr::Assume(expr) => {
                let ExprAssume {
                    metadata: _,
                    local_axiom,
                    alias: _,
                    expr: inner,
                } = expr.as_mut();
                *local_axiom = self.fully_inst(local_axiom);
                self.fully_inst_expr(inner);
            }
            Expr::App(expr) => {
                let ExprApp {
                    metadata: _,
                    expr1,
                    expr2,
                } = expr.as_mut();
                self.fully_inst_expr(expr1);
                self.fully_inst_expr(expr2);
            }
            Expr::Take(expr) => {
                let ExprTake {
                    metadata: _,
                    id: _,
                    ty,
                    expr: inner,
                } = expr.as_mut();
                *ty = self.fully_inst_type(ty);
                self.fully_inst_expr(inner);
            }
            Expr::Inst(expr) => {
                let ExprInst {
                    metadata: _,
                    expr: inner,
                    arg,
                } = expr.as_mut();
                self.fully_inst_expr(inner);
                *arg = self.fully_inst(arg);
            }
            Expr::Const(expr) => {
                let ExprConst {
                    metadata: _,
                    name: _,
                    ty_args,
                    instances,
                } = expr.as_mut();
                for ty in ty_args {
                    *ty = self.fully_inst_type(ty);
                }
                let new_instances = instances
                    .iter()
                    .map(|instance| self.fully_inst_instance(instance))
                    .collect::<Vec<_>>();
                if instances
                    .iter()
                    .zip(&new_instances)
                    .any(|(lhs, rhs)| lhs != rhs)
                {
                    *instances = new_instances;
                }
            }
            Expr::LetTerm(expr) => {
                let ExprLetTerm {
                    metadata: _,
                    name: _,
                    ty,
                    value,
                    body,
                } = expr.as_mut();
                if let Some(ty) = ty {
                    *ty = self.fully_inst_type(ty);
                }
                *value = self.fully_inst(value);
                self.fully_inst_expr(body);
            }
            Expr::LetStructure(expr) => {
                let ExprLetStructure {
                    metadata: _,
                    name: _,
                    fields,
                    body,
                } = expr.as_mut();
                for field in &mut *fields {
                    match field {
                        LocalStructureField::Const(LocalStructureConst { ty, .. }) => {
                            *ty = self.fully_inst_type(ty);
                        }
                        LocalStructureField::Axiom(LocalStructureAxiom { target, .. }) => {
                            *target = self.fully_inst(target);
                        }
                    }
                }
                self.fully_inst_expr(body);
            }
            Expr::Change(expr) => {
                let ExprChange {
                    metadata: _,
                    target,
                    expr: inner,
                } = expr.as_mut();
                *target = self.fully_inst(target);
                self.fully_inst_expr(inner);
            }
        }
    }

    fn add_unfold_constraint(
        &mut self,
        local_env: LocalEnv,
        left: Term,
        right: Term,
        error: Error,
    ) {
        if log::log_enabled!(log::Level::Debug) {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!(
                "{sp}new constraint (unfold):\n{sp}- {}\n{sp}  {}",
                left, right
            );
        }

        let c = Rc::new(EqConstraint {
            local_env,
            left,
            right,
            kind: ConstraintKind::Unfold,
            error,
        });
        self.trail.push(Record::AddEqConstraint(c.clone()));
        self.queue_unfold.push_back(c.clone());
    }

    fn add_flex_constraint(
        &mut self,
        local_env: LocalEnv,
        mut left: Term,
        mut right: Term,
        error: Error,
    ) {
        left = self.inst_arg_head(&left);
        right = self.inst_arg_head(&right);
        let kind;
        if left.is_quasi_pattern(&local_env) {
            kind = ConstraintKind::QuasiPattern;
        } else if right.is_quasi_pattern(&local_env) {
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

        if log::log_enabled!(log::Level::Debug) {
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
            kind,
            error,
        });

        self.trail.push(Record::AddEqConstraint(c.clone()));

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
            ConstraintKind::Unfold => unreachable!(),
        }

        self.watch(c);
    }

    fn add_method_constraint(
        &mut self,
        local_env: LocalEnv,
        left: Term,
        right: Term,
        error: Error,
    ) {
        if log::log_enabled!(log::Level::Debug) {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!(
                "{sp}new constraint (method):\n{sp}- {}\n{sp}  {}",
                left, right
            );
        }

        let c = Rc::new(MethodConstraint {
            local_env,
            left,
            right,
            error,
        });
        self.trail.push(Record::AddMethodConstraint(c.clone()));
        self.queue_method.push_back(c.clone());
        self.watch_instance(c);
    }

    fn add_class_constraint(&mut self, local_env: LocalEnv, hole: Id, class: Class, error: Error) {
        if log::log_enabled!(log::Level::Debug) {
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
        self.trail.push(Record::AddClassConstraint(c.clone()));
        self.queue_class.push_back(c.clone());
        self.watch_type(&c);
    }

    fn add_subst(&mut self, id: Id, m: Term, error: Error) {
        if log::log_enabled!(log::Level::Debug) {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}new subst {id} := {m}");
        }

        self.subst_map.insert(id, m.clone());
        self.trail.push(Record::AddSubst { id });

        if let Some(constraints) = self.watch_list.get(&id) {
            for c in constraints {
                // skip constraints already resolved anyway
                if c.left.head().alpha_eq(&mk_hole(id)) {
                    if let Term::Hole(right_hole) = c.right.head()
                        && self.subst_map.contains_key(&right_hole.id)
                    {
                        continue;
                    }
                } else if let Term::Hole(left_hole) = c.left.head()
                    && self.subst_map.contains_key(&left_hole.id)
                {
                    continue;
                }
                let c = (**c).clone();
                if log::log_enabled!(log::Level::Debug) {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}→waking constraint {} =?= {}", c.left, c.right);
                }
                self.term_constraints.push((
                    c.local_env,
                    c.left,
                    c.right,
                    mk_error_join(c.error, error.clone()),
                ));
            }
        }
    }

    fn add_type_subst(&mut self, id: Id, ty: Type, error: Error) {
        if log::log_enabled!(log::Level::Debug) {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}new type subst {id} := {ty}");
        }

        self.type_subst_map.insert(id, ty.clone());
        self.trail.push(Record::AddTypeSubst { id });

        if let Some(constraints) = self.type_watch_list.get(&id) {
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

    fn add_instance_subst(&mut self, id: Id, instance: Instance, error: Error) {
        if log::log_enabled!(log::Level::Debug) {
            let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
            println!("{sp}new instance subst {id} := {instance}");
        }

        self.instance_subst_map.insert(id, instance.clone());
        self.trail.push(Record::AddInstanceSubst { id });

        if let Some(constraints) = self.instance_watch_list.get(&id) {
            for c in constraints {
                let c = (**c).clone();
                if log::log_enabled!(log::Level::Debug) {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}→waking constraint {} =?= {}", c.left, c.right);
                }
                self.term_constraints.push((
                    c.local_env,
                    c.left,
                    c.right,
                    mk_error_join(c.error, error.clone()),
                ));
            }
        }
    }

    fn get_hole_type(&self, id: Id) -> Option<&Type> {
        self.term_holes
            .iter()
            .find(|&&(n, _)| n == id)
            .map(|(_, t)| t)
    }

    fn add_hole_type(&mut self, id: Id, ty: Type) {
        self.term_holes.push((id, ty));
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
        let mut instantiated = false;
        if let Some(new_t1) = self.inst_type_head(&t1) {
            t1 = new_t1;
            instantiated = true;
        }
        if let Some(new_t2) = self.inst_type_head(&t2) {
            t2 = new_t2;
            instantiated = true;
        }
        if instantiated {
            self.push_type_constraint(t1, t2, error);
            return None;
        }
        match (t1, t2) {
            (Type::Arrow(inner1), Type::Arrow(inner2)) => {
                let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                self.push_type_constraint(inner1.dom, inner2.dom, error.clone());
                self.push_type_constraint(inner1.cod, inner2.cod, error);
            }
            (Type::App(inner1), Type::App(inner2)) => {
                // Since we have no higher-kinded polymorphism, it is impossible to match the following two types:
                //  ?M₁ t =?= ?M₂ t₁ t₂
                // But such a case is checked and ruled out in the kind checking phase that runs before
                // this unificaiton phase.
                let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                self.push_type_constraint(inner1.fun, inner2.fun, error.clone());
                self.push_type_constraint(inner1.arg, inner2.arg, error);
            }
            (Type::Hole(hole), t) | (t, Type::Hole(hole)) => {
                let hole_id = hole.id;
                let t = self.fully_inst_type(&t); // TODO: avoid instantiation
                if t.contains_hole(hole_id) {
                    return Some(error);
                }
                self.add_type_subst(hole_id, t, error);
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
        if let (Term::Abs(l), Term::Abs(r)) = (&left, &right) {
            self.push_type_constraint(l.binder_type.clone(), r.binder_type.clone(), error.clone());
            let x = Local {
                id: Id::fresh(),
                ty: l.binder_type.clone(),
            };
            let local = mk_local(x.id);
            let left = l.body.open(std::slice::from_ref(&local), 0);
            let right = r.body.open(&[local], 0);
            local_env.locals.push(x);
            self.push_term_constraint(local_env, left, right, error);
            return None;
        }
        let new_left = left.whnf();
        let left_changed = new_left.is_some();
        if let Some(new_left) = new_left {
            left = new_left;
        }
        let new_right = right.whnf();
        let right_changed = new_right.is_some();
        if let Some(new_right) = new_right {
            right = new_right;
        }
        if left_changed || right_changed {
            self.push_term_constraint(local_env, left, right, error);
            return None;
        }
        let new_left = self.inst_head(&left);
        let new_right = self.inst_head(&right);
        if new_left.is_some() || new_right.is_some() {
            if let Some(term) = new_left {
                left = term;
            }
            if let Some(term) = new_right {
                right = term;
            }
            self.push_term_constraint(local_env, left, right, error);
            return None;
        }
        if left.is_abs() {
            mem::swap(&mut left, &mut right);
        }
        if let Term::Abs(_) = right {
            // solvable only when
            // 1. L is stuck by an unfoldable constant
            // 2. L is stuck by an unassigned hole
            if let Term::Const(left_head) = left.head().clone() {
                if self.proof_env.tt_env.has_kappa(&left_head.name) {
                    if let Some(new_left) = self.inst_recv(&left) {
                        left = new_left;
                    }
                    let Term::Const(updated_left_head) = left.head().clone() else {
                        unreachable!();
                    };
                    if updated_left_head.instances[0].is_hole() {
                        self.add_method_constraint(local_env, left, right, error);
                        return None;
                    }
                }
                if let Some(new_left) = self.proof_env.tt_env.unfold_head(&local_env, &left) {
                    left = new_left;
                    self.push_term_constraint(local_env, left, right, error);
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
                let TermAbs {
                    metadata: _,
                    binder_type: right_binder_type,
                    binder_name: _,
                    body: right_body,
                } = {
                    let Term::Abs(right_inner) = right else {
                        unreachable!()
                    };
                    Arc::unwrap_or_clone(right_inner)
                };
                let x = Local {
                    id: Id::fresh(),
                    ty: right_binder_type,
                };
                let right = right_body.open(&[mk_local(x.id)], 0);
                left = left.apply([mk_local(x.id)]);
                local_env.locals.push(x);
                self.push_term_constraint(local_env, left, right, error);
                return None;
            } else {
                return Some(error);
            }
        }
        // then each of the heads can be a local, a const, or a hole
        if let Term::Hole(right_head) = right.head() {
            let right_head = right_head.id;
            right = self.inst_arg_head(&right);
            if let Some(args) = right.is_pattern(&local_env)
                && self.occur_check(&left, right_head)
                && left.is_supported_by(&args)
            {
                let binders = args
                    .into_iter()
                    .map(|arg| Local {
                        id: arg,
                        ty: local_env.get_local(arg).unwrap().clone(),
                    })
                    .collect::<Vec<_>>();
                left = left.abs(&binders);
                self.add_subst(right_head, left, error);
                return None;
            }
        }
        if let Term::Hole(left_head) = left.head() {
            let left_head = left_head.id;
            left = self.inst_arg_head(&left);
            if let Some(args) = left.is_pattern(&local_env)
                && self.occur_check(&right, left_head)
                && right.is_supported_by(&args)
            {
                let binders = args
                    .into_iter()
                    .map(|arg| Local {
                        id: arg,
                        ty: local_env.get_local(arg).unwrap().clone(),
                    })
                    .collect::<Vec<_>>();
                right = right.abs(&binders);
                self.add_subst(left_head, right, error);
                return None;
            }
        }
        if right.head().is_hole() || left.head().is_hole() {
            self.add_flex_constraint(local_env, left, right, error);
            return None;
        }
        // then each of the heads can be a local or a const.
        if let Some(new_left) = self.inst_recv(&left) {
            left = new_left;
        }
        if let Some(new_right) = self.inst_recv(&right) {
            right = new_right;
        }
        if let Term::Const(left_head) = left.head()
            && self.proof_env.tt_env.has_kappa(&left_head.name)
            && left_head.instances[0].is_hole()
        {
            self.add_method_constraint(local_env.clone(), left, right, error);
            return None;
        }
        if let Term::Const(right_head) = right.head()
            && self.proof_env.tt_env.has_kappa(&right_head.name)
            && right_head.instances[0].is_hole()
        {
            self.add_method_constraint(local_env.clone(), left, right, error);
            return None;
        }
        // then each of the heads is either opaque or unfoldable.
        if self.proof_env.tt_env.is_opaque(&local_env, left.head())
            && self.proof_env.tt_env.is_opaque(&local_env, right.head())
        {
            match (left.head(), right.head()) {
                (Term::Local(left_head), Term::Local(right_head)) => {
                    if left_head.id != right_head.id {
                        return Some(error);
                    }
                }
                (Term::Const(left_head), Term::Const(right_head)) => {
                    if left_head.name != right_head.name {
                        return Some(error);
                    }
                    for (left_ty_arg, right_ty_arg) in
                        left_head.ty_args.iter().zip(right_head.ty_args.iter())
                    {
                        self.push_type_constraint(
                            left_ty_arg.clone(),
                            right_ty_arg.clone(),
                            error.clone(),
                        );
                    }
                }
                _ => return Some(error),
            }
            let left_args = left.args();
            let right_args = right.args();
            if left_args.len() != right_args.len() {
                return Some(error);
            }
            for (left_arg, right_arg) in left_args.into_iter().zip(right_args.into_iter()).rev() {
                self.push_term_constraint(
                    local_env.clone(),
                    left_arg.clone(),
                    right_arg.clone(),
                    error.clone(),
                );
            }
            return None;
        }
        // now at least one of the heads is unfoldable.
        // (f t₁ ⋯ tₙ) ≈ (f s₁ ⋯ sₘ) where f is unfoldable
        match (left.head(), right.head()) {
            (Term::Local(left_head), Term::Local(right_head)) if left_head.id == right_head.id => {
                self.add_unfold_constraint(local_env, left, right, error);
                return None;
            }
            (Term::Const(left_head), Term::Const(right_head))
                if left_head.name == right_head.name
                    && self
                        .proof_env
                        .tt_env
                        .is_delta_redex(&local_env, left.head()) =>
            {
                self.add_unfold_constraint(local_env, left, right, error);
                return None;
            }
            (Term::Const(left_head), Term::Const(right_head))
                if left_head.name == right_head.name
                    && self.proof_env.tt_env.has_kappa(&left_head.name) =>
            {
                assert!(self.proof_env.tt_env.has_kappa(&left_head.name));
                let Const {
                    local_types,
                    local_classes,
                    ty: _,
                } = self
                    .proof_env
                    .tt_env
                    .const_table
                    .get(&left_head.name)
                    .unwrap();
                let mut subst = Vec::with_capacity(local_types.len());
                for (x, t) in zip(local_types, &left_head.ty_args) {
                    subst.push((*x, t.clone()));
                }
                let left_class = local_classes[0].subst(&subst);
                let mut subst = Vec::with_capacity(local_types.len());
                for (x, t) in zip(local_types, &right_head.ty_args) {
                    subst.push((*x, t.clone()));
                }
                let right_class = local_classes[0].subst(&subst);
                if left_class == right_class {
                    self.add_unfold_constraint(local_env, left, right, error);
                    return None;
                }
            }
            _ => {}
        }
        let left_priority = self
            .proof_env
            .tt_env
            .unfold_priority(&local_env, left.head());
        let right_priority = self
            .proof_env
            .tt_env
            .unfold_priority(&local_env, right.head());
        match left_priority.cmp(&right_priority) {
            std::cmp::Ordering::Greater => {
                let Some(new_left) = self.proof_env.tt_env.unfold_head(&local_env, &left) else {
                    unreachable!()
                };
                left = new_left;
            }
            std::cmp::Ordering::Less => {
                let Some(new_right) = self.proof_env.tt_env.unfold_head(&local_env, &right) else {
                    unreachable!()
                };
                right = new_right;
            }
            std::cmp::Ordering::Equal => {
                let Some(new_left) = self.proof_env.tt_env.unfold_head(&local_env, &left) else {
                    unreachable!()
                };
                left = new_left;
                let Some(new_right) = self.proof_env.tt_env.unfold_head(&local_env, &right) else {
                    unreachable!()
                };
                right = new_right;
            }
        }
        self.push_term_constraint(local_env, left, right, error);
        None
    }

    fn resolve_class(&self, local_env: &LocalEnv, class: &Class) -> Option<Instance> {
        for local_class in &local_env.local_classes {
            if local_class == class {
                return Some(mk_instance_local(local_class.clone()));
            }
        }
        'next_instance: for (name, instance) in self.proof_env.tt_env.class_instance_table {
            let ClassInstance {
                local_types,
                local_classes,
                target,
                method_table: _,
            } = instance;
            let mut type_subst = Vec::with_capacity(local_types.len());
            for local_type in local_types.iter() {
                type_subst.push((*local_type, mk_fresh_type_hole()));
            }
            let target = target.subst(&type_subst);
            // TODO: C a ?b ⇒ C ?b c ⇒ C a c
            let Some(subst) = class.matches(&target) else {
                continue;
            };
            let ty_args = type_subst
                .into_iter()
                .map(|(_, ty)| ty.inst(&subst))
                .collect::<Vec<_>>();
            let subst = local_types
                .iter()
                .zip(&ty_args)
                .map(|(name, ty)| (*name, ty.clone()))
                .collect::<Vec<_>>();
            let mut args = vec![];
            for local_class in local_classes {
                let local_class = local_class.subst(&subst);
                let Some(instance) = self.resolve_class(local_env, &local_class) else {
                    continue 'next_instance;
                };
                args.push(instance);
            }
            return Some(mk_instance_global(name.clone(), ty_args, args));
        }
        None
    }

    fn find_conflict_in_class(
        &mut self,
        local_env: LocalEnv,
        hole: Id,
        class: Class,
        error: Error,
    ) -> Option<Error> {
        let class = self.fully_inst_class(&class);
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
        if log::log_enabled!(log::Level::Debug) {
            self.print_state();
        }
        while !self.type_constraints.is_empty()
            || !self.class_constraints.is_empty()
            || !self.term_constraints.is_empty()
        {
            if let Some((t1, t2, error)) = self.type_constraints.pop() {
                if log::log_enabled!(log::Level::Debug) {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    let t1 = self.fully_inst_type(&t1);
                    let t2 = self.fully_inst_type(&t2);
                    println!("{sp}find conflict in {t1} =?= {t2}");
                }
                if let Some(error) = self.find_conflict_in_types(t1, t2, error) {
                    if log::log_enabled!(log::Level::Debug) {
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
                if log::log_enabled!(log::Level::Debug) {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    let m1 = self.fully_inst(&m1);
                    let m2 = self.fully_inst(&m2);
                    println!("{sp}find conflict in {m1} =?= {m2}");
                }
                if let Some(error) = self.find_conflict_in_terms(local_env, m1, m2, error) {
                    if log::log_enabled!(log::Level::Debug) {
                        let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                        println!("{sp}conflict in terms: {error}");
                    }
                    return Some(error);
                }
            }
        }
        None
    }

    fn save(&self) -> Snapshot {
        Snapshot {
            trail_len: self.trail.len(),
        }
    }

    fn restore(&mut self, snapshot: &Snapshot) {
        for _ in 0..self.trail.len() - snapshot.trail_len {
            match self.trail.pop().unwrap() {
                Record::AddEqConstraint(c) => match c.kind {
                    ConstraintKind::Unfold => {
                        self.queue_unfold.pop_back();
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
                Record::AddMethodConstraint(c) => {
                    self.queue_method.pop_back();
                    self.unwatch_instance(&c);
                }
                Record::AddClassConstraint(c) => {
                    self.queue_class.pop_back();
                    self.unwatch_type(&c);
                }
                Record::AddSubst { id } => {
                    self.subst_map.remove(&id);
                }
                Record::AddTypeSubst { id } => {
                    self.type_subst_map.remove(&id);
                }
                Record::AddInstanceSubst { id } => {
                    self.instance_subst_map.remove(&id);
                }
                Record::RemoveEqConstraint(c) => match c.kind {
                    ConstraintKind::Unfold => {
                        self.queue_unfold.push_front(c);
                    }
                    ConstraintKind::QuasiPattern => {
                        self.queue_qp.push_front(c);
                    }
                    ConstraintKind::FlexRigid => {
                        self.queue_fr.push_front(c);
                    }
                    ConstraintKind::FlexFlex => {
                        unreachable!()
                    }
                },
            }
        }
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
            self.push_type_constraint(left, right, error);
        }
        for (local_env, left, right, error) in node.term_constraints.into_iter().rev() {
            self.push_term_constraint(local_env, left, right, error);
        }
        true
    }

    fn choice_unfold(&self, c: &EqConstraint) -> Vec<Node> {
        // Suppose (h t₁ ⋯ tₙ) ≈ (h s₁ ⋯ sₙ), where h is local or const.
        let left_args = c.left.args();
        let right_args = c.right.args();
        // Try first (t₁ ≈ s₁) ∧ ⋯ ∧ (tₙ ≈ sₙ)
        let node1 = {
            let mut node = Node::default();
            match (c.left.head(), c.right.head()) {
                (Term::Const(left_head), Term::Const(right_head)) => {
                    for (t1, t2) in zip(&left_head.ty_args, &right_head.ty_args) {
                        node.type_constraints
                            .push((t1.clone(), t2.clone(), c.error.clone()));
                    }
                }
                (Term::Local(left_head), Term::Local(right_head)) => {
                    debug_assert_eq!(left_head.id, right_head.id);
                }
                _ => unreachable!(),
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
            let Some(new_left) = self.proof_env.tt_env.unfold_head(&c.local_env, &left) else {
                unreachable!()
            };
            left = new_left;
            let Some(new_right) = self.proof_env.tt_env.unfold_head(&c.local_env, &right) else {
                unreachable!()
            };
            right = new_right;
            node.term_constraints
                .push((c.local_env.clone(), left, right, c.error.clone()));
            node
        };
        vec![node1, node2]
    }

    fn choice_fr(&mut self, c: &EqConstraint) -> Vec<Node> {
        // left  ≡ ?M t[1] .. t[p]
        // right ≡  @ u[1] .. u[q]
        let Term::Hole(left_head) = c.left.head() else {
            panic!()
        };
        let left_head = left_head.id;
        let left_args = c.left.args();
        let right_args = c.right.args();
        let right_head = c.right.head();

        let mut nodes = vec![];

        // τ(?M)
        let left_head_ty = self
            .get_hole_type(left_head)
            .map(|t| self.fully_inst_type(t)) // TODO: avoid full instantiation
            .unwrap();

        // τ(?M t[1] .. t[p]) (= τ(@ u[1] .. u[q]))
        let left_ty = left_head_ty.target().arrow(
            left_head_ty
                .components()
                .into_iter()
                .skip(left_args.len())
                .cloned(),
        );

        // z[1] .. z[p]
        let new_binders = left_head_ty
            .components()
            .iter()
            .take(left_args.len())
            .map(|&t| Local {
                id: Id::fresh(),
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

            let t =
                z.ty.target()
                    .arrow(z.ty.components().into_iter().skip(m).cloned());

            // Y[1] .. Y[m]
            let arg_holes =
                z.ty.components()
                    .iter()
                    .take(m)
                    .map(|&arg_ty| {
                        let new_hole = Id::fresh();
                        let ty = arg_ty.arrow(new_binders.iter().map(|z| z.ty.clone()));
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
                    let mut arg = mk_hole(hole);
                    arg = arg.apply(new_binders.iter().map(|z| mk_local(z.id)));
                    arg
                })
                .collect::<Vec<_>>();

            // TODO: try eta equal condidates when the hole ?M is used twice or more among the whole set of constraints.
            let mut target = mk_local(z.id);
            target = target.apply(new_args);
            target = target.abs(&new_binders);
            nodes.push(Node {
                subst: vec![(left_head, target, c.error.clone())],
                type_constraints: vec![(t, left_ty.clone(), c.error.clone())],
                // This is ok because later add_subst(left_head, target) is called and the constraint is woken up again.
                term_constraints: vec![],
            });
        }

        // Imitation step.
        //
        //   M ↦ λ z[1] .. z[p], C (Y[1] z[1] .. z[p]) .. (Y[q] z[1] .. z[p])
        //
        // when @ = C.
        let imitation_head_ty = match right_head {
            Term::Const(right_head_inner) => {
                let ty = {
                    let Const {
                        local_types,
                        local_classes: _,
                        ty,
                    } = self
                        .proof_env
                        .tt_env
                        .const_table
                        .get(&right_head_inner.name)
                        .unwrap();
                    let mut subst = Vec::with_capacity(local_types.len());
                    for (x, t) in zip(local_types, &right_head_inner.ty_args) {
                        subst.push((*x, t.clone()));
                    }
                    ty.subst(&subst)
                };
                Some(self.fully_inst_type(&ty))
            }
            Term::Local(inner) => c
                .local_env
                .locals
                .iter()
                .rev()
                .find(|local| local.id == inner.id)
                .map(|local| self.fully_inst_type(&local.ty)),
            Term::Var(_) | Term::Abs(_) | Term::App(_) | Term::Hole(_) => None,
        };
        if let Some(right_head_ty) = imitation_head_ty {
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
                    let new_hole = Id::fresh();
                    let ty = arg_ty.arrow(new_binders.iter().map(|z| z.ty.clone()));
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
                    let mut arg = mk_hole(hole);
                    arg = arg.apply(new_binders.iter().map(|z| mk_local(z.id)));
                    arg
                })
                .collect::<Vec<_>>();

            // TODO: try eta equal condidates when the hole ?M is used twice or more among the whole set of constraints.
            let mut target = right_head.clone();
            target = target.apply(new_args);
            target = target.abs(&new_binders);
            nodes.push(Node {
                subst: vec![(left_head, target, c.error.clone())],
                type_constraints: vec![],
                // This is ok because later add_subst(left_head, target) is called and the constraint is woken up again.
                term_constraints: vec![],
            });
        }

        nodes
    }

    fn is_resolved_constraint(&self, c: &EqConstraint) -> bool {
        if let Term::Hole(right_head) = c.right.head()
            && self.subst_map.contains_key(&right_head.id)
        {
            return true;
        }
        if let Term::Hole(left_head) = c.left.head()
            && self.subst_map.contains_key(&left_head.id)
        {
            return true;
        }
        false
    }

    // Returns false if the constraints are pre-unified.
    // This function does not resolve flex-flex constraints nor method constraints.
    // There may be cases that can be resolved by checking method constraints, but we don't do that:
    // - method-flex case: m l₁ ⋯ lₙ =?= ?M r₁ ⋯ rₘ
    // - method-const case: m l₁ ⋯ lₙ =?= c r₁ ⋯ rₘ  (infer the type of m by searching the method table)
    fn decide(&mut self) -> bool {
        let nodes = 'next: {
            if let Some(c) = self.queue_unfold.pop_front() {
                self.trail.push(Record::RemoveEqConstraint(c.clone()));
                if log::log_enabled!(log::Level::Debug) {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!(
                        "{sp}making a decision (unfold):\n{sp}- {}\n{sp}  {}",
                        c.left, c.right
                    );
                }
                break 'next self.choice_unfold(&c);
            }
            while let Some(c) = self.queue_qp.pop_front() {
                self.trail.push(Record::RemoveEqConstraint(c.clone()));
                if !self.is_resolved_constraint(&c) {
                    if log::log_enabled!(log::Level::Debug) {
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
                self.trail.push(Record::RemoveEqConstraint(c.clone()));
                if !self.is_resolved_constraint(&c) {
                    if log::log_enabled!(log::Level::Debug) {
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

        self.decisions.push(Branch {
            snapshot: self.save(),
            nodes: Box::new(nodes.into_iter()),
        });

        self.next();
        true
    }

    fn backjump(&mut self) -> bool {
        self.term_constraints.clear();
        self.type_constraints.clear();
        self.class_constraints.clear();
        while !self.next() {
            if self.decisions.pop().is_none() {
                return false;
            }
        }
        true
    }

    fn solve(&mut self) -> Result<(), Error> {
        loop {
            while let Some(error) = self.find_conflict() {
                if log::log_enabled!(log::Level::Debug) {
                    let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                    println!("{sp}conflict found!");
                }
                if !self.backjump() {
                    return Err(error);
                }
            }
            if log::log_enabled!(log::Level::Debug) {
                let sp = repeat_n(' ', self.decisions.len()).collect::<String>();
                println!("{sp}simplification done");
                self.print_state();
            }
            if !self.decide() {
                return Ok(());
            }
        }
    }

    // TODO: 本当は find_conflict の中でやるべき。ノードごとに生成した hole を記録して、制約がなくなった hole について inhabitant を合成する。
    fn synthesize_inhabitant(&self, mut facts: Vec<(Id, Type)>, goal: &Type) -> Option<Term> {
        let (components, goal_base) = goal.unarrow();
        let mut binders = vec![];
        for component in components {
            let binder = Local {
                id: Id::fresh(),
                ty: component.clone(),
            };
            binders.push(binder.clone());
            facts.push((binder.id, component));
        }
        let goal = goal_base;
        if let Some(instance) = self.resolve_class(
            self.tt_local_env,
            &Class {
                name: QualifiedName::from_str("default"),
                args: vec![goal.clone()],
            },
        ) {
            let mut m = mk_const(
                QualifiedName::from_str("default").extend("value"),
                vec![goal.clone()],
                vec![instance],
            );
            m = m.abs(&binders);
            return Some(m);
        }
        for (name, fact) in &facts {
            let (xs, head) = fact.unarrow();
            if head == goal {
                let mut args = vec![];
                for x in &xs {
                    if let Some(arg) = self.synthesize_inhabitant(facts.clone(), x) {
                        args.push(arg);
                    } else {
                        break;
                    }
                }
                if args.len() == xs.len() {
                    let mut m = mk_local(*name);
                    m = m.apply(args);
                    m = m.abs(&binders);
                    return Some(m);
                }
            }
        }
        None
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
    if log::log_enabled!(log::Level::Debug) {
        println!("elaborating:\n{target}");
    }

    let mut elab = Elaborator::new(proof_env, local_env, vec![]);

    let t = elab.visit_term(target)?;
    let error = visit_error("type mismatch", target.span().cloned());
    elab.push_type_constraint(t, ty.clone(), error);

    if let Err(error) = elab.solve() {
        bail!("unification failed: {error}");
    }

    *target = elab.fully_inst(target);
    ensure!(
        target.is_instance_ground(),
        "unification failed: could not synthesize instance"
    );

    ensure!(target.is_ground());
    ensure!(target.is_type_ground());

    if log::log_enabled!(log::Level::Debug) {
        println!("elaborated:\n{target}");
    }

    Ok(())
}

// prop is trusted
pub fn elaborate_expr(
    proof_env: proof::Env,
    local_env: &mut LocalEnv,
    term_holes: Vec<(Id, Type)>,
    e: &mut Expr,
    prop: &Term,
) -> anyhow::Result<()> {
    if log::log_enabled!(log::Level::Debug) {
        // print local_env
        println!("local env:");
        for param in &local_env.locals {
            println!("  {} : {}", param.id, param.ty);
        }
        for local_type in &local_env.local_types {
            println!("  {} : Type", local_type);
        }
        for local_class in &local_env.local_classes {
            println!("  [{}]", local_class);
        }
        println!("elaborating:\n{e}");
    }

    let mut elab = Elaborator::new(proof_env, local_env, term_holes);

    let p = elab.visit_expr(e)?;
    elab.push_term_constraint(
        elab.tt_local_env.clone(),
        p,
        prop.clone(),
        visit_error(
            format!("proposition mismatch: expected {prop}"),
            e.span().cloned(),
        ),
    );

    if let Err(error) = elab.solve() {
        bail!("unification failed: {error}");
    }

    elab.fully_inst_expr(e);
    ensure!(
        e.is_instance_ground(),
        "unification failed: could not synthesize instance"
    );

    if log::log_enabled!(log::Level::Debug) {
        println!("fully instantiated:\n{e}");
    }

    ensure!(e.is_type_ground());

    e.replace_hole(&|name| {
        for (local, ty) in &elab.term_holes {
            if *local == name {
                return elab.synthesize_inhabitant(vec![], ty);
            }
        }
        None
    });
    ensure!(
        e.is_instance_ground(),
        "unification failed: could not synthesize instance"
    );

    ensure!(e.is_ground());

    *e = mk_expr_change(prop.clone(), mem::take(e));

    if log::log_enabled!(log::Level::Debug) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        proof,
        proof::mk_type_prop,
        tt::{
            self, ClassInstance, ClassType, Const, Delta, Id, Kappa, Kind, Local, Name, mk_abs,
            mk_app, mk_const, mk_hole, mk_local, mk_type_app, mk_type_arrow, mk_type_const,
            mk_type_local, mk_var,
        },
    };
    use std::collections::HashMap;

    #[test]
    fn const_expr_does_not_resolve_local_axiom_from_local_table() {
        let mut tt_local_env = tt::LocalEnv::default();
        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::new();
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let mut elab = Elaborator::new(proof_env, &mut tt_local_env, vec![]);
        let local_axiom_name = QualifiedName::from_str("foo.a");
        elab.local_axioms.push((
            local_axiom_name.clone(),
            LocalAxiom {
                target: mk_const(QualifiedName::from_str("p"), vec![], vec![]),
            },
        ));

        let mut expr = proof::mk_expr_const(local_axiom_name, vec![], vec![]);
        let error = elab
            .visit_expr(&mut expr)
            .expect_err("const expression should not resolve via local axiom table");
        assert!(error.to_string().contains("proposition not found"));
    }

    #[test]
    fn unify_fails_for_inhabited_terms() {
        let name_u = Name::from_str("u");
        let ty_u = mk_type_local(Id::from_name(&name_u));
        let name_is_inhabited = QualifiedName::from_str("is_inhabited");
        let ty_is_inhabited_u = mk_type_app(mk_type_const(name_is_inhabited.clone()), ty_u.clone());
        let ty_u_to_prop = mk_type_arrow(ty_u.clone(), mk_type_prop());

        let hole_id = Id::from_name(&Name::from_str("46380"));
        let hole_type = mk_type_arrow(
            ty_is_inhabited_u.clone(),
            mk_type_arrow(
                ty_u_to_prop.clone(),
                mk_type_arrow(
                    ty_is_inhabited_u.clone(),
                    mk_type_arrow(ty_u.clone(), ty_u.clone()),
                ),
            ),
        );

        let h_id = Id::from_name(&Name::from_str("h"));
        let x_id = Id::from_name(&Name::from_str("x46373"));

        let rep_term = mk_const(
            QualifiedName::from_str("is_inhabited")
                .extend("inhab")
                .extend("rep"),
            vec![ty_u.clone()],
            vec![],
        );
        let rep_applied = mk_app(rep_term, mk_local(h_id));

        let hole = mk_hole(hole_id);
        let hole_applied = mk_app(
            mk_app(
                mk_app(mk_app(hole.clone(), mk_var(3)), mk_var(2)),
                mk_var(1),
            ),
            mk_var(0),
        );
        let body = mk_app(mk_var(2), hole_applied);
        let lambda = mk_abs(Some(Name::from_str("46379")), ty_u.clone(), body);
        let lambda = mk_abs(
            Some(Name::from_str("46378")),
            ty_is_inhabited_u.clone(),
            lambda,
        );
        let lambda = mk_abs(Some(Name::from_str("46377")), ty_u_to_prop.clone(), lambda);
        let lambda = mk_abs(
            Some(Name::from_str("46376")),
            ty_is_inhabited_u.clone(),
            lambda,
        );

        let left = mk_app(
            mk_app(
                mk_app(mk_app(lambda, mk_local(h_id)), rep_applied.clone()),
                mk_local(h_id),
            ),
            mk_local(x_id),
        );

        let in_term = mk_const(QualifiedName::from_str("in"), vec![ty_u.clone()], vec![]);
        let right = mk_app(mk_app(in_term, mk_local(x_id)), rep_applied.clone());

        let locals = vec![
            Local {
                id: h_id,
                ty: ty_is_inhabited_u.clone(),
            },
            Local {
                id: x_id,
                ty: ty_u.clone(),
            },
        ];

        let local_env = tt::LocalEnv {
            local_types: vec![Id::from_name(&name_u)],
            local_classes: vec![],
            locals,
            local_deltas: vec![],
        };
        let mut tt_local_env = local_env.clone();

        let name_prop = QualifiedName::from_str("Prop");

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::from([
            (name_prop.clone(), Kind::base()),
            (name_is_inhabited.clone(), Kind(1)),
        ]);
        let const_table: HashMap<QualifiedName, Const> = HashMap::new();
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();

        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };

        let term_holes = vec![(hole_id, hole_type)];
        let mut elab = Elaborator::new(proof_env, &mut tt_local_env, term_holes);

        println!("left: {left}");
        println!("right: {right}");

        let error = visit_error("expected failure", None);
        elab.push_term_constraint(local_env.clone(), left, right, error);

        let result = elab.solve();
        println!("result: {result:?}");
        assert!(result.is_err(), "unification unexpectedly succeeded");
    }

    #[test]
    fn mk_term_hole_uses_only_non_unfoldable_locals() {
        let x_id = Id::from_name(&Name::from_str("x"));
        let q_id = Id::from_qualified_name(&QualifiedName::from_str("foo.q"));
        let u_id = Id::from_qualified_name(&QualifiedName::from_str("foo.u"));

        let x_ty = mk_type_prop();
        let q_ty = mk_type_prop();
        let u_ty = mk_type_prop();

        let mut local_env = tt::LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![LocalDelta {
                id: u_id,
                target: mk_const(QualifiedName::from_str("c"), vec![], vec![]),
                height: 0,
            }],
            locals: vec![
                Local {
                    id: x_id,
                    ty: x_ty.clone(),
                },
                Local {
                    id: q_id,
                    ty: q_ty.clone(),
                },
                Local { id: u_id, ty: u_ty },
            ],
        };

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::new();
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let mut elab = Elaborator::new(proof_env, &mut local_env, vec![]);

        let hole = elab.mk_term_hole(mk_type_prop());
        let args = hole.args();
        assert_eq!(args.len(), 2);
        let Term::Local(arg0) = args[0] else {
            panic!("expected local argument");
        };
        assert_eq!(arg0.id, x_id);
        let Term::Local(arg1) = args[1] else {
            panic!("expected local argument");
        };
        assert_eq!(arg1.id, q_id);

        let (_, hole_ty) = elab
            .term_holes
            .last()
            .expect("hole type should be registered");
        let expected_hole_ty = mk_type_prop().arrow([x_ty, q_ty]);
        assert_eq!(*hole_ty, expected_hole_ty);
    }

    #[test]
    fn unify_local_and_const_uses_local_unfold() {
        let c = QualifiedName::from_str("c");
        let l_id = Id::from_qualified_name(&QualifiedName::from_str("foo.l"));
        let c_term = mk_const(c.clone(), vec![], vec![]);

        let mut local_env = tt::LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![LocalDelta {
                id: l_id,
                target: c_term.clone(),
                height: 0,
            }],
            locals: vec![Local {
                id: l_id,
                ty: mk_type_prop(),
            }],
        };

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::from([(
            c.clone(),
            Const {
                local_types: vec![],
                local_classes: vec![],
                ty: mk_type_prop(),
            },
        )]);
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let local_env_snapshot = local_env.clone();
        let mut elab = Elaborator::new(proof_env, &mut local_env, vec![]);

        let error = visit_error("expected success", None);
        elab.push_term_constraint(
            local_env_snapshot.clone(),
            mk_local(l_id),
            c_term.clone(),
            error.clone(),
        );
        elab.push_term_constraint(local_env_snapshot, c_term, mk_local(l_id), error);
        assert!(
            elab.solve().is_ok(),
            "local/const unification should succeed by local unfold"
        );
    }

    #[test]
    fn unify_local_local_with_unfoldable_side() {
        let unfoldable_id = Id::from_qualified_name(&QualifiedName::from_str("foo.l"));
        let rigid_id = Id::from_name(&Name::from_str("x"));

        let mut local_env = tt::LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![LocalDelta {
                id: unfoldable_id,
                target: mk_local(rigid_id),
                height: 0,
            }],
            locals: vec![
                Local {
                    id: unfoldable_id,
                    ty: mk_type_prop(),
                },
                Local {
                    id: rigid_id,
                    ty: mk_type_prop(),
                },
            ],
        };

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::new();
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let local_env_snapshot = local_env.clone();
        let mut elab = Elaborator::new(proof_env, &mut local_env, vec![]);

        let error = visit_error("expected success", None);
        elab.push_term_constraint(
            local_env_snapshot,
            mk_local(unfoldable_id),
            mk_local(rigid_id),
            error,
        );
        assert!(
            elab.solve().is_ok(),
            "local/local unification should succeed by unfolding the unfoldable side"
        );
    }

    #[test]
    fn unify_same_kappa_const_with_local_instance_is_reachable() {
        let method_name = QualifiedName::from_str("m");
        let class_name = QualifiedName::from_str("C");
        let x_id = Id::from_name(&Name::from_str("x"));
        let y_id = Id::from_name(&Name::from_str("y"));
        let instance = mk_instance_local(Class {
            name: class_name.clone(),
            args: vec![],
        });
        let head = mk_const(method_name.clone(), vec![], vec![instance]);

        let mut local_env = tt::LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![],
            locals: vec![
                Local {
                    id: x_id,
                    ty: mk_type_prop(),
                },
                Local {
                    id: y_id,
                    ty: mk_type_prop(),
                },
            ],
        };

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::from([(
            method_name.clone(),
            Const {
                local_types: vec![],
                local_classes: vec![],
                ty: mk_type_prop().arrow([mk_type_prop()]),
            },
        )]);
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> =
            HashMap::from([(method_name.clone(), Kappa)]);
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let local_env_snapshot = local_env.clone();
        let mut elab = Elaborator::new(proof_env, &mut local_env, vec![]);

        let error = visit_error("expected failure", None);
        elab.push_term_constraint(
            local_env_snapshot,
            mk_app(head.clone(), mk_local(x_id)),
            mk_app(head, mk_local(y_id)),
            error,
        );

        let result = elab.solve();
        assert!(
            result.is_err(),
            "unification should fail by rigid argument mismatch"
        );
    }

    #[test]
    fn unify_same_local_delta_head_with_mismatched_args_fails_without_panic() {
        let f_id = Id::from_qualified_name(&QualifiedName::from_str("foo.f"));
        let x_id = Id::from_name(&Name::from_str("x"));
        let y_id = Id::from_name(&Name::from_str("y"));
        let c = QualifiedName::from_str("c");
        let c_term = mk_const(c.clone(), vec![], vec![]);

        let mut local_env = tt::LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![LocalDelta {
                id: f_id,
                target: c_term.clone(),
                height: 0,
            }],
            locals: vec![
                Local {
                    id: f_id,
                    ty: mk_type_prop().arrow([mk_type_prop()]),
                },
                Local {
                    id: x_id,
                    ty: mk_type_prop(),
                },
                Local {
                    id: y_id,
                    ty: mk_type_prop(),
                },
            ],
        };

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::from([(
            c.clone(),
            Const {
                local_types: vec![],
                local_classes: vec![],
                ty: mk_type_prop().arrow([mk_type_prop()]),
            },
        )]);
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let local_env_snapshot = local_env.clone();
        let mut elab = Elaborator::new(proof_env, &mut local_env, vec![]);

        let error = visit_error("expected failure", None);
        elab.push_term_constraint(
            local_env_snapshot,
            mk_app(mk_local(f_id), mk_local(x_id)),
            mk_app(mk_local(f_id), mk_local(y_id)),
            error,
        );
        let result = elab.solve();
        assert!(
            result.is_err(),
            "unification should fail by rigid argument mismatch"
        );
    }

    #[test]
    fn unfold_constraint_keeps_head_arguments_as_is() {
        let f = QualifiedName::from_str("f");
        let g = QualifiedName::from_str("g");
        let u = Id::from_name(&Name::from_str("u"));
        let mut local_env = tt::LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![],
            locals: vec![],
        };

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::from([
            (
                f.clone(),
                Const {
                    local_types: vec![u],
                    local_classes: vec![],
                    ty: mk_type_prop(),
                },
            ),
            (
                g.clone(),
                Const {
                    local_types: vec![],
                    local_classes: vec![],
                    ty: mk_type_prop(),
                },
            ),
        ]);
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::from([(
            f.clone(),
            Delta {
                local_types: vec![u],
                local_classes: vec![],
                target: mk_const(g, vec![], vec![]),
                height: 0,
            },
        )]);
        let kappa_table: HashMap<QualifiedName, Kappa> = HashMap::new();
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::new();
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let mut elab = Elaborator::new(proof_env, &mut local_env, vec![]);

        let left_ty_arg = mk_fresh_type_hole();
        let Type::Hole(hole) = left_ty_arg else {
            unreachable!();
        };
        elab.type_subst_map.insert(hole.id, mk_type_prop());

        let error = visit_error("expected success", None);
        let left = mk_const(f.clone(), vec![Type::Hole(hole.clone())], vec![]);
        let right = mk_const(f, vec![mk_type_prop()], vec![]);
        let conflict = elab.find_conflict_in_terms(
            tt::LocalEnv {
                local_types: vec![],
                local_classes: vec![],
                local_deltas: vec![],
                locals: vec![],
            },
            left,
            right,
            error,
        );
        assert!(
            conflict.is_none(),
            "should defer by adding an unfold constraint"
        );

        let c = elab
            .queue_unfold
            .front()
            .expect("unfold constraint should be queued");
        let Term::Const(left_head) = c.left.head() else {
            panic!("expected const head");
        };
        assert_eq!(left_head.ty_args, vec![Type::Hole(hole)]);
    }

    #[test]
    fn kappa_unfold_constraint_uses_head_type_not_receiver_instance() {
        let method_name = QualifiedName::from_str("m");
        let body_name = QualifiedName::from_str("id");
        let class_name = QualifiedName::from_str("C");
        let instance_name = QualifiedName::from_str("inst.C");
        let u = Id::from_name(&Name::from_str("u"));
        let v = Id::from_name(&Name::from_str("v"));
        let x_id = Id::from_name(&Name::from_str("x"));
        let y_id = Id::from_name(&Name::from_str("y"));

        let left_head = mk_const(
            method_name.clone(),
            vec![mk_type_prop(), mk_type_prop()],
            vec![mk_instance_global(
                instance_name.clone(),
                vec![mk_type_prop(), mk_type_prop()],
                vec![],
            )],
        );
        let right_head = mk_const(
            method_name.clone(),
            vec![mk_type_prop(), mk_type_prop()],
            vec![mk_instance_global(
                instance_name.clone(),
                vec![
                    mk_type_prop(),
                    mk_type_arrow(mk_type_prop(), mk_type_prop()),
                ],
                vec![],
            )],
        );

        let mut local_env = tt::LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![],
            locals: vec![
                Local {
                    id: x_id,
                    ty: mk_type_prop(),
                },
                Local {
                    id: y_id,
                    ty: mk_type_prop(),
                },
            ],
        };

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::from([
            (
                method_name.clone(),
                Const {
                    local_types: vec![u, v],
                    local_classes: vec![Class {
                        name: class_name.clone(),
                        args: vec![mk_type_local(u), mk_type_local(v)],
                    }],
                    ty: mk_type_prop().arrow([mk_type_prop()]),
                },
            ),
            (
                body_name.clone(),
                Const {
                    local_types: vec![],
                    local_classes: vec![],
                    ty: mk_type_prop().arrow([mk_type_prop()]),
                },
            ),
        ]);
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> =
            HashMap::from([(method_name.clone(), Kappa)]);
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::from([(
            instance_name,
            ClassInstance {
                local_types: vec![u, v],
                local_classes: vec![],
                target: Class {
                    name: class_name,
                    args: vec![mk_type_local(u), mk_type_local(v)],
                },
                method_table: HashMap::from([(method_name, mk_const(body_name, vec![], vec![]))]),
            },
        )]);
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let mut elab = Elaborator::new(proof_env, &mut local_env, vec![]);

        let conflict = elab.find_conflict_in_terms(
            tt::LocalEnv {
                local_types: vec![],
                local_classes: vec![],
                local_deltas: vec![],
                locals: vec![
                    Local {
                        id: x_id,
                        ty: mk_type_prop(),
                    },
                    Local {
                        id: y_id,
                        ty: mk_type_prop(),
                    },
                ],
            },
            mk_app(left_head, mk_local(x_id)),
            mk_app(right_head, mk_local(y_id)),
            visit_error("expected success", None),
        );
        assert!(
            conflict.is_none(),
            "comparison should keep searching by unfolding, not fail immediately"
        );
        assert!(
            !elab.queue_unfold.is_empty(),
            "kappa unfold constraints should be queued based on head type even when receiver instances differ"
        );
    }

    #[test]
    fn kappa_unfold_constraint_requires_matching_head_class() {
        let method_name = QualifiedName::from_str("m");
        let body_name = QualifiedName::from_str("id");
        let class_name = QualifiedName::from_str("C");
        let instance_name = QualifiedName::from_str("inst.C");
        let u = Id::from_name(&Name::from_str("u"));
        let v = Id::from_name(&Name::from_str("v"));
        let x_id = Id::from_name(&Name::from_str("x"));
        let y_id = Id::from_name(&Name::from_str("y"));

        let left_head = mk_const(
            method_name.clone(),
            vec![mk_type_prop(), mk_type_prop()],
            vec![mk_instance_global(
                instance_name.clone(),
                vec![mk_type_prop(), mk_type_prop()],
                vec![],
            )],
        );
        let right_head = mk_const(
            method_name.clone(),
            vec![
                mk_type_prop(),
                mk_type_arrow(mk_type_prop(), mk_type_prop()),
            ],
            vec![mk_instance_global(
                instance_name.clone(),
                vec![mk_type_prop(), mk_type_prop()],
                vec![],
            )],
        );

        let mut local_env = tt::LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![],
            locals: vec![
                Local {
                    id: x_id,
                    ty: mk_type_prop(),
                },
                Local {
                    id: y_id,
                    ty: mk_type_prop(),
                },
            ],
        };

        let type_const_table: HashMap<QualifiedName, Kind> = HashMap::new();
        let const_table: HashMap<QualifiedName, Const> = HashMap::from([
            (
                method_name.clone(),
                Const {
                    local_types: vec![u, v],
                    local_classes: vec![Class {
                        name: class_name.clone(),
                        args: vec![mk_type_local(u), mk_type_local(v)],
                    }],
                    ty: mk_type_prop().arrow([mk_type_prop()]),
                },
            ),
            (
                body_name.clone(),
                Const {
                    local_types: vec![],
                    local_classes: vec![],
                    ty: mk_type_prop().arrow([mk_type_prop()]),
                },
            ),
        ]);
        let delta_table: HashMap<QualifiedName, Delta> = HashMap::new();
        let kappa_table: HashMap<QualifiedName, Kappa> =
            HashMap::from([(method_name.clone(), Kappa)]);
        let class_predicate_table: HashMap<QualifiedName, ClassType> = HashMap::new();
        let class_instance_table: HashMap<QualifiedName, ClassInstance> = HashMap::from([(
            instance_name,
            ClassInstance {
                local_types: vec![u, v],
                local_classes: vec![],
                target: Class {
                    name: class_name,
                    args: vec![mk_type_local(u), mk_type_local(v)],
                },
                method_table: HashMap::from([(method_name, mk_const(body_name, vec![], vec![]))]),
            },
        )]);
        let axiom_table: HashMap<QualifiedName, proof::Axiom> = HashMap::new();
        let tt_env = tt::Env {
            type_const_table: &type_const_table,
            const_table: &const_table,
            delta_table: &delta_table,
            kappa_table: &kappa_table,
            class_predicate_table: &class_predicate_table,
            class_instance_table: &class_instance_table,
        };
        let proof_env = proof::Env {
            tt_env,
            axiom_table: &axiom_table,
        };
        let mut elab = Elaborator::new(proof_env, &mut local_env, vec![]);

        let conflict = elab.find_conflict_in_terms(
            tt::LocalEnv {
                local_types: vec![],
                local_classes: vec![],
                local_deltas: vec![],
                locals: vec![
                    Local {
                        id: x_id,
                        ty: mk_type_prop(),
                    },
                    Local {
                        id: y_id,
                        ty: mk_type_prop(),
                    },
                ],
            },
            mk_app(left_head, mk_local(x_id)),
            mk_app(right_head, mk_local(y_id)),
            visit_error("expected success", None),
        );
        assert!(
            conflict.is_none(),
            "comparison should keep searching by unfolding, not fail immediately"
        );
        assert!(
            elab.queue_unfold.is_empty(),
            "kappa unfold constraints should not be queued when instantiated head classes differ"
        );
        assert!(
            !elab.term_constraints.is_empty(),
            "when not queued, unfold should continue via pushed term constraints"
        );
    }
}
