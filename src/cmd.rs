use std::{collections::HashMap, iter::zip};

use anyhow::bail;

use crate::{
    elab,
    expr::{self, mk_expr_app, mk_expr_assume, mk_expr_assump, Expr},
    parse::{AxiomInfo, ConstInfo, Nasmespace, TokenTable},
    print::OpTable,
    proof::{self, mk_type_prop},
    tt::{
        mk_const, mk_fresh_type_hole, mk_local, mk_type_arrow, mk_type_const, mk_type_local,
        DefInfo, Kind, LocalEnv, Name, ProjInfo, Term, Type,
    },
};

#[derive(Debug, Clone)]
pub enum Cmd {
    Infix(CmdInfix),
    Infixr(CmdInfixr),
    Infixl(CmdInfixl),
    Prefix(CmdPrefix),
    Nofix(CmdNofix),
    Def(CmdDef),
    Axiom(CmdAxiom),
    Lemma(CmdLemma),
    Const(CmdConst),
    TypeConst(CmdTypeConst),
    LocalTypeConst(CmdLocalTypeConst),
    TypeInductive(CmdTypeInductive),
    Inductive(CmdInductive),
    Structure(CmdStructure),
    Instance(CmdInstance),
    Class(CmdClass),
}

#[derive(Clone, Debug)]
pub struct CmdInfix {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug)]
pub struct CmdInfixr {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug)]
pub struct CmdInfixl {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug)]
pub struct CmdPrefix {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug)]
pub struct CmdNofix {
    pub op: String,
    pub entity: Name,
}

#[derive(Clone, Debug)]
pub struct CmdDef {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub local_classes: Vec<(Name, Type)>,
    pub ty: Type,
    pub holes: Vec<(Name, Type)>,
    pub class_constraints: Vec<Term>,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdAxiom {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdLemma {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub target: Term,
    pub holes: Vec<(Name, Type)>,
    pub expr: Expr,
}

#[derive(Clone, Debug)]
pub struct CmdConst {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct CmdTypeConst {
    pub name: Name,
    pub kind: Kind,
}

#[derive(Clone, Debug)]
pub struct CmdLocalTypeConst {
    pub variables: Vec<Name>,
}

#[derive(Clone, Debug)]
pub struct CmdTypeInductive {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub ctors: Vec<DataConstructor>,
}

#[derive(Clone, Debug)]
pub struct DataConstructor {
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct CmdInductive {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub params: Vec<(Name, Type)>,
    pub target_ty: Type,
    pub ctors: Vec<Constructor>,
}

#[derive(Clone, Debug)]
pub struct Constructor {
    pub name: Name,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdStructure {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub fields: Vec<StructureField>,
}

#[derive(Clone, Debug)]
pub enum StructureField {
    Const(StructureConst),
    Axiom(StructureAxiom),
}

#[derive(Clone, Debug)]
pub struct StructureConst {
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct StructureAxiom {
    pub name: Name,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct CmdInstance {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub params: Vec<(Name, Type)>,
    pub target_ty: Type,
    pub fields: Vec<InstanceField>,
}

#[derive(Clone, Debug)]
pub enum InstanceField {
    Def(InstanceDef),
    Lemma(InstanceLemma),
}

#[derive(Clone, Debug)]
pub struct InstanceDef {
    pub name: Name,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct InstanceLemma {
    pub name: Name,
    pub target: Term,
    pub holes: Vec<(Name, Type)>,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct CmdClass {
    pub local_types: Vec<Name>,
    pub params: Vec<(Name, Type)>,
    pub ty: Type,
    pub target: Term,
}

#[derive(Debug, Clone, Default)]
pub struct Eval {
    pub proof_env: proof::Env,
    pub tt: TokenTable,
    pub ns: Nasmespace,
    pub pp: OpTable,
    pub local_type_consts: Vec<Name>,
    pub structure_table: HashMap<Name, CmdStructure>,
    pub database: Vec<CmdClass>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Fixity {
    Infix,
    Infixl,
    Infixr,
    Nofix,
    Prefix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operator {
    pub symbol: String,
    pub fixity: Fixity,
    pub prec: usize,
    pub entity: Name,
}

impl Eval {
    fn add_const(
        &mut self,
        name: Name,
        local_types: Vec<Name>,
        local_classes: Vec<(Name, Type)>,
        ty: Type,
    ) {
        self.ns.consts.insert(
            name,
            ConstInfo {
                type_arity: local_types.len(),
                num_local_classes: local_classes.len(),
            },
        );
        self.proof_env.tt_env.consts.insert(name, (local_types, ty));
    }

    fn add_axiom(&mut self, name: Name, local_types: Vec<Name>, target: Term) {
        println!("{target}");
        assert!(self.is_wff(&local_types, &target));
        self.ns.axioms.insert(
            name,
            AxiomInfo {
                type_arity: local_types.len(),
                num_params: target.clone().ungeneralize().len(),
            },
        );
        self.proof_env.axioms.insert(name, (local_types, target));
    }

    fn add_type_const(&mut self, name: Name, kind: Kind) {
        self.ns.type_consts.insert(name);
        self.proof_env.tt_env.type_consts.insert(name, kind);
    }

    fn has_const(&self, name: Name) -> bool {
        self.proof_env.tt_env.consts.contains_key(&name)
    }

    fn has_axiom(&self, name: Name) -> bool {
        self.proof_env.axioms.contains_key(&name)
    }

    fn has_type_const(&self, name: Name) -> bool {
        self.proof_env.tt_env.type_consts.contains_key(&name)
    }

    fn is_wff(&self, local_types: &[Name], target: &Term) -> bool {
        let mut local_env = LocalEnv {
            local_types: local_types.to_vec(),
            locals: vec![],
            holes: vec![],
        };
        let mut target = target.clone();
        self.proof_env
            .tt_env
            .check_type(&mut local_env, &mut target, &mut mk_type_prop())
            .is_ok()
    }

    pub fn run_cmd(&mut self, cmd: Cmd) -> anyhow::Result<()> {
        match cmd {
            Cmd::Infix(inner) => {
                let CmdInfix { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infix,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Infixr(inner) => {
                let CmdInfixr { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infixr,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;

                Ok(())
            }
            Cmd::Infixl(inner) => {
                let CmdInfixl { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infixl,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;

                Ok(())
            }
            Cmd::Prefix(inner) => {
                let CmdPrefix { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Prefix,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Nofix(inner) => {
                let CmdNofix { op, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Nofix,
                    prec: usize::MAX,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Def(inner) => {
                let CmdDef {
                    name,
                    mut local_types,
                    local_classes,
                    mut ty,
                    holes,
                    class_constraints,
                    mut target,
                } = inner;
                if self.has_const(name) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !ty.contains_local(local_type_const)
                        && !local_classes
                            .iter()
                            .any(|(_, t)| t.contains_local(local_type_const))
                    {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes,
                };
                for i in 0..local_classes.len() {
                    for j in i + 1..local_classes.len() {
                        if local_classes[i].0 == local_classes[j].0 {
                            bail!("duplicate local class parameters");
                        }
                    }
                }
                for &(x, ref t) in &local_classes {
                    self.proof_env.tt_env.ensure_wft(&local_env, t)?;
                    local_env.locals.push((x, t.clone()));
                }
                elab::Elaborator::new(
                    &self.proof_env.tt_env,
                    &mut local_env,
                    &self.proof_env.axioms,
                    &self.structure_table,
                    &self.database,
                )
                .elaborate_term(&mut target, &ty, class_constraints)?;
                // well-formedness check is completed.
                ty.arrow(local_classes.iter().map(|(_, t)| t.clone()));
                target.abs(&local_classes, false);
                self.add_const(
                    name,
                    local_env.local_types.clone(),
                    local_classes,
                    ty.clone(),
                );
                self.proof_env.tt_env.defs.insert(
                    name,
                    DefInfo {
                        local_types: local_env.local_types,
                        target,
                        hint: self.proof_env.tt_env.defs.len(),
                    },
                );
                Ok(())
            }
            Cmd::Axiom(inner) => {
                let CmdAxiom {
                    name,
                    mut local_types,
                    mut target,
                } = inner;
                if self.has_axiom(name) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !target.contains_local_type(local_type_const) {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target,
                    &mut mk_type_prop(),
                )?;
                self.add_axiom(name, local_env.local_types, target);
                Ok(())
            }
            Cmd::Lemma(inner) => {
                let CmdLemma {
                    name,
                    mut local_types,
                    mut target,
                    holes,
                    expr,
                } = inner;
                if self.has_axiom(name) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !target.contains_local_type(local_type_const) {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: holes.clone(),
                };
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target,
                    &mut mk_type_prop(),
                )?;
                // auto insert 'change'
                let mut expr = mk_expr_app(
                    mk_expr_assume(target.clone(), mk_expr_assump(target.clone())),
                    expr,
                    target.clone(),
                );
                elab::Elaborator::new(
                    &self.proof_env.tt_env,
                    &mut local_env,
                    &self.proof_env.axioms,
                    &self.structure_table,
                    &self.database,
                )
                .elaborate_expr(&mut expr)?;
                local_env
                    .holes
                    .truncate(local_env.holes.len() - holes.len());
                let mut h = expr::Env {
                    axioms: &self.proof_env.axioms,
                    tt_env: &self.proof_env.tt_env,
                    tt_local_env: &mut local_env,
                }
                .run(&expr);
                self.proof_env.check_prop(
                    &mut local_env,
                    &mut proof::Context::default(),
                    &mut h,
                    &target,
                )?;
                self.add_axiom(name, local_env.local_types, target);
                Ok(())
            }
            Cmd::Const(inner) => {
                let CmdConst {
                    name,
                    mut local_types,
                    ty,
                } = inner;
                if self.has_const(name) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !ty.contains_local(local_type_const) {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env.tt_env.ensure_wft(&local_env, &ty)?;
                self.add_const(
                    name,
                    local_env.local_types,
                    vec![], /* TODO(typeclass) */
                    ty,
                );
                Ok(())
            }
            Cmd::TypeConst(inner) => {
                let CmdTypeConst { name, kind } = inner;
                if self.has_type_const(name) {
                    bail!("already defined");
                }
                self.add_type_const(name, kind);
                Ok(())
            }
            Cmd::LocalTypeConst(inner) => {
                let CmdLocalTypeConst { variables } = inner;
                for i in 0..variables.len() {
                    for j in i + 1..variables.len() {
                        if variables[i] == variables[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for v in &variables {
                    if self.local_type_consts.contains(v) {
                        bail!("type variable already defined");
                    }
                }
                self.local_type_consts.extend(variables);
                Ok(())
            }
            Cmd::TypeInductive(cmd) => self.run_type_inductive_cmd(cmd),
            Cmd::Inductive(cmd) => self.run_inductive_cmd(cmd),
            Cmd::Structure(cmd) => self.run_structure_cmd(cmd),
            Cmd::Instance(cmd) => self.run_instance_cmd(cmd),
            Cmd::Class(cmd) => {
                let CmdClass {
                    mut local_types,
                    params,
                    mut ty,
                    mut target,
                } = cmd;
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                for local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !ty.contains_local(local_type_const)
                        && !params
                            .iter()
                            .any(|(_, t)| t.contains_local(local_type_const))
                    {
                        // unused
                        continue;
                    }
                    local_types.insert(0, *local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.clone(),
                    locals: vec![],
                    holes: vec![],
                };
                for i in 0..params.len() {
                    for j in i + 1..params.len() {
                        if params[i].0 == params[j].0 {
                            bail!("duplicate parameter names");
                        }
                    }
                }
                for &(x, ref t) in &params {
                    self.proof_env.tt_env.ensure_wft(&local_env, t)?;
                    local_env.locals.push((x, t.clone()));
                }
                self.proof_env
                    .tt_env
                    .check_type(&mut local_env, &mut target, &mut ty)?;
                for rule in &self.database {
                    let ty = {
                        let mut subst = vec![];
                        for &name in &local_env.local_types {
                            subst.push((name, mk_fresh_type_hole()));
                        }
                        let mut ty = ty.clone();
                        ty.subst(&subst);
                        ty
                    };
                    let rule_head = {
                        let mut subst = vec![];
                        for &name in &rule.local_types {
                            subst.push((name, mk_fresh_type_hole()));
                        }
                        let mut ty = rule.ty.clone();
                        ty.subst(&subst);
                        ty
                    };
                    if ty.unify(&rule_head).is_some() {
                        bail!("overlapping instances are disallowed");
                    }
                }
                // TODO(typeclass): detect cycles
                // well-formedness check is completed
                self.database.push(CmdClass {
                    local_types,
                    params,
                    ty,
                    target,
                });
                Ok(())
            }
        }
    }

    fn run_type_inductive_cmd(&mut self, cmd: CmdTypeInductive) -> anyhow::Result<()> {
        let CmdTypeInductive {
            name,
            local_types,
            ctors,
        } = cmd;
        if self.has_type_const(name) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i] == local_types[j] {
                    bail!("duplicate type variables");
                }
            }
        }
        let mut local_env = LocalEnv {
            local_types: local_types.clone(),
            locals: vec![],
            holes: vec![],
        };
        local_env.local_types.insert(0, name);
        for i in 0..ctors.len() {
            for j in i + 1..ctors.len() {
                if ctors[i].name == ctors[j].name {
                    bail!("duplicate constructors");
                }
            }
        }
        for ctor in &ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            if self.has_const(ctor_name) {
                bail!("already defined");
            }
            let ctor_spec_name = Name::intern(&format!("{}.spec", ctor_name)).unwrap();
            if self.has_const(ctor_spec_name) {
                bail!("already defined");
            }
            self.proof_env.tt_env.ensure_wft(&local_env, &ctor.ty)?;
            let mut t = ctor.ty.clone();
            let args = t.unarrow();
            if t != mk_type_local(name) {
                bail!("invalid constructor: {t}");
            }
            for mut a in args {
                let xs = a.unarrow();
                for x in &xs {
                    if x.contains_local(&name) {
                        bail!("constructor violates strict positivity");
                    }
                }
                if a != mk_type_local(name) && a.contains_local(&name) {
                    bail!("nested inductive type is unsupported");
                }
            }
        }
        let ind_name = Name::intern(&format!("{}.ind", name)).unwrap();
        if self.has_axiom(ind_name) {
            bail!("already defined");
        }
        let rec_name = Name::intern(&format!("{}.rec", name)).unwrap();
        if self.has_const(rec_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.

        // generate type constructor
        self.add_type_const(name, Kind(local_types.len()));

        // generate data constructors
        let target_ty = {
            // Foo u v
            let mut c = mk_type_const(name);
            c.apply(local_types.iter().map(|t| mk_type_local(*t)));
            c
        };
        // Foo ↦ Foo u v
        let subst = [(name, target_ty.clone())];
        let mut cs = vec![];
        for ctor in &ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut ty = ctor.ty.clone();
            ty.subst(&subst);
            cs.push((ctor_name, ty));
        }
        for (name, ty) in cs {
            self.add_const(
                name,
                local_types.clone(),
                vec![], /* TODO(typeclass) */
                ty,
            );
        }

        // generate the induction principle
        //
        // For the following definition of the type of ordinal numbers,
        //
        //   inductive ord : Type
        //   | limit : (ℕ → ord) → ord
        //   | succ : ord → ord
        //   | zero : ord
        //
        // the following induction principle is defined:
        //
        //   ind : ∀ α P,
        //           (∀ f, (∀ n, P (f n)) → P (limit f)) →
        //           (∀ α, P α → P (succ α)) →
        //           P zero →
        //           P α
        let motive = Name::fresh_with_name("motive");
        let mut guards = vec![];
        for ctor in &ctors {
            let mut args = vec![];
            for arg in ctor.ty.clone().unarrow() {
                args.push((Name::fresh(), arg));
            }
            // induction hypotheses
            let mut ih_list = vec![];
            for (arg_name, arg_ty) in &args {
                let mut t = arg_ty.clone();
                let mut xs = vec![];
                for x in t.unarrow() {
                    xs.push((Name::fresh(), x));
                }
                if t != mk_type_local(name) {
                    continue;
                }
                // ∀ xs, P (a xs)
                let mut a = mk_local(*arg_name);
                a.apply(xs.iter().map(|(name, _)| mk_local(*name)));
                let mut h = mk_local(motive);
                h.apply([a]);
                h.generalize(&xs);
                ih_list.push(h);
            }
            // ∀ args, {IH} → P (C args)
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut a = mk_const(
                ctor_name,
                local_types.iter().map(|t| mk_type_local(*t)).collect(),
            );
            a.apply(args.iter().map(|(name, _)| mk_local(*name)));
            let mut target = mk_local(motive);
            target.apply([a]);
            target.guard(ih_list);
            for (_, ty) in &mut args {
                ty.subst(&subst);
            }
            target.generalize(&args);
            guards.push(target);
        }
        // ∀ x P, {guards} → P x
        let x = Name::fresh_with_name("x");
        let mut target = mk_local(motive);
        target.apply([mk_local(x)]);
        target.guard(guards);
        target.generalize(&[
            (x, target_ty.clone()),
            (motive, mk_type_arrow(target_ty.clone(), mk_type_prop())),
        ]);
        self.add_axiom(ind_name, local_types.clone(), target);

        // generate the recursion principle
        //
        // For ord, the following recursor is defined:
        //
        //   rec.{u} : ord → ((ℕ → ord) → (ℕ → u) → u) → (ord → u → u) → u → u
        //
        // together with the following rules:
        //
        //   rec (limit f) ≡ λ k₁ k₂ k₃, k₁ f (λ x, rec (f x) k₁ k₂ k₃)
        //   rec (succ α) ≡ λ k₁ k₂ k₃, k₂ α (rec α k₁ k₂ k₃)
        //   rec zero ≡ λ k₁ k₂ k₃, k₃
        //
        let rec_ty_var = Name::fresh_with_name("α");
        let mut rec_local_types = local_types.clone();
        rec_local_types.push(rec_ty_var);
        let mut ctor_params_list = vec![];
        for ctor in &ctors {
            let mut ctor_params = vec![];
            let ctor_param_tys = ctor.ty.clone().unarrow();
            for mut ctor_param_ty in ctor_param_tys {
                ctor_param_ty.subst(&subst);
                ctor_params.push((Name::fresh(), ctor_param_ty));
            }
            ctor_params_list.push(ctor_params);
        }
        let mut cont_params = vec![];
        for _ in &ctors {
            cont_params.push(Name::fresh_with_name("k"));
        }
        let mut cont_param_tys = vec![];
        let mut rhs_bodies = vec![];
        for ((ctor, cont), ctor_params) in ctors
            .iter()
            .zip(cont_params.iter())
            .zip(ctor_params_list.iter())
        {
            let mut cont_arg_tys = vec![];
            let mut target = mk_local(*cont);

            // pass the constructor arguments through
            for (param, param_ty) in ctor_params {
                cont_arg_tys.push(param_ty.clone());
                target.apply([mk_local(*param)]);
            }
            // stepping
            let ctor_arg_tys = ctor.ty.clone().unarrow();
            for (ctor_arg, (param, _)) in ctor_arg_tys.into_iter().zip(ctor_params.iter()) {
                let mut ctor_arg_target = ctor_arg.clone();
                let arg_tys = ctor_arg_target.unarrow();
                if ctor_arg_target != mk_type_local(name) {
                    continue;
                }
                let mut t = ctor_arg.clone();
                t.subst(&[(name, mk_type_local(rec_ty_var))]);
                cont_arg_tys.push(t);

                let binders: Vec<_> = arg_tys
                    .into_iter()
                    .map(|arg_ty| {
                        let name = Name::fresh();
                        (name, arg_ty)
                    })
                    .collect();
                let mut m = mk_const(
                    rec_name,
                    rec_local_types.iter().map(|t| mk_type_local(*t)).collect(),
                );
                let mut a = mk_local(*param);
                a.apply(binders.iter().map(|(x, _)| mk_local(*x)));
                m.apply([a]);
                m.apply(cont_params.iter().map(|k| mk_local(*k)));
                m.abs(&binders, true);
                target.apply([m]);
            }

            let mut cont_param_ty = mk_type_local(rec_ty_var);
            cont_param_ty.arrow(cont_arg_tys);
            cont_param_tys.push(cont_param_ty);

            rhs_bodies.push(target);
        }
        let mut rec_ty = mk_type_local(rec_ty_var);
        rec_ty.arrow(cont_param_tys.clone());
        rec_ty.arrow([target_ty]);
        self.add_const(
            rec_name,
            rec_local_types.clone(),
            vec![], /* TODO(typeclass) */
            rec_ty,
        );

        let rhs_binders = cont_params
            .into_iter()
            .zip(&cont_param_tys)
            .map(|(x, t)| (x, t.clone()))
            .collect::<Vec<_>>();
        for ((rhs_body, ctor_params), ctor) in rhs_bodies
            .into_iter()
            .zip(ctor_params_list.into_iter())
            .zip(ctors.iter())
        {
            let mut lhs = mk_const(
                rec_name,
                rec_local_types.iter().map(|t| mk_type_local(*t)).collect(),
            );
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut lhs_arg = mk_const(
                ctor_name,
                local_types.iter().map(|t| mk_type_local(*t)).collect(),
            );
            lhs_arg.apply(ctor_params.iter().map(|(x, _)| mk_local(*x)));
            lhs.apply([lhs_arg]);

            let mut rhs = rhs_body;
            rhs.abs(&rhs_binders, true);

            let mut eq_ty = mk_type_local(rec_ty_var);
            eq_ty.arrow(cont_param_tys.clone());

            let mut spec = mk_const(Name::intern("eq").unwrap(), vec![eq_ty]);
            spec.apply([lhs, rhs]);
            spec.generalize(&ctor_params);

            let ctor_spec_name = Name::intern(&format!("{}.spec", ctor_name)).unwrap();
            self.add_axiom(ctor_spec_name, rec_local_types.clone(), spec);
        }
        Ok(())
    }

    fn run_inductive_cmd(&mut self, cmd: CmdInductive) -> anyhow::Result<()> {
        // Given the following inductive predicate:
        //
        //   inductive P.{u} (x : τ) : σ → Prop
        //   | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        //
        // the following set of delcarations is generated:
        //
        //  const P.{u} : τ → σ → Prop
        //  axiom P.intro.{u} (x : τ) : ∀ y, φ → (∀ z, ψ → P.{u} x M) → P.{u} x N
        //  axiom P.ind.{u} (x : τ) (w : σ) (C : σ → Prop)
        //  : P x w → (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        //
        let CmdInductive {
            name,
            mut local_types,
            params,
            target_ty,
            mut ctors,
        } = cmd;
        if self.has_const(name) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i] == local_types[j] {
                    bail!("duplicate type variables");
                }
            }
        }
        for local_type_const in self.local_type_consts.iter().rev() {
            if local_types.contains(local_type_const) {
                // shadowed by the .{} binder
                continue;
            }
            if params
                .iter()
                .any(|(_, ty)| ty.contains_local(local_type_const))
                || target_ty.contains_local(local_type_const)
            {
                local_types.insert(0, *local_type_const);
            }
        }
        let mut local_env = LocalEnv {
            local_types,
            locals: vec![],
            holes: vec![],
        };
        for i in 0..params.len() {
            for j in i + 1..params.len() {
                if params[i].0 == params[j].0 {
                    bail!("duplicate parameters");
                }
            }
            self.proof_env.tt_env.ensure_wft(&local_env, &params[i].1)?;
            local_env.locals.push((params[i].0, params[i].1.clone()));
        }
        self.proof_env.tt_env.ensure_wft(&local_env, &target_ty)?;
        if target_ty.target() != &mk_type_prop() {
            bail!("the target type of an inductive predicate must be Prop");
        }
        for i in 0..ctors.len() {
            for j in i + 1..ctors.len() {
                if ctors[i].name == ctors[j].name {
                    bail!("duplicate constructors");
                }
            }
        }
        local_env.locals.insert(0, (name, target_ty.clone()));
        let mut ctor_params_list = vec![];
        let mut ctor_args_list = vec![];
        let mut ctor_target_list = vec![];
        let mut ctor_ind_args_list = vec![];
        for ctor in &mut ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            if self.has_axiom(ctor_name) {
                bail!("already defined");
            }
            self.proof_env.tt_env.check_type(
                &mut local_env,
                &mut ctor.target,
                &mut mk_type_prop(),
            )?;

            let mut m = ctor.target.clone();
            let ctor_params = m.ungeneralize();
            ctor_params_list.push(ctor_params);
            let ctor_args = m.unguard();
            ctor_args_list.push(ctor_args.clone());
            if !m.head().typed_eq(&mk_local(name)) {
                bail!("invalid constructor. Currently only Horn clauses are supported in inductive clauses: {m}");
            }
            for a in m.args() {
                if a.contains_local(&name) {
                    bail!("invalid target");
                }
            }
            ctor_target_list.push(m);
            let mut ctor_ind_args = vec![];
            for ctor_arg in &ctor_args {
                let mut m = ctor_arg.clone();
                loop {
                    let params = m.ungeneralize();
                    let args = m.unguard();
                    if params.is_empty() && args.is_empty() {
                        break;
                    }
                }
                if m.contains_local(&name) {
                    if !m.head().typed_eq(&mk_local(name)) {
                        bail!("invalid target");
                    }
                    for a in m.args() {
                        if a.contains_local(&name) {
                            bail!("invalid target");
                        }
                    }
                    ctor_ind_args.push(ctor_arg.clone());
                }
            }
            ctor_ind_args_list.push(ctor_ind_args);
        }
        local_env.locals.remove(0);
        let ind_name = Name::intern(&format!("{}.ind", name)).unwrap();
        if self.has_axiom(ind_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.

        // inductive P.{u} (x : τ) : σ → Prop
        // ↦ const P.{u} : τ → σ → Prop
        let mut pred_ty = target_ty.clone();
        let mut param_types = vec![];
        for (_, t) in &params {
            param_types.push(t.clone());
        }
        pred_ty.arrow(param_types);
        self.add_const(
            name,
            local_env.local_types.clone(),
            vec![], /* TODO(typeclass) */
            pred_ty,
        );

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.intro.{u} (x : τ) : ∀ y, φ → (∀ z, ψ → P.{u} x M) → P.{u} x N
        for ctor in &ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut target = ctor.target.clone();
            // P.{u} x
            let mut stash = mk_const(
                name,
                local_env
                    .local_types
                    .iter()
                    .map(|name| mk_type_local(*name))
                    .collect(),
            );
            stash.apply(params.iter().map(|(name, _)| mk_local(*name)));
            let subst = [(name, stash)];
            target.subst(&subst);
            target.generalize(&params);
            self.add_axiom(ctor_name, local_env.local_types.clone(), target);
        }

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.ind.{u} (x : τ) (w : σ) (C : σ → Prop)
        //  : P x w → (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        let indexes = target_ty
            .clone()
            .unarrow()
            .into_iter()
            .map(|t| (Name::fresh(), t))
            .collect::<Vec<_>>();
        let motive = Name::fresh_with_name("motive");
        // C w
        let mut target = mk_local(motive);
        target.apply(indexes.iter().map(|(x, _)| mk_local(*x)));
        let mut guards = vec![];
        // (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        for (ctor_params, (mut ctor_args, (ctor_target, mut ctor_ind_args))) in zip(
            ctor_params_list,
            zip(ctor_args_list, zip(ctor_target_list, ctor_ind_args_list)),
        ) {
            // P ↦ C
            let subst_with_motive = [(name, mk_local(motive))];

            let mut guard = ctor_target;

            // C N
            guard.subst(&subst_with_motive);

            // (∀ z, ψ → C M) → C N
            for ctor_ind_arg in &mut ctor_ind_args {
                ctor_ind_arg.subst(&subst_with_motive);
            }
            guard.guard(ctor_ind_args);

            // P ↦ P.{u} x
            let mut stash = mk_const(
                name,
                local_env
                    .local_types
                    .iter()
                    .map(|name| mk_type_local(*name))
                    .collect(),
            );
            stash.apply(params.iter().map(|(name, _)| mk_local(*name)));
            let subst = [(name, stash)];

            // φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
            for ctor_arg in &mut ctor_args {
                ctor_arg.subst(&subst);
            }
            guard.guard(ctor_args);

            // ∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
            guard.generalize(&ctor_params);

            guards.push(guard);
        }
        target.guard(guards);

        let mut p = mk_const(
            name,
            local_env
                .local_types
                .iter()
                .map(|name| mk_type_local(*name))
                .collect(),
        );
        p.apply(params.iter().map(|(name, _)| mk_local(*name)));
        p.apply(indexes.iter().map(|(x, _)| mk_local(*x)));
        target.guard([p]);

        target.generalize(&[(motive, target_ty.clone())]);
        target.generalize(&indexes);
        target.generalize(&params);

        self.add_axiom(ind_name, local_env.local_types, target);
        Ok(())
    }

    fn run_structure_cmd(&mut self, cmd: CmdStructure) -> anyhow::Result<()> {
        // Use the inhab type as a prototypical example:
        //
        // structure inhab u := {
        //  const rep : set u
        //  axiom inhabited : ∃ x, x ∈ rep
        // }
        let CmdStructure {
            name,
            local_types,
            mut fields,
        } = cmd;
        if self.has_type_const(name) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i] == local_types[j] {
                    bail!("duplicate type variables");
                }
            }
        }
        let mut local_env = LocalEnv {
            local_types: local_types.clone(),
            locals: vec![],
            holes: vec![],
        };
        let mut const_field_names = vec![];
        let mut axiom_field_names = vec![];
        for field in &mut fields {
            match field {
                StructureField::Const(field) => {
                    let StructureConst {
                        name: field_name,
                        ty: field_ty,
                    } = &*field;
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_const(fullname) {
                        bail!("already defined");
                    }
                    if const_field_names.contains(&field_name) {
                        bail!("duplicate const field");
                    }
                    const_field_names.push(field_name);
                    self.proof_env.tt_env.ensure_wft(&local_env, field_ty)?;
                    local_env.locals.push((*field_name, field_ty.clone()));
                }
                StructureField::Axiom(field) => {
                    let StructureAxiom {
                        name: ref field_name,
                        target,
                    } = field;
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_axiom(fullname) {
                        bail!("already defined");
                    }
                    if axiom_field_names.contains(&field_name) {
                        bail!("duplicate axiom field");
                    }
                    axiom_field_names.push(field_name);
                    self.proof_env.tt_env.check_type(
                        &mut local_env,
                        target,
                        &mut mk_type_prop(),
                    )?;
                }
            }
        }
        let abs_name = Name::intern(&format!("{}.abs", name)).unwrap();
        if self.has_axiom(abs_name) {
            bail!("already defined");
        }
        let ext_name = Name::intern(&format!("{}.ext", name)).unwrap();
        if self.has_axiom(ext_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.
        self.structure_table.insert(
            name,
            CmdStructure {
                name,
                local_types: local_types.clone(),
                fields: fields.clone(),
            },
        );
        self.add_type_const(name, Kind(local_types.len()));
        let instance = Name::fresh_with_name("d");
        let instance_ty = {
            let mut ty = mk_type_const(name);
            ty.apply(local_types.iter().map(|x| mk_type_local(*x)));
            ty
        };
        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    // rep : set u
                    // ↦ inhab.rep.{u} : inhab u → set u
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let mut ty = field.ty.clone();
                    ty.arrow([instance_ty.clone()]);
                    self.add_const(
                        fullname,
                        local_types.clone(),
                        vec![], /* TODO(typeclass) */
                        ty,
                    );

                    // rep ↦ inhab.rep.{u} d
                    let mut target = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                    );
                    target.apply([mk_local(instance)]);
                    subst.push((field.name, target));
                }
                StructureField::Axiom(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();

                    let mut target = field.target.clone();
                    target.subst(&subst);

                    target.generalize(&[(instance, instance_ty.clone())]);

                    self.add_axiom(fullname, local_types.clone(), target);
                }
            }
        }
        // generate abstraction principle
        // axiom inhab.abs.{u} (s : set u) : (∃ x, x ∈ s) → ∃ d, s = inhab.rep d
        let mut params = vec![];
        let mut guards = vec![];
        let mut chars = vec![];
        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    // (s : set u)
                    let param = Name::fresh_from(field.name);
                    params.push((param, field.ty.clone()));

                    // inhab.rep d
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let mut rhs = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                    );
                    rhs.apply([mk_local(instance)]);

                    // s = inhab.rep d
                    let mut char = mk_const(Name::intern("eq").unwrap(), vec![field.ty.clone()]);
                    char.apply([mk_local(param), rhs]);
                    chars.push(char);

                    // rep ↦ s
                    subst.push((field.name, mk_local(param)));
                }
                StructureField::Axiom(field) => {
                    let mut target = field.target.clone();
                    target.subst(&subst);

                    guards.push(target);
                }
            }
        }
        let mut abs = mk_const(Name::intern("exists").unwrap(), vec![instance_ty.clone()]);
        abs.apply([{
            let mut char = chars
                .into_iter()
                .reduce(|left, right| {
                    let mut conj = mk_const(Name::intern("and").unwrap(), vec![]);
                    conj.apply([left, right]);
                    conj
                })
                .unwrap_or_else(|| mk_const(Name::intern("true").unwrap(), vec![]));
            char.abs(&[(instance, instance_ty.clone())], true);
            char
        }]);
        abs.guard(guards);
        abs.generalize(&params);
        self.add_axiom(abs_name, local_types.clone(), abs);

        // generate extensionality
        // axiom inhab.ext.{u} (d₁ d₂ : inhab u) : inhab.rep d₁ = inhab.rep d₂ → d₁ = d₂
        let instance1 = Name::fresh_with_name("d₁");
        let instance2 = Name::fresh_with_name("d₂");
        let mut guards = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let proj = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                    );

                    let mut lhs = proj.clone();
                    lhs.apply([mk_local(instance1)]);
                    let mut rhs = proj;
                    rhs.apply([mk_local(instance2)]);

                    let mut guard = mk_const(Name::intern("eq").unwrap(), vec![field.ty.clone()]);
                    guard.apply([lhs, rhs]);
                    guards.push(guard);
                }
                StructureField::Axiom(_) => {}
            }
        }
        let mut target = mk_const(Name::intern("eq").unwrap(), vec![instance_ty.clone()]);
        target.apply([mk_local(instance1), mk_local(instance2)]);
        target.guard(guards);
        target.generalize(&[
            (instance1, instance_ty.clone()),
            (instance2, instance_ty.clone()),
        ]);
        self.add_axiom(ext_name, local_types.clone(), target);
        Ok(())
    }

    fn run_instance_cmd(&mut self, cmd: CmdInstance) -> anyhow::Result<()> {
        // instance power.inhab.{u} (A : set u) : inhab (set u) := {
        //   def rep := power A
        //   lemma inhabited := exists.intro empty_in_power
        // }
        //
        // generates:
        //
        //   const power.inhab.{u} : set u → inhab (set u)
        //   def power.inhab.rep.{u} (A : set u) : set (set u) := power A
        //   lemma power.inhab.inhabited.{u} : ∃ a, a ∈ power x := (..)
        //
        // with a definitional equality
        //
        //  inhab.rep (power.inhab A) ≡ power A
        //
        let CmdInstance {
            name,
            mut local_types,
            params,
            target_ty,
            mut fields,
        } = cmd;
        if self.has_const(name) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i] == local_types[j] {
                    bail!("duplicate type variables");
                }
            }
        }
        for local_type_const in self.local_type_consts.iter().rev() {
            if local_types.contains(local_type_const) {
                // shadowed by the .{} binder
                continue;
            }
            if params
                .iter()
                .any(|(_, ty)| ty.contains_local(local_type_const))
                || target_ty.contains_local(local_type_const)
            {
                local_types.insert(0, *local_type_const);
            }
        }
        let mut local_env = LocalEnv {
            local_types,
            locals: vec![],
            holes: vec![],
        };
        for i in 0..params.len() {
            for j in i + 1..params.len() {
                if params[i].0 == params[j].0 {
                    bail!("duplicate parameters");
                }
            }
            self.proof_env.tt_env.ensure_wft(&local_env, &params[i].1)?;
            local_env.locals.push((params[i].0, params[i].1.clone()));
        }
        self.proof_env.tt_env.ensure_wft(&local_env, &target_ty)?;
        let Type::Const(structure_name) = target_ty.head() else {
            bail!("type of instance must be a structure");
        };
        let Some(cmd_structure) = self.structure_table.get(structure_name) else {
            bail!("type of instance must be a structure");
        };
        let mut type_subst = vec![];
        for (&x, t) in zip(&cmd_structure.local_types, target_ty.args()) {
            type_subst.push((x, t.clone()));
        }
        let type_subst = type_subst;
        if cmd_structure.fields.len() != fields.len() {
            bail!("number of fields mismatch");
        }
        let mut subst = vec![];
        for (structure_field, field) in zip(&cmd_structure.fields, &mut fields) {
            match structure_field {
                StructureField::Const(structure_field) => {
                    let InstanceField::Def(InstanceDef {
                        name: ref field_name,
                        ty,
                        target,
                    }) = field
                    else {
                        bail!("definition expected");
                    };
                    let field_fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_const(field_fullname) {
                        bail!("already defined");
                    }
                    let axiom_fullname =
                        Name::intern(&format!("{}.{}.{}", structure_name, field_name, name))
                            .unwrap();
                    if self.has_axiom(axiom_fullname) {
                        bail!("already defined");
                    }
                    if structure_field.name != *field_name {
                        bail!("field name mismatch");
                    }
                    self.proof_env
                        .tt_env
                        .check_type(&mut local_env, target, ty)?;
                    let mut structure_field_ty = structure_field.ty.clone();
                    structure_field_ty.subst(&type_subst);
                    if structure_field_ty != *ty {
                        bail!("type mismatch");
                    }
                    subst.push((*field_name, target.clone()));
                }
                StructureField::Axiom(structure_field) => {
                    let InstanceField::Lemma(InstanceLemma {
                        name: ref field_name,
                        target,
                        ref holes,
                        ref expr,
                    }) = field
                    else {
                        bail!("lemma expected");
                    };
                    let field_fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_axiom(field_fullname) {
                        bail!("already defined");
                    }
                    if structure_field.name != *field_name {
                        bail!("field name mismatch");
                    }
                    self.proof_env.tt_env.check_type(
                        &mut local_env,
                        target,
                        &mut mk_type_prop(),
                    )?;
                    // auto insert 'change'
                    let mut expr = mk_expr_app(
                        mk_expr_assume(target.clone(), mk_expr_assump(target.clone())),
                        expr.clone(),
                        target.clone(),
                    );
                    local_env.holes.extend(holes.iter().cloned());
                    elab::Elaborator::new(
                        &self.proof_env.tt_env,
                        &mut local_env,
                        &self.proof_env.axioms,
                        &self.structure_table,
                        &self.database,
                    )
                    .elaborate_expr(&mut expr)?;
                    let mut h = expr::Env {
                        axioms: &self.proof_env.axioms,
                        tt_env: &self.proof_env.tt_env,
                        tt_local_env: &mut local_env,
                    }
                    .run(&expr);
                    local_env
                        .holes
                        .truncate(local_env.holes.len() - holes.len());
                    self.proof_env.check_prop(
                        &mut local_env,
                        &mut proof::Context::default(),
                        &mut h,
                        target,
                    )?;
                    let mut structure_field_target = structure_field.target.clone();
                    structure_field_target.subst_type(&type_subst);
                    structure_field_target.subst(&subst);
                    if !structure_field_target.typed_eq(target) {
                        bail!("target mismatch");
                    }
                }
            }
        }
        // well-formedness check is completed.

        // e.g. const power.inhab.{u} : set u → inhab (set u)
        let mut instance_ty = target_ty.clone();
        for (_, t) in params.iter().rev() {
            instance_ty.arrow([t.clone()]);
        }
        self.add_const(
            name,
            local_env.local_types.clone(),
            vec![], /* TODO(typeclass) */
            instance_ty,
        );

        for field in &fields {
            match field {
                InstanceField::Def(field) => {
                    let InstanceDef {
                        name: field_name,
                        ty,
                        target,
                    } = field;
                    // e.g. def power.inhab.rep.{u} (A : set u) : set (set u) := power A
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    let def_target_ty = {
                        let mut t = ty.clone();
                        t.arrow(params.iter().map(|(_, t)| t.clone()));
                        t
                    };
                    let def_target = {
                        let mut m = target.clone();
                        m.abs(&params, true);
                        m
                    };
                    self.add_const(
                        fullname,
                        local_env.local_types.clone(),
                        vec![], /* TODO(typeclass) */
                        def_target_ty,
                    );
                    self.proof_env.tt_env.defs.insert(
                        name,
                        DefInfo {
                            local_types: local_env.local_types.clone(),
                            target: def_target,
                            hint: self.proof_env.tt_env.defs.len(),
                        },
                    );

                    // e.g. example rep_of_power.{u} (A : set u) : inhab.rep (power.inhab A) = power A := eq.refl
                    let proj_name =
                        Name::intern(&format!("{}.{}", structure_name, field_name)).unwrap();
                    self.proof_env.tt_env.add_proj_rule(
                        proj_name,
                        name,
                        ProjInfo {
                            local_types: local_env.local_types.clone(),
                            params: params.iter().map(|&(x, _)| x).collect(),
                            target: target.clone(),
                        },
                    );
                }
                InstanceField::Lemma(field) => {
                    let InstanceLemma {
                        name: field_name,
                        target,
                        holes: _,
                        expr: _,
                    } = field;
                    // e.g. lemma power.inhab.inhabited.{u} : ∃ a, a ∈ power x := (..)
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    let mut target = target.clone();
                    target.generalize(&params);
                    self.add_axiom(fullname, local_env.local_types.clone(), target);
                }
            }
        }
        Ok(())
    }
}
