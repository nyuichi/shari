use std::{collections::HashMap, iter::zip, slice, vec};

use anyhow::bail;

use crate::{
    elab,
    expr::{self, Expr},
    parse::{AxiomInfo, ConstInfo, Nasmespace, TokenTable},
    print::OpTable,
    proof::{self, Axiom},
    tt::{
        self, mk_const, mk_fresh_type_hole, mk_instance_local, mk_local, mk_type_arrow,
        mk_type_const, mk_type_local, mk_type_prop, Class, ClassRule, ClassType, Const, Delta,
        Iota, Kind, LocalEnv, Name, Parameter, Term, Type,
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
    ClassStructure(CmdClassStructure),
    ClassInstance(CmdClassInstance),
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
    pub local_classes: Vec<Class>,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdAxiom {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdLemma {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub target: Term,
    pub holes: Vec<(Name, Type)>,
    pub expr: Expr,
}

#[derive(Clone, Debug)]
pub struct CmdConst {
    pub name: Name,
    pub local_classes: Vec<Class>,
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
    pub params: Vec<Parameter>,
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
    pub local_classes: Vec<Class>,
    pub params: Vec<Parameter>,
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
pub struct CmdClassStructure {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub fields: Vec<ClassStructureField>,
}

#[derive(Clone, Debug)]
pub enum ClassStructureField {
    Const(ClassStructureConst),
    Axiom(ClassStructureAxiom),
}

#[derive(Clone, Debug)]
pub struct ClassStructureConst {
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct ClassStructureAxiom {
    pub name: Name,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct CmdClassInstance {
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub target: Class,
    pub fields: Vec<ClassInstanceField>,
}

#[derive(Clone, Debug)]
pub enum ClassInstanceField {
    Def(ClassInstanceDef),
    Lemma(ClassInstanceLemma),
}

#[derive(Clone, Debug)]
pub struct ClassInstanceDef {
    pub name: Name,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct ClassInstanceLemma {
    pub name: Name,
    pub target: Term,
    pub holes: Vec<(Name, Type)>,
    pub expr: Expr,
}

#[derive(Debug, Clone, Default)]
pub struct Eval {
    pub tt: TokenTable,
    pub ns: Nasmespace,
    pub pp: OpTable,
    pub local_type_consts: Vec<Name>,
    pub type_const_table: HashMap<Name, Kind>,
    pub const_table: HashMap<Name, Const>,
    pub axiom_table: HashMap<Name, Axiom>,
    pub delta_table: HashMap<Name, Delta>,
    pub iota_table: HashMap<Name, HashMap<Name, Iota>>,
    pub class_predicate_table: HashMap<Name, ClassType>,
    pub class_database: Vec<ClassRule>,
    pub structure_table: HashMap<Name, CmdStructure>,
    pub class_structure_table: HashMap<Name, CmdClassStructure>,
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
        local_classes: Vec<Class>,
        ty: Type,
    ) {
        // TODO: remove and integrate into const_table
        self.ns.consts.insert(
            name,
            ConstInfo {
                type_arity: local_types.len(),
                num_local_classes: local_classes.len(),
            },
        );

        self.const_table.insert(
            name,
            Const {
                local_types,
                local_classes,
                ty,
            },
        );
    }

    fn add_axiom(
        &mut self,
        name: Name,
        local_types: Vec<Name>,
        local_classes: Vec<Class>,
        target: Term,
    ) {
        assert!(self.is_wff(&local_types, &target));

        // TODO: remove and integrate into axiom_table
        self.ns.axioms.insert(
            name,
            AxiomInfo {
                type_arity: local_types.len(),
                num_params: target.clone().ungeneralize().len(),
                num_local_classes: local_classes.len(),
            },
        );

        self.axiom_table.insert(
            name,
            Axiom {
                local_types,
                local_classes,
                target,
            },
        );
    }

    fn add_type_const(&mut self, name: Name, kind: Kind) {
        // TODO: remove this
        self.ns.type_consts.insert(name);

        self.type_const_table.insert(name, kind.clone());
    }

    fn add_class_predicate(&mut self, name: Name, ty: ClassType) {
        // TODO: remove this
        self.ns.class_predicates.insert(name);

        self.class_predicate_table.insert(name, ty);
    }

    fn add_class_rule(
        &mut self,
        local_types: Vec<Name>,
        local_classes: Vec<Class>,
        target: Class,
        method_table: HashMap<Name, Term>,
    ) {
        self.class_database.push(ClassRule {
            local_types,
            local_classes,
            target,
            method_table,
        });
    }

    fn add_delta(
        &mut self,
        name: Name,
        local_classes: Vec<Class>,
        local_types: Vec<Name>,
        target: Term,
    ) {
        self.delta_table.insert(
            name,
            Delta {
                local_types,
                local_classes,
                target,
                hint: self.delta_table.len(),
            },
        );
    }

    fn add_iota(
        &mut self,
        rec_name: Name,
        ctor_name: Name,
        local_types: Vec<Name>,
        params: Vec<Name>,
        target: Term,
    ) {
        self.iota_table.entry(rec_name).or_default().insert(
            ctor_name,
            Iota {
                local_types,
                params,
                target,
            },
        );
    }

    fn has_const(&self, name: Name) -> bool {
        self.const_table.contains_key(&name)
    }

    fn has_axiom(&self, name: Name) -> bool {
        self.axiom_table.contains_key(&name)
    }

    fn has_type_const(&self, name: Name) -> bool {
        self.type_const_table.contains_key(&name)
    }

    fn has_class_predicate(&self, name: Name) -> bool {
        self.class_predicate_table.contains_key(&name)
    }

    fn elaborate_type(
        &self,
        local_env: &mut LocalEnv,
        ty: &Type,
        kind: Kind,
    ) -> anyhow::Result<()> {
        elab::Elaborator::new(self.proof_env(), &self.structure_table, local_env, vec![])
            .elaborate_type(ty, kind)
    }

    fn elaborate_class(&self, local_env: &mut LocalEnv, c: &Class) -> anyhow::Result<()> {
        elab::Elaborator::new(self.proof_env(), &self.structure_table, local_env, vec![])
            .elaborate_class(c)
    }

    fn elaborate_term(
        &self,
        local_env: &mut LocalEnv,
        target: &mut Term,
        ty: &Type,
    ) -> anyhow::Result<()> {
        elab::Elaborator::new(self.proof_env(), &self.structure_table, local_env, vec![])
            .elaborate_term(target, ty)
    }

    fn elaborate_expr(
        &self,
        local_env: &mut LocalEnv,
        holes: Vec<(Name, Type)>,
        expr: &mut Expr,
        target: &Term,
    ) -> anyhow::Result<()> {
        elab::Elaborator::new(self.proof_env(), &self.structure_table, local_env, holes)
            .elaborate_expr(expr, target)
    }

    // TODO: move to Term
    fn is_wff(&self, local_types: &[Name], target: &Term) -> bool {
        let mut local_env = LocalEnv {
            local_types: local_types.to_vec(),
            local_classes: vec![], // FIXME
            locals: vec![],
        };
        self.tt_env().is_wff(&mut local_env, target)
    }

    fn tt_env(&self) -> tt::Env {
        tt::Env {
            type_const_table: &self.type_const_table,
            const_table: &self.const_table,
            delta_table: &self.delta_table,
            iota_table: &self.iota_table,
            class_predicate_table: &self.class_predicate_table,
            class_database: &self.class_database,
        }
    }

    fn proof_env(&self) -> proof::Env {
        proof::Env {
            axiom_table: &self.axiom_table,
            tt_env: self.tt_env(),
        }
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
                    ty,
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
                for &local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(&local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !local_classes
                        .iter()
                        .any(|local_class| local_class.contains_local(local_type_const))
                        && !ty.contains_local(local_type_const)
                    {
                        // unused
                        continue;
                    }
                    local_types.insert(0, local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.clone(),
                    local_classes: vec![],
                    locals: vec![],
                };
                for local_class in &local_classes {
                    self.elaborate_class(&mut local_env, local_class)?;
                    local_env.local_classes.push(local_class.clone());
                }
                self.elaborate_type(&mut local_env, &ty, Kind::base())?;
                self.elaborate_term(&mut local_env, &mut target, &ty)?;
                // well-formedness check is completed.
                self.add_const(name, local_types.clone(), local_classes.clone(), ty.clone());
                self.add_delta(name, local_classes, local_types, target);
                Ok(())
            }
            Cmd::Axiom(inner) => {
                let CmdAxiom {
                    name,
                    mut local_types,
                    local_classes,
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
                for &local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(&local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !local_classes
                        .iter()
                        .any(|local_class| local_class.contains_local(local_type_const))
                        && !target.contains_local_type(local_type_const)
                    {
                        // unused
                        continue;
                    }
                    local_types.insert(0, local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.clone(),
                    local_classes: vec![],
                    locals: vec![],
                };
                for local_class in &local_classes {
                    self.elaborate_class(&mut local_env, local_class)?;
                    local_env.local_classes.push(local_class.clone());
                }
                self.elaborate_term(&mut local_env, &mut target, &mk_type_prop())?;
                // well-formedness check is completed.
                self.add_axiom(name, local_types, local_classes, target);
                Ok(())
            }
            Cmd::Lemma(inner) => {
                let CmdLemma {
                    name,
                    mut local_types,
                    local_classes,
                    mut target,
                    holes,
                    mut expr,
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
                for &local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(&local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !local_classes
                        .iter()
                        .any(|local_class| local_class.contains_local(local_type_const))
                        && !target.contains_local_type(local_type_const)
                    {
                        // unused
                        continue;
                    }
                    local_types.insert(0, local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.clone(),
                    local_classes: vec![],
                    locals: vec![],
                };
                for local_class in &local_classes {
                    self.elaborate_class(&mut local_env, local_class)?;
                    local_env.local_classes.push(local_class.clone());
                }
                self.elaborate_term(&mut local_env, &mut target, &mk_type_prop())?;
                self.elaborate_expr(&mut local_env, holes.clone(), &mut expr, &target)?;
                let h = expr::Env {
                    proof_env: self.proof_env(),
                    tt_local_env: &mut local_env,
                }
                .run(&expr);
                if !self.proof_env().check_prop(
                    &mut local_env,
                    &mut proof::LocalEnv::default(),
                    &h,
                    &target,
                ) {
                    bail!("proof failed");
                }
                self.add_axiom(name, local_types, local_classes, target);
                Ok(())
            }
            Cmd::Const(inner) => {
                let CmdConst {
                    name,
                    mut local_types,
                    local_classes,
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
                for &local_type_const in self.local_type_consts.iter().rev() {
                    if local_types.contains(&local_type_const) {
                        // shadowed by the .{} binder
                        continue;
                    }
                    if !local_classes
                        .iter()
                        .any(|local_class| local_class.contains_local(local_type_const))
                        && !ty.contains_local(local_type_const)
                    {
                        // unused
                        continue;
                    }
                    local_types.insert(0, local_type_const);
                }
                let mut local_env = LocalEnv {
                    local_types: local_types.clone(),
                    local_classes: vec![],
                    locals: vec![],
                };
                for local_class in &local_classes {
                    self.elaborate_class(&mut local_env, local_class)?;
                    local_env.local_classes.push(local_class.clone());
                }
                self.elaborate_type(&mut local_env, &ty, Kind::base())?;
                self.add_const(name, local_types, local_classes, ty);
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
            Cmd::ClassStructure(cmd) => self.run_class_structure_cmd(cmd),
            Cmd::ClassInstance(cmd) => self.run_class_instance_cmd(cmd),
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
            local_classes: vec![],
            locals: vec![],
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
            self.elaborate_type(&mut local_env, &ctor.ty, Kind::base())?;
            let mut t = ctor.ty.clone();
            let args = t.unarrow();
            if t != mk_type_local(name) {
                bail!("invalid constructor: {t}");
            }
            for mut a in args {
                let xs = a.unarrow();
                for x in &xs {
                    if x.contains_local(name) {
                        bail!("constructor violates strict positivity");
                    }
                }
                if a != mk_type_local(name) && a.contains_local(name) {
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
            self.add_const(name, local_types.clone(), vec![], ty);
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
        let motive = Parameter {
            name: Name::fresh_with_name("motive"),
            ty: mk_type_arrow(target_ty.clone(), mk_type_prop()),
        };
        let mut guards = vec![];
        for ctor in &ctors {
            let mut args = vec![];
            for arg_ty in ctor.ty.clone().unarrow() {
                args.push(Parameter {
                    name: Name::fresh(),
                    ty: arg_ty,
                });
            }
            // induction hypotheses
            let mut ih_list = vec![];
            for arg in &args {
                let mut t = arg.ty.clone();
                let mut xs = vec![];
                for x in t.unarrow() {
                    xs.push(Parameter {
                        name: Name::fresh(),
                        ty: x,
                    });
                }
                if t != mk_type_local(name) {
                    continue;
                }
                // ∀ xs, P (a xs)
                let mut a = mk_local(arg.name);
                a.apply(xs.iter().map(|x| mk_local(x.name)));
                let mut h = mk_local(motive.name);
                h.apply([a]);
                h.generalize(&xs);
                ih_list.push(h);
            }
            // ∀ args, {IH} → P (C args)
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut a = mk_const(
                ctor_name,
                local_types.iter().map(|t| mk_type_local(*t)).collect(),
                vec![],
            );
            a.apply(args.iter().map(|arg| mk_local(arg.name)));
            let mut target = mk_local(motive.name);
            target.apply([a]);
            target.guard(ih_list);
            for arg in &mut args {
                arg.ty.subst(&subst);
            }
            target.generalize(&args);
            guards.push(target);
        }
        // ∀ x P, {guards} → P x
        let x = Parameter {
            name: Name::fresh_with_name("x"),
            ty: target_ty.clone(),
        };
        let mut target = mk_local(motive.name);
        target.apply([mk_local(x.name)]);
        target.guard(guards);
        target.generalize(&[x, motive]);
        self.add_axiom(ind_name, local_types.clone(), vec![], target);

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
                ctor_params.push(Parameter {
                    name: Name::fresh(),
                    ty: ctor_param_ty,
                });
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
            for param in ctor_params {
                cont_arg_tys.push(param.ty.clone());
                target.apply([mk_local(param.name)]);
            }
            // stepping
            let ctor_arg_tys = ctor.ty.clone().unarrow();
            for (ctor_arg, param) in zip(ctor_arg_tys, ctor_params) {
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
                    .map(|arg_ty| Parameter {
                        name: Name::fresh(),
                        ty: arg_ty,
                    })
                    .collect();
                let mut m = mk_const(
                    rec_name,
                    rec_local_types.iter().map(|t| mk_type_local(*t)).collect(),
                    vec![],
                );
                let mut a = mk_local(param.name);
                a.apply(binders.iter().map(|x| mk_local(x.name)));
                m.apply([a]);
                m.apply(cont_params.iter().map(|&k| mk_local(k)));
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
        self.add_const(rec_name, rec_local_types.clone(), vec![], rec_ty);

        let mut rhs_binders = vec![];
        for (x, t) in zip(cont_params, &cont_param_tys) {
            rhs_binders.push(Parameter {
                name: x,
                ty: t.clone(),
            });
        }
        for ((rhs_body, ctor_params), ctor) in zip(zip(rhs_bodies, ctor_params_list), &ctors) {
            let mut lhs = mk_const(
                rec_name,
                rec_local_types.iter().map(|t| mk_type_local(*t)).collect(),
                vec![],
            );
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut lhs_arg = mk_const(
                ctor_name,
                local_types.iter().map(|t| mk_type_local(*t)).collect(),
                vec![],
            );
            lhs_arg.apply(ctor_params.iter().map(|x| mk_local(x.name)));
            lhs.apply([lhs_arg]);

            let mut rhs = rhs_body;
            rhs.abs(&rhs_binders, true);

            let mut eq_ty = mk_type_local(rec_ty_var);
            eq_ty.arrow(cont_param_tys.clone());

            let mut spec = mk_const(Name::intern("eq").unwrap(), vec![eq_ty], vec![]);
            spec.apply([lhs, rhs]);
            spec.generalize(&ctor_params);

            let ctor_spec_name = Name::intern(&format!("{}.spec", ctor_name)).unwrap();
            self.add_axiom(ctor_spec_name, rec_local_types.clone(), vec![], spec);
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
        for &local_type_const in self.local_type_consts.iter().rev() {
            if local_types.contains(&local_type_const) {
                // shadowed by the .{} binder
                continue;
            }
            if !params
                .iter()
                .any(|param| param.ty.contains_local(local_type_const))
                && !target_ty.contains_local(local_type_const)
            {
                // unused
                continue;
            }
            local_types.insert(0, local_type_const);
        }
        let mut local_env = LocalEnv {
            local_types: local_types.clone(),
            local_classes: vec![],
            locals: vec![],
        };
        for i in 0..params.len() {
            for j in i + 1..params.len() {
                if params[i].name == params[j].name {
                    bail!("duplicate parameters");
                }
            }
        }
        for param in &params {
            self.elaborate_type(&mut local_env, &param.ty, Kind::base())?;
            local_env.locals.push(param.clone());
        }
        self.elaborate_type(&mut local_env, &target_ty, Kind::base())?;
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
        local_env.locals.insert(
            0,
            Parameter {
                name,
                ty: target_ty.clone(),
            },
        );
        let mut ctor_params_list = vec![];
        let mut ctor_args_list = vec![];
        let mut ctor_target_list = vec![];
        let mut ctor_ind_args_list = vec![];
        for ctor in &mut ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            if self.has_axiom(ctor_name) {
                bail!("already defined");
            }
            self.elaborate_term(&mut local_env, &mut ctor.target, &mk_type_prop())?;

            let mut m = ctor.target.clone();
            let ctor_params = m.ungeneralize();
            ctor_params_list.push(ctor_params);
            let ctor_args = m.unguard();
            ctor_args_list.push(ctor_args.clone());
            if !m.head().alpha_eq(&mk_local(name)) {
                bail!("invalid constructor. Currently only Horn clauses are supported in inductive clauses: {m}");
            }
            for a in m.args() {
                if a.contains_local(name) {
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
                if m.contains_local(name) {
                    if !m.head().alpha_eq(&mk_local(name)) {
                        bail!("invalid target");
                    }
                    for a in m.args() {
                        if a.contains_local(name) {
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
        for param in &params {
            param_types.push(param.ty.clone());
        }
        pred_ty.arrow(param_types);
        self.add_const(name, local_types.clone(), vec![], pred_ty);

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.intro.{u} (x : τ) : ∀ y, φ → (∀ z, ψ → P.{u} x M) → P.{u} x N
        for ctor in &ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name)).unwrap();
            let mut target = ctor.target.clone();
            // P.{u} x
            let mut stash = mk_const(
                name,
                local_types
                    .iter()
                    .map(|name| mk_type_local(*name))
                    .collect(),
                vec![],
            );
            stash.apply(params.iter().map(|param| mk_local(param.name)));
            let subst = [(name, stash)];
            target.subst(&subst);
            target.generalize(&params);
            self.add_axiom(ctor_name, local_types.clone(), vec![], target);
        }

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.ind.{u} (x : τ) (w : σ) (C : σ → Prop)
        //  : P x w → (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        let indexes = target_ty
            .clone()
            .unarrow()
            .into_iter()
            .map(|t| Parameter {
                name: Name::fresh(),
                ty: t,
            })
            .collect::<Vec<_>>();
        let motive = Parameter {
            name: Name::fresh_with_name("motive"),
            ty: target_ty.clone(),
        };
        // C w
        let mut target = mk_local(motive.name);
        target.apply(indexes.iter().map(|index| mk_local(index.name)));
        let mut guards = vec![];
        // (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        for (ctor_params, (mut ctor_args, (ctor_target, mut ctor_ind_args))) in zip(
            ctor_params_list,
            zip(ctor_args_list, zip(ctor_target_list, ctor_ind_args_list)),
        ) {
            // P ↦ C
            let subst_with_motive = [(name, mk_local(motive.name))];

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
                local_types
                    .iter()
                    .map(|name| mk_type_local(*name))
                    .collect(),
                vec![],
            );
            stash.apply(params.iter().map(|param| mk_local(param.name)));
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
            local_types
                .iter()
                .map(|name| mk_type_local(*name))
                .collect(),
            vec![],
        );
        p.apply(params.iter().map(|param| mk_local(param.name)));
        p.apply(indexes.iter().map(|index| mk_local(index.name)));
        target.guard([p]);

        target.generalize(&[motive]);
        target.generalize(&indexes);
        target.generalize(&params);

        self.add_axiom(ind_name, local_types, vec![], target);
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
            local_classes: vec![],
            locals: vec![],
        };
        let mut const_field_names = vec![];
        let mut axiom_field_names = vec![];
        for field in &mut fields {
            match field {
                StructureField::Const(field) => {
                    let &mut StructureConst {
                        name: field_name,
                        ty: ref field_ty,
                    } = field;
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_const(fullname) {
                        bail!("already defined");
                    }
                    if const_field_names.contains(&field_name) {
                        bail!("duplicate const field");
                    }
                    const_field_names.push(field_name);
                    self.elaborate_type(&mut local_env, field_ty, Kind::base())?;
                    local_env.locals.push(Parameter {
                        name: field_name,
                        ty: field_ty.clone(),
                    });
                }
                StructureField::Axiom(field) => {
                    let &mut StructureAxiom {
                        name: field_name,
                        ref mut target,
                    } = field;
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_axiom(fullname) {
                        bail!("already defined");
                    }
                    if axiom_field_names.contains(&field_name) {
                        bail!("duplicate axiom field");
                    }
                    axiom_field_names.push(field_name);
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
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
        let instance = Parameter {
            name: Name::fresh_with_name("d"),
            ty: {
                let mut ty = mk_type_const(name);
                ty.apply(local_types.iter().map(|x| mk_type_local(*x)));
                ty
            },
        };
        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    // rep : set u
                    // ↦ inhab.rep.{u} : inhab u → set u
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let mut ty = field.ty.clone();
                    ty.arrow([instance.ty.clone()]);
                    self.add_const(fullname, local_types.clone(), vec![], ty);

                    // rep ↦ inhab.rep.{u} d
                    let mut target = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                        vec![],
                    );
                    target.apply([mk_local(instance.name)]);
                    subst.push((field.name, target));
                }
                StructureField::Axiom(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();

                    let mut target = field.target.clone();
                    target.subst(&subst);

                    target.generalize(slice::from_ref(&instance));

                    self.add_axiom(fullname, local_types.clone(), vec![], target);
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
                    let param = Parameter {
                        name: Name::fresh_from(field.name),
                        ty: field.ty.clone(),
                    };

                    // inhab.rep d
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let mut rhs = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                        vec![],
                    );
                    rhs.apply([mk_local(instance.name)]);

                    // s = inhab.rep d
                    let mut char =
                        mk_const(Name::intern("eq").unwrap(), vec![field.ty.clone()], vec![]);
                    char.apply([mk_local(param.name), rhs]);
                    chars.push(char);

                    // rep ↦ s
                    subst.push((field.name, mk_local(param.name)));

                    params.push(param);
                }
                StructureField::Axiom(field) => {
                    let mut target = field.target.clone();
                    target.subst(&subst);

                    guards.push(target);
                }
            }
        }
        let mut abs = mk_const(
            Name::intern("exists").unwrap(),
            vec![instance.ty.clone()],
            vec![],
        );
        abs.apply([{
            let mut char = chars
                .into_iter()
                .reduce(|left, right| {
                    let mut conj = mk_const(Name::intern("and").unwrap(), vec![], vec![]);
                    conj.apply([left, right]);
                    conj
                })
                .unwrap_or_else(|| mk_const(Name::intern("true").unwrap(), vec![], vec![]));
            char.abs(slice::from_ref(&instance), true);
            char
        }]);
        abs.guard(guards);
        abs.generalize(&params);
        self.add_axiom(abs_name, local_types.clone(), vec![], abs);

        // generate extensionality
        // axiom inhab.ext.{u} (d₁ d₂ : inhab u) : inhab.rep d₁ = inhab.rep d₂ → d₁ = d₂
        let instance1 = Parameter {
            name: Name::fresh_with_name("d₁"),
            ty: instance.ty.clone(),
        };
        let instance2 = Parameter {
            name: Name::fresh_with_name("d₂"),
            ty: instance.ty.clone(),
        };
        let mut guards = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let proj = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                        vec![],
                    );

                    let mut lhs = proj.clone();
                    lhs.apply([mk_local(instance1.name)]);
                    let mut rhs = proj;
                    rhs.apply([mk_local(instance2.name)]);

                    let mut guard =
                        mk_const(Name::intern("eq").unwrap(), vec![field.ty.clone()], vec![]);
                    guard.apply([lhs, rhs]);
                    guards.push(guard);
                }
                StructureField::Axiom(_) => {}
            }
        }
        let mut target = mk_const(
            Name::intern("eq").unwrap(),
            vec![instance.ty.clone()],
            vec![],
        );
        target.apply([mk_local(instance1.name), mk_local(instance2.name)]);
        target.guard(guards);
        target.generalize(&[instance1, instance2]);
        self.add_axiom(ext_name, local_types.clone(), vec![], target);
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
            local_classes,
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
        for &local_type_const in self.local_type_consts.iter().rev() {
            if local_types.contains(&local_type_const) {
                // shadowed by the .{} binder
                continue;
            }
            if !local_classes
                .iter()
                .any(|local_class| local_class.contains_local(local_type_const))
                && !params
                    .iter()
                    .any(|param| param.ty.contains_local(local_type_const))
                && !target_ty.contains_local(local_type_const)
            {
                // unused
                continue;
            }
            local_types.insert(0, local_type_const);
        }
        let mut local_env = LocalEnv {
            local_types: local_types.clone(),
            local_classes: vec![],
            locals: vec![],
        };
        for local_class in &local_classes {
            self.elaborate_class(&mut local_env, local_class)?;
            local_env.local_classes.push(local_class.clone());
        }
        for i in 0..params.len() {
            for j in i + 1..params.len() {
                if params[i].name == params[j].name {
                    bail!("duplicate parameters");
                }
            }
        }
        for param in &params {
            self.elaborate_type(&mut local_env, &param.ty, Kind::base())?;
            local_env.locals.push(param.clone());
        }
        self.elaborate_type(&mut local_env, &target_ty, Kind::base())?;
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
                        ref ty,
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
                    self.elaborate_type(&mut local_env, ty, Kind::base())?;
                    self.elaborate_term(&mut local_env, target, ty)?;
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
                        ref mut expr,
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
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
                    self.elaborate_expr(&mut local_env, holes.clone(), expr, target)?;
                    let h = expr::Env {
                        proof_env: self.proof_env(),
                        tt_local_env: &mut local_env,
                    }
                    .run(&*expr);
                    if !self.proof_env().check_prop(
                        &mut local_env,
                        &mut proof::LocalEnv::default(),
                        &h,
                        target,
                    ) {
                        bail!("proof failed");
                    }
                    let mut structure_field_target = structure_field.target.clone();
                    structure_field_target.subst_type(&type_subst);
                    structure_field_target.subst(&subst);
                    if !structure_field_target.alpha_eq(target) {
                        bail!("target mismatch");
                    }
                }
            }
        }
        // well-formedness check is completed.

        // e.g. const power.inhab.{u} : set u → inhab (set u)
        let mut instance_ty = target_ty.clone();
        for param in params.iter().rev() {
            instance_ty.arrow([param.ty.clone()]);
        }
        self.add_const(
            name,
            local_types.clone(),
            local_classes.clone(),
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
                        t.arrow(params.iter().map(|param| param.ty.clone()));
                        t
                    };
                    let def_target = {
                        let mut m = target.clone();
                        m.abs(&params, true);
                        m
                    };
                    self.add_const(
                        fullname,
                        local_types.clone(),
                        local_classes.clone(),
                        def_target_ty,
                    );
                    self.add_delta(name, local_classes.clone(), local_types.clone(), def_target);

                    // e.g. example rep_of_power.{u} (A : set u) : inhab.rep (power.inhab A) = power A := eq.refl
                    let proj_name =
                        Name::intern(&format!("{}.{}", structure_name, field_name)).unwrap();
                    self.add_iota(
                        proj_name,
                        name,
                        local_types.clone(),
                        params.iter().map(|param| param.name).collect(),
                        target.clone(),
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
                    self.add_axiom(fullname, local_types.clone(), local_classes.clone(), target);
                }
            }
        }
        Ok(())
    }

    fn run_class_structure_cmd(&mut self, cmd: CmdClassStructure) -> anyhow::Result<()> {
        let CmdClassStructure {
            name,
            local_types,
            mut fields,
        } = cmd;
        if self.has_class_predicate(name) {
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
            local_classes: vec![],
            locals: vec![],
        };
        let mut const_field_names = vec![];
        let mut axiom_field_names = vec![];
        for field in &mut fields {
            match field {
                ClassStructureField::Const(field) => {
                    let &mut ClassStructureConst {
                        name: field_name,
                        ty: ref field_ty,
                    } = field;
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_const(fullname) {
                        bail!("already defined");
                    }
                    if const_field_names.contains(&field_name) {
                        bail!("duplicate const field");
                    }
                    const_field_names.push(field_name);
                    self.elaborate_type(&mut local_env, field_ty, Kind::base())?;
                    local_env.locals.push(Parameter {
                        name: field_name,
                        ty: field_ty.clone(),
                    });
                }
                ClassStructureField::Axiom(field) => {
                    let &mut ClassStructureAxiom {
                        name: field_name,
                        ref mut target,
                    } = field;
                    let fullname = Name::intern(&format!("{}.{}", name, field_name)).unwrap();
                    if self.has_axiom(fullname) {
                        bail!("already defined");
                    }
                    if axiom_field_names.contains(&field_name) {
                        bail!("duplicate axiom field");
                    }
                    axiom_field_names.push(field_name);
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
                }
            }
        }
        // well-formedness check is completed.
        self.class_structure_table.insert(
            name,
            CmdClassStructure {
                name,
                local_types: local_types.clone(),
                fields: fields.clone(),
            },
        );
        self.add_class_predicate(
            name,
            ClassType {
                arity: local_types.len(),
            },
        );
        let this_class = Class {
            name,
            args: local_types.iter().map(|&x| mk_type_local(x)).collect(),
        };
        let this_instance = mk_instance_local(this_class.clone());
        let mut subst = vec![];
        for field in &fields {
            match field {
                ClassStructureField::Const(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    self.add_const(
                        fullname,
                        local_types.clone(),
                        vec![this_class.clone()],
                        field.ty.clone(),
                    );

                    let target = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                        vec![this_instance.clone()],
                    );
                    subst.push((field.name, target));
                }
                ClassStructureField::Axiom(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name)).unwrap();
                    let mut target = field.target.clone();
                    target.subst(&subst);
                    self.add_axiom(
                        fullname,
                        local_types.clone(),
                        vec![this_class.clone()],
                        target,
                    );
                }
            }
        }
        Ok(())
    }

    fn run_class_instance_cmd(&mut self, cmd: CmdClassInstance) -> anyhow::Result<()> {
        let CmdClassInstance {
            local_types,
            local_classes,
            target,
            mut fields,
        } = cmd;
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i] == local_types[j] {
                    bail!("duplicate type variables");
                }
            }
        }
        let mut local_env = LocalEnv {
            local_types: local_types.clone(),
            local_classes: vec![],
            locals: vec![],
        };
        for local_class in &local_classes {
            self.elaborate_class(&mut local_env, local_class)?;
            local_env.local_classes.push(local_class.clone());
        }
        self.elaborate_class(&mut local_env, &target)?;
        // TODO: this implementation is too conservative.
        for rule in &self.class_database {
            let rule_head = {
                let mut type_subst = vec![];
                for &name in &rule.local_types {
                    type_subst.push((name, mk_fresh_type_hole()));
                }
                let mut target = rule.target.clone();
                target.subst(&type_subst);
                target
            };
            if target.matches(&rule_head).is_some() {
                bail!("overlapping instances are disallowed");
            }
        }
        let cmd_structure = self.class_structure_table.get(&target.name).unwrap();
        let mut type_subst = vec![];
        for (&x, t) in zip(&cmd_structure.local_types, &target.args) {
            type_subst.push((x, t.clone()));
        }
        if cmd_structure.fields.len() != fields.len() {
            bail!("number of fields mismatch");
        }
        let mut subst = vec![];
        for (structure_field, field) in zip(&cmd_structure.fields, &mut fields) {
            match structure_field {
                ClassStructureField::Const(structure_field) => {
                    let ClassInstanceField::Def(ClassInstanceDef {
                        name: ref field_name,
                        ref ty,
                        target,
                    }) = field
                    else {
                        bail!("definition expected");
                    };
                    if structure_field.name != *field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_type(&mut local_env, ty, Kind::base())?;
                    let mut structure_field_ty = structure_field.ty.clone();
                    structure_field_ty.subst(&type_subst);
                    if structure_field_ty != *ty {
                        bail!("type mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, ty)?;
                    subst.push((*field_name, target.clone()));
                }
                ClassStructureField::Axiom(structure_field) => {
                    let ClassInstanceField::Lemma(ClassInstanceLemma {
                        name: ref field_name,
                        target,
                        ref holes,
                        ref mut expr,
                    }) = field
                    else {
                        bail!("lemma expected");
                    };
                    if structure_field.name != *field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
                    let mut structure_field_target = structure_field.target.clone();
                    structure_field_target.subst_type(&type_subst);
                    structure_field_target.subst(&subst);
                    if !structure_field_target.alpha_eq(target) {
                        bail!("target mismatch");
                    }
                    self.elaborate_expr(&mut local_env, holes.clone(), expr, target)?;
                    let h = expr::Env {
                        proof_env: self.proof_env(),
                        tt_local_env: &mut local_env,
                    }
                    .run(&*expr);
                    if !self.proof_env().check_prop(
                        &mut local_env,
                        &mut proof::LocalEnv::default(),
                        &h,
                        target,
                    ) {
                        bail!("proof failed");
                    }
                }
            }
        }
        // well-formedness check is completed.
        let mut method_table = HashMap::new();
        for field in &fields {
            match field {
                ClassInstanceField::Def(field) => {
                    let &ClassInstanceDef {
                        name: field_name,
                        ty: _,
                        ref target,
                    } = field;
                    method_table.insert(field_name, target.clone());
                }
                ClassInstanceField::Lemma(_) => {}
            }
        }
        self.add_class_rule(local_types, local_classes, target, method_table);
        Ok(())
    }
}
