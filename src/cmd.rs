use std::{collections::HashMap, iter::zip, slice, vec};

use anyhow::bail;

use crate::{
    elab,
    parse::TokenTable,
    print::{OpTable, Pretty},
    proof::{self, Axiom, Expr, generalize, guard, mk_type_prop, ungeneralize, unguard},
    tt::{
        self, Class, ClassInstance, ClassType, Const, Delta, Kappa, Kind, LocalEnv, Name,
        Parameter, Term, Type, mk_const, mk_fresh_type_hole, mk_instance_local, mk_local,
        mk_type_arrow, mk_type_const, mk_type_local,
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
    pub name: Name,
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

impl std::fmt::Display for Cmd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cmd::Infix(cmd) => write!(f, "infix {} {} {}", cmd.op, cmd.prec, cmd.entity),
            Cmd::Infixr(cmd) => write!(f, "infixr {} {} {}", cmd.op, cmd.prec, cmd.entity),
            Cmd::Infixl(cmd) => write!(f, "infixl {} {} {}", cmd.op, cmd.prec, cmd.entity),
            Cmd::Prefix(cmd) => write!(f, "prefix {} {} {}", cmd.op, cmd.prec, cmd.entity),
            Cmd::Nofix(cmd) => write!(f, "nofix {} {}", cmd.op, cmd.entity),
            Cmd::Def(cmd) => write!(
                f,
                "def {}.{{{}}} : {} := {}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.ty,
                cmd.target
            ),
            Cmd::Axiom(cmd) => write!(
                f,
                "axiom {}.{{{}}} : {}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.target
            ),
            Cmd::Lemma(cmd) => write!(
                f,
                "lemma {}.{{{}}} : {} := {}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.target,
                cmd.expr
            ),
            Cmd::Const(cmd) => write!(
                f,
                "const {}.{{{}}} : {}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.ty
            ),
            Cmd::TypeConst(cmd) => write!(f, "type const {} : {}", cmd.name, cmd.kind),
            Cmd::LocalTypeConst(cmd) => write!(
                f,
                "local type const {}",
                cmd.variables
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Cmd::TypeInductive(cmd) => write!(
                f,
                "inductive {}.{{{}}} {{\n{}\n}}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.ctors
                    .iter()
                    .map(|ctor| format!("{} : {}", ctor.name, ctor.ty))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::Inductive(cmd) => write!(
                f,
                "inductive {}.{{{}}} ({}) : {} {{\n{}\n}}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.params
                    .iter()
                    .map(|p| format!("{} : {}", p.name, p.ty))
                    .collect::<Vec<_>>()
                    .join(", "),
                cmd.target_ty,
                cmd.ctors
                    .iter()
                    .map(|ctor| format!("{} : {}", ctor.name, ctor.target))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::Structure(cmd) => write!(
                f,
                "structure {}.{{{}}} {{\n{}\n}}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.fields
                    .iter()
                    .map(|field| match field {
                        StructureField::Const(c) => format!("  constant {} : {}", c.name, c.ty),
                        StructureField::Axiom(a) => format!("  axiom {} : {}", a.name, a.target),
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::Instance(cmd) => write!(
                f,
                "instance {}.{{{}}} ({}) : {} {{\n{}\n}}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.params
                    .iter()
                    .map(|p| format!("{} : {}", p.name, p.ty))
                    .collect::<Vec<_>>()
                    .join(", "),
                cmd.target_ty,
                cmd.fields
                    .iter()
                    .map(|field| match field {
                        InstanceField::Def(d) =>
                            format!("  def {} : {} := {}", d.name, d.ty, d.target),
                        InstanceField::Lemma(l) =>
                            format!("  lemma {} : {} := {}", l.name, l.target, l.expr),
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::ClassStructure(cmd) => write!(
                f,
                "class structure {}.{{{}}} {{\n{}\n}}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.fields
                    .iter()
                    .map(|field| match field {
                        ClassStructureField::Const(c) =>
                            format!("  constant {} : {}", c.name, c.ty),
                        ClassStructureField::Axiom(a) =>
                            format!("  axiom {} : {}", a.name, a.target),
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::ClassInstance(cmd) => write!(
                f,
                "class instance {}.{{{}}} : {} {{\n{}\n}}",
                cmd.name,
                cmd.local_types
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                cmd.target,
                cmd.fields
                    .iter()
                    .map(|field| match field {
                        ClassInstanceField::Def(d) =>
                            format!("  def {} : {} := {}", d.name, d.ty, d.target),
                        ClassInstanceField::Lemma(l) =>
                            format!("  lemma {} : {} := {}", l.name, l.target, l.expr),
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Eval {
    pub tt: TokenTable,
    pub pp: OpTable,
    pub local_type_consts: Vec<Name>,
    pub type_const_table: HashMap<Name, Kind>,
    pub const_table: HashMap<Name, Const>,
    pub axiom_table: HashMap<Name, Axiom>,
    pub delta_table: HashMap<Name, Delta>,
    pub kappa_table: HashMap<Name, Kappa>,
    pub class_predicate_table: HashMap<Name, ClassType>,
    pub class_instance_table: HashMap<Name, ClassInstance>,
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
        self.const_table.insert(
            name,
            Const {
                local_types,
                local_classes, // TODO: shrink
                ty,
            },
        );

        log::info!(
            "+ {}",
            Pretty::new(&self.pp, self.const_table.get_key_value(&name).unwrap())
        );
    }

    fn add_axiom(
        &mut self,
        name: Name,
        local_types: Vec<Name>,
        local_classes: Vec<Class>,
        target: Term,
    ) {
        self.tt_env().check_wff(
            &mut LocalEnv {
                local_types: local_types.clone(),
                local_classes: local_classes.clone(),
                locals: vec![],
            },
            &target,
        );

        self.axiom_table.insert(
            name,
            Axiom {
                local_types,
                local_classes,
                target,
            },
        );

        log::info!(
            "+ {}",
            Pretty::new(&self.pp, self.axiom_table.get_key_value(&name).unwrap())
        );
    }

    fn add_type_const(&mut self, name: Name, kind: Kind) {
        self.type_const_table.insert(name, kind.clone());

        log::info!(
            "+ {}",
            Pretty::new(
                &self.pp,
                self.type_const_table.get_key_value(&name).unwrap()
            )
        );
    }

    fn add_class_predicate(&mut self, name: Name, ty: ClassType) {
        self.class_predicate_table.insert(name, ty);

        log::info!(
            "+ {}",
            Pretty::new(
                &self.pp,
                self.class_predicate_table.get_key_value(&name).unwrap()
            )
        );
    }

    fn add_class_instance(
        &mut self,
        name: Name,
        local_types: Vec<Name>,
        local_classes: Vec<Class>,
        target: Class,
        method_table: HashMap<Name, Term>,
    ) {
        self.class_instance_table.insert(
            name,
            ClassInstance {
                local_types,
                local_classes,
                target,
                method_table,
            },
        );
    }

    fn add_delta(&mut self, name: Name, target: Term) {
        let Const {
            local_types,
            local_classes,
            ty,
        } = self.const_table.get(&name).unwrap();

        self.tt_env().check_type(
            &mut LocalEnv {
                local_types: local_types.clone(),
                local_classes: local_classes.clone(),
                locals: vec![],
            },
            &target,
            ty,
        );

        self.delta_table.insert(
            name,
            Delta {
                local_types: local_types.clone(),
                local_classes: local_classes.clone(),
                height: self.tt_env().height(&target),
                target,
            },
        );
    }

    fn add_kappa(&mut self, name: Name) {
        self.kappa_table.insert(name, Kappa);
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

    fn has_class_instance(&self, name: Name) -> bool {
        self.class_instance_table.contains_key(&name)
    }

    fn elaborate_type(
        &self,
        local_env: &mut LocalEnv,
        ty: &Type,
        kind: Kind,
    ) -> anyhow::Result<()> {
        elab::elaborate_type(self.proof_env(), local_env, ty, kind)
    }

    fn elaborate_class(&self, local_env: &mut LocalEnv, c: &Class) -> anyhow::Result<()> {
        elab::elaborate_class(self.proof_env(), local_env, c)
    }

    fn elaborate_term(
        &self,
        local_env: &mut LocalEnv,
        target: &mut Term,
        ty: &Type,
    ) -> anyhow::Result<()> {
        elab::elaborate_term(self.proof_env(), local_env, target, ty)
    }

    fn elaborate_expr(
        &self,
        local_env: &mut LocalEnv,
        holes: Vec<(Name, Type)>,
        expr: &mut Expr,
        target: &Term,
    ) -> anyhow::Result<()> {
        elab::elaborate_expr(self.proof_env(), local_env, holes, expr, target)
    }

    fn tt_env(&self) -> tt::Env {
        tt::Env {
            type_const_table: &self.type_const_table,
            const_table: &self.const_table,
            delta_table: &self.delta_table,
            kappa_table: &self.kappa_table,
            class_predicate_table: &self.class_predicate_table,
            class_instance_table: &self.class_instance_table,
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
                self.add_delta(name, target);
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
                self.proof_env().check_prop(
                    &mut local_env,
                    &mut proof::LocalEnv::default(),
                    &expr,
                    &target,
                );
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
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name));
            if self.has_const(ctor_name) {
                bail!("already defined");
            }
            let ctor_spec_name = Name::intern(&format!("{}.spec", ctor_name));
            if self.has_const(ctor_spec_name) {
                bail!("already defined");
            }
            self.elaborate_type(&mut local_env, &ctor.ty, Kind::base())?;
            let (args, target) = ctor.ty.unarrow();
            if target != mk_type_local(name) {
                bail!("invalid constructor: {}", ctor.ty);
            }
            for a in args {
                let (xs, head) = a.unarrow();
                for x in &xs {
                    if x.contains_local(name) {
                        bail!("constructor violates strict positivity");
                    }
                }
                if head != mk_type_local(name) && head.contains_local(name) {
                    bail!("nested inductive type is unsupported");
                }
            }
        }
        let ind_name = Name::intern(&format!("{}.ind", name));
        if self.has_axiom(ind_name) {
            bail!("already defined");
        }
        let rec_name = Name::intern(&format!("{}.rec", name));
        if self.has_const(rec_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.

        // generate type constructor
        self.add_type_const(name, Kind(local_types.len()));

        // generate data constructors
        let target_ty = {
            // Foo u v
            mk_type_const(name).apply(local_types.iter().map(|t| mk_type_local(*t)))
        };
        // Foo ↦ Foo u v
        let subst = [(name, target_ty.clone())];
        let mut cs = vec![];
        for ctor in &ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name));
            let ty = ctor.ty.subst(&subst);
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
            let (ctor_arg_tys, _) = ctor.ty.unarrow();
            for arg_ty in ctor_arg_tys {
                args.push(Parameter {
                    name: Name::fresh(),
                    ty: arg_ty,
                });
            }
            // induction hypotheses
            let mut ih_list = vec![];
            for arg in &args {
                let (xs_types, head) = arg.ty.unarrow();
                let xs: Vec<_> = xs_types
                    .into_iter()
                    .map(|x| Parameter {
                        name: Name::fresh(),
                        ty: x,
                    })
                    .collect();
                if head != mk_type_local(name) {
                    continue;
                }
                // ∀ xs, P (a xs)
                let mut a = mk_local(arg.name);
                a = a.apply(xs.iter().map(|x| mk_local(x.name)));
                let mut h = mk_local(motive.name);
                h = h.apply([a]);
                h = generalize(&h, &xs);
                ih_list.push(h);
            }
            // ∀ args, {IH} → P (C args)
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name));
            let mut a = mk_const(
                ctor_name,
                local_types.iter().map(|t| mk_type_local(*t)).collect(),
                vec![],
            );
            a = a.apply(args.iter().map(|arg| mk_local(arg.name)));
            let mut target = mk_local(motive.name);
            target = target.apply([a]);
            target = guard(&target, ih_list);
            for arg in &mut args {
                arg.ty = arg.ty.subst(&subst);
            }
            target = generalize(&target, &args);
            guards.push(target);
        }
        // ∀ x P, {guards} → P x
        let x = Parameter {
            name: Name::fresh_with_name("x"),
            ty: target_ty.clone(),
        };
        let mut target = mk_local(motive.name);
        target = target.apply([mk_local(x.name)]);
        target = guard(&target, guards);
        target = generalize(&target, &[x, motive]);
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
            let (ctor_param_tys, _) = ctor.ty.unarrow();
            for ctor_param_ty in ctor_param_tys {
                let ctor_param_ty = ctor_param_ty.subst(&subst);
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
                target = target.apply([mk_local(param.name)]);
            }
            // stepping
            let (ctor_arg_tys, _) = ctor.ty.unarrow();
            for (ctor_arg, param) in zip(ctor_arg_tys, ctor_params) {
                let (arg_tys, ctor_arg_target) = ctor_arg.unarrow();
                if ctor_arg_target != mk_type_local(name) {
                    continue;
                }
                let t = ctor_arg.subst(&[(name, mk_type_local(rec_ty_var))]);
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
                a = a.apply(binders.iter().map(|x| mk_local(x.name)));
                m = m.apply([a]);
                m = m.apply(cont_params.iter().map(|&k| mk_local(k)));
                m.abs(&binders);
                target = target.apply([m]);
            }

            let cont_param_ty = mk_type_local(rec_ty_var).arrow(cont_arg_tys);
            cont_param_tys.push(cont_param_ty);

            rhs_bodies.push(target);
        }
        let rec_ty = mk_type_local(rec_ty_var)
            .arrow(cont_param_tys.clone())
            .arrow([target_ty]);
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
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name));
            let mut lhs_arg = mk_const(
                ctor_name,
                local_types.iter().map(|t| mk_type_local(*t)).collect(),
                vec![],
            );
            lhs_arg = lhs_arg.apply(ctor_params.iter().map(|x| mk_local(x.name)));
            lhs = lhs.apply([lhs_arg]);

            let mut rhs = rhs_body;
            rhs.abs(&rhs_binders);

            let eq_ty = mk_type_local(rec_ty_var).arrow(cont_param_tys.clone());

            let mut spec = mk_const(Name::intern("eq"), vec![eq_ty], vec![]);
            spec = spec.apply([lhs, rhs]);
            spec = generalize(&spec, &ctor_params);

            let ctor_spec_name = Name::intern(&format!("{}.spec", ctor_name));
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
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name));
            if self.has_axiom(ctor_name) {
                bail!("already defined");
            }
            self.elaborate_term(&mut local_env, &mut ctor.target, &mk_type_prop())?;

            let (ctor_params, m) = ungeneralize(&ctor.target);
            ctor_params_list.push(ctor_params.clone());
            let (ctor_args, m) = unguard(&m);
            ctor_args_list.push(ctor_args.clone());
            if !m.head().alpha_eq(&mk_local(name)) {
                bail!(
                    "invalid constructor. Currently only Horn clauses are supported in inductive clauses: {m}"
                );
            }
            for a in m.args() {
                if a.contains_local(name) {
                    bail!("invalid target");
                }
            }
            ctor_target_list.push(m.clone());
            let mut ctor_ind_args = vec![];
            for ctor_arg in &ctor_args {
                let mut current = ctor_arg.clone();
                loop {
                    let (params, body) = ungeneralize(&current);
                    let (args, next) = unguard(&body);
                    if params.is_empty() && args.is_empty() {
                        break;
                    }
                    current = next;
                }
                if current.contains_local(name) {
                    if !current.head().alpha_eq(&mk_local(name)) {
                        bail!("invalid target");
                    }
                    for a in current.args() {
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
        let ind_name = Name::intern(&format!("{}.ind", name));
        if self.has_axiom(ind_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.

        // inductive P.{u} (x : τ) : σ → Prop
        // ↦ const P.{u} : τ → σ → Prop
        let mut param_types = vec![];
        for param in &params {
            param_types.push(param.ty.clone());
        }
        let pred_ty = target_ty.arrow(param_types);
        self.add_const(name, local_types.clone(), vec![], pred_ty);

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.intro.{u} (x : τ) : ∀ y, φ → (∀ z, ψ → P.{u} x M) → P.{u} x N
        for ctor in &ctors {
            let ctor_name = Name::intern(&format!("{}.{}", name, ctor.name));
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
            stash = stash.apply(params.iter().map(|param| mk_local(param.name)));
            let subst = [(name, stash)];
            let new_target = target.subst(&subst);
            target = new_target;
            target = generalize(&target, &params);
            self.add_axiom(ctor_name, local_types.clone(), vec![], target);
        }

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.ind.{u} (x : τ) (w : σ) (C : σ → Prop)
        //  : P x w → (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        let (index_types, _) = target_ty.unarrow();
        let indexes = index_types
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
        target = target.apply(indexes.iter().map(|index| mk_local(index.name)));
        let mut guards = vec![];
        // (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        for (ctor_params, (mut ctor_args, (ctor_target, mut ctor_ind_args))) in zip(
            ctor_params_list,
            zip(ctor_args_list, zip(ctor_target_list, ctor_ind_args_list)),
        ) {
            // P ↦ C
            let subst_with_motive = [(name, mk_local(motive.name))];

            let mut guard_term = ctor_target;

            // C N
            let new_guard = guard_term.subst(&subst_with_motive);
            guard_term = new_guard;

            // (∀ z, ψ → C M) → C N
            for ctor_ind_arg in &mut ctor_ind_args {
                let new_arg = ctor_ind_arg.subst(&subst_with_motive);
                *ctor_ind_arg = new_arg;
            }
            guard_term = guard(&guard_term, ctor_ind_args);

            // P ↦ P.{u} x
            let mut stash = mk_const(
                name,
                local_types
                    .iter()
                    .map(|name| mk_type_local(*name))
                    .collect(),
                vec![],
            );
            stash = stash.apply(params.iter().map(|param| mk_local(param.name)));
            let subst = [(name, stash)];

            // φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
            for ctor_arg in &mut ctor_args {
                let new_arg = ctor_arg.subst(&subst);
                *ctor_arg = new_arg;
            }
            guard_term = guard(&guard_term, ctor_args);

            // ∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N
            guard_term = generalize(&guard_term, &ctor_params);

            guards.push(guard_term);
        }
        target = guard(&target, guards);

        let mut p = mk_const(
            name,
            local_types
                .iter()
                .map(|name| mk_type_local(*name))
                .collect(),
            vec![],
        );
        p = p.apply(params.iter().map(|param| mk_local(param.name)));
        p = p.apply(indexes.iter().map(|index| mk_local(index.name)));
        target = guard(&target, [p]);

        target = generalize(&target, &[motive]);
        target = generalize(&target, &indexes);
        target = generalize(&target, &params);

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
                    let fullname = Name::intern(&format!("{}.{}", name, field_name));
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
                    let fullname = Name::intern(&format!("{}.{}", name, field_name));
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
        let rec_name = Name::intern(&format!("{}.rec", name));
        if self.has_const(rec_name) {
            bail!("already defined");
        }
        let abs_name = Name::intern(&format!("{}.abs", name));
        if self.has_axiom(abs_name) {
            bail!("already defined");
        }
        let ext_name = Name::intern(&format!("{}.ext", name));
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

        // inhab u
        let this = Parameter {
            name: Name::fresh_with_name("this"),
            ty: { mk_type_const(name).apply(local_types.iter().map(|&x| mk_type_local(x))) },
        };

        let mut const_fields = vec![];
        for field in &fields {
            if let StructureField::Const(field) = field {
                const_fields.push(Parameter {
                    name: field.name,
                    ty: field.ty.clone(),
                });
            }
        }

        // generate recursor
        //   rec.{u, α} : inhab u → (set u → α) → α
        let ret_ty = Name::fresh();
        let mut rec_local_types = local_types.clone();
        rec_local_types.push(ret_ty);
        let rec_ty = mk_type_local(ret_ty).arrow(vec![
            this.ty.clone(),
            mk_type_local(ret_ty).arrow(const_fields.iter().map(|field| field.ty.clone())),
        ]);
        self.add_const(rec_name, rec_local_types, vec![], rec_ty);

        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(field) => {
                    // rep : set u
                    // ↦ def inhab.rep.{u} : inhab u → set u := λ (this : inhab u), inhab.rec.{u, set u} this (λ (rep : set u), rep)
                    let fullname = Name::intern(&format!("{}.{}", name, field.name));
                    let ty = field.ty.arrow([this.ty.clone()]);
                    self.add_const(fullname, local_types.clone(), vec![], ty);

                    let mut target = mk_const(
                        rec_name,
                        local_types
                            .iter()
                            .map(|&x| mk_type_local(x))
                            .chain([field.ty.clone()])
                            .collect(),
                        vec![],
                    );
                    target = target.apply([mk_local(this.name), {
                        let mut target = mk_local(field.name);
                        target.abs(&const_fields);
                        target
                    }]);
                    target.abs(slice::from_ref(&this));
                    self.add_delta(fullname, target);

                    // rep ↦ inhab.rep.{u} this
                    let mut target = mk_const(
                        fullname,
                        local_types.iter().map(|&x| mk_type_local(x)).collect(),
                        vec![],
                    );
                    target = target.apply([mk_local(this.name)]);
                    subst.push((field.name, target));
                }
                StructureField::Axiom(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name));
                    let mut target = field.target.clone();
                    let new_target = target.subst(&subst);
                    target = new_target;
                    target = generalize(&target, slice::from_ref(&this));
                    self.add_axiom(fullname, local_types.clone(), vec![], target);
                }
            }
        }
        // generate abstraction principle
        // axiom inhab.abs.{u} (s : set u) : (∃ x, x ∈ s) → ∃ this, s = inhab.rep this
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

                    // inhab.rep this
                    let fullname = Name::intern(&format!("{}.{}", name, field.name));
                    let mut rhs = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                        vec![],
                    );
                    rhs = rhs.apply([mk_local(this.name)]);

                    // s = inhab.rep this
                    let mut char = mk_const(Name::intern("eq"), vec![field.ty.clone()], vec![]);
                    char = char.apply([mk_local(param.name), rhs]);
                    chars.push(char);

                    // rep ↦ s
                    subst.push((field.name, mk_local(param.name)));

                    params.push(param);
                }
                StructureField::Axiom(field) => {
                    let mut target = field.target.clone();
                    let new_target = target.subst(&subst);
                    target = new_target;
                    guards.push(target);
                }
            }
        }
        let mut abs = mk_const(Name::intern("exists"), vec![this.ty.clone()], vec![]);
        abs = abs.apply([{
            let mut char = chars
                .into_iter()
                .reduce(|left, right| {
                    let mut conj = mk_const(Name::intern("and"), vec![], vec![]);
                    conj = conj.apply([left, right]);
                    conj
                })
                .unwrap_or_else(|| mk_const(Name::intern("true"), vec![], vec![]));
            char.abs(slice::from_ref(&this));
            char
        }]);
        abs = guard(&abs, guards);
        abs = generalize(&abs, &params);
        self.add_axiom(abs_name, local_types.clone(), vec![], abs);

        // generate extensionality
        // axiom inhab.ext.{u} (this₁ this₂ : inhab u) : inhab.rep this₁ = inhab.rep this₂ → this₁ = this₂
        let this1 = Parameter {
            name: Name::fresh_with_name("this₁"),
            ty: this.ty.clone(),
        };
        let this2 = Parameter {
            name: Name::fresh_with_name("this₂"),
            ty: this.ty.clone(),
        };
        let mut guards = vec![];
        for field in &const_fields {
            let fullname = Name::intern(&format!("{}.{}", name, field.name));
            let proj = mk_const(
                fullname,
                local_types.iter().map(|x| mk_type_local(*x)).collect(),
                vec![],
            );

            let mut lhs = proj.clone();
            lhs = lhs.apply([mk_local(this1.name)]);
            let mut rhs = proj;
            rhs = rhs.apply([mk_local(this2.name)]);

            let mut guard = mk_const(Name::intern("eq"), vec![field.ty.clone()], vec![]);
            guard = guard.apply([lhs, rhs]);
            guards.push(guard);
        }
        let mut target = mk_const(Name::intern("eq"), vec![this.ty.clone()], vec![]);
        target = target.apply([mk_local(this1.name), mk_local(this2.name)]);
        target = guard(&target, guards);
        target = generalize(&target, &[this1, this2]);
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
        //   def power.inhab.rep.{u} (A : set u) : set (set u) := power A
        //   lemma power.inhab.inhabited.{u} : ∃ a, a ∈ power.inhab.rep A := (..)
        //   const power.inhab.{u} : set u → inhab (set u)
        //   axiom power.inhab.spec.{u} (A : set u) : inhab.rec (power.inhab A) = λ f, f (power.inhab.rep A)
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
        let structure_name = structure_name.name;
        let Some(cmd_structure) = self.structure_table.get(&structure_name) else {
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
        let mut num_consts = 0;
        for (structure_field, field) in zip(&cmd_structure.fields, &mut fields) {
            match structure_field {
                StructureField::Const(structure_field) => {
                    let &mut InstanceField::Def(InstanceDef {
                        name: ref field_name,
                        ref ty,
                        target: _,
                    }) = field
                    else {
                        bail!("definition expected");
                    };
                    let field_fullname = Name::intern(&format!("{}.{}", name, field_name));
                    if self.has_const(field_fullname) {
                        bail!("already defined");
                    }
                    if structure_field.name != *field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_type(&mut local_env, ty, Kind::base())?;
                    let structure_field_ty = structure_field.ty.subst(&type_subst);
                    if structure_field_ty != *ty {
                        bail!("type mismatch");
                    }
                    local_env.locals.push(Parameter {
                        name: *field_name,
                        ty: ty.clone(),
                    });
                    num_consts += 1;
                }
                StructureField::Axiom(structure_field) => {
                    let &mut InstanceField::Lemma(InstanceLemma {
                        name: ref field_name,
                        ref mut target,
                        holes: _,
                        expr: _,
                    }) = field
                    else {
                        bail!("lemma expected");
                    };
                    let field_fullname = Name::intern(&format!("{}.{}", name, field_name));
                    if self.has_axiom(field_fullname) {
                        bail!("already defined");
                    }
                    if structure_field.name != *field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
                    let mut structure_field_target = structure_field.target.clone();
                    let new_target = structure_field_target.subst_type(&type_subst);
                    structure_field_target = new_target;
                    if !structure_field_target.alpha_eq(target) {
                        bail!("target mismatch");
                    }
                }
            }
        }
        local_env
            .locals
            .truncate(local_env.locals.len() - num_consts);
        let spec_name = Name::intern(&format!("{}.spec", name));
        if self.has_axiom(spec_name) {
            bail!("already defined");
        }
        // well-formedness check (all but entity elaboration) is completed.

        // generate a delcaration per field first
        let mut subst = vec![];
        for field in &mut fields {
            match field {
                InstanceField::Def(field) => {
                    let InstanceDef {
                        name: field_name,
                        ref ty,
                        ref mut target,
                    } = *field;
                    // e.g. def power.inhab.rep.{u} (A : set u) : set (set u) := power A
                    let new_target = target.subst(&subst);
                    *target = new_target;
                    self.elaborate_term(&mut local_env, target, ty)?;

                    let fullname = Name::intern(&format!("{}.{}", name, field_name));
                    let target_ty = ty.arrow(params.iter().map(|param| param.ty.clone()));
                    self.add_const(
                        fullname,
                        local_types.clone(),
                        local_classes.clone(),
                        target_ty,
                    );
                    let target = {
                        let mut m = target.clone();
                        m.abs(&params);
                        m
                    };
                    self.add_delta(fullname, target);

                    // rep ↦ inhab.rep.{u} A
                    let mut target = mk_const(
                        fullname,
                        local_types.iter().map(|&x| mk_type_local(x)).collect(),
                        local_classes
                            .iter()
                            .map(|c| mk_instance_local(c.clone()))
                            .collect(),
                    );
                    target = target.apply(params.iter().map(|param| mk_local(param.name)));
                    subst.push((field_name, target));
                }
                InstanceField::Lemma(field) => {
                    let InstanceLemma {
                        name: field_name,
                        ref mut target,
                        ref holes,
                        ref mut expr,
                    } = *field;
                    // e.g. lemma power.inhab.inhabited.{u} : ∃ a, a ∈ rep := (..)
                    let new_target = target.subst(&subst);
                    *target = new_target;
                    expr.subst(&subst);
                    self.elaborate_expr(&mut local_env, holes.clone(), expr, target)?;
                    self.proof_env().check_prop(
                        &mut local_env,
                        &mut proof::LocalEnv::default(),
                        expr,
                        target,
                    );

                    let fullname = Name::intern(&format!("{}.{}", name, field_name));
                    let mut target = target.clone();
                    target = generalize(&target, &params);
                    self.add_axiom(fullname, local_types.clone(), local_classes.clone(), target);
                }
            }
        }

        // e.g. const power.inhab.{u} : set u → inhab (set u)
        let mut target = target_ty.clone();
        for param in params.iter().rev() {
            target = target.arrow([param.ty.clone()]);
        }
        self.add_const(name, local_types.clone(), local_classes.clone(), target);

        // generate spec
        //   axiom power.inhab.spec.{u, α} (A : set u) : inhab.rec.{set u, α} (power.inhab A) = λ (f : set (set u) → α), f (power.inhab.rep A)
        let ret_ty = Name::fresh();
        let mut left = mk_const(
            Name::intern(&format!("{}.rec", structure_name)),
            target_ty
                .args()
                .into_iter()
                .cloned()
                .chain([mk_type_local(ret_ty)])
                .collect(),
            vec![],
        );
        left = left.apply([{
            let mut target = mk_const(
                name,
                local_types.iter().map(|&x| mk_type_local(x)).collect(),
                local_classes
                    .iter()
                    .map(|c| mk_instance_local(c.clone()))
                    .collect(),
            );
            target = target.apply(params.iter().map(|param| mk_local(param.name)));
            target
        }]);
        let f = Parameter {
            name: Name::fresh_with_name("f"),
            ty: mk_type_local(ret_ty).arrow(fields.iter().filter_map(|field| match field {
                InstanceField::Def(field) => Some(field.ty.clone()),
                InstanceField::Lemma(_) => None,
            })),
        };
        let mut right = mk_local(f.name);
        right = right.apply(fields.iter().filter_map(|field| match field {
            InstanceField::Def(field) => {
                let mut target = mk_const(
                    Name::intern(&format!("{}.{}", name, field.name)),
                    local_types.iter().map(|&x| mk_type_local(x)).collect(),
                    vec![],
                );
                target = target.apply(params.iter().map(|param| mk_local(param.name)));
                Some(target)
            }
            InstanceField::Lemma(_) => None,
        }));
        right.abs(slice::from_ref(&f));
        let mut target = mk_const(
            Name::intern("eq"),
            vec![{ mk_type_local(ret_ty).arrow([f.ty.clone()]) }],
            vec![],
        );
        target = target.apply([left, right]);
        target = generalize(&target, &params);
        let mut local_types = local_types.clone();
        local_types.push(ret_ty);
        self.add_axiom(spec_name, local_types, local_classes, target);
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
                    let fullname = Name::intern(&format!("{}.{}", name, field_name));
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
                    let fullname = Name::intern(&format!("{}.{}", name, field_name));
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
                    let fullname = Name::intern(&format!("{}.{}", name, field.name));
                    self.add_const(
                        fullname,
                        local_types.clone(),
                        vec![this_class.clone()],
                        field.ty.clone(),
                    );
                    self.add_kappa(fullname);

                    let target = mk_const(
                        fullname,
                        local_types.iter().map(|x| mk_type_local(*x)).collect(),
                        vec![this_instance.clone()],
                    );
                    subst.push((field.name, target));
                }
                ClassStructureField::Axiom(field) => {
                    let fullname = Name::intern(&format!("{}.{}", name, field.name));
                    let mut target = field.target.clone();
                    let new_target = target.subst(&subst);
                    target = new_target;
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
            name,
            local_types,
            local_classes,
            target,
            mut fields,
        } = cmd;
        if self.has_class_instance(name) {
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
        for local_class in &local_classes {
            self.elaborate_class(&mut local_env, local_class)?;
            local_env.local_classes.push(local_class.clone());
        }
        self.elaborate_class(&mut local_env, &target)?;
        // TODO: this implementation is too conservative.
        for instance in self.class_instance_table.values() {
            let instance_target = {
                let mut type_subst = vec![];
                for &name in &instance.local_types {
                    type_subst.push((name, mk_fresh_type_hole()));
                }
                instance.target.subst(&type_subst)
            };
            if target.matches(&instance_target).is_some() {
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
                    let &mut ClassInstanceField::Def(ClassInstanceDef {
                        name: ref field_name,
                        ref ty,
                        ref mut target,
                    }) = field
                    else {
                        bail!("definition expected");
                    };
                    if structure_field.name != *field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_type(&mut local_env, ty, Kind::base())?;
                    let structure_field_ty = structure_field.ty.subst(&type_subst);
                    if structure_field_ty != *ty {
                        bail!("type mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, ty)?;
                    subst.push((*field_name, target.clone()));
                }
                ClassStructureField::Axiom(structure_field) => {
                    let &mut ClassInstanceField::Lemma(ClassInstanceLemma {
                        name: ref field_name,
                        ref mut target,
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
                    let new_target = structure_field_target.subst_type(&type_subst);
                    structure_field_target = new_target;
                    let new_target = structure_field_target.subst(&subst);
                    structure_field_target = new_target;
                    if !structure_field_target.alpha_eq(target) {
                        bail!("target mismatch");
                    }
                    self.elaborate_expr(&mut local_env, holes.clone(), expr, target)?;
                    self.proof_env().check_prop(
                        &mut local_env,
                        &mut proof::LocalEnv::default(),
                        expr,
                        target,
                    );
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
                    let fullname = Name::intern(&format!("{}.{}", cmd_structure.name, field_name));
                    method_table.insert(fullname, target.clone());
                }
                ClassInstanceField::Lemma(_) => {}
            }
        }
        self.add_class_instance(name, local_types, local_classes, target, method_table);
        Ok(())
    }
}
