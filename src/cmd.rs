use std::{collections::HashMap, iter::zip, slice, vec};

use anyhow::bail;

use crate::{
    elab,
    parse::TokenTable,
    print::{OpTable, Pretty},
    proof::{self, Axiom, Expr, generalize, guard, mk_type_prop, ungeneralize, unguard},
    tt::{
        self, Class, ClassInstance, ClassType, Const, Delta, Id, Kappa, Kind, Local, LocalEnv,
        Name, Path, QualifiedName, Term, Type, mk_const, mk_fresh_type_hole, mk_instance_local,
        mk_local, mk_type_arrow, mk_type_const, mk_type_local,
    },
};

#[derive(Clone, Debug, Default)]
pub struct Namespace {
    pub use_table: HashMap<Name, QualifiedName>,
}

impl Namespace {
    pub fn add(&mut self, alias: Name, target: QualifiedName) {
        self.use_table.insert(alias, target);
    }
}

#[derive(Debug, Clone)]
pub enum Cmd {
    NamespaceStart(CmdNamespaceStart),
    BlockEnd,
    Use(CmdUse),
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
    TypeInductive(CmdTypeInductive),
    Inductive(CmdInductive),
    Structure(CmdStructure),
    Instance(CmdInstance),
    ClassStructure(CmdClassStructure),
    ClassInstance(CmdClassInstance),
}

#[derive(Clone, Debug)]
pub struct CmdNamespaceStart {
    pub path: Path,
}

#[derive(Clone, Debug)]
pub struct CmdInfix {
    pub op: String,
    pub prec: usize,
    pub entity: QualifiedName,
}

#[derive(Clone, Debug)]
pub struct CmdInfixr {
    pub op: String,
    pub prec: usize,
    pub entity: QualifiedName,
}

#[derive(Clone, Debug)]
pub struct CmdInfixl {
    pub op: String,
    pub prec: usize,
    pub entity: QualifiedName,
}

#[derive(Clone, Debug)]
pub struct CmdPrefix {
    pub op: String,
    pub prec: usize,
    pub entity: QualifiedName,
}

#[derive(Clone, Debug)]
pub struct CmdNofix {
    pub op: String,
    pub entity: QualifiedName,
}

#[derive(Clone, Debug)]
pub struct CmdUse {
    pub absolute: bool,
    pub decls: Vec<UseDecl>,
}

#[derive(Clone, Debug)]
pub struct UseDecl {
    pub alias: Name,
    pub target: QualifiedName,
}

#[derive(Clone, Debug)]
pub struct CmdDef {
    pub name: QualifiedName,
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdAxiom {
    pub name: QualifiedName,
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdLemma {
    pub name: QualifiedName,
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub target: Term,
    pub holes: Vec<(Id, Type)>,
    pub expr: Expr,
}

#[derive(Clone, Debug)]
pub struct CmdConst {
    pub name: QualifiedName,
    pub local_classes: Vec<Class>,
    pub local_types: Vec<Id>,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct CmdTypeConst {
    pub name: QualifiedName,
    pub kind: Kind,
}

#[derive(Clone, Debug)]
pub struct CmdTypeInductive {
    pub name: QualifiedName,
    pub self_id: Id,
    pub local_types: Vec<Id>,
    pub ctors: Vec<DataConstructor>,
}

#[derive(Clone, Debug)]
pub struct DataConstructor {
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct CmdInductive {
    pub name: QualifiedName,
    pub self_id: Id,
    pub local_types: Vec<Id>,
    pub params: Vec<Local>,
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
    pub name: QualifiedName,
    pub local_types: Vec<Id>,
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
    pub name: QualifiedName,
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub params: Vec<Local>,
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
    pub holes: Vec<(Id, Type)>,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct CmdClassStructure {
    pub name: QualifiedName,
    pub local_types: Vec<Id>,
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
    pub name: QualifiedName,
    pub local_types: Vec<Id>,
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
    pub holes: Vec<(Id, Type)>,
    pub expr: Expr,
}

impl std::fmt::Display for Cmd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cmd::NamespaceStart(cmd) => write!(f, "namespace {} {{", cmd.path),
            Cmd::BlockEnd => write!(f, "}}"),
            Cmd::Use(cmd) => {
                let prefix = if cmd.absolute { "." } else { "" };
                write!(
                    f,
                    "use {prefix}{}",
                    cmd.decls
                        .iter()
                        .map(|decl| format!("{} as {}", decl.target, decl.alias))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
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
                    .map(|p| format!("{} : {}", p.id, p.ty))
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
                    .map(|p| format!("{} : {}", p.id, p.ty))
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

#[derive(Debug, Clone)]
pub struct Eval {
    pub tt: TokenTable,
    pub pp: OpTable,
    // Invariant: namespace entries are prefix-closed.
    pub namespace_table: HashMap<Path, Namespace>,
    // Invariant: `namespace_table` always contains an entry for `current_namespace`.
    pub current_namespace: Path,
    pub namespace_stack: Vec<Path>,
    pub type_const_table: HashMap<QualifiedName, Kind>,
    pub const_table: HashMap<QualifiedName, Const>,
    pub axiom_table: HashMap<QualifiedName, Axiom>,
    pub delta_table: HashMap<QualifiedName, Delta>,
    pub kappa_table: HashMap<QualifiedName, Kappa>,
    pub class_predicate_table: HashMap<QualifiedName, ClassType>,
    pub class_instance_table: HashMap<QualifiedName, ClassInstance>,
    pub structure_table: HashMap<QualifiedName, CmdStructure>,
    pub class_structure_table: HashMap<QualifiedName, CmdClassStructure>,
}

impl Default for Eval {
    fn default() -> Self {
        let current_namespace = Path::root();
        let mut namespace_table = HashMap::new();
        namespace_table.insert(current_namespace.clone(), Namespace::default());
        Self {
            tt: TokenTable::default(),
            pp: OpTable::default(),
            namespace_table,
            current_namespace,
            namespace_stack: vec![],
            type_const_table: HashMap::new(),
            const_table: HashMap::new(),
            axiom_table: HashMap::new(),
            delta_table: HashMap::new(),
            kappa_table: HashMap::new(),
            class_predicate_table: HashMap::new(),
            class_instance_table: HashMap::new(),
            structure_table: HashMap::new(),
            class_structure_table: HashMap::new(),
        }
    }
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
    pub entity: QualifiedName,
}

impl Eval {
    fn resolve(&mut self, base: Path, target: &QualifiedName) -> QualifiedName {
        let mut path = base;
        let mut names = target.names().into_iter();
        while let Some(name) = names.next() {
            let namespace = self
                .namespace_table
                .get(&path)
                .expect("namespace path must exist");
            let Some(target) = namespace.use_table.get(&name) else {
                path = QualifiedName::from_parts(path, name).into_path();
                for tail in names {
                    path = QualifiedName::from_parts(path, tail).into_path();
                }
                return path.into_qualified_name().unwrap();
            };
            path = target.clone().into_path();
        }
        path.into_qualified_name().unwrap()
    }

    fn add_const(
        &mut self,
        name: QualifiedName,
        local_types: Vec<Id>,
        local_classes: Vec<Class>,
        ty: Type,
    ) {
        assert!(!self.const_table.contains_key(&name));
        for local_class in &local_classes {
            self.tt_env().check_wfc(
                &LocalEnv {
                    local_types: local_types.clone(),
                    local_classes: vec![],
                    locals: vec![],
                    local_deltas: vec![],
                },
                local_class,
            );
        }
        self.tt_env().check_wft(
            &LocalEnv {
                local_types: local_types.clone(),
                local_classes: local_classes.clone(),
                locals: vec![],
                local_deltas: vec![],
            },
            &ty,
        );

        self.const_table.insert(
            name.clone(),
            Const {
                local_types,
                local_classes, // TODO: shrink
                ty,
            },
        );

        log::info!(
            "+ {}",
            Pretty::new(&self.pp, (&name, self.const_table.get(&name).unwrap()),)
        );
    }

    fn add_axiom(
        &mut self,
        name: QualifiedName,
        local_types: Vec<Id>,
        local_classes: Vec<Class>,
        target: Term,
    ) {
        assert!(!self.axiom_table.contains_key(&name));
        for local_class in &local_classes {
            self.tt_env().check_wfc(
                &LocalEnv {
                    local_types: local_types.clone(),
                    local_classes: vec![],
                    locals: vec![],
                    local_deltas: vec![],
                },
                local_class,
            );
        }
        self.tt_env().check_wff(
            &mut LocalEnv {
                local_types: local_types.clone(),
                local_classes: local_classes.clone(),
                locals: vec![],
                local_deltas: vec![],
            },
            &target,
        );

        self.axiom_table.insert(
            name.clone(),
            Axiom {
                local_types,
                local_classes,
                target,
            },
        );

        log::info!(
            "+ {}",
            Pretty::new(&self.pp, (&name, self.axiom_table.get(&name).unwrap()),)
        );
    }

    fn add_type_const(&mut self, name: QualifiedName, kind: Kind) {
        assert!(!self.type_const_table.contains_key(&name));

        self.type_const_table.insert(name.clone(), kind.clone());

        log::info!(
            "+ {}",
            Pretty::new(&self.pp, (&name, self.type_const_table.get(&name).unwrap()),)
        );
    }

    fn add_class_predicate(&mut self, name: QualifiedName, ty: ClassType) {
        assert!(!self.class_predicate_table.contains_key(&name));

        self.class_predicate_table.insert(name.clone(), ty);

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
        name: QualifiedName,
        local_types: Vec<Id>,
        local_classes: Vec<Class>,
        target: Class,
        method_table: HashMap<QualifiedName, Term>,
    ) {
        assert!(!self.class_instance_table.contains_key(&name));
        for local_class in &local_classes {
            self.tt_env().check_wfc(
                &LocalEnv {
                    local_types: local_types.clone(),
                    local_classes: vec![],
                    locals: vec![],
                    local_deltas: vec![],
                },
                local_class,
            );
        }
        self.tt_env().check_wfc(
            &LocalEnv {
                local_types: local_types.clone(),
                local_classes: local_classes.clone(),
                locals: vec![],
                local_deltas: vec![],
            },
            &target,
        );
        // TODO: check method_table

        self.class_instance_table.insert(
            name.clone(),
            ClassInstance {
                local_types,
                local_classes,
                target,
                method_table,
            },
        );
    }

    fn add_delta(&mut self, name: QualifiedName, target: Term) {
        assert!(!self.delta_table.contains_key(&name));

        let Const {
            local_types,
            local_classes,
            ty,
        } = self
            .const_table
            .get(&name)
            .expect("constant must be defined before delta");

        let mut local_env = LocalEnv {
            local_types: local_types.clone(),
            local_classes: local_classes.clone(),
            locals: vec![],
            local_deltas: vec![],
        };

        self.tt_env().check_type(&mut local_env, &target, ty);

        self.delta_table.insert(
            name,
            Delta {
                local_types: local_types.clone(),
                local_classes: local_classes.clone(),
                height: self.tt_env().height(&local_env, &target),
                target,
            },
        );
    }

    fn add_kappa(&mut self, name: QualifiedName) {
        assert!(!self.kappa_table.contains_key(&name));

        self.kappa_table.insert(name, Kappa);
    }

    fn has_const(&self, name: &QualifiedName) -> bool {
        self.const_table.contains_key(name)
    }

    fn has_axiom(&self, name: &QualifiedName) -> bool {
        self.axiom_table.contains_key(name)
    }

    fn has_type_const(&self, name: &QualifiedName) -> bool {
        self.type_const_table.contains_key(name)
    }

    fn has_class_predicate(&self, name: &QualifiedName) -> bool {
        self.class_predicate_table.contains_key(name)
    }

    fn has_class_instance(&self, name: &QualifiedName) -> bool {
        self.class_instance_table.contains_key(name)
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
        holes: Vec<(Id, Type)>,
        expr: &mut Expr,
        target: &Term,
    ) -> anyhow::Result<()> {
        elab::elaborate_expr(self.proof_env(), local_env, holes, expr, target)
    }

    fn tt_env(&self) -> tt::Env<'_> {
        tt::Env {
            type_const_table: &self.type_const_table,
            const_table: &self.const_table,
            delta_table: &self.delta_table,
            kappa_table: &self.kappa_table,
            class_predicate_table: &self.class_predicate_table,
            class_instance_table: &self.class_instance_table,
        }
    }

    fn proof_env(&self) -> proof::Env<'_> {
        proof::Env {
            axiom_table: &self.axiom_table,
            tt_env: self.tt_env(),
        }
    }

    pub fn run_cmd(&mut self, cmd: Cmd) -> anyhow::Result<()> {
        match cmd {
            Cmd::NamespaceStart(inner) => {
                let CmdNamespaceStart { path } = inner;
                let mut parent = Path::root();
                for name in path.names() {
                    let child = QualifiedName::from_parts(parent.clone(), name).into_path();
                    self.namespace_table.entry(child.clone()).or_default();
                    parent = child;
                }
                let previous_namespace = self.current_namespace.clone();
                self.namespace_stack.push(previous_namespace);
                self.current_namespace = path;
                Ok(())
            }
            Cmd::BlockEnd => {
                let Some(previous_namespace) = self.namespace_stack.pop() else {
                    // TODO: this should become unreachable once parser reports brace mismatch as parse error.
                    bail!("unexpected block end");
                };
                self.current_namespace = previous_namespace;
                Ok(())
            }
            Cmd::Use(inner) => {
                let CmdUse { absolute, decls } = inner;
                let current_namespace = self.current_namespace.clone();
                let base = if absolute {
                    Path::root()
                } else {
                    current_namespace.clone()
                };
                for decl in decls {
                    let UseDecl { alias, target } = decl;
                    let target = self.resolve(base.clone(), &target);
                    self.namespace_table
                        .get_mut(&current_namespace)
                        .expect("current namespace must exist")
                        .add(alias, target);
                }
                Ok(())
            }
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
                    local_types,
                    local_classes,
                    ty,
                    mut target,
                } = inner;
                if self.has_const(&name) {
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
                    local_deltas: vec![],
                };
                for local_class in &local_classes {
                    self.elaborate_class(&mut local_env, local_class)?;
                    local_env.local_classes.push(local_class.clone());
                }
                self.elaborate_type(&mut local_env, &ty, Kind::base())?;
                self.elaborate_term(&mut local_env, &mut target, &ty)?;
                // well-formedness check is completed.
                self.add_const(
                    name.clone(),
                    local_types.clone(),
                    local_classes.clone(),
                    ty.clone(),
                );
                self.add_delta(name, target);
                Ok(())
            }
            Cmd::Axiom(inner) => {
                let CmdAxiom {
                    name,
                    local_types,
                    local_classes,
                    mut target,
                } = inner;
                if self.has_axiom(&name) {
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
                    local_deltas: vec![],
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
                    local_types,
                    local_classes,
                    mut target,
                    holes,
                    mut expr,
                } = inner;
                if self.has_axiom(&name) {
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
                    local_deltas: vec![],
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
                    local_types,
                    local_classes,
                    ty,
                } = inner;
                if self.has_const(&name) {
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
                    local_deltas: vec![],
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
                if self.has_type_const(&name) {
                    bail!("already defined");
                }
                self.add_type_const(name, kind);
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
            self_id,
            local_types,
            ctors,
        } = cmd;
        if self.has_type_const(&name) {
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
            local_deltas: vec![],
        };
        local_env.local_types.insert(0, self_id);
        for i in 0..ctors.len() {
            for j in i + 1..ctors.len() {
                if ctors[i].name == ctors[j].name {
                    bail!("duplicate constructors");
                }
            }
        }
        for ctor in &ctors {
            let ctor_name = name.extend(ctor.name.clone());
            if self.has_const(&ctor_name) {
                bail!("already defined");
            }
            let ctor_spec_name = ctor_name.extend(Name::from_str("spec"));
            if self.has_const(&ctor_spec_name) {
                bail!("already defined");
            }
            self.elaborate_type(&mut local_env, &ctor.ty, Kind::base())?;
            let (args, target) = ctor.ty.unarrow();
            if target != mk_type_local(self_id) {
                bail!("invalid constructor: {}", ctor.ty);
            }
            for a in args {
                let (xs, head) = a.unarrow();
                for x in &xs {
                    if x.contains_local(self_id) {
                        bail!("constructor violates strict positivity");
                    }
                }
                if head != mk_type_local(self_id) && head.contains_local(self_id) {
                    bail!("nested inductive type is unsupported");
                }
            }
        }
        let ind_name = name.extend(Name::from_str("ind"));
        if self.has_axiom(&ind_name) {
            bail!("already defined");
        }
        let rec_name = name.extend(Name::from_str("rec"));
        if self.has_const(&rec_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.

        // generate type constructor
        self.add_type_const(name.clone(), Kind(local_types.len()));

        // generate data constructors
        let target_ty = {
            // Foo u v
            mk_type_const(name.clone()).apply(local_types.iter().cloned().map(mk_type_local))
        };
        // Foo ↦ Foo u v
        let subst = [(self_id, target_ty.clone())];
        let mut cs = vec![];
        for ctor in &ctors {
            let ctor_name = name.extend(ctor.name.clone());
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
        let motive = Local {
            id: Id::fresh_with_name(Name::from_str("motive")),
            ty: mk_type_arrow(target_ty.clone(), mk_type_prop()),
        };
        let mut guards = vec![];
        for ctor in &ctors {
            let mut args = vec![];
            let (ctor_arg_tys, _) = ctor.ty.unarrow();
            for arg_ty in ctor_arg_tys {
                args.push(Local {
                    id: Id::fresh(),
                    ty: arg_ty,
                });
            }
            // induction hypotheses
            let mut ih_list = vec![];
            for arg in &args {
                let (xs_types, head) = arg.ty.unarrow();
                let xs: Vec<_> = xs_types
                    .into_iter()
                    .map(|x| Local {
                        id: Id::fresh(),
                        ty: x,
                    })
                    .collect();
                if head != mk_type_local(self_id) {
                    continue;
                }
                // ∀ xs, P (a xs)
                let mut a = mk_local(arg.id);
                a = a.apply(xs.iter().map(|x| mk_local(x.id)));
                let mut h = mk_local(motive.id);
                h = h.apply([a]);
                h = generalize(&h, &xs);
                ih_list.push(h);
            }
            // ∀ args, {IH} → P (C args)
            let ctor_name = name.extend(ctor.name.clone());
            let mut a = mk_const(
                ctor_name,
                local_types.iter().cloned().map(mk_type_local).collect(),
                vec![],
            );
            a = a.apply(args.iter().map(|arg| mk_local(arg.id)));
            let mut target = mk_local(motive.id);
            target = target.apply([a]);
            target = guard(&target, ih_list);
            for arg in &mut args {
                arg.ty = arg.ty.subst(&subst);
            }
            target = generalize(&target, &args);
            guards.push(target);
        }
        // ∀ x P, {guards} → P x
        let x = Local {
            id: Id::fresh_with_name(Name::from_str("x")),
            ty: target_ty.clone(),
        };
        let mut target = mk_local(motive.id);
        target = target.apply([mk_local(x.id)]);
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
        let rec_ty_var = Id::fresh_with_name(Name::from_str("u"));
        let mut rec_local_types = local_types.clone();
        rec_local_types.push(rec_ty_var);
        let mut ctor_params_list = vec![];
        for ctor in &ctors {
            let mut ctor_params = vec![];
            let (ctor_param_tys, _) = ctor.ty.unarrow();
            for ctor_param_ty in ctor_param_tys {
                let ctor_param_ty = ctor_param_ty.subst(&subst);
                ctor_params.push(Local {
                    id: Id::fresh(),
                    ty: ctor_param_ty,
                });
            }
            ctor_params_list.push(ctor_params);
        }
        let mut cont_params = vec![];
        for _ in &ctors {
            cont_params.push(Id::fresh_with_name(Name::from_str("k")));
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
                target = target.apply([mk_local(param.id)]);
            }
            // stepping
            let (ctor_arg_tys, _) = ctor.ty.unarrow();
            for (ctor_arg, param) in zip(ctor_arg_tys, ctor_params) {
                let (arg_tys, ctor_arg_target) = ctor_arg.unarrow();
                if ctor_arg_target != mk_type_local(self_id) {
                    continue;
                }
                let t = ctor_arg.subst(&[(self_id, mk_type_local(rec_ty_var))]);
                cont_arg_tys.push(t);

                let binders: Vec<_> = arg_tys
                    .into_iter()
                    .map(|arg_ty| Local {
                        id: Id::fresh(),
                        ty: arg_ty,
                    })
                    .collect();
                let mut m = mk_const(
                    rec_name.clone(),
                    rec_local_types.iter().cloned().map(mk_type_local).collect(),
                    vec![],
                );
                let mut a = mk_local(param.id);
                a = a.apply(binders.iter().map(|x| mk_local(x.id)));
                m = m.apply([a]);
                m = m.apply(cont_params.iter().map(|&k| mk_local(k)));
                m = m.abs(&binders);
                target = target.apply([m]);
            }

            let cont_param_ty = mk_type_local(rec_ty_var).arrow(cont_arg_tys);
            cont_param_tys.push(cont_param_ty);

            rhs_bodies.push(target);
        }
        let rec_ty = mk_type_local(rec_ty_var)
            .arrow(cont_param_tys.clone())
            .arrow([target_ty]);
        self.add_const(rec_name.clone(), rec_local_types.clone(), vec![], rec_ty);

        let mut rhs_binders = vec![];
        for (x, t) in zip(cont_params, &cont_param_tys) {
            rhs_binders.push(Local {
                id: x,
                ty: t.clone(),
            });
        }
        for ((rhs_body, ctor_params), ctor) in zip(zip(rhs_bodies, ctor_params_list), &ctors) {
            let mut lhs = mk_const(
                rec_name.clone(),
                rec_local_types.iter().cloned().map(mk_type_local).collect(),
                vec![],
            );
            let ctor_name = name.extend(ctor.name.clone());
            let mut lhs_arg = mk_const(
                ctor_name.clone(),
                local_types.iter().cloned().map(mk_type_local).collect(),
                vec![],
            );
            lhs_arg = lhs_arg.apply(ctor_params.iter().map(|x| mk_local(x.id)));
            lhs = lhs.apply([lhs_arg]);

            let mut rhs = rhs_body;
            rhs = rhs.abs(&rhs_binders);

            let eq_ty = mk_type_local(rec_ty_var).arrow(cont_param_tys.clone());

            let mut spec = mk_const(
                QualifiedName::from_name(Name::from_str("eq")),
                vec![eq_ty],
                vec![],
            );
            spec = spec.apply([lhs, rhs]);
            spec = generalize(&spec, &ctor_params);

            let ctor_spec_name = ctor_name.extend(Name::from_str("spec"));
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
            self_id,
            local_types,
            params,
            target_ty,
            mut ctors,
        } = cmd;
        if self.has_const(&name) {
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
            local_deltas: vec![],
        };
        for i in 0..params.len() {
            for j in i + 1..params.len() {
                if params[i].id == params[j].id {
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
            Local {
                id: self_id,
                ty: target_ty.clone(),
            },
        );
        let mut ctor_params_list = vec![];
        let mut ctor_args_list = vec![];
        let mut ctor_target_list = vec![];
        let mut ctor_ind_args_list = vec![];
        for ctor in &mut ctors {
            let ctor_name = name.extend(ctor.name.clone());
            if self.has_axiom(&ctor_name) {
                bail!("already defined");
            }
            self.elaborate_term(&mut local_env, &mut ctor.target, &mk_type_prop())?;

            let (ctor_params, m) = ungeneralize(&ctor.target);
            ctor_params_list.push(ctor_params.clone());
            let (ctor_args, m) = unguard(&m);
            ctor_args_list.push(ctor_args.clone());
            if !m.head().alpha_eq(&mk_local(self_id)) {
                bail!(
                    "invalid constructor. Currently only Horn clauses are supported in inductive clauses: {m}"
                );
            }
            for a in m.args() {
                if a.contains_local(self_id) {
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
                if current.contains_local(self_id) {
                    if !current.head().alpha_eq(&mk_local(self_id)) {
                        bail!("invalid target");
                    }
                    for a in current.args() {
                        if a.contains_local(self_id) {
                            bail!("invalid target");
                        }
                    }
                    ctor_ind_args.push(ctor_arg.clone());
                }
            }
            ctor_ind_args_list.push(ctor_ind_args);
        }
        local_env.locals.remove(0);
        let ind_name = name.extend(Name::from_str("ind"));
        if self.has_axiom(&ind_name) {
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
        self.add_const(name.clone(), local_types.clone(), vec![], pred_ty);

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.intro.{u} (x : τ) : ∀ y, φ → (∀ z, ψ → P.{u} x M) → P.{u} x N
        for ctor in &ctors {
            let ctor_name = name.extend(ctor.name.clone());
            let mut target = ctor.target.clone();
            // P.{u} x
            let mut stash = mk_const(
                name.clone(),
                local_types.iter().map(|id| mk_type_local(*id)).collect(),
                vec![],
            );
            stash = stash.apply(params.iter().map(|param| mk_local(param.id)));
            let subst = [(self_id, stash)];
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
            .map(|t| Local {
                id: Id::fresh(),
                ty: t,
            })
            .collect::<Vec<_>>();
        let motive = Local {
            id: Id::fresh_with_name(Name::from_str("motive")),
            ty: target_ty.clone(),
        };
        // C w
        let mut target = mk_local(motive.id);
        target = target.apply(indexes.iter().map(|index| mk_local(index.id)));
        let mut guards = vec![];
        // (∀ y, φ → (∀ z, ψ → P x M) → (∀ z, ψ → C M) → C N) → C w
        for (ctor_params, (mut ctor_args, (ctor_target, mut ctor_ind_args))) in zip(
            ctor_params_list,
            zip(ctor_args_list, zip(ctor_target_list, ctor_ind_args_list)),
        ) {
            // P ↦ C
            let subst_with_motive = [(self_id, mk_local(motive.id))];

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
                name.clone(),
                local_types.iter().map(|id| mk_type_local(*id)).collect(),
                vec![],
            );
            stash = stash.apply(params.iter().map(|param| mk_local(param.id)));
            let subst = [(self_id, stash)];

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
            name.clone(),
            local_types.iter().map(|id| mk_type_local(*id)).collect(),
            vec![],
        );
        p = p.apply(params.iter().map(|param| mk_local(param.id)));
        p = p.apply(indexes.iter().map(|index| mk_local(index.id)));
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
        if self.has_type_const(&name) {
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
            local_deltas: vec![],
        };
        let mut const_field_names: Vec<Name> = vec![];
        let mut axiom_field_names: Vec<Name> = vec![];
        for field in &mut fields {
            match field {
                StructureField::Const(StructureConst {
                    name: field_name,
                    ty: field_ty,
                }) => {
                    let field_name = field_name.clone();
                    let fullname = name.extend(field_name.clone());
                    if self.has_const(&fullname) {
                        bail!("already defined");
                    }
                    if const_field_names.contains(&field_name) {
                        bail!("duplicate const field");
                    }
                    const_field_names.push(field_name.clone());
                    self.elaborate_type(&mut local_env, field_ty, Kind::base())?;
                    local_env.locals.push(Local {
                        id: Id::from_name(&field_name),
                        ty: field_ty.clone(),
                    });
                }
                StructureField::Axiom(StructureAxiom {
                    name: field_name,
                    target,
                }) => {
                    let field_name = field_name.clone();
                    let fullname = name.extend(field_name.clone());
                    if self.has_axiom(&fullname) {
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
        let abs_name = name.extend(Name::from_str("abs"));
        if self.has_axiom(&abs_name) {
            bail!("already defined");
        }
        // well-formedness check is completed.
        self.structure_table.insert(
            name.clone(),
            CmdStructure {
                name: name.clone(),
                local_types: local_types.clone(),
                fields: fields.clone(),
            },
        );
        self.add_type_const(name.clone(), Kind(local_types.len()));

        // inhab u
        let this = Local {
            id: Id::fresh_with_name(Name::from_str("this")),
            ty: {
                mk_type_const(name.clone()).apply(local_types.iter().cloned().map(mk_type_local))
            },
        };

        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(StructureConst {
                    name: field_name,
                    ty: field_ty,
                }) => {
                    let fullname = name.extend(field_name.clone());
                    let ty = field_ty.arrow([this.ty.clone()]);
                    self.add_const(fullname.clone(), local_types.clone(), vec![], ty);

                    // rep ↦ inhab.rep.{u} this
                    let mut target = mk_const(
                        fullname,
                        local_types.iter().cloned().map(mk_type_local).collect(),
                        vec![],
                    );
                    target = target.apply([mk_local(this.id)]);
                    subst.push((Id::from_name(field_name), target));
                }
                StructureField::Axiom(StructureAxiom {
                    name: field_name,
                    target,
                }) => {
                    let fullname = name.extend(field_name.clone());
                    let mut target = target.clone();
                    let new_target = target.subst(&subst);
                    target = new_target;
                    target = generalize(&target, slice::from_ref(&this));
                    self.add_axiom(fullname, local_types.clone(), vec![], target);
                }
            }
        }
        // generate abstraction principle
        // axiom inhab.abs.{u} (s : set u) : (∃ x, x ∈ s) → ∃! this, s = inhab.rep this
        let mut params = vec![];
        let mut guards = vec![];
        let mut chars = vec![];
        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(StructureConst {
                    name: field_name,
                    ty: field_ty,
                }) => {
                    // (s : set u)
                    let param = Local {
                        id: Id::fresh_with_name(field_name.clone()),
                        ty: field_ty.clone(),
                    };

                    // inhab.rep this
                    let fullname = name.extend(field_name.clone());
                    let mut rhs = mk_const(
                        fullname,
                        local_types.iter().cloned().map(mk_type_local).collect(),
                        vec![],
                    );
                    rhs = rhs.apply([mk_local(this.id)]);

                    // s = inhab.rep this
                    let mut char = mk_const(
                        QualifiedName::from_name(Name::from_str("eq")),
                        vec![field_ty.clone()],
                        vec![],
                    );
                    char = char.apply([mk_local(param.id), rhs]);
                    chars.push(char);

                    // rep ↦ s
                    subst.push((Id::from_name(field_name), mk_local(param.id)));

                    params.push(param);
                }
                StructureField::Axiom(StructureAxiom { target, .. }) => {
                    let mut target = target.clone();
                    let new_target = target.subst(&subst);
                    target = new_target;
                    guards.push(target);
                }
            }
        }
        let mut abs = mk_const(
            QualifiedName::from_name(Name::from_str("uexists")),
            vec![this.ty.clone()],
            vec![],
        );
        abs = abs.apply([{
            let mut char = chars
                .into_iter()
                .reduce(|left, right| {
                    let mut conj = mk_const(
                        QualifiedName::from_name(Name::from_str("and")),
                        vec![],
                        vec![],
                    );
                    conj = conj.apply([left, right]);
                    conj
                })
                .unwrap_or_else(|| {
                    mk_const(
                        QualifiedName::from_name(Name::from_str("true")),
                        vec![],
                        vec![],
                    )
                });
            char = char.abs(slice::from_ref(&this));
            char
        }]);
        abs = guard(&abs, guards);
        abs = generalize(&abs, &params);
        self.add_axiom(abs_name, local_types.clone(), vec![], abs);
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
        //   axiom power.inhab.rep.spec.{u} (A : set u) :
        //     inhab.rep (power.inhab A) = power.inhab.rep A
        //
        let CmdInstance {
            name,
            local_types,
            local_classes,
            params,
            target_ty,
            mut fields,
        } = cmd;
        if self.has_const(&name) {
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
            local_deltas: vec![],
        };
        for local_class in &local_classes {
            self.elaborate_class(&mut local_env, local_class)?;
            local_env.local_classes.push(local_class.clone());
        }
        for i in 0..params.len() {
            for j in i + 1..params.len() {
                if params[i].id == params[j].id {
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
        let structure_name = structure_name.name.clone();
        let Some(cmd_structure) = self.structure_table.get(&structure_name) else {
            bail!("type of instance must be a structure");
        };
        let mut type_subst = Vec::with_capacity(cmd_structure.local_types.len());
        for (x, t) in zip(&cmd_structure.local_types, target_ty.args()) {
            type_subst.push((*x, t.clone()));
        }
        let type_subst = type_subst;
        if cmd_structure.fields.len() != fields.len() {
            bail!("number of fields mismatch");
        }
        let mut num_consts = 0;
        for (structure_field, field) in zip(&cmd_structure.fields, &mut fields) {
            match (structure_field, field) {
                (
                    StructureField::Const(StructureConst {
                        name: structure_field_name,
                        ty: structure_field_ty,
                    }),
                    InstanceField::Def(InstanceDef {
                        name: field_name,
                        ty,
                        ..
                    }),
                ) => {
                    let structure_field_name = structure_field_name.clone();
                    let field_name = field_name.clone();
                    let field_fullname = name.extend(field_name.clone());
                    if self.has_const(&field_fullname) {
                        bail!("already defined");
                    }
                    if structure_field_name != field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_type(&mut local_env, ty, Kind::base())?;
                    let structure_field_ty = structure_field_ty.subst(&type_subst);
                    if structure_field_ty != *ty {
                        bail!("type mismatch");
                    }
                    local_env.locals.push(Local {
                        id: Id::from_name(&field_name),
                        ty: ty.clone(),
                    });
                    num_consts += 1;
                }
                (StructureField::Const(_), _) => {
                    bail!("definition expected");
                }
                (
                    StructureField::Axiom(StructureAxiom {
                        name: structure_field_name,
                        target: structure_field_target,
                    }),
                    InstanceField::Lemma(InstanceLemma {
                        name: field_name,
                        target,
                        ..
                    }),
                ) => {
                    let structure_field_name = structure_field_name.clone();
                    let field_name = field_name.clone();
                    let field_fullname = name.extend(field_name.clone());
                    if self.has_axiom(&field_fullname) {
                        bail!("already defined");
                    }
                    if structure_field_name != field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
                    let mut structure_field_target = structure_field_target.clone();
                    let new_target = structure_field_target.subst_type(&type_subst);
                    structure_field_target = new_target;
                    if !structure_field_target.alpha_eq(target) {
                        bail!("target mismatch");
                    }
                }
                (StructureField::Axiom(_), _) => {
                    bail!("lemma expected");
                }
            }
        }
        local_env
            .locals
            .truncate(local_env.locals.len() - num_consts);
        // well-formedness check (all but entity elaboration) is completed.

        // generate a delcaration per field first
        let mut subst = vec![];
        for field in &mut fields {
            match field {
                InstanceField::Def(InstanceDef {
                    name: field_name,
                    ty,
                    target,
                }) => {
                    let field_name = field_name.clone();
                    // e.g. def power.inhab.rep.{u} (A : set u) : set (set u) := power A
                    let new_target = target.subst(&subst);
                    *target = new_target;
                    self.elaborate_term(&mut local_env, target, ty)?;

                    let fullname = name.extend(field_name.clone());
                    let target_ty = ty.arrow(params.iter().map(|param| param.ty.clone()));
                    self.add_const(
                        fullname.clone(),
                        local_types.clone(),
                        local_classes.clone(),
                        target_ty,
                    );
                    let target = {
                        let mut m = target.clone();
                        m = m.abs(&params);
                        m
                    };
                    self.add_delta(fullname.clone(), target);

                    // rep ↦ inhab.rep.{u} A
                    let mut target = mk_const(
                        fullname,
                        local_types.iter().cloned().map(mk_type_local).collect(),
                        local_classes
                            .iter()
                            .map(|c| mk_instance_local(c.clone()))
                            .collect(),
                    );
                    target = target.apply(params.iter().map(|param| mk_local(param.id)));
                    subst.push((Id::from_name(&field_name), target));
                }
                InstanceField::Lemma(InstanceLemma {
                    name: field_name,
                    target,
                    holes,
                    expr,
                }) => {
                    let field_name = field_name.clone();
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

                    let fullname = name.extend(field_name.clone());
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
        self.add_const(
            name.clone(),
            local_types.clone(),
            local_classes.clone(),
            target,
        );

        // generate per-field spec axioms
        let mut this = mk_const(
            name.clone(),
            local_types.iter().cloned().map(mk_type_local).collect(),
            local_classes
                .iter()
                .map(|c| mk_instance_local(c.clone()))
                .collect(),
        );
        this = this.apply(params.iter().map(|param| mk_local(param.id)));
        for field in &fields {
            let InstanceField::Def(InstanceDef {
                name: field_name,
                ty,
                ..
            }) = field
            else {
                continue;
            };
            let field_name = field_name.clone();
            let spec_name = name
                .extend(field_name.clone())
                .extend(Name::from_str("spec"));
            if self.has_axiom(&spec_name) {
                bail!("already defined");
            }

            let mut lhs = mk_const(
                structure_name.extend(field_name.clone()),
                target_ty.args().into_iter().cloned().collect(),
                vec![],
            );
            lhs = lhs.apply([this.clone()]);

            let mut rhs = mk_const(
                name.extend(field_name.clone()),
                local_types.iter().cloned().map(mk_type_local).collect(),
                local_classes
                    .iter()
                    .map(|c| mk_instance_local(c.clone()))
                    .collect(),
            );
            rhs = rhs.apply(params.iter().map(|param| mk_local(param.id)));

            let mut target = mk_const(
                QualifiedName::from_name(Name::from_str("eq")),
                vec![ty.clone()],
                vec![],
            );
            target = target.apply([lhs, rhs]);
            target = generalize(&target, &params);
            self.add_axiom(
                spec_name,
                local_types.clone(),
                local_classes.clone(),
                target,
            );
        }
        Ok(())
    }

    fn run_class_structure_cmd(&mut self, cmd: CmdClassStructure) -> anyhow::Result<()> {
        let CmdClassStructure {
            name,
            local_types,
            mut fields,
        } = cmd;
        if self.has_class_predicate(&name) {
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
            local_deltas: vec![],
        };
        let mut const_field_names: Vec<Name> = vec![];
        let mut axiom_field_names: Vec<Name> = vec![];
        for field in &mut fields {
            match field {
                ClassStructureField::Const(ClassStructureConst {
                    name: field_name,
                    ty: field_ty,
                }) => {
                    let field_name = field_name.clone();
                    let fullname = name.extend(field_name.clone());
                    if self.has_const(&fullname) {
                        bail!("already defined");
                    }
                    if const_field_names.contains(&field_name) {
                        bail!("duplicate const field");
                    }
                    const_field_names.push(field_name.clone());
                    self.elaborate_type(&mut local_env, field_ty, Kind::base())?;
                    local_env.locals.push(Local {
                        id: Id::from_name(&field_name),
                        ty: field_ty.clone(),
                    });
                }
                ClassStructureField::Axiom(ClassStructureAxiom {
                    name: field_name,
                    target,
                }) => {
                    let field_name = field_name.clone();
                    let fullname = name.extend(field_name.clone());
                    if self.has_axiom(&fullname) {
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
            name.clone(),
            CmdClassStructure {
                name: name.clone(),
                local_types: local_types.clone(),
                fields: fields.clone(),
            },
        );
        self.add_class_predicate(
            name.clone(),
            ClassType {
                arity: local_types.len(),
            },
        );
        let this_class = Class {
            name: name.clone(),
            args: local_types.iter().cloned().map(mk_type_local).collect(),
        };
        let this_instance = mk_instance_local(this_class.clone());
        let mut subst = vec![];
        for field in &fields {
            match field {
                ClassStructureField::Const(ClassStructureConst {
                    name: field_name,
                    ty,
                }) => {
                    let fullname = name.extend(field_name.clone());
                    self.add_const(
                        fullname.clone(),
                        local_types.clone(),
                        vec![this_class.clone()],
                        ty.clone(),
                    );
                    self.add_kappa(fullname.clone());

                    let target = mk_const(
                        fullname.clone(),
                        local_types.iter().cloned().map(mk_type_local).collect(),
                        vec![this_instance.clone()],
                    );
                    subst.push((Id::from_name(field_name), target));
                }
                ClassStructureField::Axiom(ClassStructureAxiom {
                    name: field_name,
                    target,
                }) => {
                    let fullname = name.extend(field_name.clone());
                    let mut target = target.clone();
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
        if self.has_class_instance(&name) {
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
            local_deltas: vec![],
        };
        for local_class in &local_classes {
            self.elaborate_class(&mut local_env, local_class)?;
            local_env.local_classes.push(local_class.clone());
        }
        self.elaborate_class(&mut local_env, &target)?;
        // TODO: this implementation is too conservative.
        for instance in self.class_instance_table.values() {
            let instance_target = {
                let mut type_subst = Vec::with_capacity(instance.local_types.len());
                for id in &instance.local_types {
                    type_subst.push((*id, mk_fresh_type_hole()));
                }
                instance.target.subst(&type_subst)
            };
            if target.matches(&instance_target).is_some() {
                bail!("overlapping instances are disallowed");
            }
        }
        let cmd_structure = self.class_structure_table.get(&target.name).unwrap();
        let mut type_subst = Vec::with_capacity(cmd_structure.local_types.len());
        for (x, t) in zip(&cmd_structure.local_types, &target.args) {
            type_subst.push((*x, t.clone()));
        }
        if cmd_structure.fields.len() != fields.len() {
            bail!("number of fields mismatch");
        }
        let mut subst = vec![];
        for (structure_field, field) in zip(&cmd_structure.fields, &mut fields) {
            match (structure_field, field) {
                (
                    ClassStructureField::Const(ClassStructureConst {
                        name: structure_field_name,
                        ty: structure_field_ty,
                    }),
                    ClassInstanceField::Def(ClassInstanceDef {
                        name: field_name,
                        ty,
                        target,
                    }),
                ) => {
                    let structure_field_name = structure_field_name.clone();
                    let field_name = field_name.clone();
                    if structure_field_name != field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_type(&mut local_env, ty, Kind::base())?;
                    let structure_field_ty = structure_field_ty.subst(&type_subst);
                    if structure_field_ty != *ty {
                        bail!("type mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, ty)?;
                    subst.push((Id::from_name(&field_name), target.clone()));
                }
                (ClassStructureField::Const(_), _) => {
                    bail!("definition expected");
                }
                (
                    ClassStructureField::Axiom(ClassStructureAxiom {
                        name: structure_field_name,
                        target: structure_field_target,
                    }),
                    ClassInstanceField::Lemma(ClassInstanceLemma {
                        name: field_name,
                        target,
                        holes,
                        expr,
                    }),
                ) => {
                    let structure_field_name = structure_field_name.clone();
                    let field_name = field_name.clone();
                    if structure_field_name != field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
                    let mut structure_field_target = structure_field_target.clone();
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
                (ClassStructureField::Axiom(_), _) => {
                    bail!("lemma expected");
                }
            }
        }
        // well-formedness check is completed.
        let mut method_table = HashMap::new();
        for field in &fields {
            match field {
                ClassInstanceField::Def(ClassInstanceDef {
                    name: field_name,
                    target,
                    ..
                }) => {
                    let field_name = field_name.clone();
                    let target = target.clone();
                    let fullname = cmd_structure.name.extend(field_name.clone());
                    method_table.insert(fullname, target);
                }
                ClassInstanceField::Lemma(_) => {}
            }
        }
        self.add_class_instance(
            name.clone(),
            local_types,
            local_classes,
            target,
            method_table,
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{Cmd, CmdNamespaceStart, CmdTypeConst, CmdUse, Eval, Namespace, UseDecl};
    use crate::tt::{Kind, Name, Path, QualifiedName};

    fn path(value: &str) -> Path {
        let mut path = Path::root();
        if value.is_empty() {
            return path;
        }
        for part in value.split('.') {
            path = QualifiedName::from_parts(path, Name::from_str(part)).into_path();
        }
        path
    }

    fn qualified(value: &str) -> QualifiedName {
        let mut parts = value.split('.');
        let first = parts.next().expect("qualified name must not be empty");
        let mut name = QualifiedName::from_name(Name::from_str(first));
        for part in parts {
            name = name.extend(Name::from_str(part));
        }
        name
    }

    #[test]
    fn namespace_add_stores_qualified_name_target() {
        let mut namespace = Namespace::default();
        let alias = Name::from_str("alias");
        let target = QualifiedName::from_name(Name::from_str("foo"));
        namespace.add(alias.clone(), target.clone());
        assert_eq!(namespace.use_table.get(&alias), Some(&target));
    }

    #[test]
    fn use_decl_stores_qualified_name_target() {
        let alias = Name::from_str("alias");
        let target = QualifiedName::from_name(Name::from_str("foo"));
        let decl = UseDecl {
            alias: alias.clone(),
            target: target.clone(),
        };
        assert_eq!(decl.alias, alias);
        assert_eq!(decl.target, target);
    }

    #[test]
    fn block_end_without_open_namespace_is_error() {
        let mut eval = Eval::default();
        let err = eval
            .run_cmd(Cmd::BlockEnd)
            .expect_err("block end should fail at top level");
        assert_eq!(err.to_string(), "unexpected block end");
    }

    #[test]
    fn block_end_restores_previous_namespace() {
        let mut eval = Eval::default();
        let path = QualifiedName::from_parts(Path::root(), Name::from_str("foo")).into_path();
        eval.run_cmd(Cmd::NamespaceStart(CmdNamespaceStart { path }))
            .expect("namespace start should succeed");
        eval.run_cmd(Cmd::BlockEnd)
            .expect("block end should close opened namespace");
        assert_eq!(eval.current_namespace, Path::root());
        assert!(eval.namespace_stack.is_empty());
    }

    #[test]
    fn namespace_start_does_not_register_namespace_alias() {
        let mut eval = Eval::default();
        let path = QualifiedName::from_parts(Path::root(), Name::from_str("foo")).into_path();
        eval.run_cmd(Cmd::NamespaceStart(CmdNamespaceStart {
            path: path.clone(),
        }))
        .expect("namespace start should succeed");
        assert!(
            !eval.namespace_table[&Path::root()]
                .use_table
                .contains_key(&Name::from_str("foo"))
        );
    }

    #[test]
    fn namespace_start_creates_all_prefix_entries() {
        let mut eval = Eval::default();
        let namespace_path = path("foo.bar.baz");
        eval.run_cmd(Cmd::NamespaceStart(CmdNamespaceStart {
            path: namespace_path,
        }))
        .expect("namespace start should succeed");
        assert!(eval.namespace_table.contains_key(&path("foo")));
        assert!(eval.namespace_table.contains_key(&path("foo.bar")));
        assert!(eval.namespace_table.contains_key(&path("foo.bar.baz")));
    }

    #[test]
    fn type_const_command_does_not_register_declaration_alias() {
        let mut eval = Eval::default();
        let foo_path = QualifiedName::from_parts(Path::root(), Name::from_str("foo")).into_path();
        eval.namespace_table
            .insert(foo_path.clone(), Namespace::default());
        eval.namespace_table
            .get_mut(&Path::root())
            .expect("root namespace must exist")
            .add(Name::from_str("foo"), qualified("foo"));

        eval.run_cmd(Cmd::TypeConst(CmdTypeConst {
            name: QualifiedName::from_name(Name::from_str("foo")).extend(Name::from_str("bar")),
            kind: Kind(0),
        }))
        .expect("type const command should succeed");

        assert!(
            !eval.namespace_table[&foo_path]
                .use_table
                .contains_key(&Name::from_str("bar"))
        );
    }

    #[test]
    fn type_const_command_does_not_create_missing_prefixes_for_declaration_path() {
        let mut eval = Eval::default();

        eval.run_cmd(Cmd::TypeConst(CmdTypeConst {
            name: QualifiedName::from_name(Name::from_str("foo"))
                .extend(Name::from_str("bar"))
                .extend(Name::from_str("baz")),
            kind: Kind(0),
        }))
        .expect("type const command should succeed");

        assert!(!eval.namespace_table.contains_key(&path("foo")));
        assert!(!eval.namespace_table.contains_key(&path("foo.bar")));
        assert!(!eval.namespace_table.contains_key(&path("foo.bar.baz")));
    }

    #[test]
    fn use_command_resolves_relative_target_when_running() {
        let mut eval = Eval::default();
        let root_namespace = Path::root();
        let current_namespace = path("foo");
        eval.namespace_table
            .insert(current_namespace.clone(), Namespace::default());
        eval.namespace_table
            .get_mut(&root_namespace)
            .expect("root namespace must exist")
            .add(Name::from_str("foo"), qualified("foo"));
        eval.namespace_table
            .get_mut(&current_namespace)
            .expect("current namespace must exist")
            .add(Name::from_str("bar"), qualified("real"));
        eval.namespace_table
            .insert(path("real"), Namespace::default());
        eval.current_namespace = current_namespace.clone();

        eval.run_cmd(Cmd::Use(CmdUse {
            absolute: false,
            decls: vec![UseDecl {
                alias: Name::from_str("baz"),
                target: qualified("bar.qux"),
            }],
        }))
        .expect("use command should succeed");

        assert_eq!(
            eval.namespace_table[&current_namespace]
                .use_table
                .get(&Name::from_str("baz")),
            Some(&qualified("real.qux"))
        );
    }

    #[test]
    fn use_command_resolves_absolute_target_when_running() {
        let mut eval = Eval::default();
        let root_namespace = Path::root();
        let current_namespace = path("foo");
        eval.namespace_table
            .insert(current_namespace.clone(), Namespace::default());
        eval.namespace_table
            .get_mut(&root_namespace)
            .expect("root namespace must exist")
            .add(Name::from_str("foo"), qualified("foo"));
        eval.namespace_table
            .get_mut(&root_namespace)
            .expect("root namespace must exist")
            .add(Name::from_str("bar"), qualified("global"));
        eval.namespace_table
            .get_mut(&current_namespace)
            .expect("current namespace must exist")
            .add(Name::from_str("bar"), qualified("local"));
        eval.current_namespace = current_namespace.clone();

        eval.run_cmd(Cmd::Use(CmdUse {
            absolute: true,
            decls: vec![UseDecl {
                alias: Name::from_str("baz"),
                target: qualified("bar"),
            }],
        }))
        .expect("use command should succeed");

        assert_eq!(
            eval.namespace_table[&current_namespace]
                .use_table
                .get(&Name::from_str("baz")),
            Some(&qualified("global"))
        );
    }

    #[test]
    fn use_command_resolves_decls_left_to_right() {
        let mut eval = Eval::default();
        let root_namespace = Path::root();
        eval.namespace_table
            .get_mut(&root_namespace)
            .expect("root namespace must exist")
            .add(Name::from_str("hoge"), qualified("real"));

        eval.run_cmd(Cmd::Use(CmdUse {
            absolute: false,
            decls: vec![
                UseDecl {
                    alias: Name::from_str("fuga"),
                    target: qualified("hoge"),
                },
                UseDecl {
                    alias: Name::from_str("piyo"),
                    target: qualified("fuga"),
                },
            ],
        }))
        .expect("use command should succeed");

        assert_eq!(
            eval.namespace_table[&root_namespace]
                .use_table
                .get(&Name::from_str("fuga")),
            Some(&qualified("real"))
        );
        assert_eq!(
            eval.namespace_table[&root_namespace]
                .use_table
                .get(&Name::from_str("piyo")),
            Some(&qualified("real"))
        );
    }

    #[test]
    fn use_command_does_not_create_missing_namespaces_during_resolution() {
        let mut eval = Eval::default();
        let root_namespace = Path::root();

        eval.run_cmd(Cmd::Use(CmdUse {
            absolute: false,
            decls: vec![UseDecl {
                alias: Name::from_str("alias"),
                target: qualified("qux.quux"),
            }],
        }))
        .expect("use command should succeed");

        assert_eq!(
            eval.namespace_table[&root_namespace]
                .use_table
                .get(&Name::from_str("alias")),
            Some(&qualified("qux.quux"))
        );
        assert!(
            !eval.namespace_table.contains_key(&path("qux")),
            "resolve should not create intermediate namespace entries"
        );
        assert!(
            !eval.namespace_table.contains_key(&path("qux.quux")),
            "resolve should not create terminal namespace entries"
        );
        assert_eq!(
            eval.namespace_table[&root_namespace]
                .use_table
                .get(&Name::from_str("qux")),
            None
        );
    }

    #[test]
    fn use_command_stops_resolution_after_first_missing_alias() {
        let mut eval = Eval::default();
        let root_namespace = Path::root();
        let missing_head_path = path("qux");
        let mut missing_head_namespace = Namespace::default();
        missing_head_namespace.add(Name::from_str("leaf"), qualified("real"));
        eval.namespace_table
            .insert(missing_head_path, missing_head_namespace);

        eval.run_cmd(Cmd::Use(CmdUse {
            absolute: false,
            decls: vec![UseDecl {
                alias: Name::from_str("alias"),
                target: qualified("qux.leaf"),
            }],
        }))
        .expect("use command should succeed");

        assert_eq!(
            eval.namespace_table[&root_namespace]
                .use_table
                .get(&Name::from_str("alias")),
            Some(&qualified("qux.leaf"))
        );
    }
}
