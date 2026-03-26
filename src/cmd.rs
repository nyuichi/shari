use std::{collections::HashMap, iter::zip, slice, vec};

use anyhow::bail;

use crate::{
    elab,
    parse::TokenTable,
    print::{OpTable, Pretty},
    proof::{self, Axiom, Expr, generalize, guard, mk_type_prop, ungeneralize, unguard},
    tt::{
        self, Class, ClassInstance, ClassType, Const, Delta, GlobalId, Id, Kappa, Kind, Local,
        LocalEnv, LocalType, Name, Term, Type, mk_const, mk_fresh_type_hole, mk_instance_global,
        mk_instance_local, mk_local, mk_type_arrow, mk_type_const, mk_type_hole, mk_type_local,
    },
};

fn global_id(value: &str) -> GlobalId {
    GlobalId::from_name(Name::from_str(value))
}

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash, Default)]
pub struct Path {
    inner: Vec<Name>,
}

impl Path {
    pub fn root() -> Self {
        Self { inner: vec![] }
    }

    pub fn is_root(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn names(&self) -> &[Name] {
        &self.inner
    }

    pub fn extend(mut self, name: Name) -> Self {
        self.inner.push(name);
        self
    }

    pub fn to_global_id(&self) -> GlobalId {
        GlobalId::from_name(Name::from_str(&self.to_string()))
    }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_root() {
            return Ok(());
        }
        let Some((first, rest)) = self.inner.split_first() else {
            return Ok(());
        };
        write!(f, "{first}")?;
        for name in rest {
            write!(f, ".{name}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct Namespace {
    pub use_table: HashMap<Name, Path>,
}

impl Namespace {
    pub fn add(&mut self, alias: Name, target: Path) {
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
    TypeInfix(CmdTypeInfix),
    TypeInfixr(CmdTypeInfixr),
    TypeInfixl(CmdTypeInfixl),
    TypePrefix(CmdTypePrefix),
    TypeNofix(CmdTypeNofix),
    Def(CmdDef),
    Axiom(CmdAxiom),
    Lemma(CmdLemma),
    Const(CmdConst),
    TypeConst(CmdTypeConst),
    TypeDef(CmdTypeDef),
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
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdInfixr {
    pub op: String,
    pub prec: usize,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdInfixl {
    pub op: String,
    pub prec: usize,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdPrefix {
    pub op: String,
    pub prec: usize,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdNofix {
    pub op: String,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdTypeInfix {
    pub op: String,
    pub prec: usize,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdTypeInfixr {
    pub op: String,
    pub prec: usize,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdTypeInfixl {
    pub op: String,
    pub prec: usize,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdTypePrefix {
    pub op: String,
    pub prec: usize,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdTypeNofix {
    pub op: String,
    pub entity: GlobalId,
}

#[derive(Clone, Debug)]
pub struct CmdUse {
    pub decls: Vec<UseDecl>,
}

#[derive(Clone, Debug)]
pub struct UseDecl {
    pub alias: Name,
    pub target: Path,
}

#[derive(Clone, Debug)]
pub struct CmdDef {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
    pub local_classes: Vec<Class>,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdAxiom {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
    pub local_classes: Vec<Class>,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdLemma {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
    pub local_classes: Vec<Class>,
    pub target: Term,
    pub holes: Vec<(Id, Type)>,
    pub expr: Expr,
}

#[derive(Clone, Debug)]
pub struct CmdConst {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
    pub local_classes: Vec<Class>,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct CmdTypeConst {
    pub id: GlobalId,
    pub kind: Kind,
}

#[derive(Clone, Debug)]
pub struct CmdTypeDef {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
    pub target: Type,
}

#[derive(Clone, Debug)]
pub struct CmdTypeInductive {
    pub id: GlobalId,
    pub this: Id,
    pub this_name: Name,
    pub local_types: Vec<LocalType>,
    pub ind_id: GlobalId,
    pub rec_id: GlobalId,
    pub ctors: Vec<TypeInductiveConstructor>,
}

#[derive(Clone, Debug)]
pub struct TypeInductiveConstructor {
    pub ctor_id: GlobalId,
    pub name: Name,
    pub ctor_spec_id: GlobalId,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct CmdInductive {
    pub id: GlobalId,
    pub this: Id,
    pub this_name: Name,
    pub local_types: Vec<LocalType>,
    pub params: Vec<Local>,
    pub target_ty: Type,
    pub ind_id: GlobalId,
    pub ctors: Vec<InductiveConstructor>,
}

#[derive(Clone, Debug)]
pub struct InductiveConstructor {
    pub ctor_id: GlobalId,
    pub name: Name,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct CmdStructure {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
    pub abs_id: GlobalId,
    pub fields: Vec<StructureField>,
}

#[derive(Clone, Debug)]
pub enum StructureField {
    Const(StructureConst),
    Axiom(StructureAxiom),
}

#[derive(Clone, Debug)]
pub struct StructureConst {
    pub field_id: Id,
    pub field_name: Name,
    pub id: GlobalId,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct StructureAxiom {
    pub id: GlobalId,
    pub field_name: Name,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct CmdInstance {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
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
    pub field_id: Id,
    pub field_name: Name,
    pub id: GlobalId,
    pub spec_id: GlobalId,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct InstanceLemma {
    pub field_id: Id,
    pub field_name: Name,
    pub id: GlobalId,
    pub target: Term,
    pub holes: Vec<(Id, Type)>,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct CmdClassStructure {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
    pub fields: Vec<ClassStructureField>,
}

#[derive(Clone, Debug)]
pub enum ClassStructureField {
    Const(ClassStructureConst),
    Axiom(ClassStructureAxiom),
}

#[derive(Clone, Debug)]
pub struct ClassStructureConst {
    pub field_id: Id,
    pub field_name: Name,
    pub id: GlobalId,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub struct ClassStructureAxiom {
    pub id: GlobalId,
    pub field_name: Name,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct CmdClassInstance {
    pub id: GlobalId,
    pub local_types: Vec<LocalType>,
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
    pub field_id: Id,
    pub field_name: Name,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct ClassInstanceLemma {
    pub field_id: Id,
    pub field_name: Name,
    pub target: Term,
    pub holes: Vec<(Id, Type)>,
    pub expr: Expr,
}

impl std::fmt::Display for Cmd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: Once printer supports commands, simplify this debug-oriented display impl.
        let local_type_name = |local_types: &[LocalType], id: Id| {
            local_types
                .iter()
                .find(|local_type| local_type.id == id)
                .and_then(|local_type| local_type.name.as_ref())
                .map_or_else(|| id.to_string(), |name| name.to_string())
        };
        let format_local_types = |local_types: &[LocalType]| {
            local_types
                .iter()
                .map(|local_type| {
                    local_type
                        .name
                        .as_ref()
                        .map_or_else(|| local_type.id.to_string(), |name| name.to_string())
                })
                .collect::<Vec<_>>()
                .join(" ")
        };
        let format_type = |local_types: &[LocalType], ty: &Type| {
            fn fmt_type(
                local_types: &[LocalType],
                local_type_name: &impl Fn(&[LocalType], Id) -> String,
                ty: &Type,
                out: &mut String,
                prec: u8,
            ) {
                const TYPE_PREC_ARROW: u8 = 0;
                const TYPE_PREC_APP: u8 = 1;
                const TYPE_PREC_ATOM: u8 = 2;

                match ty {
                    Type::Const(inner) => {
                        out.push_str(&inner.id.to_string());
                    }
                    Type::Arrow(inner) => {
                        let needs_paren = prec > TYPE_PREC_ARROW;
                        if needs_paren {
                            out.push('(');
                        }
                        fmt_type(local_types, local_type_name, &inner.dom, out, TYPE_PREC_APP);
                        out.push_str(" → ");
                        fmt_type(
                            local_types,
                            local_type_name,
                            &inner.cod,
                            out,
                            TYPE_PREC_ARROW,
                        );
                        if needs_paren {
                            out.push(')');
                        }
                    }
                    Type::App(inner) => {
                        let needs_paren = prec > TYPE_PREC_APP;
                        if needs_paren {
                            out.push('(');
                        }
                        fmt_type(local_types, local_type_name, &inner.fun, out, TYPE_PREC_APP);
                        out.push(' ');
                        fmt_type(
                            local_types,
                            local_type_name,
                            &inner.arg,
                            out,
                            TYPE_PREC_ATOM,
                        );
                        if needs_paren {
                            out.push(')');
                        }
                    }
                    Type::Local(inner) => {
                        out.push('$');
                        out.push_str(&local_type_name(local_types, inner.id));
                    }
                    Type::Hole(inner) => {
                        out.push('?');
                        out.push_str(&inner.id.to_string());
                    }
                }
            }

            let mut out = String::new();
            fmt_type(local_types, &local_type_name, ty, &mut out, 0);
            out
        };
        match self {
            Cmd::NamespaceStart(cmd) => write!(f, "namespace {} {{", cmd.path),
            Cmd::BlockEnd => write!(f, "}}"),
            Cmd::Use(cmd) => {
                write!(
                    f,
                    "use {}",
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
            Cmd::TypeInfix(cmd) => {
                write!(f, "type infix {} {} {}", cmd.op, cmd.prec, cmd.entity)
            }
            Cmd::TypeInfixr(cmd) => {
                write!(f, "type infixr {} {} {}", cmd.op, cmd.prec, cmd.entity)
            }
            Cmd::TypeInfixl(cmd) => {
                write!(f, "type infixl {} {} {}", cmd.op, cmd.prec, cmd.entity)
            }
            Cmd::TypePrefix(cmd) => {
                write!(f, "type prefix {} {} {}", cmd.op, cmd.prec, cmd.entity)
            }
            Cmd::TypeNofix(cmd) => write!(f, "type nofix {} {}", cmd.op, cmd.entity),
            Cmd::Def(cmd) => write!(
                f,
                "def {}.{{{}}} : {} := {}",
                cmd.id,
                format_local_types(&cmd.local_types),
                format_type(&cmd.local_types, &cmd.ty),
                cmd.target
            ),
            Cmd::Axiom(cmd) => write!(
                f,
                "axiom {}.{{{}}} : {}",
                cmd.id,
                format_local_types(&cmd.local_types),
                cmd.target
            ),
            Cmd::Lemma(cmd) => write!(
                f,
                "lemma {}.{{{}}} : {} := {}",
                cmd.id,
                format_local_types(&cmd.local_types),
                cmd.target,
                cmd.expr
            ),
            Cmd::Const(cmd) => write!(
                f,
                "const {}.{{{}}} : {}",
                cmd.id,
                format_local_types(&cmd.local_types),
                format_type(&cmd.local_types, &cmd.ty)
            ),
            Cmd::TypeConst(cmd) => write!(f, "type const {} : {}", cmd.id, cmd.kind),
            Cmd::TypeDef(cmd) => write!(
                f,
                "type def {}.{{{}}} := {}",
                cmd.id,
                format_local_types(&cmd.local_types),
                format_type(&cmd.local_types, &cmd.target)
            ),
            Cmd::TypeInductive(cmd) => write!(
                f,
                "inductive {}.{{{}}} {{\n{}\n}}",
                cmd.id,
                format_local_types(&cmd.local_types),
                cmd.ctors
                    .iter()
                    .map(|ctor| format!("{} : {}", ctor.name, ctor.ty))
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::Inductive(cmd) => write!(
                f,
                "inductive {}.{{{}}} ({}) : {} {{\n{}\n}}",
                cmd.id,
                format_local_types(&cmd.local_types),
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
                cmd.id,
                format_local_types(&cmd.local_types),
                cmd.fields
                    .iter()
                    .map(|field| match field {
                        StructureField::Const(c) =>
                            format!("  constant {} : {}", c.field_name, c.ty),
                        StructureField::Axiom(a) =>
                            format!("  axiom {} : {}", a.field_name, a.target),
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::Instance(cmd) => write!(
                f,
                "instance {}.{{{}}} ({}) : {} {{\n{}\n}}",
                cmd.id,
                format_local_types(&cmd.local_types),
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
                            format!("  def {} : {} := {}", d.field_name, d.ty, d.target),
                        InstanceField::Lemma(l) =>
                            format!("  lemma {} : {} := {}", l.field_name, l.target, l.expr),
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::ClassStructure(cmd) => write!(
                f,
                "class structure {}.{{{}}} {{\n{}\n}}",
                cmd.id,
                format_local_types(&cmd.local_types),
                cmd.fields
                    .iter()
                    .map(|field| match field {
                        ClassStructureField::Const(c) =>
                            format!("  constant {} : {}", c.field_name, c.ty),
                        ClassStructureField::Axiom(a) =>
                            format!("  axiom {} : {}", a.field_name, a.target),
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
            Cmd::ClassInstance(cmd) => write!(
                f,
                "class instance {}.{{{}}} : {} {{\n{}\n}}",
                cmd.id,
                format_local_types(&cmd.local_types),
                cmd.target,
                cmd.fields
                    .iter()
                    .map(|field| match field {
                        ClassInstanceField::Def(d) =>
                            format!("  def {} : {} := {}", d.field_name, d.ty, d.target),
                        ClassInstanceField::Lemma(l) =>
                            format!("  lemma {} : {} := {}", l.field_name, l.target, l.expr),
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
    // Invariant: a type name appears in exactly one of `type_const_table` or `type_def_table`.
    pub type_const_table: HashMap<GlobalId, Kind>,
    pub type_def_table: HashMap<GlobalId, CmdTypeDef>,
    pub const_table: HashMap<GlobalId, Const>,
    pub axiom_table: HashMap<GlobalId, Axiom>,
    pub delta_table: HashMap<GlobalId, Delta>,
    pub kappa_table: HashMap<GlobalId, Kappa>,
    pub class_predicate_table: HashMap<GlobalId, ClassType>,
    pub class_instance_table: HashMap<GlobalId, ClassInstance>,
    pub structure_table: HashMap<GlobalId, CmdStructure>,
    pub class_structure_table: HashMap<GlobalId, CmdClassStructure>,
    pub coherence_proofs: Vec<(GlobalId, Vec<LocalType>, Vec<Class>, Term)>,
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
            type_def_table: HashMap::new(),
            const_table: HashMap::new(),
            axiom_table: HashMap::new(),
            delta_table: HashMap::new(),
            kappa_table: HashMap::new(),
            class_predicate_table: HashMap::new(),
            class_instance_table: HashMap::new(),
            structure_table: HashMap::new(),
            class_structure_table: HashMap::new(),
            coherence_proofs: vec![],
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
    pub entity: GlobalId,
}

impl Eval {
    fn add_const(
        &mut self,
        id: GlobalId,
        local_types: Vec<LocalType>,
        local_classes: Vec<Class>,
        ty: Type,
    ) {
        assert!(!self.const_table.contains_key(&id));
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
            id.clone(),
            Const {
                local_types,
                local_classes, // TODO: shrink
                ty,
            },
        );

        log::info!(
            "+ {}",
            Pretty::new(&self.pp, (&id, self.const_table.get(&id).unwrap()),)
        );
    }

    fn add_axiom(
        &mut self,
        id: GlobalId,
        local_types: Vec<LocalType>,
        local_classes: Vec<Class>,
        target: Term,
    ) {
        assert!(!self.axiom_table.contains_key(&id));
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
            id.clone(),
            Axiom {
                local_types,
                local_classes,
                target,
            },
        );

        log::info!(
            "+ {}",
            Pretty::new(&self.pp, (&id, self.axiom_table.get(&id).unwrap()),)
        );
    }

    fn add_type_const(&mut self, id: GlobalId, kind: Kind) {
        assert!(!self.type_const_table.contains_key(&id));

        self.type_const_table.insert(id.clone(), kind.clone());

        log::info!(
            "+ {}",
            Pretty::new(&self.pp, (&id, self.type_const_table.get(&id).unwrap()),)
        );
    }

    fn add_type_def(&mut self, cmd: CmdTypeDef) {
        let id = cmd.id.clone();
        assert!(!self.type_def_table.contains_key(&id));

        self.type_def_table.insert(id, cmd.clone());

        log::info!(
            "+ {}",
            Pretty::new(
                &self.pp,
                (&cmd.id, self.type_def_table.get(&cmd.id).unwrap()),
            )
        );
    }

    fn add_class_predicate(&mut self, id: GlobalId, ty: ClassType) {
        assert!(!self.class_predicate_table.contains_key(&id));

        self.class_predicate_table.insert(id.clone(), ty);

        log::info!(
            "+ {}",
            Pretty::new(
                &self.pp,
                self.class_predicate_table.get_key_value(&id).unwrap()
            )
        );
    }

    fn add_class_instance(
        &mut self,
        id: GlobalId,
        local_types: Vec<LocalType>,
        local_classes: Vec<Class>,
        target: Class,
        method_table: HashMap<GlobalId, Term>,
    ) {
        assert!(!self.class_instance_table.contains_key(&id));
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
            id.clone(),
            ClassInstance {
                local_types,
                local_classes,
                target,
                method_table,
            },
        );
    }

    fn resolve_global_class(&self, class: &Class) -> Option<tt::Instance> {
        'next_instance: for (id, instance) in &self.class_instance_table {
            let mut type_subst = Vec::with_capacity(instance.local_types.len());
            for local_type in &instance.local_types {
                type_subst.push((local_type.id, mk_fresh_type_hole()));
            }
            let target = instance.target.subst(&type_subst);
            let Some(subst) = class.matches(&target) else {
                continue;
            };
            let ty_args = type_subst
                .into_iter()
                .map(|(_, ty)| ty.inst(&subst))
                .collect::<Vec<_>>();
            let type_subst = instance
                .local_types
                .iter()
                .zip(&ty_args)
                .map(|(local_type, ty)| (local_type.id, ty.clone()))
                .collect::<Vec<_>>();
            let mut args = vec![];
            for local_class in &instance.local_classes {
                let local_class = local_class.subst(&type_subst);
                let Some(arg) = self.resolve_global_class(&local_class) else {
                    continue 'next_instance;
                };
                args.push(arg);
            }
            return Some(mk_instance_global(id.clone(), ty_args, args));
        }
        None
    }

    fn check_class_instance_coherence(
        &self,
        id: &GlobalId,
        local_types: &[LocalType],
        local_classes: &[Class],
        target: &Class,
        fields: &[ClassInstanceField],
        cmd_structure: &CmdClassStructure,
    ) -> anyhow::Result<()> {
        let same_shape = |left_types: &[LocalType],
                          left_classes: &[Class],
                          left_target: &Term,
                          right_types: &[LocalType],
                          right_classes: &[Class],
                          right_target: &Term| {
            if left_types.len() != right_types.len() || left_classes.len() != right_classes.len() {
                return false;
            }
            let type_subst = left_types
                .iter()
                .zip(right_types)
                .map(|(left, right)| (left.id, mk_type_local(right.id)))
                .collect::<Vec<_>>();
            if left_classes
                .iter()
                .map(|class| class.subst(&type_subst))
                .collect::<Vec<_>>()
                != right_classes
            {
                return false;
            }
            left_target.subst_type(&type_subst).alpha_eq(right_target)
        };
        let mut obligations: Vec<(Vec<LocalType>, Vec<Class>, Term)> = vec![];
        for instance in self.class_instance_table.values() {
            let new_holes = local_types
                .iter()
                .map(|local_type| (local_type.clone(), Id::fresh()))
                .collect::<Vec<_>>();
            let old_holes = instance
                .local_types
                .iter()
                .map(|local_type| (local_type.clone(), Id::fresh()))
                .collect::<Vec<_>>();
            let new_target = target.subst(
                &new_holes
                    .iter()
                    .map(|(local_type, hole_id)| (local_type.id, mk_type_hole(*hole_id)))
                    .collect::<Vec<_>>(),
            );
            let old_target = instance.target.subst(
                &old_holes
                    .iter()
                    .map(|(local_type, hole_id)| (local_type.id, mk_type_hole(*hole_id)))
                    .collect::<Vec<_>>(),
            );
            let Some(type_subst) = new_target.unify_with(&old_target) else {
                continue;
            };
            let norm_type = |ty: &Type| {
                ty.replace_hole(&|hole_id| {
                    type_subst
                        .iter()
                        .find(|(id, _)| *id == hole_id)
                        .map(|(_, value)| value.clone())
                })
            };
            let mut new_type_subst = new_holes
                .iter()
                .map(|(local_type, hole_id)| (local_type.id, norm_type(&mk_type_hole(*hole_id))))
                .collect::<Vec<_>>();
            let mut old_type_subst = old_holes
                .iter()
                .map(|(local_type, hole_id)| (local_type.id, norm_type(&mk_type_hole(*hole_id))))
                .collect::<Vec<_>>();
            let mut unified_target = Class {
                id: target.id.clone(),
                args: new_target.args.iter().map(norm_type).collect(),
            };
            let old_classes = instance
                .local_classes
                .iter()
                .map(|class| class.subst(&old_type_subst))
                .collect::<Vec<_>>();
            let new_classes = local_classes
                .iter()
                .map(|class| class.subst(&new_type_subst))
                .collect::<Vec<_>>();
            let uses_hole = |hole_id| {
                unified_target
                    .args
                    .iter()
                    .any(|arg| arg.contains_hole(hole_id))
                    || new_type_subst
                        .iter()
                        .any(|(_, ty)| ty.contains_hole(hole_id))
                    || old_type_subst
                        .iter()
                        .any(|(_, ty)| ty.contains_hole(hole_id))
                    || old_classes
                        .iter()
                        .any(|class| class.args.iter().any(|arg| arg.contains_hole(hole_id)))
                    || new_classes
                        .iter()
                        .any(|class| class.args.iter().any(|arg| arg.contains_hole(hole_id)))
            };
            let mut obligation_local_types = vec![];
            let mut hole_subst = vec![];
            for (local_type, hole_id) in &new_holes {
                if !uses_hole(*hole_id) {
                    continue;
                }
                let tmp = LocalType {
                    id: Id::fresh(),
                    name: local_type.name.clone(),
                };
                hole_subst.push((*hole_id, mk_type_local(tmp.id)));
                obligation_local_types.push(tmp);
            }
            for (local_type, hole_id) in &old_holes {
                if !uses_hole(*hole_id) {
                    continue;
                }
                let tmp = LocalType {
                    id: Id::fresh(),
                    name: local_type.name.clone(),
                };
                hole_subst.push((*hole_id, mk_type_local(tmp.id)));
                obligation_local_types.push(tmp);
            }
            let fill_type = |ty: &Type| {
                ty.replace_hole(&|hole_id| {
                    hole_subst
                        .iter()
                        .find(|(id, _)| *id == hole_id)
                        .map(|(_, value)| value.clone())
                })
            };
            new_type_subst = new_type_subst
                .into_iter()
                .map(|(id, ty)| (id, fill_type(&ty)))
                .collect();
            old_type_subst = old_type_subst
                .into_iter()
                .map(|(id, ty)| (id, fill_type(&ty)))
                .collect();
            unified_target = Class {
                id: unified_target.id,
                args: unified_target.args.iter().map(fill_type).collect(),
            };
            let target_type_subst = cmd_structure
                .local_types
                .iter()
                .zip(&unified_target.args)
                .map(|(local_type, arg)| (local_type.id, arg.clone()))
                .collect::<Vec<_>>();
            let old_classes = instance
                .local_classes
                .iter()
                .map(|class| class.subst(&old_type_subst))
                .collect::<Vec<_>>();
            let new_classes = local_classes
                .iter()
                .map(|class| class.subst(&new_type_subst))
                .collect::<Vec<_>>();
            let mut obligation_classes = vec![];
            let mut old_instance_subst = vec![];
            for class in &old_classes {
                let arg = if class.is_ground() {
                    self.resolve_global_class(class)
                        .unwrap_or_else(|| mk_instance_local(class.clone()))
                } else {
                    obligation_classes.push(class.clone());
                    mk_instance_local(class.clone())
                };
                old_instance_subst.push((class.clone(), arg));
            }
            let mut new_instance_subst = vec![];
            for class in &new_classes {
                let arg = if class.is_ground() {
                    self.resolve_global_class(class)
                        .unwrap_or_else(|| mk_instance_local(class.clone()))
                } else {
                    if !obligation_classes.contains(class) {
                        obligation_classes.push(class.clone());
                    }
                    mk_instance_local(class.clone())
                };
                new_instance_subst.push((class.clone(), arg));
            }
            let obligation_env = LocalEnv {
                local_types: obligation_local_types.clone(),
                local_classes: obligation_classes.clone(),
                locals: vec![],
                local_deltas: vec![],
            };
            let mut old_subst = vec![];
            let mut new_subst = vec![];
            for (structure_field, field) in zip(&cmd_structure.fields, fields) {
                let (
                    ClassStructureField::Const(ClassStructureConst {
                        field_id: structure_field_id,
                        id: method_id,
                        ..
                    }),
                    ClassInstanceField::Def(ClassInstanceDef { target, .. }),
                ) = (structure_field, field)
                else {
                    continue;
                };
                let old_term = instance
                    .method_table
                    .get(method_id)
                    .expect("existing method should exist")
                    .subst_type(&old_type_subst)
                    .subst_instance(&old_instance_subst);
                let new_term = target
                    .subst_type(&new_type_subst)
                    .subst_instance(&new_instance_subst);
                old_subst.push((*structure_field_id, old_term));
                new_subst.push((*structure_field_id, new_term));
            }
            for (structure_field, field) in zip(&cmd_structure.fields, fields) {
                match (structure_field, field) {
                    (
                        ClassStructureField::Const(ClassStructureConst {
                            field_id: structure_field_id,
                            ty,
                            ..
                        }),
                        ClassInstanceField::Def(ClassInstanceDef { .. }),
                    ) => {
                        let old_term = old_subst
                            .iter()
                            .find(|(field_id, _)| field_id == structure_field_id)
                            .map(|(_, term)| term.clone())
                            .expect("const substitution should exist");
                        let new_term = new_subst
                            .iter()
                            .find(|(field_id, _)| field_id == structure_field_id)
                            .map(|(_, term)| term.clone())
                            .expect("const substitution should exist");
                        let field_ty = ty.subst(&target_type_subst);
                        if self
                            .proof_env()
                            .tt_env
                            .equiv(&obligation_env, &old_term, &new_term)
                        {
                            continue;
                        }
                        let mut target = mk_const(global_id("eq"), vec![field_ty], vec![]);
                        target = target.apply([old_term, new_term]);
                        let obligation = (
                            obligation_local_types.clone(),
                            obligation_classes.clone(),
                            target,
                        );
                        if !obligations.iter().any(|existing| {
                            same_shape(
                                &existing.0,
                                &existing.1,
                                &existing.2,
                                &obligation.0,
                                &obligation.1,
                                &obligation.2,
                            )
                        }) {
                            obligations.push(obligation);
                        }
                    }
                    (
                        ClassStructureField::Axiom(ClassStructureAxiom { target, .. }),
                        ClassInstanceField::Lemma(_),
                    ) => {
                        let old_prop = target.subst_type(&target_type_subst).subst(&old_subst);
                        let new_prop = target.subst_type(&target_type_subst).subst(&new_subst);
                        if self
                            .proof_env()
                            .tt_env
                            .equiv(&obligation_env, &old_prop, &new_prop)
                        {
                            continue;
                        }
                        let mut target = mk_const(global_id("iff"), vec![], vec![]);
                        target = target.apply([old_prop, new_prop]);
                        let obligation = (
                            obligation_local_types.clone(),
                            obligation_classes.clone(),
                            target,
                        );
                        if !obligations.iter().any(|existing| {
                            same_shape(
                                &existing.0,
                                &existing.1,
                                &existing.2,
                                &obligation.0,
                                &obligation.1,
                                &obligation.2,
                            )
                        }) {
                            obligations.push(obligation);
                        }
                    }
                    _ => {}
                }
            }
        }
        for obligation in &obligations {
            let prefix = format!("{id}.coherence.");
            if self.coherence_proofs.iter().any(|proof| {
                proof.0.to_string().starts_with(&prefix)
                    && same_shape(
                        &proof.1,
                        &proof.2,
                        &proof.3,
                        &obligation.0,
                        &obligation.1,
                        &obligation.2,
                    )
            }) {
                continue;
            }
            bail!("missing coherence proof: {}", obligation.2);
        }
        Ok(())
    }

    fn add_delta(&mut self, id: GlobalId, target: Term) {
        assert!(!self.delta_table.contains_key(&id));

        let Const {
            local_types,
            local_classes,
            ty,
        } = self
            .const_table
            .get(&id)
            .expect("constant must be defined before delta");

        let mut local_env = LocalEnv {
            local_types: local_types.clone(),
            local_classes: local_classes.clone(),
            locals: vec![],
            local_deltas: vec![],
        };

        self.tt_env().check_type(&mut local_env, &target, ty);

        self.delta_table.insert(
            id,
            Delta {
                local_types: local_types.clone(),
                local_classes: local_classes.clone(),
                height: self.tt_env().height(&local_env, &target),
                target,
            },
        );
    }

    fn add_kappa(&mut self, id: GlobalId) {
        assert!(!self.kappa_table.contains_key(&id));

        self.kappa_table.insert(id, Kappa);
    }

    fn has_const(&self, id: &GlobalId) -> bool {
        self.const_table.contains_key(id)
    }

    fn has_axiom(&self, id: &GlobalId) -> bool {
        self.axiom_table.contains_key(id)
    }

    fn has_type_const(&self, id: &GlobalId) -> bool {
        self.type_const_table.contains_key(id)
    }

    fn has_type_def(&self, id: &GlobalId) -> bool {
        self.type_def_table.contains_key(id)
    }

    fn has_type_id(&self, id: &GlobalId) -> bool {
        self.has_type_const(id) || self.has_type_def(id)
    }

    fn has_class_predicate(&self, id: &GlobalId) -> bool {
        self.class_predicate_table.contains_key(id)
    }

    fn has_class_instance(&self, id: &GlobalId) -> bool {
        self.class_instance_table.contains_key(id)
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
        proof_local_env: &proof::LocalEnv,
        local_env: &mut LocalEnv,
        holes: Vec<(Id, Type)>,
        expr: &mut Expr,
        target: &Term,
    ) -> anyhow::Result<()> {
        elab::elaborate_expr(
            self.proof_env(),
            proof_local_env,
            local_env,
            holes,
            expr,
            target,
        )
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
                    let child = parent.clone().extend(name.clone());
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
                    bail!("unexpected block end");
                };
                self.current_namespace = previous_namespace;
                Ok(())
            }
            Cmd::Use(inner) => {
                let CmdUse { decls } = inner;
                let current_namespace = self.current_namespace.clone();
                for decl in decls {
                    let UseDecl { alias, target } = decl;
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
            Cmd::TypeInfix(inner) => {
                let CmdTypeInfix { op, prec, entity } = inner;
                let Some(arity) = self
                    .type_const_table
                    .get(&entity)
                    .map(|kind| kind.0)
                    .or_else(|| {
                        self.type_def_table
                            .get(&entity)
                            .map(|cmd| cmd.local_types.len())
                    })
                else {
                    bail!("unknown type notation target");
                };
                if arity != 2 {
                    bail!("type notation target has wrong arity");
                }
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infix,
                    prec,
                    entity,
                };
                self.tt.add_type(op.clone())?;
                self.pp.add_type(op)?;
                Ok(())
            }
            Cmd::TypeInfixr(inner) => {
                let CmdTypeInfixr { op, prec, entity } = inner;
                let Some(arity) = self
                    .type_const_table
                    .get(&entity)
                    .map(|kind| kind.0)
                    .or_else(|| {
                        self.type_def_table
                            .get(&entity)
                            .map(|cmd| cmd.local_types.len())
                    })
                else {
                    bail!("unknown type notation target");
                };
                if arity != 2 {
                    bail!("type notation target has wrong arity");
                }
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infixr,
                    prec,
                    entity,
                };
                self.tt.add_type(op.clone())?;
                self.pp.add_type(op)?;
                Ok(())
            }
            Cmd::TypeInfixl(inner) => {
                let CmdTypeInfixl { op, prec, entity } = inner;
                let Some(arity) = self
                    .type_const_table
                    .get(&entity)
                    .map(|kind| kind.0)
                    .or_else(|| {
                        self.type_def_table
                            .get(&entity)
                            .map(|cmd| cmd.local_types.len())
                    })
                else {
                    bail!("unknown type notation target");
                };
                if arity != 2 {
                    bail!("type notation target has wrong arity");
                }
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infixl,
                    prec,
                    entity,
                };
                self.tt.add_type(op.clone())?;
                self.pp.add_type(op)?;
                Ok(())
            }
            Cmd::TypePrefix(inner) => {
                let CmdTypePrefix { op, prec, entity } = inner;
                let Some(arity) = self
                    .type_const_table
                    .get(&entity)
                    .map(|kind| kind.0)
                    .or_else(|| {
                        self.type_def_table
                            .get(&entity)
                            .map(|cmd| cmd.local_types.len())
                    })
                else {
                    bail!("unknown type notation target");
                };
                if arity != 1 {
                    bail!("type notation target has wrong arity");
                }
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Prefix,
                    prec,
                    entity,
                };
                self.tt.add_type(op.clone())?;
                self.pp.add_type(op)?;
                Ok(())
            }
            Cmd::TypeNofix(inner) => {
                let CmdTypeNofix { op, entity } = inner;
                let Some(arity) = self
                    .type_const_table
                    .get(&entity)
                    .map(|kind| kind.0)
                    .or_else(|| {
                        self.type_def_table
                            .get(&entity)
                            .map(|cmd| cmd.local_types.len())
                    })
                else {
                    bail!("unknown type notation target");
                };
                if arity != 0 {
                    bail!("type notation target has wrong arity");
                }
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Nofix,
                    prec: usize::MAX,
                    entity,
                };
                self.tt.add_type(op.clone())?;
                self.pp.add_type(op)?;
                Ok(())
            }
            Cmd::Def(inner) => {
                let CmdDef {
                    id,
                    local_types,
                    local_classes,
                    ty,
                    mut target,
                } = inner;
                if self.has_const(&id) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i].id == local_types[j].id {
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
                    id.clone(),
                    local_types.clone(),
                    local_classes.clone(),
                    ty.clone(),
                );
                self.add_delta(id, target);
                Ok(())
            }
            Cmd::Axiom(inner) => {
                let CmdAxiom {
                    id,
                    local_types,
                    local_classes,
                    mut target,
                } = inner;
                if self.has_axiom(&id) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i].id == local_types[j].id {
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
                self.add_axiom(
                    id.clone(),
                    local_types.clone(),
                    local_classes.clone(),
                    target.clone(),
                );
                // TODO: Search only <class instance>.coherence.* when elaborating
                // <class instance>.
                if id.to_string().contains(".coherence.") {
                    self.coherence_proofs
                        .push((id, local_types, local_classes, target));
                }
                Ok(())
            }
            Cmd::Lemma(inner) => {
                let CmdLemma {
                    id,
                    local_types,
                    local_classes,
                    mut target,
                    holes,
                    mut expr,
                } = inner;
                if self.has_axiom(&id) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i].id == local_types[j].id {
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
                self.elaborate_expr(
                    &proof::LocalEnv::default(),
                    &mut local_env,
                    holes.clone(),
                    &mut expr,
                    &target,
                )?;
                self.proof_env().check_prop(
                    &mut local_env,
                    &mut proof::LocalEnv::default(),
                    &expr,
                    &target,
                );
                self.add_axiom(
                    id.clone(),
                    local_types.clone(),
                    local_classes.clone(),
                    target.clone(),
                );
                // TODO: Search only <class instance>.coherence.* when elaborating
                // <class instance>.
                if id.to_string().contains(".coherence.") {
                    self.coherence_proofs
                        .push((id, local_types, local_classes, target));
                }
                Ok(())
            }
            Cmd::Const(inner) => {
                let CmdConst {
                    id,
                    local_types,
                    local_classes,
                    ty,
                } = inner;
                if self.has_const(&id) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i].id == local_types[j].id {
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
                self.add_const(id, local_types, local_classes, ty);
                Ok(())
            }
            Cmd::TypeConst(inner) => {
                let CmdTypeConst { id, kind } = inner;
                if self.has_type_id(&id) {
                    bail!("already defined");
                }
                self.add_type_const(id, kind);
                Ok(())
            }
            Cmd::TypeDef(inner) => {
                let CmdTypeDef {
                    id,
                    local_types,
                    target,
                } = inner;
                if self.has_type_id(&id) {
                    bail!("already defined");
                }
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i].id == local_types[j].id {
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
                self.elaborate_type(&mut local_env, &target, Kind::base())?;
                self.add_type_def(CmdTypeDef {
                    id,
                    local_types,
                    target,
                });
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
            id,
            this,
            this_name,
            local_types,
            ind_id,
            rec_id,
            ctors,
        } = cmd;
        if self.has_type_id(&id) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i].id == local_types[j].id {
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
        local_env.local_types.insert(
            0,
            LocalType {
                id: this,
                name: Some(this_name.clone()),
            },
        );
        for i in 0..ctors.len() {
            for j in i + 1..ctors.len() {
                if ctors[i].name == ctors[j].name {
                    bail!("duplicate constructors");
                }
            }
        }
        for ctor in &ctors {
            if self.has_const(&ctor.ctor_id) {
                bail!("already defined");
            }
            if self.has_const(&ctor.ctor_spec_id) {
                bail!("already defined");
            }
            self.elaborate_type(&mut local_env, &ctor.ty, Kind::base())?;
            let (args, target) = ctor.ty.unarrow();
            if target != mk_type_local(this) {
                bail!("invalid constructor: {}", ctor.ty);
            }
            for a in args {
                let (xs, head) = a.unarrow();
                for x in &xs {
                    if x.contains_local(this) {
                        bail!("constructor violates strict positivity");
                    }
                }
                if head != mk_type_local(this) && head.contains_local(this) {
                    bail!("nested inductive type is unsupported");
                }
            }
        }
        if self.has_axiom(&ind_id) {
            bail!("already defined");
        }
        if self.has_const(&rec_id) {
            bail!("already defined");
        }
        // well-formedness check is completed.

        // generate type constructor
        self.add_type_const(id.clone(), Kind(local_types.len()));

        // generate data constructors
        let target_ty = {
            // Foo u v
            mk_type_const(id.clone()).apply(
                local_types
                    .iter()
                    .map(|local_type| mk_type_local(local_type.id)),
            )
        };
        // Foo ↦ Foo u v
        let subst = [(this, target_ty.clone())];
        let mut cs = vec![];
        for ctor in &ctors {
            let ty = ctor.ty.subst(&subst);
            cs.push((ctor.ctor_id.clone(), ty));
        }
        for (id, ty) in cs {
            self.add_const(id, local_types.clone(), vec![], ty);
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
            id: Id::fresh(),
            name: Some(Name::from_str("motive")),
            ty: mk_type_arrow(target_ty.clone(), mk_type_prop()),
        };
        let mut guards = vec![];
        for ctor in &ctors {
            let mut args = vec![];
            let (ctor_arg_tys, _) = ctor.ty.unarrow();
            for arg_ty in ctor_arg_tys {
                args.push(Local {
                    id: Id::fresh(),
                    name: None,
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
                        name: None,
                        ty: x,
                    })
                    .collect();
                if head != mk_type_local(this) {
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
            let mut a = mk_const(
                ctor.ctor_id.clone(),
                local_types
                    .iter()
                    .map(|local_type| mk_type_local(local_type.id))
                    .collect(),
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
            id: Id::fresh(),
            name: Some(Name::from_str("x")),
            ty: target_ty.clone(),
        };
        let mut target = mk_local(motive.id);
        target = target.apply([mk_local(x.id)]);
        target = guard(&target, guards);
        target = generalize(&target, &[x, motive]);
        self.add_axiom(ind_id, local_types.clone(), vec![], target);

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
        let rec_ty_var = Id::fresh();
        let mut rec_local_types = local_types.clone();
        rec_local_types.push(LocalType {
            id: rec_ty_var,
            name: Some(Name::from_str("u")),
        });
        let mut ctor_params_list = vec![];
        for ctor in &ctors {
            let mut ctor_params = vec![];
            let (ctor_param_tys, _) = ctor.ty.unarrow();
            for ctor_param_ty in ctor_param_tys {
                let ctor_param_ty = ctor_param_ty.subst(&subst);
                ctor_params.push(Local {
                    id: Id::fresh(),
                    name: None,
                    ty: ctor_param_ty,
                });
            }
            ctor_params_list.push(ctor_params);
        }
        let mut cont_params = vec![];
        for _ in &ctors {
            cont_params.push(Id::fresh());
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
                if ctor_arg_target != mk_type_local(this) {
                    continue;
                }
                let t = ctor_arg.subst(&[(this, mk_type_local(rec_ty_var))]);
                cont_arg_tys.push(t);

                let binders: Vec<_> = arg_tys
                    .into_iter()
                    .map(|arg_ty| Local {
                        id: Id::fresh(),
                        name: None,
                        ty: arg_ty,
                    })
                    .collect();
                let mut m = mk_const(
                    rec_id.clone(),
                    rec_local_types
                        .iter()
                        .map(|local_type| mk_type_local(local_type.id))
                        .collect(),
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
        self.add_const(rec_id.clone(), rec_local_types.clone(), vec![], rec_ty);

        let mut rhs_binders = vec![];
        for (x, t) in zip(cont_params, &cont_param_tys) {
            rhs_binders.push(Local {
                id: x,
                name: Some(Name::from_str("k")),
                ty: t.clone(),
            });
        }
        for ((rhs_body, ctor_params), ctor) in zip(zip(rhs_bodies, ctor_params_list), &ctors) {
            let mut lhs = mk_const(
                rec_id.clone(),
                rec_local_types
                    .iter()
                    .map(|local_type| mk_type_local(local_type.id))
                    .collect(),
                vec![],
            );
            let mut lhs_arg = mk_const(
                ctor.ctor_id.clone(),
                local_types
                    .iter()
                    .map(|local_type| mk_type_local(local_type.id))
                    .collect(),
                vec![],
            );
            lhs_arg = lhs_arg.apply(ctor_params.iter().map(|x| mk_local(x.id)));
            lhs = lhs.apply([lhs_arg]);

            let mut rhs = rhs_body;
            rhs = rhs.abs(&rhs_binders);

            let eq_ty = mk_type_local(rec_ty_var).arrow(cont_param_tys.clone());

            let mut spec = mk_const(global_id("eq"), vec![eq_ty], vec![]);
            spec = spec.apply([lhs, rhs]);
            spec = generalize(&spec, &ctor_params);

            self.add_axiom(
                ctor.ctor_spec_id.clone(),
                rec_local_types.clone(),
                vec![],
                spec,
            );
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
            id,
            this,
            this_name,
            local_types,
            params,
            target_ty,
            ind_id,
            mut ctors,
        } = cmd;
        if self.has_const(&id) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i].id == local_types[j].id {
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
                id: this,
                name: Some(this_name.clone()),
                ty: target_ty.clone(),
            },
        );
        let mut ctor_params_list = vec![];
        let mut ctor_args_list = vec![];
        let mut ctor_target_list = vec![];
        let mut ctor_ind_args_list = vec![];
        for ctor in &mut ctors {
            if self.has_axiom(&ctor.ctor_id) {
                bail!("already defined");
            }
            self.elaborate_term(&mut local_env, &mut ctor.target, &mk_type_prop())?;

            let (ctor_params, m) = ungeneralize(&ctor.target);
            ctor_params_list.push(ctor_params.clone());
            let (ctor_args, m) = unguard(&m);
            ctor_args_list.push(ctor_args.clone());
            if !m.head().alpha_eq(&mk_local(this)) {
                bail!(
                    "invalid constructor. Currently only Horn clauses are supported in inductive clauses: {m}"
                );
            }
            for a in m.args() {
                if a.contains_local(this) {
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
                if current.contains_local(this) {
                    if !current.head().alpha_eq(&mk_local(this)) {
                        bail!("invalid target");
                    }
                    for a in current.args() {
                        if a.contains_local(this) {
                            bail!("invalid target");
                        }
                    }
                    ctor_ind_args.push(ctor_arg.clone());
                }
            }
            ctor_ind_args_list.push(ctor_ind_args);
        }
        local_env.locals.remove(0);
        if self.has_axiom(&ind_id) {
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
        self.add_const(id.clone(), local_types.clone(), vec![], pred_ty);

        // inductive P.{u} (x : τ) : σ → Prop
        // | intro : ∀ y, φ → (∀ z, ψ → P M) → P N
        // ↦ axiom P.intro.{u} (x : τ) : ∀ y, φ → (∀ z, ψ → P.{u} x M) → P.{u} x N
        for ctor in &ctors {
            let mut target = ctor.target.clone();
            // P.{u} x
            let mut stash = mk_const(
                id.clone(),
                local_types
                    .iter()
                    .map(|local_type| mk_type_local(local_type.id))
                    .collect(),
                vec![],
            );
            stash = stash.apply(params.iter().map(|param| mk_local(param.id)));
            let subst = [(this, stash)];
            let new_target = target.subst(&subst);
            target = new_target;
            target = generalize(&target, &params);
            self.add_axiom(ctor.ctor_id.clone(), local_types.clone(), vec![], target);
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
                name: None,
                ty: t,
            })
            .collect::<Vec<_>>();
        let motive = Local {
            id: Id::fresh(),
            name: Some(Name::from_str("motive")),
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
            let subst_with_motive = [(this, mk_local(motive.id))];

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
                id.clone(),
                local_types
                    .iter()
                    .map(|local_type| mk_type_local(local_type.id))
                    .collect(),
                vec![],
            );
            stash = stash.apply(params.iter().map(|param| mk_local(param.id)));
            let subst = [(this, stash)];

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
            id.clone(),
            local_types
                .iter()
                .map(|local_type| mk_type_local(local_type.id))
                .collect(),
            vec![],
        );
        p = p.apply(params.iter().map(|param| mk_local(param.id)));
        p = p.apply(indexes.iter().map(|index| mk_local(index.id)));
        target = guard(&target, [p]);

        target = generalize(&target, &[motive]);
        target = generalize(&target, &indexes);
        target = generalize(&target, &params);

        self.add_axiom(ind_id, local_types, vec![], target);
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
            id,
            local_types,
            abs_id,
            mut fields,
        } = cmd;
        if self.has_type_id(&id) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i].id == local_types[j].id {
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
                    field_id,
                    field_name,
                    id: field_global_id,
                    ty: field_ty,
                }) => {
                    let field_name = field_name.clone();
                    if self.has_const(field_global_id) {
                        bail!("already defined");
                    }
                    if const_field_names.contains(&field_name) {
                        bail!("duplicate const field");
                    }
                    const_field_names.push(field_name.clone());
                    self.elaborate_type(&mut local_env, field_ty, Kind::base())?;
                    local_env.locals.push(Local {
                        id: *field_id,
                        name: Some(field_name.clone()),
                        ty: field_ty.clone(),
                    });
                }
                StructureField::Axiom(StructureAxiom {
                    id,
                    field_name,
                    target,
                }) => {
                    let field_name = field_name.clone();
                    if self.has_axiom(id) {
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
        if self.has_axiom(&abs_id) {
            bail!("already defined");
        }
        // well-formedness check is completed.
        self.structure_table.insert(
            id.clone(),
            CmdStructure {
                id: id.clone(),
                local_types: local_types.clone(),
                abs_id: abs_id.clone(),
                fields: fields.clone(),
            },
        );
        self.add_type_const(id.clone(), Kind(local_types.len()));

        // inhab u
        let this = Local {
            id: Id::fresh(),
            name: Some(Name::from_str("this")),
            ty: {
                mk_type_const(id.clone()).apply(
                    local_types
                        .iter()
                        .map(|local_type| mk_type_local(local_type.id)),
                )
            },
        };

        let mut subst = vec![];
        for field in &fields {
            match field {
                StructureField::Const(StructureConst {
                    field_id,
                    id: field_global_id,
                    ty: field_ty,
                    ..
                }) => {
                    let ty = field_ty.arrow([this.ty.clone()]);
                    self.add_const(field_global_id.clone(), local_types.clone(), vec![], ty);

                    // rep ↦ inhab.rep.{u} this
                    let mut target = mk_const(
                        field_global_id.clone(),
                        local_types
                            .iter()
                            .map(|local_type| mk_type_local(local_type.id))
                            .collect(),
                        vec![],
                    );
                    target = target.apply([mk_local(this.id)]);
                    subst.push((*field_id, target));
                }
                StructureField::Axiom(StructureAxiom { id, target, .. }) => {
                    let mut target = target.clone();
                    let new_target = target.subst(&subst);
                    target = new_target;
                    target = generalize(&target, slice::from_ref(&this));
                    self.add_axiom(id.clone(), local_types.clone(), vec![], target);
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
                    field_id,
                    field_name,
                    id: field_global_id,
                    ty: field_ty,
                }) => {
                    // (s : set u)
                    let param = Local {
                        id: Id::fresh(),
                        name: Some(field_name.clone()),
                        ty: field_ty.clone(),
                    };

                    // inhab.rep this
                    let mut rhs = mk_const(
                        field_global_id.clone(),
                        local_types
                            .iter()
                            .map(|local_type| mk_type_local(local_type.id))
                            .collect(),
                        vec![],
                    );
                    rhs = rhs.apply([mk_local(this.id)]);

                    // s = inhab.rep this
                    let mut char = mk_const(global_id("eq"), vec![field_ty.clone()], vec![]);
                    char = char.apply([mk_local(param.id), rhs]);
                    chars.push(char);

                    // rep ↦ s
                    subst.push((*field_id, mk_local(param.id)));

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
        let mut abs = mk_const(global_id("uexists"), vec![this.ty.clone()], vec![]);
        abs = abs.apply([{
            let mut char = chars
                .into_iter()
                .reduce(|left, right| {
                    let mut conj = mk_const(global_id("and"), vec![], vec![]);
                    conj = conj.apply([left, right]);
                    conj
                })
                .unwrap_or_else(|| mk_const(global_id("true"), vec![], vec![]));
            char = char.abs(slice::from_ref(&this));
            char
        }]);
        abs = guard(&abs, guards);
        abs = generalize(&abs, &params);
        self.add_axiom(abs_id, local_types.clone(), vec![], abs);
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
            id,
            local_types,
            local_classes,
            params,
            target_ty,
            mut fields,
        } = cmd;
        if self.has_const(&id) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i].id == local_types[j].id {
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
        let structure_name = structure_name.id.clone();
        let Some(cmd_structure) = self.structure_table.get(&structure_name).cloned() else {
            bail!("type of instance must be a structure");
        };
        let mut type_subst = Vec::with_capacity(cmd_structure.local_types.len());
        for (x, t) in zip(&cmd_structure.local_types, target_ty.args()) {
            type_subst.push((x.id, t.clone()));
        }
        let type_subst = type_subst;
        if cmd_structure.fields.len() != fields.len() {
            bail!("number of fields mismatch");
        }
        let mut num_consts = 0;
        let mut field_subst = vec![];
        for (structure_field, field) in zip(&cmd_structure.fields, &mut fields) {
            match (structure_field, field) {
                (
                    StructureField::Const(StructureConst {
                        field_id: structure_field_id,
                        field_name: structure_field_name,
                        ty: structure_field_ty,
                        ..
                    }),
                    InstanceField::Def(InstanceDef {
                        field_id,
                        field_name,
                        id,
                        ty,
                        ..
                    }),
                ) => {
                    let structure_field_name = structure_field_name.clone();
                    let field_name = field_name.clone();
                    if self.has_const(id) {
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
                        id: *field_id,
                        name: Some(field_name.clone()),
                        ty: ty.clone(),
                    });
                    field_subst.push((*structure_field_id, mk_local(*field_id)));
                    num_consts += 1;
                }
                (StructureField::Const(_), _) => {
                    bail!("definition expected");
                }
                (
                    StructureField::Axiom(StructureAxiom {
                        field_name: structure_field_name,
                        target: structure_field_target,
                        ..
                    }),
                    InstanceField::Lemma(InstanceLemma {
                        field_name,
                        id,
                        target,
                        ..
                    }),
                ) => {
                    let structure_field_name = structure_field_name.clone();
                    let field_name = field_name.clone();
                    if self.has_axiom(id) {
                        bail!("already defined");
                    }
                    if structure_field_name != field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
                    let mut structure_field_target = structure_field_target.clone();
                    let new_target = structure_field_target.subst_type(&type_subst);
                    structure_field_target = new_target;
                    structure_field_target = structure_field_target.subst(&field_subst);
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
        let mut proof_local_env = proof::LocalEnv::default();
        for field in &mut fields {
            match field {
                InstanceField::Def(InstanceDef {
                    field_id,
                    id,
                    ty,
                    target,
                    ..
                }) => {
                    // e.g. def power.inhab.rep.{u} (A : set u) : set (set u) := power A
                    *target = target.subst(&subst);
                    self.elaborate_term(&mut local_env, target, ty)?;

                    let target_ty = ty.arrow(params.iter().map(|param| param.ty.clone()));
                    self.add_const(
                        id.clone(),
                        local_types.clone(),
                        local_classes.clone(),
                        target_ty,
                    );
                    let target = {
                        let mut m = target.clone();
                        m = m.abs(&params);
                        m
                    };
                    self.add_delta(id.clone(), target);

                    // rep ↦ inhab.rep.{u} A
                    let mut target = mk_const(
                        id.clone(),
                        local_types
                            .iter()
                            .map(|local_type| mk_type_local(local_type.id))
                            .collect(),
                        local_classes
                            .iter()
                            .map(|c| mk_instance_local(c.clone()))
                            .collect(),
                    );
                    target = target.apply(params.iter().map(|param| mk_local(param.id)));
                    subst.push((*field_id, target));
                }
                InstanceField::Lemma(InstanceLemma {
                    field_id,
                    id,
                    target,
                    holes,
                    expr,
                    ..
                }) => {
                    // e.g. lemma power.inhab.inhabited.{u} : ∃ a, a ∈ rep := (..)
                    *target = target.subst(&subst);
                    expr.subst(&subst);
                    self.elaborate_expr(
                        &proof_local_env,
                        &mut local_env,
                        holes.clone(),
                        expr,
                        target,
                    )?;
                    self.proof_env()
                        .check_prop(&mut local_env, &mut proof_local_env, expr, target);
                    proof_local_env.local_axioms.push(proof::LocalAxiom {
                        id: Some(*field_id),
                        prop: target.clone(),
                    });

                    let mut target = target.clone();
                    target = generalize(&target, &params);
                    self.add_axiom(
                        id.clone(),
                        local_types.clone(),
                        local_classes.clone(),
                        target,
                    );
                }
            }
        }

        // e.g. const power.inhab.{u} : set u → inhab (set u)
        let mut target = target_ty.clone();
        for param in params.iter().rev() {
            target = target.arrow([param.ty.clone()]);
        }
        self.add_const(
            id.clone(),
            local_types.clone(),
            local_classes.clone(),
            target,
        );

        // generate per-field spec axioms
        let mut this = mk_const(
            id.clone(),
            local_types
                .iter()
                .map(|local_type| mk_type_local(local_type.id))
                .collect(),
            local_classes
                .iter()
                .map(|c| mk_instance_local(c.clone()))
                .collect(),
        );
        this = this.apply(params.iter().map(|param| mk_local(param.id)));
        for (structure_field, field) in zip(&cmd_structure.fields, &fields) {
            let (
                StructureField::Const(StructureConst {
                    id: structure_field_id,
                    ..
                }),
                InstanceField::Def(InstanceDef {
                    id, spec_id, ty, ..
                }),
            ) = (structure_field, field)
            else {
                continue;
            };
            if self.has_axiom(spec_id) {
                bail!("already defined");
            }

            let mut lhs = mk_const(
                structure_field_id.clone(),
                target_ty.args().into_iter().cloned().collect(),
                vec![],
            );
            lhs = lhs.apply([this.clone()]);

            let mut rhs = mk_const(
                id.clone(),
                local_types
                    .iter()
                    .map(|local_type| mk_type_local(local_type.id))
                    .collect(),
                local_classes
                    .iter()
                    .map(|c| mk_instance_local(c.clone()))
                    .collect(),
            );
            rhs = rhs.apply(params.iter().map(|param| mk_local(param.id)));

            let mut target = mk_const(global_id("eq"), vec![ty.clone()], vec![]);
            target = target.apply([lhs, rhs]);
            target = generalize(&target, &params);
            self.add_axiom(
                spec_id.clone(),
                local_types.clone(),
                local_classes.clone(),
                target,
            );
        }
        Ok(())
    }

    fn run_class_structure_cmd(&mut self, cmd: CmdClassStructure) -> anyhow::Result<()> {
        let CmdClassStructure {
            id,
            local_types,
            mut fields,
        } = cmd;
        if self.has_class_predicate(&id) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i].id == local_types[j].id {
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
                    field_id,
                    field_name,
                    id,
                    ty: field_ty,
                }) => {
                    let field_name = field_name.clone();
                    if self.has_const(id) {
                        bail!("already defined");
                    }
                    if const_field_names.contains(&field_name) {
                        bail!("duplicate const field");
                    }
                    const_field_names.push(field_name.clone());
                    self.elaborate_type(&mut local_env, field_ty, Kind::base())?;
                    local_env.locals.push(Local {
                        id: *field_id,
                        name: Some(field_name.clone()),
                        ty: field_ty.clone(),
                    });
                }
                ClassStructureField::Axiom(ClassStructureAxiom {
                    id,
                    field_name,
                    target,
                }) => {
                    let field_name = field_name.clone();
                    if self.has_axiom(id) {
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
            id.clone(),
            CmdClassStructure {
                id: id.clone(),
                local_types: local_types.clone(),
                fields: fields.clone(),
            },
        );
        self.add_class_predicate(
            id.clone(),
            ClassType {
                arity: local_types.len(),
            },
        );
        let this_class = Class {
            id: id.clone(),
            args: local_types
                .iter()
                .map(|local_type| mk_type_local(local_type.id))
                .collect(),
        };
        let this_instance = mk_instance_local(this_class.clone());
        let mut subst = vec![];
        for field in &fields {
            match field {
                ClassStructureField::Const(ClassStructureConst {
                    field_id, id, ty, ..
                }) => {
                    let method_id = id.clone();
                    self.add_const(
                        method_id.clone(),
                        local_types.clone(),
                        vec![this_class.clone()],
                        ty.clone(),
                    );
                    self.add_kappa(method_id.clone());

                    let target = mk_const(
                        method_id.clone(),
                        local_types
                            .iter()
                            .map(|local_type| mk_type_local(local_type.id))
                            .collect(),
                        vec![this_instance.clone()],
                    );
                    subst.push((*field_id, target));
                }
                ClassStructureField::Axiom(ClassStructureAxiom { id, target, .. }) => {
                    let mut target = target.clone();
                    let new_target = target.subst(&subst);
                    target = new_target;
                    self.add_axiom(
                        id.clone(),
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
            id,
            local_types,
            local_classes,
            target,
            mut fields,
        } = cmd;
        if self.has_class_instance(&id) {
            bail!("already defined");
        }
        for i in 0..local_types.len() {
            for j in i + 1..local_types.len() {
                if local_types[i].id == local_types[j].id {
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
        let cmd_structure = self.class_structure_table.get(&target.id).cloned().unwrap();
        let mut type_subst = Vec::with_capacity(cmd_structure.local_types.len());
        for (x, t) in zip(&cmd_structure.local_types, &target.args) {
            type_subst.push((x.id, t.clone()));
        }
        if cmd_structure.fields.len() != fields.len() {
            bail!("number of fields mismatch");
        }
        let mut structure_subst = vec![];
        let mut instance_subst = vec![];
        let mut proof_local_env = proof::LocalEnv::default();
        for (structure_field, field) in zip(&cmd_structure.fields, &mut fields) {
            match (structure_field, field) {
                (
                    ClassStructureField::Const(ClassStructureConst {
                        field_id: structure_field_id,
                        field_name: structure_field_name,
                        ty: structure_field_ty,
                        ..
                    }),
                    ClassInstanceField::Def(ClassInstanceDef {
                        field_id,
                        field_name,
                        ty,
                        target,
                        ..
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
                    *target = target.subst(&instance_subst);
                    self.elaborate_term(&mut local_env, target, ty)?;
                    structure_subst.push((*structure_field_id, target.clone()));
                    instance_subst.push((*field_id, target.clone()));
                }
                (ClassStructureField::Const(_), _) => {
                    bail!("definition expected");
                }
                (
                    ClassStructureField::Axiom(ClassStructureAxiom {
                        field_name: structure_field_name,
                        target: structure_field_target,
                        ..
                    }),
                    ClassInstanceField::Lemma(ClassInstanceLemma {
                        field_id,
                        field_name,
                        target,
                        holes,
                        expr,
                        ..
                    }),
                ) => {
                    let structure_field_name = structure_field_name.clone();
                    let field_name = field_name.clone();
                    if structure_field_name != field_name {
                        bail!("field name mismatch");
                    }
                    self.elaborate_term(&mut local_env, target, &mk_type_prop())?;
                    let mut structure_field_target = structure_field_target.clone();
                    structure_field_target = structure_field_target.subst_type(&type_subst);
                    structure_field_target = structure_field_target.subst(&structure_subst);
                    if !structure_field_target.alpha_eq(target) {
                        bail!("target mismatch");
                    }
                    self.elaborate_expr(
                        &proof_local_env,
                        &mut local_env,
                        holes.clone(),
                        expr,
                        target,
                    )?;
                    self.proof_env()
                        .check_prop(&mut local_env, &mut proof_local_env, expr, target);
                    proof_local_env.local_axioms.push(proof::LocalAxiom {
                        id: Some(*field_id),
                        prop: target.clone(),
                    });
                }
                (ClassStructureField::Axiom(_), _) => {
                    bail!("lemma expected");
                }
            }
        }
        // well-formedness check is completed.
        let mut method_table = HashMap::new();
        for (structure_field, field) in zip(&cmd_structure.fields, &fields) {
            let (
                ClassStructureField::Const(ClassStructureConst { id, .. }),
                ClassInstanceField::Def(ClassInstanceDef { target, .. }),
            ) = (structure_field, field)
            else {
                continue;
            };
            method_table.insert(id.clone(), target.clone());
        }
        self.check_class_instance_coherence(
            &id,
            &local_types,
            &local_classes,
            &target,
            &fields,
            &cmd_structure,
        )?;
        self.add_class_instance(id.clone(), local_types, local_classes, target, method_table);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Cmd, CmdAxiom, CmdInductive, CmdInstance, CmdLemma, CmdNamespaceStart, CmdStructure,
        CmdTypeConst, CmdTypeInductive, CmdUse, Eval, InductiveConstructor, InstanceDef,
        InstanceField, Namespace, Path, StructureConst, StructureField, TypeInductiveConstructor,
        UseDecl,
    };
    use crate::{
        proof::mk_type_prop,
        tt::{
            GlobalId, Id, Kind, LocalType, Name, mk_const, mk_local, mk_type_arrow, mk_type_const,
            mk_type_local,
        },
    };

    fn path(value: &str) -> Path {
        let mut path = Path::root();
        if value.is_empty() {
            return path;
        }
        for part in value.split('.') {
            path = path.extend(Name::from_str(part));
        }
        path
    }

    fn global_id(value: &str) -> GlobalId {
        GlobalId::from_name(Name::from_str(value))
    }

    fn install_minimal_logic(eval: &mut Eval) {
        eval.add_type_const(global_id("Prop"), Kind(0));
        eval.add_const(
            global_id("imp"),
            vec![],
            vec![],
            mk_type_arrow(
                mk_type_prop(),
                mk_type_arrow(mk_type_prop(), mk_type_prop()),
            ),
        );
        for name in ["forall", "uexists", "eq"] {
            let u = Id::fresh();
            let local_types = vec![LocalType {
                id: u,
                name: Some(Name::from_str("u")),
            }];
            let ty = match name {
                "forall" | "uexists" => mk_type_arrow(
                    mk_type_arrow(mk_type_local(u), mk_type_prop()),
                    mk_type_prop(),
                ),
                "eq" => mk_type_arrow(
                    mk_type_local(u),
                    mk_type_arrow(mk_type_local(u), mk_type_prop()),
                ),
                _ => unreachable!("unexpected minimal logic constant"),
            };
            eval.add_const(global_id(name), local_types, vec![], ty);
        }
        eval.add_const(
            global_id("and"),
            vec![],
            vec![],
            mk_type_arrow(
                mk_type_prop(),
                mk_type_arrow(mk_type_prop(), mk_type_prop()),
            ),
        );
        eval.add_const(global_id("true"), vec![], vec![], mk_type_prop());
    }

    #[test]
    fn path_extend_appends_segment() {
        let actual = Path::root()
            .extend(Name::from_str("foo"))
            .extend(Name::from_str("bar"));

        assert_eq!(actual, path("foo.bar"));
        assert_eq!(
            actual.names(),
            &[Name::from_str("foo"), Name::from_str("bar")]
        );
    }

    #[test]
    fn path_to_global_id_uses_dotted_name() {
        assert_eq!(path("foo.bar").to_global_id(), global_id("foo.bar"));
    }

    #[test]
    fn namespace_add_stores_path_target() {
        let mut namespace = Namespace::default();
        let alias = Name::from_str("alias");
        let target = path("foo");
        namespace.add(alias.clone(), target.clone());
        assert_eq!(namespace.use_table.get(&alias), Some(&target));
    }

    #[test]
    fn use_decl_stores_path_target() {
        let alias = Name::from_str("alias");
        let target = path("foo");
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
        let path = path("foo");
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
        let path = path("foo");
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
        let foo_path = path("foo");
        eval.namespace_table
            .insert(foo_path.clone(), Namespace::default());
        eval.namespace_table
            .get_mut(&Path::root())
            .expect("root namespace must exist")
            .add(Name::from_str("foo"), path("foo"));

        eval.run_cmd(Cmd::TypeConst(CmdTypeConst {
            id: global_id("foo.bar"),
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
            id: global_id("foo.bar.baz"),
            kind: Kind(0),
        }))
        .expect("type const command should succeed");

        assert!(!eval.namespace_table.contains_key(&path("foo")));
        assert!(!eval.namespace_table.contains_key(&path("foo.bar")));
        assert!(!eval.namespace_table.contains_key(&path("foo.bar.baz")));
    }

    #[test]
    fn use_command_installs_resolved_relative_target_verbatim() {
        let mut eval = Eval::default();
        let current_namespace = path("foo");
        eval.namespace_table
            .insert(current_namespace.clone(), Namespace::default());
        eval.current_namespace = current_namespace.clone();

        eval.run_cmd(Cmd::Use(CmdUse {
            decls: vec![UseDecl {
                alias: Name::from_str("baz"),
                target: path("real.qux"),
            }],
        }))
        .expect("use command should succeed");

        assert_eq!(
            eval.namespace_table[&current_namespace]
                .use_table
                .get(&Name::from_str("baz")),
            Some(&path("real.qux"))
        );
    }

    #[test]
    fn use_command_installs_resolved_absolute_target_verbatim() {
        let mut eval = Eval::default();
        let current_namespace = path("foo");
        eval.namespace_table
            .insert(current_namespace.clone(), Namespace::default());
        eval.current_namespace = current_namespace.clone();

        eval.run_cmd(Cmd::Use(CmdUse {
            decls: vec![UseDecl {
                alias: Name::from_str("baz"),
                target: path("global"),
            }],
        }))
        .expect("use command should succeed");

        assert_eq!(
            eval.namespace_table[&current_namespace]
                .use_table
                .get(&Name::from_str("baz")),
            Some(&path("global"))
        );
    }

    #[test]
    fn use_command_does_not_rewrite_targets_using_prior_decls() {
        let mut eval = Eval::default();
        let root_namespace = Path::root();

        eval.run_cmd(Cmd::Use(CmdUse {
            decls: vec![
                UseDecl {
                    alias: Name::from_str("fuga"),
                    target: path("real"),
                },
                UseDecl {
                    alias: Name::from_str("piyo"),
                    target: path("fuga"),
                },
            ],
        }))
        .expect("use command should succeed");

        assert_eq!(
            eval.namespace_table[&root_namespace]
                .use_table
                .get(&Name::from_str("fuga")),
            Some(&path("real"))
        );
        assert_eq!(
            eval.namespace_table[&root_namespace]
                .use_table
                .get(&Name::from_str("piyo")),
            Some(&path("fuga"))
        );
    }

    #[test]
    fn type_inductive_command_uses_parser_generated_derived_names() {
        let mut eval = Eval::default();
        install_minimal_logic(&mut eval);

        let this = Id::fresh();
        let ctor_id = global_id("meta.ctor");
        let ctor_spec_id = global_id("meta.ctor_rule");
        let ind_id = global_id("meta.type_ind");
        let rec_id = global_id("meta.type_rec");

        eval.run_cmd(Cmd::TypeInductive(CmdTypeInductive {
            id: global_id("foo"),
            this,
            this_name: Name::from_str("foo"),
            local_types: vec![],
            ind_id: ind_id.clone(),
            rec_id: rec_id.clone(),
            ctors: vec![TypeInductiveConstructor {
                ctor_id: ctor_id.clone(),
                name: Name::from_str("mk"),
                ctor_spec_id: ctor_spec_id.clone(),
                ty: mk_type_local(this),
            }],
        }))
        .expect("type inductive command should succeed");

        assert!(eval.const_table.contains_key(&global_id("meta.ctor")));
        assert!(eval.const_table.contains_key(&global_id("meta.type_rec")));
        assert!(eval.axiom_table.contains_key(&global_id("meta.ctor_rule")));
        assert!(eval.axiom_table.contains_key(&global_id("meta.type_ind")));
        assert!(!eval.const_table.contains_key(&global_id("foo.mk")));
        assert!(!eval.const_table.contains_key(&global_id("foo.rec")));
        assert!(!eval.axiom_table.contains_key(&global_id("foo.mk.spec")));
        assert!(!eval.axiom_table.contains_key(&global_id("foo.ind")));
    }

    #[test]
    fn inductive_command_uses_parser_generated_derived_names() {
        let mut eval = Eval::default();
        install_minimal_logic(&mut eval);

        let this = Id::fresh();
        let ctor_id = global_id("meta.intro");
        let ind_id = global_id("meta.prop_ind");

        eval.run_cmd(Cmd::Inductive(CmdInductive {
            id: global_id("foo"),
            this,
            this_name: Name::from_str("foo"),
            local_types: vec![],
            params: vec![],
            target_ty: mk_type_prop(),
            ind_id: ind_id.clone(),
            ctors: vec![InductiveConstructor {
                ctor_id: ctor_id.clone(),
                name: Name::from_str("mk"),
                target: mk_local(this),
            }],
        }))
        .expect("inductive command should succeed");

        assert!(eval.const_table.contains_key(&global_id("foo")));
        assert!(eval.axiom_table.contains_key(&global_id("meta.intro")));
        assert!(eval.axiom_table.contains_key(&global_id("meta.prop_ind")));
        assert!(!eval.axiom_table.contains_key(&global_id("foo.mk")));
        assert!(!eval.axiom_table.contains_key(&global_id("foo.ind")));
    }

    #[test]
    fn structure_command_uses_parser_generated_abs_name() {
        let mut eval = Eval::default();
        install_minimal_logic(&mut eval);

        let abs_id = global_id("meta.struct_abs");

        eval.run_cmd(Cmd::Structure(CmdStructure {
            id: global_id("foo"),
            local_types: vec![],
            abs_id: abs_id.clone(),
            fields: vec![StructureField::Const(StructureConst {
                field_id: Id::fresh(),
                field_name: Name::from_str("rep"),
                id: global_id("foo.rep"),
                ty: mk_type_prop(),
            })],
        }))
        .expect("structure command should succeed");

        assert!(eval.axiom_table.contains_key(&global_id("meta.struct_abs")));
        assert!(!eval.axiom_table.contains_key(&global_id("foo.abs")));
    }

    #[test]
    fn instance_command_uses_parser_generated_spec_name() {
        let mut eval = Eval::default();
        install_minimal_logic(&mut eval);

        let rep_field_id = Id::fresh();
        eval.add_type_const(global_id("foo"), Kind(0));
        eval.add_const(
            global_id("foo.rep"),
            vec![],
            vec![],
            mk_type_arrow(mk_type_const(global_id("foo")), mk_type_prop()),
        );
        eval.structure_table.insert(
            global_id("foo"),
            CmdStructure {
                id: global_id("foo"),
                local_types: vec![],
                abs_id: global_id("meta.foo_abs"),
                fields: vec![StructureField::Const(StructureConst {
                    field_id: rep_field_id,
                    field_name: Name::from_str("rep"),
                    id: global_id("foo.rep"),
                    ty: mk_type_prop(),
                })],
            },
        );

        let spec_id = global_id("meta.inst_rep_rule");
        eval.run_cmd(Cmd::Instance(CmdInstance {
            id: global_id("inst"),
            local_types: vec![],
            local_classes: vec![],
            params: vec![],
            target_ty: mk_type_const(global_id("foo")),
            fields: vec![InstanceField::Def(InstanceDef {
                field_id: Id::fresh(),
                field_name: Name::from_str("rep"),
                id: global_id("inst.rep"),
                spec_id: spec_id.clone(),
                ty: mk_type_prop(),
                target: mk_const(global_id("true"), vec![], vec![]),
            })],
        }))
        .expect("instance command should succeed");

        assert!(
            eval.axiom_table
                .contains_key(&global_id("meta.inst_rep_rule"))
        );
        assert!(!eval.axiom_table.contains_key(&global_id("inst.rep.spec")));
    }

    #[test]
    fn only_coherence_named_axiom_and_lemma_are_recorded_as_coherence_proofs() {
        let mut eval = Eval::default();
        install_minimal_logic(&mut eval);
        eval.add_type_const(global_id("foo"), Kind(0));

        eval.run_cmd(Cmd::Axiom(CmdAxiom {
            id: global_id("foo.ax"),
            local_types: vec![],
            local_classes: vec![],
            target: mk_const(global_id("true"), vec![], vec![]),
        }))
        .expect("axiom command should succeed");
        eval.run_cmd(Cmd::Lemma(CmdLemma {
            id: global_id("foo.lm"),
            local_types: vec![],
            local_classes: vec![],
            target: mk_const(global_id("true"), vec![], vec![]),
            holes: vec![],
            expr: crate::proof::mk_expr_const(global_id("foo.ax"), vec![], vec![]),
        }))
        .expect("lemma command should succeed");
        eval.run_cmd(Cmd::Axiom(CmdAxiom {
            id: global_id("foo.inst.coherence.ax"),
            local_types: vec![],
            local_classes: vec![],
            target: mk_const(global_id("true"), vec![], vec![]),
        }))
        .expect("axiom command should succeed");
        eval.run_cmd(Cmd::Lemma(CmdLemma {
            id: global_id("foo.inst.coherence.lm"),
            local_types: vec![],
            local_classes: vec![],
            target: mk_const(global_id("true"), vec![], vec![]),
            holes: vec![],
            expr: crate::proof::mk_expr_const(global_id("foo.inst.coherence.ax"), vec![], vec![]),
        }))
        .expect("lemma command should succeed");

        assert_eq!(eval.coherence_proofs.len(), 2);
        assert_eq!(
            eval.coherence_proofs[0].0,
            global_id("foo.inst.coherence.ax")
        );
        assert_eq!(
            eval.coherence_proofs[1].0,
            global_id("foo.inst.coherence.lm")
        );
    }

    #[test]
    fn generated_axioms_are_not_recorded_as_coherence_proofs() {
        let mut eval = Eval::default();
        install_minimal_logic(&mut eval);

        let abs_id = global_id("meta.struct_abs");
        eval.run_cmd(Cmd::Structure(CmdStructure {
            id: global_id("foo"),
            local_types: vec![],
            abs_id: abs_id.clone(),
            fields: vec![StructureField::Const(StructureConst {
                field_id: Id::fresh(),
                field_name: Name::from_str("rep"),
                id: global_id("foo.rep"),
                ty: mk_type_prop(),
            })],
        }))
        .expect("structure command should succeed");

        assert!(eval.coherence_proofs.is_empty());
    }
}
