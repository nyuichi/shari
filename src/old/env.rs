use crate::kernel::{
    proof::mk_type_prop,
    tt::{mk_type_arrow, mk_type_local, Kind, Name, Term, Type},
};
use crate::print::{Fixity, OpTable, Operator, TokenTable};

use anyhow::bail;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::sync::RwLock;

#[derive(Debug, Default, Clone)]
pub struct Env {
    decls: Vec<(Name, Decl)>,
    type_decls: HashMap<Name, usize>,
    term_decls: HashMap<Name, usize>,
    prop_decls: HashMap<Name, usize>,
    notations: NotationTable,
}

#[derive(Debug, Clone)]
pub enum Decl {
    Const(DeclConst),
    Def(DeclDef),
    TypeConst(DeclTypeConst),
    Axiom(DeclAxiom),
    Lemma(DeclLemma),
}

#[derive(Debug, Clone)]
pub struct DeclConst {
    pub local_types: Vec<Name>,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct DeclDef {
    pub local_types: Vec<Name>,
    pub ty: Type,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct DeclTypeConst {
    pub kind: Kind,
}

#[derive(Debug, Clone)]
pub struct DeclAxiom {
    pub local_types: Vec<Name>,
    pub axiom: Fact,
}

#[derive(Debug, Clone)]
pub struct DeclLemma {
    pub local_types: Vec<Name>,
    pub fact: Fact,
}

#[derive(Debug, Clone)]
pub struct DeclType {
    pub local_types: Vec<Name>,
    pub char: Term,
}

#[derive(Debug, Clone)]
pub struct DeclDesc {
    pub local_types: Vec<Name>,
    pub ty: Type,
    // TODO: or maybe the name of a fact?
    pub spec: Fact,
}

#[derive(Debug, Default, Clone)]
struct NotationTable {
    // symbol to name
    tt: TokenTable,
    // name to symbol
    pp: OpTable,
}

#[derive(Debug, Clone)]
pub enum TermDecl {
    Const(DeclConst),
    Def(DeclDef),
}

#[derive(Debug, Clone)]
pub enum TypeDecl {
    Const(DeclTypeConst),
}

#[derive(Debug, Clone)]
pub enum ProofDecl {
    Axiom(DeclAxiom),
    Lemma(DeclLemma),
}

impl From<TermDecl> for Decl {
    fn from(value: TermDecl) -> Self {
        match value {
            TermDecl::Const(d) => Decl::Const(d),
            TermDecl::Def(d) => Decl::Def(d),
        }
    }
}

impl From<TypeDecl> for Decl {
    fn from(value: TypeDecl) -> Self {
        match value {
            TypeDecl::Const(d) => Decl::TypeConst(d),
        }
    }
}

impl From<ProofDecl> for Decl {
    fn from(value: ProofDecl) -> Self {
        match value {
            ProofDecl::Axiom(d) => Decl::Axiom(d),
            ProofDecl::Lemma(d) => Decl::Lemma(d),
        }
    }
}

impl TryFrom<Decl> for TermDecl {
    type Error = ();

    fn try_from(value: Decl) -> Result<Self, Self::Error> {
        match value {
            Decl::Const(d) => Ok(TermDecl::Const(d)),
            Decl::Def(d) => Ok(TermDecl::Def(d)),
            Decl::TypeConst(_) => Err(()),
            Decl::Axiom(_) => Err(()),
            Decl::Lemma(_) => Err(()),
        }
    }
}

impl TryFrom<Decl> for TypeDecl {
    type Error = ();

    fn try_from(value: Decl) -> Result<Self, Self::Error> {
        match value {
            Decl::Const(_) => Err(()),
            Decl::Def(_) => Err(()),
            Decl::TypeConst(d) => Ok(TypeDecl::Const(d)),
            Decl::Axiom(_) => Err(()),
            Decl::Lemma(_) => Err(()),
        }
    }
}

impl TryFrom<Decl> for ProofDecl {
    type Error = ();

    fn try_from(value: Decl) -> Result<Self, Self::Error> {
        match value {
            Decl::Const(_) => Err(()),
            Decl::Def(_) => Err(()),
            Decl::TypeConst(_) => Err(()),
            Decl::Axiom(d) => Ok(ProofDecl::Axiom(d)),
            Decl::Lemma(d) => Ok(ProofDecl::Lemma(d)),
        }
    }
}

static ENV: Lazy<RwLock<Env>> = Lazy::new(|| RwLock::new(Env::new_kernel()));

impl Env {
    pub(crate) fn new_kernel() -> Env {
        let mut env = Env::default();

        env.add_type_decl(
            "Prop".try_into().unwrap(),
            TypeDecl::Const(DeclTypeConst { kind: Kind::base() }),
        )
        .unwrap();

        env.add_term_decl(
            "imp".try_into().unwrap(),
            TermDecl::Const(DeclConst {
                local_types: vec![],
                ty: mk_type_arrow(
                    mk_type_prop(),
                    mk_type_arrow(mk_type_prop(), mk_type_prop()),
                ),
            }),
        )
        .unwrap();

        env.add_term_decl(
            "forall".try_into().unwrap(),
            TermDecl::Const(DeclConst {
                local_types: vec!["u".try_into().unwrap()],
                ty: mk_type_arrow(
                    mk_type_arrow(mk_type_local("u".try_into().unwrap()), mk_type_prop()),
                    mk_type_prop(),
                ),
            }),
        )
        .unwrap();

        env.add_term_decl(
            "eq".try_into().unwrap(),
            TermDecl::Const(DeclConst {
                local_types: vec!["u".try_into().unwrap()],
                ty: mk_type_arrow(
                    mk_type_local("u".try_into().unwrap()),
                    mk_type_arrow(mk_type_local("u".try_into().unwrap()), mk_type_prop()),
                ),
            }),
        )
        .unwrap();

        env.add_notation(Operator {
            symbol: "→".to_owned(),
            fixity: Fixity::Infixr,
            prec: 25,
            entity: "imp".try_into().unwrap(),
        })
        .unwrap();
        env.add_notation(Operator {
            symbol: "=".to_owned(),
            fixity: Fixity::Infix,
            prec: 50,
            entity: "eq".try_into().unwrap(),
        })
        .unwrap();

        env
    }

    pub(crate) fn get() -> std::sync::RwLockReadGuard<'static, Env> {
        ENV.try_read().unwrap()
    }

    pub(crate) fn get_mut() -> std::sync::RwLockWriteGuard<'static, Env> {
        ENV.try_write().unwrap()
    }

    pub(crate) fn token_table(&self) -> &TokenTable {
        &self.notations.tt
    }

    pub(crate) fn op_table(&self) -> &OpTable {
        &self.notations.pp
    }

    fn add_type_decl(&mut self, name: Name, decl: TypeDecl) -> anyhow::Result<()> {
        let index = self.decls.len();
        if self.type_decls.insert(name, index).is_some() {
            bail!("type declaration with given name already defined");
        }
        self.decls.push((name, decl.into()));
        Ok(())
    }

    pub(crate) fn add_term_decl(&mut self, name: Name, decl: TermDecl) -> anyhow::Result<()> {
        let index = self.decls.len();
        if self.term_decls.insert(name, index).is_some() {
            bail!("declaration with given name already defined");
        }
        self.decls.push((name, decl.into()));
        Ok(())
    }

    fn add_prop_decl(&mut self, name: Name, decl: ProofDecl) -> anyhow::Result<()> {
        let index = self.decls.len();
        if self.prop_decls.insert(name, index).is_some() {
            bail!("proposition declaration with given name already defined");
        }
        self.decls.push((name, decl.into()));
        Ok(())
    }

    fn get_type_decl(&self, name: Name) -> Option<TypeDecl> {
        let &index = self.type_decls.get(&name)?;
        Some(self.decls[index].1.clone().try_into().unwrap())
    }

    fn get_term_decl(&self, name: Name) -> Option<TermDecl> {
        let &index = self.term_decls.get(&name)?;
        Some(self.decls[index].1.clone().try_into().unwrap())
    }

    fn get_term_decl_index(&self, name: Name) -> Option<(usize, TermDecl)> {
        let &index = self.term_decls.get(&name)?;
        Some((index, self.decls[index].1.clone().try_into().unwrap()))
    }

    fn get_prop_decl(&self, name: Name) -> Option<ProofDecl> {
        let &index = self.prop_decls.get(&name)?;
        Some(self.decls[index].1.clone().try_into().unwrap())
    }

    pub(crate) fn add_notation(&mut self, op: Operator) -> anyhow::Result<()> {
        self.notations.tt.add(op.clone())?;
        self.notations.pp.add(op)?;
        Ok(())
    }

    pub(crate) fn get_kind(&self, name: Name) -> Option<Kind> {
        let decl = self.get_type_decl(name)?;
        match decl {
            TypeDecl::Const(DeclTypeConst { kind }) => Some(kind),
        }
    }

    pub(crate) fn get_type(&self, name: Name) -> Option<(Vec<Name>, Type)> {
        let decl = self.get_term_decl(name)?;
        match decl {
            TermDecl::Const(DeclConst { local_types, ty }) => Some((local_types, ty)),
            TermDecl::Def(DeclDef {
                local_types,
                target: _,
                ty,
            }) => Some((local_types, ty)),
        }
    }
}

pub fn add_notation(symbol: &str, fixity: Fixity, prec: usize, entity: &str) -> anyhow::Result<()> {
    let Ok(entity) = Name::try_from(entity) else {
        bail!("invalid name: {entity}");
    };
    Env::get_mut().add_notation(Operator {
        symbol: symbol.to_owned(),
        fixity,
        prec,
        entity,
    })
}

pub fn add_const(name: Name, local_types: Vec<Name>, ty: Type) -> anyhow::Result<()> {
    for i in 0..local_types.len() {
        for j in i + 1..local_types.len() {
            if local_types[i] == local_types[j] {
                bail!("duplicate type variables");
            }
        }
    }
    ty.check(&Kind::base())?;
    if !ty.is_generic(local_types.as_slice()) {
        bail!("unbound local type");
    }
    if !ty.is_ground() {
        bail!("type not fully instantiated");
    }
    Env::get_mut().add_term_decl(name, TermDecl::Const(DeclConst { local_types, ty }))
}

pub fn add_const_type(name: Name, kind: Kind) -> anyhow::Result<()> {
    Env::get_mut().add_type_decl(name, TypeDecl::Const(DeclTypeConst { kind }))
}

pub fn add_axiom(name: Name, local_types: Vec<Name>, p: Term) -> anyhow::Result<()> {
    let axiom = axiom(p)?;
    if !axiom.target().is_generic(local_types.as_slice()) {
        bail!("unbound local type");
    }
    Env::get_mut().add_prop_decl(name, ProofDecl::Axiom(DeclAxiom { local_types, axiom }))
}

pub fn add_lemma(name: Name, local_types: Vec<Name>, fact: Fact) -> anyhow::Result<()> {
    if !fact.context().is_empty() {
        bail!("local context is not empty:\n\n{fact}");
    }
    if !fact.target().is_closed() {
        bail!("formula not closed:\n\n{fact}");
    }
    Env::get_mut().add_prop_decl(name, ProofDecl::Lemma(DeclLemma { local_types, fact }))
}

pub fn add_definition(name: Name, local_types: Vec<Name>, mut target: Term) -> anyhow::Result<()> {
    for i in 0..local_types.len() {
        for j in i + 1..local_types.len() {
            if local_types[i] == local_types[j] {
                bail!("duplicate type variables");
            }
        }
    }
    let ty = target.infer()?;
    if !target.is_generic(local_types.as_slice()) {
        bail!("unbound local type");
    }
    if !target.is_closed() {
        bail!("term not closed");
    }
    Env::get_mut().add_term_decl(
        name,
        TermDecl::Def(DeclDef {
            local_types,
            target,
            ty,
        }),
    )
}

pub fn get_kind(name: Name) -> Option<Kind> {
    Env::get().get_kind(name)
}

pub fn get_type(name: Name) -> Option<(Vec<Name>, Type)> {
    Env::get().get_type(name)
}

pub fn get_def(name: Name) -> Option<DeclDef> {
    let decl = Env::get().get_term_decl(name)?;
    match decl {
        TermDecl::Const(_) => None,
        TermDecl::Def(decl_def) => Some(decl_def),
    }
}

// TODO remove
pub fn get_def_hint(name: Name) -> Option<usize> {
    let (index, decl) = Env::get().get_term_decl_index(name)?;
    match decl {
        TermDecl::Const(_) => None,
        TermDecl::Def(_) => Some(index),
    }
}

pub fn get_prop(name: Name) -> Option<(Vec<Name>, Fact)> {
    let decl = Env::get().get_prop_decl(name)?;
    match decl {
        ProofDecl::Axiom(DeclAxiom { local_types, axiom }) => Some((local_types, axiom)),
        ProofDecl::Lemma(DeclLemma { local_types, fact }) => Some((local_types, fact)),
    }
}

pub fn get_decls() -> Vec<(Name, Decl)> {
    Env::get().decls.clone()
}
