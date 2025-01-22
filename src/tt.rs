//! [Type] and [Term] may be ill-formed.

use regex::Regex;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::iter::zip;
use std::sync::atomic::AtomicUsize;
use std::sync::LazyLock;
use std::sync::{Arc, Mutex};
use std::{mem, slice, vec};
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Name(pub usize);

static NAME_COUNTER: AtomicUsize = AtomicUsize::new(0);
static NAME_TABLE: LazyLock<Mutex<HashMap<String, Name>>> = LazyLock::new(Default::default);
static NAME_REV_TABLE: LazyLock<Mutex<HashMap<Name, String>>> = LazyLock::new(Default::default);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Some(nickname) = self.nickname() else {
            return write!(f, "{}", self.0);
        };
        if Name::intern(&nickname).unwrap() == *self {
            write!(f, "{}", nickname)
        } else {
            write!(f, "{}{}", nickname, self.0)
        }
    }
}

#[derive(Error, Debug, Clone)]
#[error("invalid name")]
pub struct InvalidNameError;

impl TryFrom<&str> for Name {
    type Error = InvalidNameError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Name::intern(value)
    }
}

impl Name {
    pub fn fresh() -> Self {
        let id = NAME_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Name(id)
    }

    pub fn fresh_from(name: Name) -> Self {
        let value = NAME_REV_TABLE.lock().unwrap().get(&name).cloned();
        let new_name = Name::fresh();
        if let Some(value) = value {
            NAME_REV_TABLE.lock().unwrap().insert(new_name, value);
        }
        new_name
    }

    pub fn fresh_with_name(name: &str) -> Self {
        let value = name.to_owned();
        let new_name = Name::fresh();
        NAME_REV_TABLE.lock().unwrap().insert(new_name, value);
        new_name
    }

    pub fn intern(value: &str) -> Result<Name, InvalidNameError> {
        static RE: LazyLock<Regex> = LazyLock::new(|| {
            regex::Regex::new(r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*(\.[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*)*").unwrap()
        });
        if !RE.is_match(value) {
            return Err(InvalidNameError);
        }
        let mut name_table = NAME_TABLE.lock().unwrap();
        if let Some(&name) = name_table.get(value) {
            return Ok(name);
        }
        let name = Name::fresh();
        name_table.insert(value.to_owned(), name);
        drop(name_table);
        // This can be put here outside the critical section of NAME_TABLE
        // because no one but this function knows of the value of `name`.
        NAME_REV_TABLE
            .lock()
            .unwrap()
            .insert(name, value.to_owned());
        Ok(name)
    }

    fn nickname(&self) -> Option<String> {
        NAME_REV_TABLE.lock().unwrap().get(self).cloned()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Kind(pub usize);

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut arity = self.0;
        while arity > 0 {
            write!(f, "Type → ")?;
            arity -= 1;
        }
        write!(f, "Type")
    }
}

impl Kind {
    pub const fn base() -> Self {
        Kind(0)
    }

    pub fn is_base(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Type {
    Const(Name),
    Arrow(Arc<TypeArrow>),
    App(Arc<TypeApp>),
    Local(Name),
    Hole(Name),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeArrow {
    pub dom: Type,
    pub cod: Type,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeApp {
    pub fun: Type,
    pub arg: Type,
}

impl Default for Type {
    fn default() -> Self {
        Type::Hole(Default::default())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Const(inner) => {
                write!(f, "{inner}")
            }
            Type::Arrow(inner) => {
                write!(f, "({} → {})", inner.dom, inner.cod)
            }
            Type::App(inner) => {
                write!(f, "({} {})", inner.fun, inner.arg)
            }
            Type::Local(inner) => {
                write!(f, "(local {inner})")
            }
            Type::Hole(inner) => {
                write!(f, "?{inner}")
            }
        }
    }
}

pub fn mk_type_arrow(dom: Type, mut cod: Type) -> Type {
    cod.arrow([dom]);
    cod
}

pub fn mk_fresh_type_hole() -> Type {
    Type::Hole(Name::fresh_with_name("α"))
}

pub fn mk_type_local(name: Name) -> Type {
    Type::Local(name)
}

pub fn mk_type_const(name: Name) -> Type {
    Type::Const(name)
}

pub fn mk_type_prop() -> Type {
    static T_PROP: LazyLock<Type> = LazyLock::new(|| mk_type_const(Name::intern("Prop").unwrap()));
    T_PROP.clone()
}

/// See [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    /// t.arrow([t1, t2]);
    /// assert_eq!(t, "t1 → t2 → t");
    pub fn arrow(&mut self, cs: impl IntoIterator<Item = Type>) {
        let mut iter = cs.into_iter();
        if let Some(item) = iter.next() {
            self.arrow(iter);
            *self = Type::Arrow(Arc::new(TypeArrow {
                dom: item,
                cod: mem::take(self),
            }));
        }
    }

    /// assert_eq!(t, "t1 → t2 → t");
    /// assert_eq!(t.unarrow(), [t1, t2]);
    pub fn unarrow(&mut self) -> Vec<Type> {
        let mut ts = vec![];
        let mut t = &mut *self;
        while let Type::Arrow(inner) = t {
            let TypeArrow { dom, cod } = Arc::make_mut(inner);
            ts.push(mem::take(dom));
            t = cod;
        }
        *self = mem::take(t);
        ts
    }

    pub fn components(&self) -> Vec<&Type> {
        let mut cs = vec![];
        let mut t = self;
        while let Type::Arrow(inner) = t {
            cs.push(&inner.dom);
            t = &inner.cod;
        }
        cs
    }

    pub fn apply(&mut self, args: impl IntoIterator<Item = Type>) {
        for arg in args {
            *self = Type::App(Arc::new(TypeApp {
                fun: mem::take(self),
                arg,
            }));
        }
    }

    pub fn unapply(&mut self) -> Vec<Type> {
        let mut acc = vec![];
        let mut t = self;
        while let Type::App(s) = t {
            let s = Arc::make_mut(s);
            acc.push(mem::take(&mut s.arg));
            t = &mut s.fun;
        }
        acc.reverse();
        acc
    }

    /// Simultaneously substitute `t₁ ⋯ tₙ` for locals with names `x₁ ⋯ xₙ`.
    pub fn subst(&mut self, subst: &[(Name, Type)]) {
        match self {
            Self::Const(_) => {}
            Self::Local(x) => {
                if let Some((_, t)) = subst.iter().find(|(y, _)| y == x) {
                    *self = t.clone();
                }
            }
            Self::Hole(_) => {}
            Self::Arrow(inner) => {
                let inner = Arc::make_mut(inner);
                inner.dom.subst(subst);
                inner.cod.subst(subst);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.subst(subst);
                inner.arg.subst(subst);
            }
        }
    }

    pub fn inst_hole(&mut self, subst: &[(Name, Type)]) {
        match self {
            Type::Const(_) => {}
            Type::Arrow(inner) => {
                let inner = Arc::make_mut(inner);
                inner.dom.inst_hole(subst);
                inner.cod.inst_hole(subst);
            }
            Type::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.inst_hole(subst);
                inner.arg.inst_hole(subst);
            }
            Type::Local(_) => {}
            Type::Hole(name) => {
                if let Some((_, ty)) = subst.iter().find(|(x, _)| x == name) {
                    *self = ty.clone();
                };
            }
        }
    }

    /// Returns [true] if [self] contains no meta variables.
    pub fn is_ground(&self) -> bool {
        match self {
            Type::Const(_) => true,
            Type::Arrow(inner) => inner.dom.is_ground() && inner.cod.is_ground(),
            Type::App(inner) => inner.fun.is_ground() && inner.arg.is_ground(),
            Type::Local(_) => true,
            Type::Hole(_) => false,
        }
    }

    pub fn contains_local(&self, name: Name) -> bool {
        match self {
            Type::Const(_) => false,
            Type::Arrow(t) => t.dom.contains_local(name) || t.cod.contains_local(name),
            Type::App(t) => t.fun.contains_local(name) || t.arg.contains_local(name),
            &Type::Local(t) => t == name,
            Type::Hole(_) => false,
        }
    }

    pub fn contains_hole(&self, name: Name) -> bool {
        match self {
            Type::Const(_) => false,
            Type::Arrow(t) => t.dom.contains_hole(name) || t.cod.contains_hole(name),
            Type::App(t) => t.fun.contains_hole(name) || t.arg.contains_hole(name),
            Type::Local(_) => false,
            &Type::Hole(n) => n == name,
        }
    }

    pub fn target(&self) -> &Type {
        let mut t = self;
        while let Type::Arrow(inner) = t {
            t = &inner.cod;
        }
        t
    }

    pub fn head(&self) -> &Type {
        let mut t = self;
        while let Type::App(inner) = t {
            t = &inner.fun;
        }
        t
    }

    pub fn args(&self) -> Vec<&Type> {
        let mut t = self;
        let mut args = vec![];
        while let Type::App(inner) = t {
            args.push(&inner.arg);
            t = &inner.fun;
        }
        args.reverse();
        args
    }

    fn matches_help(&self, pattern: &Type, subst: &mut Vec<(Name, Type)>) -> bool {
        match pattern {
            Type::Const(_) => self == pattern,
            Type::Arrow(pattern) => {
                let Type::Arrow(target) = self else {
                    return false;
                };
                target.dom.matches_help(&pattern.dom, subst)
                    && target.cod.matches_help(&pattern.cod, subst)
            }
            Type::App(pattern) => {
                let Type::App(target) = self else {
                    return false;
                };
                target.fun.matches_help(&pattern.fun, subst)
                    && target.arg.matches_help(&pattern.arg, subst)
            }
            Type::Local(_) => self == pattern,
            &Type::Hole(pattern) => {
                if let Some((_, t)) = subst.iter().find(|&&(x, _)| x == pattern) {
                    self.matches_help(&t.clone(), subst)
                } else {
                    subst.push((pattern, self.clone()));
                    true
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ClassType {
    pub arity: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Class {
    pub name: Name,
    pub args: Vec<Type>,
}

impl Class {
    pub fn contains_local(&self, name: Name) -> bool {
        self.args.iter().any(|t| t.contains_local(name))
    }

    pub fn subst(&mut self, subst: &[(Name, Type)]) {
        for t in &mut self.args {
            t.subst(subst);
        }
    }

    pub fn inst_hole(&mut self, subst: &[(Name, Type)]) {
        for t in &mut self.args {
            t.inst_hole(subst);
        }
    }

    pub fn is_ground(&self) -> bool {
        self.args.iter().all(|t| t.is_ground())
    }

    pub fn matches(&self, pattern: &Class) -> Option<Vec<(Name, Type)>> {
        if self.name != pattern.name || self.args.len() != pattern.args.len() {
            return None;
        }
        let mut subst = vec![];
        for (t, p) in zip(&self.args, &pattern.args) {
            if !t.matches_help(p, &mut subst) {
                return None;
            }
        }
        Some(subst)
    }
}

#[derive(Debug, Clone)]
pub enum Instance {
    Local(Class),
    Global(Arc<InstanceGlobal>),
    Hole(Name),
}

#[derive(Debug, Clone)]
pub struct InstanceGlobal {
    pub rule_id: usize,
    pub ty_args: Vec<Type>,
    pub args: Vec<Instance>,
}

pub fn mk_instance_local(class: Class) -> Instance {
    Instance::Local(class)
}

pub fn mk_instance_global(rule_id: usize, ty_args: Vec<Type>, args: Vec<Instance>) -> Instance {
    Instance::Global(Arc::new(InstanceGlobal {
        rule_id,
        ty_args,
        args,
    }))
}

impl Instance {
    fn contains_local_type(&self, name: Name) -> bool {
        match self {
            Instance::Local(c) => c.contains_local(name),
            Instance::Global(i) => {
                i.ty_args.iter().any(|t| t.contains_local(name))
                    || i.args.iter().any(|i| i.contains_local_type(name))
            }
            Instance::Hole(_) => false,
        }
    }

    fn subst_type(&mut self, subst: &[(Name, Type)]) {
        match self {
            Instance::Local(c) => c.subst(subst),
            Instance::Global(i) => {
                for t in &mut Arc::make_mut(i).ty_args {
                    t.subst(subst);
                }
                for i in &mut Arc::make_mut(i).args {
                    i.subst_type(subst);
                }
            }
            Instance::Hole(_) => {}
        }
    }

    pub fn inst_type_hole(&mut self, subst: &[(Name, Type)]) {
        match self {
            Instance::Local(c) => c.inst_hole(subst),
            Instance::Global(i) => {
                for t in &mut Arc::make_mut(i).ty_args {
                    t.inst_hole(subst);
                }
                for i in &mut Arc::make_mut(i).args {
                    i.inst_type_hole(subst);
                }
            }
            Instance::Hole(_) => {}
        }
    }

    pub fn is_type_ground(&self) -> bool {
        match self {
            Instance::Local(c) => c.is_ground(),
            Instance::Global(i) => {
                i.ty_args.iter().all(|t| t.is_ground()) && i.args.iter().all(|i| i.is_type_ground())
            }
            Instance::Hole(_) => true,
        }
    }

    fn subst(&mut self, subst: &[(Class, Instance)]) {
        match self {
            Instance::Local(c) => {
                for (u, i) in subst {
                    if c == u {
                        *self = i.clone();
                        break;
                    }
                }
            }
            Instance::Global(i) => {
                for i in &mut Arc::make_mut(i).args {
                    i.subst(subst);
                }
            }
            Instance::Hole(_) => {}
        }
    }
}

/// Locally nameless representation. See [Charguéraud, 2012].
/// Use syn's convention [https://docs.rs/syn/latest/syn/enum.Expr.html#syntax-tree-enums].
#[derive(Clone, Debug)]
pub enum Term {
    Var(usize),
    Abs(Arc<TermAbs>),
    App(Arc<TermApp>),
    Local(Name),
    Const(Arc<TermConst>),
    Hole(Name),
}

#[derive(Clone, Debug, Default)]
pub struct TermAbs {
    pub binder_type: Type,
    // for pretty-printing
    pub binder_name: Name,
    pub body: Term,
}

#[derive(Clone, Debug)]
pub struct TermApp {
    pub fun: Term,
    pub arg: Term,
}

#[derive(Clone, Debug)]
pub struct TermConst {
    pub name: Name,
    pub ty_args: Vec<Type>,
    pub instances: Vec<Instance>,
}

impl From<TermConst> for Term {
    fn from(value: TermConst) -> Self {
        Term::Const(Arc::new(value))
    }
}

impl TermConst {
    fn alpha_eq(&self, other: &TermConst) -> bool {
        if self.name != other.name || self.ty_args.len() != other.ty_args.len() {
            return false;
        }
        for (t, u) in zip(&self.ty_args, &other.ty_args) {
            if t != u {
                return false;
            }
        }
        // don't need to compare instances because of the coherency.
        true
    }
}

impl Default for Term {
    fn default() -> Self {
        Term::Var(usize::MAX)
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(i) => {
                write!(f, "(var {i})")
            }
            Term::Abs(inner) => {
                write!(f, "(lam {} {})", inner.binder_type, inner.body)
            }
            Term::App(inner) => {
                write!(f, "({} {})", inner.fun, inner.arg)
            }
            Term::Local(name) => {
                write!(f, "(local {name})")
            }
            Term::Const(inner) => {
                write!(f, "{}", inner.name)?;
                if !inner.ty_args.is_empty() {
                    write!(f, ".{{")?;
                    let mut first = true;
                    for t in &inner.ty_args {
                        if !first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{t}")?;
                        first = false;
                    }
                    write!(f, "}}")?;
                }
                Ok(())
            }
            Term::Hole(name) => {
                write!(f, "(hole {})", name)
            }
        }
    }
}

pub fn mk_abs(binder_name: Name, binder_type: Type, body: Term) -> Term {
    Term::Abs(Arc::new(TermAbs {
        binder_type,
        binder_name,
        body,
    }))
}

pub fn mk_app(fun: Term, arg: Term) -> Term {
    Term::App(Arc::new(TermApp { fun, arg }))
}

pub fn mk_const(name: Name, ty_args: Vec<Type>, instances: Vec<Instance>) -> Term {
    Term::Const(Arc::new(TermConst {
        name,
        ty_args,
        instances,
    }))
}

pub fn mk_local(name: Name) -> Term {
    Term::Local(name)
}

pub fn mk_fresh_hole() -> Term {
    Term::Hole(Name::fresh())
}

#[derive(Debug, Clone)]
pub struct Ctor {
    pub head: Arc<TermConst>,
    pub args: Vec<Term>,
}

impl TryFrom<Term> for Ctor {
    type Error = ();

    fn try_from(value: Term) -> Result<Self, Self::Error> {
        match value {
            Term::Const(value) => Ok(Ctor {
                head: value,
                args: vec![],
            }),
            Term::App(value) => {
                let value = Arc::unwrap_or_clone(value);
                let mut ctor: Ctor = value.fun.try_into()?;
                ctor.args.push(value.arg);
                Ok(ctor)
            }
            Term::Var(_) | Term::Abs(_) | Term::Local(_) | Term::Hole(_) => Err(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: Name,
    pub ty: Type,
}

impl Term {
    /// self.open(x) == [x/0]self
    pub fn open(&mut self, x: &Term) {
        self.open_at(x, 0)
    }

    fn open_at(&mut self, x: &Term, level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(i) => {
                if *i == level {
                    *self = x.clone();
                }
            }
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.open_at(x, level + 1);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.open_at(x, level);
                inner.arg.open_at(x, level);
            }
            Self::Const(_) => {}
            Self::Hole(_) => {}
        }
    }

    /// self.close(x) == [0/x]self
    pub fn close(&mut self, name: Name) {
        assert!(self.is_lclosed());
        self.close_at(name, 0)
    }

    fn close_at(&mut self, name: Name, level: usize) {
        match self {
            Self::Local(x) => {
                if x == &name {
                    *self = Self::Var(level);
                }
            }
            Self::Var(_) => {}
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.close_at(name, level + 1);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.close_at(name, level);
                inner.arg.close_at(name, level);
            }
            Self::Const(_) => {}
            Self::Hole(_) => {}
        }
    }

    /// {x₁, ⋯, xₙ} # self <==> ∀ i, xᵢ ∉ FV(self)
    pub fn is_fresh(&self, free_list: &[Name]) -> bool {
        match self {
            Self::Local(x) => !free_list.contains(x),
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_fresh(free_list),
            Self::App(inner) => inner.fun.is_fresh(free_list) && inner.arg.is_fresh(free_list),
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    /// FV(self) ⊆ {x₁, ⋯, xₙ}
    /// The term is borrowed from nominal set theory.
    pub fn is_supported_by(&self, free_list: &[Name]) -> bool {
        match self {
            Self::Local(x) => free_list.contains(x),
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_supported_by(free_list),
            Self::App(inner) => {
                inner.fun.is_supported_by(free_list) && inner.arg.is_supported_by(free_list)
            }
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    pub fn is_closed(&self) -> bool {
        self.is_supported_by(&[])
    }

    pub fn is_lclosed(&self) -> bool {
        self.is_lclosed_at(0)
    }

    fn is_lclosed_at(&self, level: usize) -> bool {
        match self {
            Self::Local(_) => true,
            Self::Var(i) => *i < level,
            Self::Abs(inner) => inner.body.is_lclosed_at(level + 1),
            Self::App(inner) => inner.fun.is_lclosed_at(level) && inner.arg.is_lclosed_at(level),
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    pub fn is_body(&self) -> bool {
        self.is_lclosed_at(1)
    }

    pub fn contains_var(&self, i: usize) -> bool {
        match self {
            &Term::Var(level) => i == level,
            Term::Abs(inner) => inner.body.contains_var(i + 1),
            Term::App(inner) => inner.fun.contains_var(i) || inner.arg.contains_var(i),
            Term::Local(_) => false,
            Term::Const(_) => false,
            Term::Hole(_) => false,
        }
    }

    pub fn head(&self) -> &Term {
        if self.is_abs() {
            return self;
        }
        let mut m = self;
        while let Self::App(inner) = m {
            m = &inner.fun;
        }
        m
    }

    pub fn head_mut(&mut self) -> &mut Term {
        if self.is_abs() {
            return self;
        }
        let mut m = self;
        while let Self::App(inner) = m {
            m = &mut Arc::make_mut(inner).fun;
        }
        m
    }

    pub fn args(&self) -> Vec<&Term> {
        if self.is_abs() {
            return vec![];
        }
        let mut m = self;
        let mut args = vec![];
        while let Self::App(inner) = m {
            m = &inner.fun;
            args.push(&inner.arg);
        }
        args.reverse();
        args
    }

    pub fn args_mut(&mut self) -> Vec<&mut Term> {
        if self.is_abs() {
            return vec![];
        }
        let mut m = self;
        let mut args = vec![];
        while let Self::App(inner) = m {
            let TermApp { fun, arg } = Arc::make_mut(inner);
            m = fun;
            args.push(arg);
        }
        args.reverse();
        args
    }

    pub fn is_abs(&self) -> bool {
        matches!(self, Term::Abs(_))
    }

    pub fn is_hole(&self) -> bool {
        matches!(self, Term::Hole(_))
    }

    pub fn is_const(&self) -> bool {
        matches!(self, Term::Const(_))
    }

    pub fn is_local(&self) -> bool {
        matches!(self, Term::Local(_))
    }

    /// Checks if self ≡ (?M l₁ ⋯ lₙ) where l₁ ⋯ lₙ are pairwise distinct locals.
    pub fn is_pattern(&self) -> Option<Vec<Name>> {
        let mut arg_locals = vec![];
        if !self.head().is_hole() {
            return None;
        }
        for arg in self.args() {
            let Term::Local(arg) = arg else {
                return None;
            };
            for a in &arg_locals {
                if a == arg {
                    return None;
                }
            }
            arg_locals.push(*arg);
        }
        Some(arg_locals)
    }

    pub fn is_quasi_pattern(&self) -> bool {
        if !self.head().is_hole() {
            return false;
        }
        for arg in self.args() {
            let Term::Local(_) = arg else {
                return false;
            };
        }
        true
    }

    pub fn contains_local_type(&self, name: Name) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Abs(m) => m.binder_type.contains_local(name) || m.body.contains_local_type(name),
            Term::App(m) => m.fun.contains_local_type(name) || m.arg.contains_local_type(name),
            Term::Local(_) => false,
            Term::Const(m) => {
                m.ty_args.iter().any(|t| t.contains_local(name))
                    || m.instances.iter().any(|i| i.contains_local_type(name))
            }
            Term::Hole(_) => false,
        }
    }

    /// m.apply([l₁ ⋯ lₙ])
    /// assert(self = m l₁ ⋯ lₙ)
    pub fn apply(&mut self, args: impl IntoIterator<Item = Term>) {
        let mut m = mem::take(self);
        for arg in args {
            m = mk_app(m, arg);
        }
        *self = m;
    }

    /// m = n l*
    /// m.unapply() // => l*
    /// assert(m = n)
    pub fn unapply(&mut self) -> Vec<Term> {
        let mut args = vec![];
        let mut m = &mut *self;
        while let Self::App(inner) = m {
            let inner = Arc::make_mut(inner);
            args.push(mem::take(&mut inner.arg));
            m = &mut inner.fun;
        }
        *self = mem::take(m);
        args.reverse();
        args
    }

    // λ x₁ ⋯ xₙ, m ↦ [x₁, ⋯ , xₙ]
    // Fresh names are generated on the fly.
    pub fn unabs(&mut self) -> Vec<Parameter> {
        let mut xs = vec![];
        while let Term::Abs(inner) = self {
            let &mut TermAbs {
                ref mut binder_type,
                binder_name,
                ref mut body,
            } = Arc::make_mut(inner);
            xs.push(Parameter {
                name: Name::fresh_from(binder_name),
                ty: mem::take(binder_type),
            });
            *self = mem::take(body);
        }
        self.unabs_help(&xs, 0);
        assert!(self.is_lclosed());
        xs
    }

    fn unabs_help(&mut self, xs: &[Parameter], level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(i) => {
                if *i < level {
                    return;
                }
                if *i - level < xs.len() {
                    *self = mk_local(xs[xs.len() - 1 - (*i - level)].name);
                }
            }
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.unabs_help(xs, level + 1);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.unabs_help(xs, level);
                inner.arg.unabs_help(xs, level);
            }
            Self::Const(_) => {}
            Self::Hole(_) => {}
        }
    }

    // assert_eq!(self, "m");
    // self.abs(&[x1, x2]);
    // assert_eq!(self, "λ x1 x2, m");
    //
    // If allow_free is true, this function always succeeds and returns true.
    // If allow_free is false and self contains extra free variables, abs returns false and the state of self is restored.
    pub fn abs(&mut self, xs: &[Parameter]) {
        self.abs_help(xs, 0);
        let mut m = mem::take(self);
        for x in xs.iter().rev() {
            m = mk_abs(x.name, x.ty.clone(), m);
        }
        *self = m;
    }

    fn abs_help(&mut self, xs: &[Parameter], level: usize) {
        match self {
            &mut Self::Local(l) => {
                for (i, x) in xs.iter().rev().enumerate() {
                    if l == x.name {
                        *self = Self::Var(level + i);
                        return;
                    }
                }
            }
            Self::Var(_) => {}
            Self::Abs(inner) => Arc::make_mut(inner).body.abs_help(xs, level + 1),
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.abs_help(xs, level);
                inner.arg.abs_help(xs, level);
            }
            Self::Const(_) => {}
            Self::Hole(_) => {}
        }
    }

    pub fn generalize(&mut self, xs: &[Parameter]) {
        static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall").unwrap());

        self.abs_help(xs, 0);

        let mut m = mem::take(self);
        for x in xs.iter().rev() {
            m = mk_abs(x.name, x.ty.clone(), m);
            let mut c = mk_const(*FORALL, vec![x.ty.clone()], vec![]);
            c.apply([m]);
            m = c;
        }
        *self = m;
    }

    // ∀ x₁ ⋯ xₙ, m ↦ [x₁, ⋯ , xₙ]
    // Fresh names are generated on the fly.
    // Does not check ty_args of forall.
    pub fn ungeneralize(&mut self) -> Vec<Parameter> {
        let mut acc = vec![];
        while let Some(x) = self.ungeneralize1() {
            acc.push(x);
        }
        acc
    }

    fn ungeneralize1(&mut self) -> Option<Parameter> {
        static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall").unwrap());

        let Term::App(m) = self else {
            return None;
        };
        let m = Arc::make_mut(m);
        let Term::Const(head) = &m.fun else {
            return None;
        };
        if head.name != *FORALL {
            return None;
        }
        let Term::Abs(abs) = &mut m.arg else {
            return None;
        };
        let TermAbs {
            binder_type,
            binder_name,
            body,
        } = Arc::make_mut(abs);
        let name = Name::fresh_from(*binder_name);
        body.open(&mk_local(name));
        let ret = Parameter {
            name,
            ty: mem::take(binder_type),
        };
        *self = mem::take(body);
        Some(ret)
    }

    pub fn guard(&mut self, guards: impl IntoIterator<Item = Term>) {
        self.guard_help(guards.into_iter())
    }

    fn guard_help(&mut self, mut guards: impl Iterator<Item = Term>) {
        static IMP: LazyLock<Name> = LazyLock::new(|| Name::intern("imp").unwrap());

        if let Some(guard) = guards.next() {
            self.guard_help(guards);
            let target = mem::take(self);
            let mut m = mk_const(*IMP, vec![], vec![]);
            m.apply([guard, target]);
            *self = m;
        }
    }

    pub fn unguard(&mut self) -> Vec<Term> {
        let mut acc = vec![];
        while let Some(guard) = self.unguard1() {
            acc.push(guard);
        }
        acc
    }

    fn unguard1(&mut self) -> Option<Term> {
        static IMP: LazyLock<Name> = LazyLock::new(|| Name::intern("imp").unwrap());

        let Term::App(m) = self else {
            return None;
        };
        let m = Arc::make_mut(m);
        let Term::App(n) = &mut m.fun else {
            return None;
        };
        let n = Arc::make_mut(n);
        let Term::Const(head) = &n.fun else {
            return None;
        };
        if head.name != *IMP {
            return None;
        }
        let left = mem::take(&mut n.arg);
        let right = mem::take(&mut m.arg);
        *self = right;
        Some(left)
    }

    pub fn subst_type(&mut self, subst: &[(Name, Type)]) {
        match self {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.binder_type.subst(subst);
                inner.body.subst_type(subst);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.subst_type(subst);
                inner.arg.subst_type(subst);
            }
            Term::Local(_) => {}
            Term::Const(inner) => {
                for s in &mut Arc::make_mut(inner).ty_args {
                    s.subst(subst);
                }
                for i in &mut Arc::make_mut(inner).instances {
                    i.subst_type(subst);
                }
            }
            Term::Hole(_) => {}
        }
    }

    pub fn subst(&mut self, subst: &[(Name, Term)]) {
        match self {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.body.subst(subst);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.subst(subst);
                inner.arg.subst(subst);
            }
            Term::Local(name) => {
                for (x, m) in subst {
                    if name == x {
                        *self = m.clone();
                        break;
                    }
                }
            }
            Term::Const(_) => {}
            Term::Hole(_) => {}
        }
    }

    pub fn inst_type_hole(&mut self, subst: &[(Name, Type)]) {
        match self {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.binder_type.inst_hole(subst);
                inner.body.inst_type_hole(subst);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.inst_type_hole(subst);
                inner.arg.inst_type_hole(subst);
            }
            Term::Local(_) => {}
            Term::Const(inner) => {
                for s in &mut Arc::make_mut(inner).ty_args {
                    s.inst_hole(subst);
                }
                for i in &mut Arc::make_mut(inner).instances {
                    i.inst_type_hole(subst);
                }
            }
            Term::Hole(_) => {}
        }
    }

    pub fn inst_hole(&mut self, subst: &[(Name, Term)]) {
        match self {
            Term::Var(_) => {}
            Term::Local(_) => {}
            Term::Const(_) => {}
            Term::Hole(x) => {
                if let Some((_, m)) = subst.iter().find(|(y, _)| y == x) {
                    *self = m.clone();
                }
            }
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.body.inst_hole(subst);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.inst_hole(subst);
                inner.arg.inst_hole(subst);
            }
        }
    }

    // checks if self has any (term-level) meta variable.
    pub fn is_ground(&self) -> bool {
        match self {
            Term::Var(_) => true,
            Term::Abs(m) => m.body.is_ground(),
            Term::App(m) => m.fun.is_ground() && m.arg.is_ground(),
            Term::Local(_) => true,
            Term::Const(_) => true,
            Term::Hole(_) => false,
        }
    }

    pub fn is_type_ground(&self) -> bool {
        match self {
            Term::Var(_) => true,
            Term::Abs(inner) => inner.binder_type.is_ground() && inner.body.is_type_ground(),
            Term::App(inner) => inner.fun.is_type_ground() && inner.arg.is_type_ground(),
            Term::Local(_) => true,
            Term::Const(inner) => {
                inner.ty_args.iter().all(Type::is_ground)
                    && inner.instances.iter().all(Instance::is_type_ground)
            }
            Term::Hole(_) => true,
        }
    }

    pub fn alpha_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1 == index2,
            (Term::Abs(inner1), Term::Abs(inner2)) => {
                inner1.binder_type == inner2.binder_type && inner1.body.alpha_eq(&inner2.body)
            }
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.alpha_eq(&inner2.fun) && inner1.arg.alpha_eq(&inner2.arg)
            }
            (Term::Local(name1), Term::Local(name2)) => name1 == name2,
            (Term::Const(inner1), Term::Const(inner2)) => inner1.alpha_eq(inner2),
            (Term::Hole(name1), Term::Hole(name2)) => name1 == name2,
            _ => false,
        }
    }

    pub fn maybe_alpha_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1 == index2,
            (Term::Abs(inner1), Term::Abs(inner2)) => inner1.body.maybe_alpha_eq(&inner2.body),
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.maybe_alpha_eq(&inner2.fun) && inner1.arg.maybe_alpha_eq(&inner2.arg)
            }
            (Term::Local(name1), Term::Local(name2)) => name1 == name2,
            (Term::Const(inner1), Term::Const(inner2)) => inner1.name == inner2.name,
            (Term::Hole(name1), Term::Hole(name2)) => name1 == name2,
            _ => false,
        }
    }

    fn beta_reduce(&mut self) -> Option<Path> {
        let path = mk_path_beta(self.clone());
        let Term::App(inner) = self else {
            return None;
        };
        let TermApp { fun, arg } = Arc::make_mut(inner);
        let Term::Abs(inner) = fun else {
            return None;
        };
        let TermAbs {
            binder_type: _,
            binder_name: _,
            body,
        } = Arc::make_mut(inner);
        body.open(arg);
        *self = mem::take(body);
        assert!(self.is_lclosed());
        Some(path)
    }

    pub fn whnf(&mut self) -> Option<Path> {
        match self {
            Term::Var(_) | Term::Local(_) | Term::Const(_) | Term::Hole(_) | Term::Abs(_) => None,
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                let p;
                if let Some(p_fun) = inner.fun.whnf() {
                    let p_arg = mk_path_refl(inner.arg.clone());
                    p = mk_path_congr_app(p_fun, p_arg);
                } else {
                    p = self.beta_reduce()?;
                }
                match self.whnf() {
                    Some(p_next) => Some(mk_path_trans(p, p_next)),
                    None => Some(p),
                }
            }
        }
    }

    pub fn contains_local(&self, name: Name) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Abs(m) => m.body.contains_local(name),
            Term::App(m) => m.fun.contains_local(name) || m.arg.contains_local(name),
            &Term::Local(m) => m == name,
            Term::Const(_) => false,
            Term::Hole(_) => false,
        }
    }

    pub fn subst_instance(&mut self, subst: &[(Class, Instance)]) {
        match self {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                Arc::make_mut(inner).body.subst_instance(subst);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.subst_instance(subst);
                inner.arg.subst_instance(subst);
            }
            Term::Local(_) => {}
            Term::Const(inner) => {
                for i in &mut Arc::make_mut(inner).instances {
                    i.subst(subst);
                }
            }
            Term::Hole(_) => {}
        }
    }
}

/// Judgmental equality for the definitional equality.
/// The type inhabitation problem of `Conv` shall be decidable.
///
/// The formation rule of Conv is as follows:
/// ```text
/// Γ ⊢ m₁ : τ    Γ ⊢ m₂ : τ
/// -------------------------
/// Γ ⊢ m₁ ≡ m₂ : τ
/// ```
#[derive(Debug, Clone)]
pub struct Conv {
    pub left: Term,
    pub right: Term,
}

impl std::fmt::Display for Conv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ≡ {}", self.left, self.right)
    }
}

#[derive(Debug, Clone)]
pub enum Path {
    /// ```text
    ///
    /// ------------------
    /// Γ ⊢ refl m : m ≡ m
    /// ```
    Refl(Term),
    /// ```text
    /// Γ ⊢ h : m₁ ≡ m₂
    /// --------------------
    /// Γ ⊢ symm h : m₂ ≡ m₁
    /// ```
    Symm(Arc<Path>),
    /// ```text
    /// Γ ⊢ h₁ : m₁ ≡ m₂   Γ ⊢ h₂ : m₂ ≡ m₃
    /// ------------------------------------
    /// Γ ⊢ trans h₁ h₂ : m₁ ≡ m₃
    /// ```
    Trans(Arc<(Path, Path)>),
    /// ```text
    /// Γ ⊢ h₁ : f₁ ≡ f₂   Γ ⊢ h₂ : a₁ ≡ a₂
    /// ------------------------------------
    /// Γ ⊢ congr_app h₁ h₂ : f₁ a₁ ≡ f₂ a₂
    /// ```
    CongrApp(Arc<(Path, Path)>),
    /// ```text
    /// Γ, x : τ ⊢ h : m₁ ≡ m₂
    /// ------------------------------------------------------------
    /// Γ ⊢ congr_abs (x : τ), h : (λ (x : τ), m₁) ≡ (λ (x : τ), m₂)
    /// ```
    CongrAbs(Arc<(Name, Type, Path)>),
    /// ```text
    ///
    /// --------------------------------------------------------
    /// Γ ⊢ beta_reduce ((λ x, m₁) m₂) : (λ x, m₁) m₂ ≡ [m₂/x]m₁
    /// ```
    Beta(Term),
    /// ```text
    ///
    /// --------------------------------------------------------------------------------------- (c.{u₁ ⋯ uₙ} :≡ m)
    /// Γ ⊢ delta_reduce c.{t₁ ⋯ tₙ}[i₁ ⋯ iₘ] : c.{t₁ ⋯ tₙ}[i₁ ⋯ iₘ] ≡ [i₁ ⋯ iₘ][t₁/u₁ ⋯ tₙ/uₙ]m
    /// ```
    Delta(Term),
    Kappa(Term),
}

impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Path::Refl(m) => write!(f, "(refl {m})"),
            Path::Symm(h) => write!(f, "(symm {h})"),
            Path::Trans(inner) => write!(f, "(trans {} {})", inner.0, inner.1),
            Path::CongrApp(inner) => write!(f, "(congr_app {} {})", inner.0, inner.1),
            Path::CongrAbs(inner) => {
                write!(f, "(congr_abs ({} : {}), {})", inner.0, inner.1, inner.2)
            }
            Path::Beta(m) => write!(f, "(beta {m})"),
            Path::Delta(m) => {
                write!(f, "(delta {m})")
            }
            Path::Kappa(m) => {
                write!(f, "(kappa {m})")
            }
        }
    }
}

pub fn mk_path_refl(m: Term) -> Path {
    Path::Refl(m)
}

pub fn mk_path_symm(h: Path) -> Path {
    Path::Symm(Arc::new(h))
}

pub fn mk_path_trans(h1: Path, h2: Path) -> Path {
    Path::Trans(Arc::new((h1, h2)))
}

pub fn mk_path_congr_app(h1: Path, h2: Path) -> Path {
    Path::CongrApp(Arc::new((h1, h2)))
}

pub fn mk_path_congr_abs(name: Name, t: Type, h: Path) -> Path {
    Path::CongrAbs(Arc::new((name, t, h)))
}

pub fn mk_path_beta(m: Term) -> Path {
    Path::Beta(m)
}

pub fn mk_path_delta(m: Term) -> Path {
    Path::Delta(m)
}

pub fn mk_path_kappa(m: Term) -> Path {
    Path::Kappa(m)
}

impl Path {
    pub fn is_refl(&self) -> bool {
        matches!(self, Path::Refl(_))
    }
}

#[derive(Debug, Default, Clone)]
pub struct LocalEnv {
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub locals: Vec<Parameter>,
}

impl LocalEnv {
    pub fn get_local(&self, name: Name) -> Option<&Type> {
        self.locals.iter().rev().find_map(|local| {
            if local.name == name {
                Some(&local.ty)
            } else {
                None
            }
        })
    }
}

#[derive(Debug, Clone)]
pub struct Const {
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Delta {
    // TODO: remove this?
    pub local_types: Vec<Name>,
    // TODO: remove this?
    pub local_classes: Vec<Class>,
    pub target: Term,
    pub hint: usize,
}

#[derive(Debug, Clone)]
pub struct ClassRule {
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub target: Class,
    pub method_table: HashMap<Name, Term>,
}

#[derive(Debug, Clone)]
pub struct Env<'a> {
    pub type_const_table: &'a HashMap<Name, Kind>,
    pub const_table: &'a HashMap<Name, Const>,
    pub delta_table: &'a HashMap<Name, Delta>,
    pub class_predicate_table: &'a HashMap<Name, ClassType>,
    pub class_database: &'a [ClassRule],
}

impl<'a> Env<'a> {
    pub fn infer_kind(&self, local_env: &LocalEnv, t: &Type) -> Option<Kind> {
        match t {
            Type::Const(name) => Some(self.type_const_table.get(name)?.clone()),
            Type::Arrow(inner) => {
                if !self.check_kind(local_env, &inner.dom, Kind::base()) {
                    return None;
                }
                if !self.check_kind(local_env, &inner.cod, Kind::base()) {
                    return None;
                }
                Some(Kind::base())
            }
            Type::App(inner) => {
                let fun_kind = self.infer_kind(local_env, &inner.fun)?;
                if fun_kind.0 == 0 {
                    return None;
                }
                if !self.check_kind(local_env, &inner.arg, Kind::base()) {
                    return None;
                }
                Some(Kind(fun_kind.0 - 1))
            }
            Type::Local(x) => {
                for local_type in &local_env.local_types {
                    if local_type == x {
                        return Some(Kind::base());
                    }
                }
                None
            }
            Type::Hole(_) => None,
        }
    }

    pub fn check_kind(&self, local_env: &LocalEnv, t: &Type, kind: Kind) -> bool {
        let Some(k) = self.infer_kind(local_env, t) else {
            return false;
        };
        k == kind
    }

    pub fn is_wft(&self, local_env: &LocalEnv, t: &Type) -> bool {
        self.check_kind(local_env, t, Kind::base())
    }

    pub fn is_wfc(&self, local_env: &LocalEnv, c: &Class) -> bool {
        let Some(class_type) = self.class_predicate_table.get(&c.name) else {
            return false;
        };
        if class_type.arity != c.args.len() {
            return false;
        }
        for arg in &c.args {
            if !self.is_wft(local_env, arg) {
                return false;
            }
        }
        true
    }

    pub fn infer_class(&self, local_env: &LocalEnv, i: &Instance) -> Option<Class> {
        match i {
            Instance::Local(i) => {
                for local_class in &local_env.local_classes {
                    if local_class == i {
                        return Some(i.clone());
                    }
                }
                None
            }
            Instance::Global(i) => {
                let &InstanceGlobal {
                    rule_id,
                    ref ty_args,
                    ref args,
                } = &**i;
                let ClassRule {
                    local_types,
                    local_classes,
                    target,
                    method_table: _,
                } = self.class_database.get(rule_id)?;
                if local_types.len() != ty_args.len() {
                    return None;
                }
                for ty_arg in ty_args {
                    if !self.is_wft(local_env, ty_arg) {
                        return None;
                    }
                }
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, ty_args) {
                    type_subst.push((x, t.clone()));
                }
                if local_classes.len() != args.len() {
                    return None;
                }
                for (local_class, arg) in zip(local_classes, args) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    if !self.check_class(local_env, arg, &local_class) {
                        return None;
                    }
                }
                let mut target = target.clone();
                target.subst(&type_subst);
                Some(target)
            }
            Instance::Hole(_) => None,
        }
    }

    // t is trusted
    pub fn check_class(&self, local_env: &LocalEnv, i: &Instance, class: &Class) -> bool {
        let Some(c) = self.infer_class(local_env, i) else {
            return false;
        };
        c == *class
    }

    pub fn infer_type(&self, local_env: &mut LocalEnv, m: &Term) -> Option<Type> {
        match m {
            Term::Var(_) => None,
            Term::Abs(m) => {
                if !self.is_wft(local_env, &m.binder_type) {
                    return None;
                }
                let x = Parameter {
                    name: Name::fresh_from(m.binder_name),
                    ty: m.binder_type.clone(),
                };
                let mut n = m.body.clone();
                n.open(&mk_local(x.name));
                local_env.locals.push(x);
                let target = self.infer_type(local_env, &n)?;
                let x = local_env.locals.pop().unwrap();
                Some(mk_type_arrow(x.ty, target))
            }
            Term::App(m) => {
                let fun_ty = self.infer_type(local_env, &m.fun)?;
                match fun_ty {
                    Type::Arrow(fun_ty) => {
                        if !self.check_type(local_env, &m.arg, &fun_ty.dom) {
                            return None;
                        }
                        Some(fun_ty.cod.clone())
                    }
                    _ => None,
                }
            }
            &Term::Local(x) => {
                for y in local_env.locals.iter().rev() {
                    if x == y.name {
                        return Some(y.ty.clone());
                    }
                }
                None
            }
            Term::Const(m) => {
                let Const {
                    local_types,
                    local_classes,
                    ty,
                } = self.const_table.get(&m.name)?;
                if local_types.len() != m.ty_args.len() {
                    return None;
                }
                for ty_arg in &m.ty_args {
                    if !self.is_wft(local_env, ty_arg) {
                        return None;
                    }
                }
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, &m.ty_args) {
                    type_subst.push((x, t.clone()));
                }
                if local_classes.len() != m.instances.len() {
                    return None;
                }
                for (local_class, instance) in zip(local_classes, &m.instances) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    if !self.is_wfc(local_env, &local_class) {
                        return None;
                    }
                    if !self.check_class(local_env, instance, &local_class) {
                        return None;
                    }
                }
                let mut ty = ty.clone();
                ty.subst(&type_subst);
                Some(ty)
            }
            Term::Hole(_) => None,
        }
    }

    pub fn check_type(&self, local_env: &mut LocalEnv, m: &Term, target: &Type) -> bool {
        let Some(t) = self.infer_type(local_env, m) else {
            return false;
        };
        t == *target
    }

    pub fn is_wff(&self, local_env: &mut LocalEnv, m: &Term) -> bool {
        self.check_type(local_env, m, &mk_type_prop())
    }

    pub fn infer_conv(&self, local_env: &mut LocalEnv, path: &Path) -> Option<Conv> {
        match path {
            Path::Refl(m) => {
                let _ty = self.infer_type(local_env, m)?;
                Some(Conv {
                    left: m.clone(),
                    right: m.clone(),
                })
            }
            Path::Symm(path) => {
                let h = self.infer_conv(local_env, path)?;
                Some(Conv {
                    left: h.right,
                    right: h.left,
                })
            }
            Path::Trans(path) => {
                let h1 = self.infer_conv(local_env, &path.0)?;
                let h2 = self.infer_conv(local_env, &path.1)?;
                if !h1.right.alpha_eq(&h2.left) {
                    return None;
                }
                // h1.right == h2.left means the types in the both sides match.
                Some(Conv {
                    left: h1.left,
                    right: h2.right,
                })
            }
            Path::CongrApp(path) => {
                let mut h1 = self.infer_conv(local_env, &path.0)?;
                let h2 = self.infer_conv(local_env, &path.1)?;
                h1.left.apply([h2.left]);
                h1.right.apply([h2.right]);
                let _ty = self.infer_type(local_env, &h1.left)?;
                Some(h1)
            }
            Path::CongrAbs(path) => {
                if !self.is_wft(local_env, &path.1) {
                    return None;
                }
                local_env.locals.push(Parameter {
                    name: path.0,
                    ty: path.1.clone(),
                });
                let mut h = self.infer_conv(local_env, &path.2)?;
                let x = local_env.locals.pop().unwrap();
                h.left.abs(slice::from_ref(&x));
                h.right.abs(slice::from_ref(&x));
                Some(h)
            }
            Path::Beta(m) => {
                let _ty = self.infer_type(local_env, m)?;
                let left = m.clone();
                let Term::App(m) = m else {
                    return None;
                };
                let Term::Abs(fun) = &m.fun else {
                    return None;
                };
                let mut right = fun.body.clone();
                right.open(&m.arg);
                Some(Conv { left, right })
            }
            Path::Delta(m) => {
                let _ty = self.infer_type(local_env, m)?;
                let left = m.clone();
                let Term::Const(m) = m else {
                    return None;
                };
                let Delta {
                    local_types,
                    local_classes,
                    target,
                    hint: _,
                } = self.delta_table.get(&m.name)?;
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, &m.ty_args) {
                    type_subst.push((x, t.clone()));
                }
                let mut instance_subst = vec![];
                for (local_class, instance) in zip(local_classes, &m.instances) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    instance_subst.push((local_class, instance.clone()));
                }
                let mut target = target.clone();
                target.subst_type(&type_subst);
                target.subst_instance(&instance_subst);
                Some(Conv {
                    left,
                    right: target,
                })
            }
            Path::Kappa(m) => {
                let _ty = self.infer_type(local_env, m)?;
                let left = m.clone();
                let Term::Const(n) = m else {
                    return None;
                };
                if n.instances.is_empty() {
                    return None;
                }
                let Instance::Global(recv) = &n.instances[0] else {
                    return None;
                };
                let &InstanceGlobal {
                    rule_id,
                    ref ty_args,
                    ref args,
                } = &**recv;
                // assert_eq!(ty_args, &n.ty_args);
                // assert_eq!(&args[..], &n.instances[1..]);
                let ClassRule {
                    local_types,
                    local_classes,
                    target: _,
                    method_table,
                } = &self.class_database[rule_id];
                let target = method_table.get(&n.name)?;
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, ty_args) {
                    type_subst.push((x, t.clone()));
                }
                let mut instance_subst = vec![];
                for (local_class, instance) in zip(local_classes, args) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    instance_subst.push((local_class, instance.clone()));
                }
                let mut target = target.clone();
                target.subst_type(&type_subst);
                target.subst_instance(&instance_subst);
                Some(Conv {
                    left,
                    right: target,
                })
            }
        }
    }

    // c.{u₁, ⋯, uₙ} := n
    // assert_eq!(m, c.{u₁, ⋯, uₙ})
    // self.delta_reduce(m);
    // assert_eq!(m, n)
    fn delta_reduce(&self, m: &mut Term) -> Option<Path> {
        let orig_m = m.clone();
        let Term::Const(n) = m else {
            return None;
        };
        let Delta {
            local_types,
            local_classes,
            target,
            hint: _,
        } = self.delta_table.get(&n.name)?;
        let mut type_subst = vec![];
        for (&x, t) in zip(local_types, &n.ty_args) {
            type_subst.push((x, t.clone()));
        }
        let mut instance_subst = vec![];
        for (local_class, instance) in zip(local_classes, &n.instances) {
            let mut local_class = local_class.clone();
            local_class.subst(&type_subst);
            instance_subst.push((local_class, instance.clone()));
        }
        let mut target = target.clone();
        target.subst_type(&type_subst);
        target.subst_instance(&instance_subst);
        *m = target;
        Some(mk_path_delta(orig_m))
    }

    fn kappa_reduce(&self, m: &mut Term) -> Option<Path> {
        let orig_m = m.clone();
        let Term::Const(n) = m else {
            return None;
        };
        if n.instances.is_empty() {
            return None;
        }
        let Instance::Global(recv) = &n.instances[0] else {
            return None;
        };
        let &InstanceGlobal {
            rule_id,
            ref ty_args,
            ref args,
        } = &**recv;
        // assert_eq!(ty_args, &n.ty_args);
        // assert_eq!(&args[..], &n.instances[1..]);
        let ClassRule {
            local_types,
            local_classes,
            target: _,
            method_table,
        } = &self.class_database[rule_id];
        let target = method_table.get(&n.name)?;
        let mut type_subst = vec![];
        for (&x, t) in zip(local_types, ty_args) {
            type_subst.push((x, t.clone()));
        }
        let mut instance_subst = vec![];
        for (local_class, instance) in zip(local_classes, args) {
            let mut local_class = local_class.clone();
            local_class.subst(&type_subst);
            instance_subst.push((local_class, instance.clone()));
        }
        let mut target = target.clone();
        target.subst_type(&type_subst);
        target.subst_instance(&instance_subst);
        *m = target;
        Some(mk_path_kappa(orig_m))
    }

    pub fn unfold_head(&self, m: &mut Term) -> Option<Path> {
        match m {
            Term::Var(_) | Term::Local(_) | Term::Abs(_) | Term::Hole(_) => None,
            Term::Const(_) => self.delta_reduce(m).or_else(|| self.kappa_reduce(m)),
            Term::App(inner) => {
                let TermApp { fun, arg } = Arc::make_mut(inner);
                let h_fun = self.unfold_head(fun)?;
                let h_arg = mk_path_refl(arg.clone());
                Some(mk_path_congr_app(h_fun, h_arg))
            }
        }
    }

    pub fn def_hint(&self, name: Name) -> Option<usize> {
        let def = self.delta_table.get(&name)?;
        Some(def.hint + 1)
    }

    fn equiv_help(&self, m1: &mut Term, m2: &mut Term) -> Option<Path> {
        if m1.alpha_eq(m2) {
            return Some(mk_path_refl(m1.clone()));
        }
        if let (Term::Abs(inner1), Term::Abs(inner2)) = (&mut *m1, &mut *m2) {
            let inner1 = Arc::make_mut(inner1);
            let inner2 = Arc::make_mut(inner2);
            let x = Name::fresh();
            let local = mk_local(x);
            inner1.body.open(&local);
            inner2.body.open(&local);
            let h = self.equiv_help(&mut inner1.body, &mut inner2.body)?;
            return Some(mk_path_congr_abs(x, inner1.binder_type.clone(), h));
        }
        let h1 = m1.whnf().unwrap_or_else(|| mk_path_refl(m1.clone()));
        let h2 = match m2.whnf() {
            Some(h) => mk_path_symm(h),
            None => mk_path_refl(m2.clone()),
        };
        // TODO: optimize this condition check
        if !h1.is_refl() || !h2.is_refl() {
            if m1.alpha_eq(m2) {
                return Some(mk_path_trans(h1, h2));
            }
            if let (Term::Abs(inner1), Term::Abs(inner2)) = (&mut *m1, &mut *m2) {
                let inner1 = Arc::make_mut(inner1);
                let inner2 = Arc::make_mut(inner2);
                let x = Name::fresh();
                let local = mk_local(x);
                inner1.body.open(&local);
                inner2.body.open(&local);
                let h = self.equiv_help(&mut inner1.body, &mut inner2.body)?;
                let h = mk_path_congr_abs(x, inner1.binder_type.clone(), h);
                return Some(mk_path_trans(h1, mk_path_trans(h, h2)));
            }
        }
        if let Term::Abs(_) = m1 {
            let h = self.equiv_help(m2, m1)?;
            return Some(mk_path_trans(h1, mk_path_trans(mk_path_symm(h), h2)));
        }
        if let Term::Abs(_) = m2 {
            // m1 must be unfoldable
            let h = self.unfold_head(m1)?;
            let h1 = mk_path_trans(h1, h);
            let h = self.equiv_help(m1, m2)?;
            return Some(mk_path_trans(h1, mk_path_trans(h, h2)));
        }
        let head1 = m1.head();
        let head2 = m2.head();
        if let (Term::Local(head1), Term::Local(head2)) = (head1, head2) {
            if head1 != head2 {
                return None;
            }
            let args1 = m1.args();
            let args2 = m2.args();
            if args1.len() != args2.len() {
                return None;
            }
            let mut h = mk_path_refl(Term::Local(*head1));
            for (a1, a2) in std::iter::zip(args1, args2) {
                let mut a1 = a1.clone();
                let mut a2 = a2.clone();
                let h_arg = self.equiv_help(&mut a1, &mut a2)?;
                h = mk_path_congr_app(h, h_arg);
            }
            return Some(mk_path_trans(h1, mk_path_trans(h, h2)));
        }
        if let Term::Local(_) = head1 {
            let h = self.equiv_help(m2, m1)?;
            return Some(mk_path_trans(h1, mk_path_trans(mk_path_symm(h), h2)));
        }
        if let Term::Local(_) = head2 {
            // m1 must be unfoldable
            let h = self.unfold_head(m1)?;
            let h1 = mk_path_trans(h1, h);
            let h = self.equiv_help(m1, m2)?;
            return Some(mk_path_trans(h1, mk_path_trans(h, h2)));
        }
        let (Term::Const(head1), Term::Const(head2)) = (head1, head2) else {
            panic!("holes found");
        };
        // optimization
        if head1.alpha_eq(head2) {
            let args1 = m1.args();
            let args2 = m2.args();
            if args1.len() == args2.len() {
                'args_eq: {
                    let mut h = mk_path_refl(Term::Const(head1.clone()));
                    for (a1, a2) in std::iter::zip(args1, args2) {
                        let mut a1 = a1.clone();
                        let mut a2 = a2.clone();
                        let Some(h_arg) = self.equiv_help(&mut a1, &mut a2) else {
                            break 'args_eq;
                        };
                        h = mk_path_congr_app(h, h_arg);
                    }
                    return Some(mk_path_trans(h1, mk_path_trans(h, h2)));
                }
            }
        }
        let def1 = self.def_hint(head1.name);
        let def2 = self.def_hint(head2.name);
        if def1.is_some() || def2.is_some() {
            let height1 = def1.unwrap_or(0);
            let height2 = def2.unwrap_or(0);
            match height1.cmp(&height2) {
                std::cmp::Ordering::Less => {
                    let h3 = mk_path_symm(self.unfold_head(m2).unwrap());
                    let h4 = self.equiv_help(m1, m2)?;
                    return Some(mk_path_trans(h1, mk_path_trans(h4, mk_path_trans(h3, h2))));
                }
                std::cmp::Ordering::Equal => {
                    let h3 = self.unfold_head(m1).unwrap();
                    let h4 = mk_path_symm(self.unfold_head(m2).unwrap());
                    let h5 = self.equiv_help(m1, m2)?;
                    return Some(mk_path_trans(
                        h1,
                        mk_path_trans(h3, mk_path_trans(h5, mk_path_trans(h4, h2))),
                    ));
                }
                std::cmp::Ordering::Greater => {
                    let h3 = self.unfold_head(m1).unwrap();
                    let h4 = self.equiv_help(m1, m2)?;
                    return Some(mk_path_trans(h1, mk_path_trans(h3, mk_path_trans(h4, h2))));
                }
            }
        }
        None
    }

    // Both terms must be ground
    pub fn equiv(&self, m1: &Term, m2: &Term) -> Option<Path> {
        let mut m1 = m1.clone();
        let mut m2 = m2.clone();
        self.equiv_help(&mut m1, &mut m2)
    }
}
