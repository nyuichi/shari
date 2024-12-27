//! [Type] and [Term] may be ill-formed.

use anyhow::bail;
use regex::Regex;
use std::collections::HashMap;
use std::fmt::Display;
use std::sync::atomic::AtomicUsize;
use std::sync::LazyLock;
use std::sync::{Arc, Mutex, RwLock};
use std::{mem, vec};
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Name(pub usize);

static NAME_COUNTER: AtomicUsize = AtomicUsize::new(0);
static NAME_TABLE: LazyLock<RwLock<HashMap<String, Name>>> = LazyLock::new(Default::default);
static NAME_REV_TABLE: LazyLock<Mutex<HashMap<Name, String>>> = LazyLock::new(Default::default);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            NAME_REV_TABLE
                .lock()
                .unwrap()
                .get(self)
                .unwrap_or(&self.0.to_string())
        )
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
        let mut name_table = NAME_TABLE.write().unwrap();
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

    /// Simultaneously substitute `t₁ ⋯ tₙ` for locals with names `x₁ ⋯ xₙ`.
    pub fn subst(&mut self, subst: &[(Name, &Type)]) {
        match self {
            Self::Const(_) => {}
            Self::Local(x) => {
                if let Some((_, t)) = subst.iter().copied().find(|(y, _)| y == x) {
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

    pub fn inst_hole(&mut self, subst: &[(Name, &Type)]) {
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
                    *self = (*ty).clone();
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

    pub fn contains_local(&self, name: &Name) -> bool {
        match self {
            Type::Const(_) => false,
            Type::Arrow(t) => t.dom.contains_local(name) || t.cod.contains_local(name),
            Type::App(t) => t.fun.contains_local(name) || t.arg.contains_local(name),
            Type::Local(t) => t == name,
            Type::Hole(_) => false,
        }
    }

    pub fn contains_hole(&self, name: &Name) -> bool {
        match self {
            Type::Const(_) => false,
            Type::Arrow(t) => t.dom.contains_hole(name) || t.cod.contains_hole(name),
            Type::App(t) => t.fun.contains_hole(name) || t.arg.contains_hole(name),
            Type::Local(_) => false,
            Type::Hole(n) => n == name,
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
}

/// Locally nameless representation. See [Charguéraud, 2012].
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

#[derive(Clone, Debug, Default)]
pub struct TermApp {
    pub fun: Term,
    pub arg: Term,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TermConst {
    pub name: Name,
    pub ty_args: Vec<Type>,
}

impl From<TermConst> for Term {
    fn from(value: TermConst) -> Self {
        Term::Const(Arc::new(value))
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

pub fn mk_const(name: Name, ty_args: Vec<Type>) -> Term {
    Term::Const(Arc::new(TermConst { name, ty_args }))
}

pub fn mk_local(name: Name) -> Term {
    Term::Local(name)
}

pub fn mk_var(i: usize) -> Term {
    Term::Var(i)
}

pub fn mk_fresh_hole() -> Term {
    Term::Hole(Name::fresh_with_name("X"))
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
    pub fn is_closed_in(&self, free_list: &[Name]) -> bool {
        match self {
            Self::Local(x) => free_list.contains(x),
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_closed_in(free_list),
            Self::App(inner) => {
                inner.fun.is_closed_in(free_list) && inner.arg.is_closed_in(free_list)
            }
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Local(_) => false,
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_closed(),
            Self::App(inner) => inner.fun.is_closed() && inner.arg.is_closed(),
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
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

    pub(crate) fn has_var(&self, i: usize) -> bool {
        match self {
            &Term::Var(level) => i == level,
            Term::Abs(inner) => inner.body.has_var(i + 1),
            Term::App(inner) => inner.fun.has_var(i) || inner.arg.has_var(i),
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

    pub fn contains_local_type(&self, name: &Name) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Abs(m) => m.binder_type.contains_local(name) || m.body.contains_local_type(name),
            Term::App(m) => m.fun.contains_local_type(name) || m.arg.contains_local_type(name),
            Term::Local(_) => false,
            Term::Const(m) => m.ty_args.iter().any(|t| t.contains_local(name)),
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
    pub fn unabs(&mut self) -> Vec<(Name, Type)> {
        let mut xs = vec![];
        while let Term::Abs(inner) = self {
            let &mut TermAbs {
                ref mut binder_type,
                binder_name,
                ref mut body,
            } = Arc::make_mut(inner);
            xs.push((Name::fresh_from(binder_name), mem::take(binder_type)));
            *self = mem::take(body);
        }
        self.unabs_help(&xs, 0);
        assert!(self.is_lclosed());
        xs
    }

    fn unabs_help(&mut self, xs: &[(Name, Type)], level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(i) => {
                if *i < level {
                    return;
                }
                if *i - level < xs.len() {
                    *self = mk_local(xs[xs.len() - 1 - (*i - level)].0);
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
    pub fn abs(&mut self, xs: &[(Name, Type)], allow_free: bool) -> bool {
        if !self.abs_help(xs, 0, allow_free) {
            self.unabs_help(xs, 0);
            return false;
        }
        let mut m = mem::take(self);
        for &(x, ref t) in xs.iter().rev() {
            m = mk_abs(x, t.clone(), m);
        }
        *self = m;
        true
    }

    fn abs_help(&mut self, xs: &[(Name, Type)], level: usize, allow_free: bool) -> bool {
        match self {
            Self::Local(x) => {
                for (i, (y, _)) in xs.iter().rev().enumerate() {
                    if x == y {
                        *self = Self::Var(level + i);
                        return true;
                    }
                }
                if !allow_free {
                    return false;
                }
                true
            }
            Self::Var(_) => true,
            Self::Abs(inner) => Arc::make_mut(inner)
                .body
                .abs_help(xs, level + 1, allow_free),
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.abs_help(xs, level, allow_free)
                    && inner.arg.abs_help(xs, level, allow_free)
            }
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    pub fn generalize(&mut self, xs: &[(Name, Type)]) {
        static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall").unwrap());

        self.abs_help(xs, 0, true);

        let mut m = mem::take(self);
        for &(x, ref t) in xs.iter().rev() {
            m = mk_abs(x, t.clone(), m);
            let mut c = mk_const(*FORALL, vec![t.clone()]);
            c.apply([m]);
            m = c;
        }
        *self = m;
    }

    // ∀ x₁ ⋯ xₙ, m ↦ [x₁, ⋯ , xₙ]
    // Fresh names are generated on the fly.
    // Does not check ty_args of forall.
    pub fn ungeneralize(&mut self) -> Vec<(Name, Type)> {
        let mut acc = vec![];
        while let Some((name, ty)) = self.ungeneralize1() {
            acc.push((name, ty));
        }
        acc
    }

    fn ungeneralize1(&mut self) -> Option<(Name, Type)> {
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
        let ret = (name, mem::take(binder_type));
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
            let mut m = mk_const(*IMP, vec![]);
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

    pub fn inst_hole(&mut self, subst: &[(Name, &Term)]) {
        match self {
            Term::Var(_) => {}
            Term::Local(_) => {}
            Term::Const(_) => {}
            Term::Hole(x) => {
                if let Some((_, m)) = subst.iter().copied().find(|(y, _)| y == x) {
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

    pub fn subst_type(&mut self, subst: &[(Name, &Type)]) {
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
            }
            Term::Hole(_) => {}
        }
    }

    pub fn subst(&mut self, subst: &[(Name, &Term)]) {
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
                        *self = (*m).clone();
                        break;
                    }
                }
            }
            Term::Const(_) => {}
            Term::Hole(_) => {}
        }
    }

    pub fn inst_type_hole(&mut self, subst: &[(Name, &Type)]) {
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
            }
            Term::Hole(_) => {}
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

    pub fn typed_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1 == index2,
            (Term::Abs(inner1), Term::Abs(inner2)) => {
                inner1.binder_type == inner2.binder_type && inner1.body.typed_eq(&inner2.body)
            }
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.typed_eq(&inner2.fun) && inner1.arg.typed_eq(&inner2.arg)
            }
            (Term::Local(name1), Term::Local(name2)) => name1 == name2,
            (Term::Const(inner1), Term::Const(inner2)) => {
                inner1.name == inner2.name && inner1.ty_args == inner2.ty_args
            }
            (Term::Hole(name1), Term::Hole(name2)) => name1 == name2,
            _ => false,
        }
    }

    pub fn untyped_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1 == index2,
            (Term::Abs(inner1), Term::Abs(inner2)) => inner1.body.untyped_eq(&inner2.body),
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.untyped_eq(&inner2.fun) && inner1.arg.untyped_eq(&inner2.arg)
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

    pub fn normalize(&mut self) -> Path {
        match self {
            Term::Var(_) | Term::Local(_) | Term::Const(_) | Term::Hole(_) => {
                mk_path_refl(self.clone())
            }
            Term::Abs(_) => {
                let binders = self.unabs();
                let mut p = self.normalize();
                for (name, ty) in binders.iter().rev() {
                    p = mk_path_congr_abs(*name, ty.clone(), p);
                }
                self.abs(&binders, true);
                p
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                let p1 = inner.fun.normalize();
                let p2 = inner.arg.normalize();
                let h = mk_path_congr_app(p1, p2);
                let Term::Abs(_) = &mut inner.fun else {
                    return h;
                };
                let h_redex = self.beta_reduce().unwrap();
                let h = mk_path_trans(h, h_redex);
                let h_next = self.normalize();
                mk_path_trans(h, h_next)
            }
        }
    }

    pub fn contains_local(&self, name: &Name) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Abs(m) => m.body.contains_local(name),
            Term::App(m) => m.fun.contains_local(name) || m.arg.contains_local(name),
            Term::Local(m) => m == name,
            Term::Const(_) => false,
            Term::Hole(_) => false,
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
    /// ------------------------------------------------------------ (c.{u₁ ⋯ uₙ} : τ :≡ m)
    /// Γ ⊢ delta_reduce c.{t₁ ⋯ tₙ} : c.{t₁ ⋯ tₙ} ≡ [t₁/u₁ ⋯ tₙ/uₙ]m
    /// ```
    Delta(Arc<(Name, Vec<Type>)>),
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
            Path::Delta(inner) => {
                write!(f, "{}", inner.0)?;
                if !inner.1.is_empty() {
                    let mut iter = inner.1.iter();
                    write!(f, ".{{{}", iter.next().unwrap())?;
                    for ty in iter {
                        write!(f, ", {}", ty)?;
                    }
                    write!(f, "}}")?;
                }
                Ok(())
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

pub fn mk_path_delta(name: Name, ty_args: Vec<Type>) -> Path {
    Path::Delta(Arc::new((name, ty_args)))
}

impl Path {
    pub fn is_refl(&self) -> bool {
        matches!(self, Path::Refl(_))
    }
}

#[derive(Debug, Default, Clone)]
pub struct Env {
    pub type_consts: HashMap<Name, Kind>,
    pub consts: HashMap<Name, (Vec<Name>, Type)>,
    // c.{τ₁ ⋯ tₙ} :≡ m
    pub defs: HashMap<Name, Def>,
}

#[derive(Debug, Clone)]
pub struct Def {
    pub local_types: Vec<Name>,
    pub ty: Type,
    pub target: Term,
    pub hint: usize,
}

#[derive(Debug, Default, Clone)]
pub struct LocalEnv {
    pub local_types: Vec<Name>,
    pub locals: Vec<(Name, Type)>,
    pub holes: Vec<(Name, Type)>,
}

impl LocalEnv {
    pub fn get_local(&self, name: Name) -> Option<&Type> {
        self.locals
            .iter()
            .find(|&&(n, _)| n == name)
            .map(|(_, t)| t)
    }
}

impl Env {
    /// Infer the kind of `t`. This method also checks whether arities are consistent.
    pub fn infer_kind(&self, local_env: &LocalEnv, t: &Type) -> anyhow::Result<Kind> {
        match t {
            Type::Const(name) => {
                let Some(kind) = self.type_consts.get(name) else {
                    bail!("constant type not found");
                };
                Ok(kind.clone())
            }
            Type::Arrow(inner) => {
                self.check_kind(local_env, &inner.dom, &Kind::base())?;
                self.check_kind(local_env, &inner.cod, &Kind::base())?;
                Ok(Kind::base())
            }
            Type::App(inner) => {
                let fun_kind = self.infer_kind(local_env, &inner.fun)?;
                if fun_kind.0 == 0 {
                    bail!("too many type arguments");
                }
                self.check_kind(local_env, &inner.arg, &Kind::base())?;
                Ok(Kind(fun_kind.0 - 1))
            }
            Type::Local(x) => {
                for local_type in &local_env.local_types {
                    if local_type == x {
                        return Ok(Kind::base());
                    }
                }
                bail!("unbound local type");
            }
            // no higher-kinded polymorphism
            Type::Hole(_) => Ok(Kind::base()),
        }
    }

    /// Check whether arities are consistent.
    pub fn check_kind(&self, local_env: &LocalEnv, t: &Type, kind: &Kind) -> anyhow::Result<()> {
        let my_kind = self.infer_kind(local_env, t)?;
        if &my_kind != kind {
            bail!("expected {kind}, but got {my_kind}");
        }
        Ok(())
    }

    pub fn infer_type(&self, local_env: &mut LocalEnv, m: &mut Term) -> anyhow::Result<Type> {
        let mut target = mk_fresh_type_hole();
        self.check_type(local_env, m, &mut target)?;
        Ok(target)
    }

    /// Unification-based type inference.
    /// Errors if
    /// - types mismatch,
    /// - uninstantiated meta type variables remain,
    /// - self is not locally closed,
    /// - an unknown constant is found, or
    /// - kind checking failed.
    pub fn check_type(
        &self,
        local_env: &mut LocalEnv,
        m: &mut Term,
        target: &mut Type,
    ) -> anyhow::Result<()> {
        let local_env = Infer {
            env: self,
            local_env,
            eq_set: EqSet::default(),
        };
        local_env.check_type(m, target)?;
        Ok(())
    }

    pub fn infer_conv(&self, local_env: &mut LocalEnv, path: &mut Path) -> anyhow::Result<Conv> {
        match path {
            Path::Refl(m) => {
                self.infer_type(local_env, m)?;
                Ok(Conv {
                    left: m.clone(),
                    right: m.clone(),
                })
            }
            Path::Symm(inner) => {
                let inner = Arc::make_mut(inner);
                let h = self.infer_conv(local_env, inner)?;
                Ok(Conv {
                    left: h.right,
                    right: h.left,
                })
            }
            Path::Trans(inner) => {
                let inner = Arc::make_mut(inner);
                let h1 = self.infer_conv(local_env, &mut inner.0)?;
                let h2 = self.infer_conv(local_env, &mut inner.1)?;
                if !h1.right.typed_eq(&h2.left) {
                    bail!("transitivity mismatch");
                }
                // h1.right == h2.left means the types in the both sides match.
                Ok(Conv {
                    left: h1.left,
                    right: h2.right,
                })
            }
            Path::CongrApp(inner) => {
                let inner = Arc::make_mut(inner);
                let h1 = self.infer_conv(local_env, &mut inner.0)?;
                let h2 = self.infer_conv(local_env, &mut inner.1)?;
                let mut m1 = h1.left;
                m1.apply([h2.left]);
                let mut m2 = h1.right;
                m2.apply([h2.right]);
                self.infer_type(local_env, &mut m1)?;
                Ok(Conv {
                    left: m1,
                    right: m2,
                })
            }
            Path::CongrAbs(inner) => {
                let inner = Arc::make_mut(inner);
                let (x, t, h) = (inner.0, inner.1.clone(), &mut inner.2);
                local_env.locals.push((x, t));
                let h = self.infer_conv(local_env, h)?;
                let (x, t) = local_env.locals.pop().unwrap();
                let mut m1 = h.left;
                let mut m2 = h.right;
                m1.abs(&[(x, t.clone())], true);
                m2.abs(&[(x, t.clone())], true);
                Ok(Conv {
                    left: m1,
                    right: m2,
                })
            }
            Path::Beta(m) => {
                self.infer_type(local_env, m)?;
                let m = m.clone();
                let Term::App(mut inner) = m.clone() else {
                    bail!("not a beta redex");
                };
                let inner = Arc::make_mut(&mut inner);
                let arg = &inner.arg;
                let Term::Abs(inner) = &mut inner.fun else {
                    bail!("not a beta redex");
                };
                let mut n = mem::take(&mut Arc::make_mut(inner).body);
                n.open(arg);
                Ok(Conv { left: m, right: n })
            }
            Path::Delta(inner) => {
                let (name, ty_args) = Arc::make_mut(inner);
                let Some(def) = self.defs.get(name).cloned() else {
                    bail!("definition not found: {name}");
                };
                let Def {
                    local_types,
                    mut target,
                    ty: _,
                    hint: _,
                } = def;
                if local_types.len() != ty_args.len() {
                    bail!("number of type arguments mismatch");
                }
                let mut subst = vec![];
                for (&x, t) in std::iter::zip(&local_types, ty_args.iter()) {
                    self.check_kind(local_env, t, &Kind::base())?;
                    subst.push((x, t));
                }
                target.subst_type(&subst);
                let c = mk_const(*name, ty_args.clone());
                Ok(Conv {
                    left: c,
                    right: target,
                })
            }
        }
    }

    // c.{u₁, ⋯, uₙ} := n
    // assert_eq!(m, c.{u₁, ⋯, uₙ})
    // self.delta_reduce(m);
    // assert_eq!(m, n)
    pub fn delta_reduce(&self, m: &mut Term) -> Option<Path> {
        let Term::Const(inner) = m else {
            return None;
        };
        let TermConst { name, ty_args } = Arc::make_mut(inner);
        let def = self.defs.get(name).cloned()?;
        let Def {
            local_types,
            ty: _,
            mut target,
            hint: _,
        } = def;
        if local_types.len() != ty_args.len() {
            return None;
        }
        let subst: Vec<_> = std::iter::zip(local_types.iter().copied(), ty_args.iter()).collect();
        target.subst_type(&subst);
        let path = mk_path_delta(*name, mem::take(ty_args));
        *m = target;
        Some(path)
    }

    pub fn unfold_head(&self, m: &mut Term) -> Option<Path> {
        match m {
            Term::Var(_) | Term::Local(_) | Term::Abs(_) | Term::Hole(_) => None,
            Term::Const(_) => self.delta_reduce(m),
            Term::App(inner) => {
                let TermApp { fun, arg } = Arc::make_mut(inner);
                let h_fun = self.unfold_head(fun)?;
                let h_arg = mk_path_refl(arg.clone());
                Some(mk_path_congr_app(h_fun, h_arg))
            }
        }
    }

    pub fn def_hint(&self, name: Name) -> Option<usize> {
        let def = self.defs.get(&name)?;
        Some(def.hint + 1)
    }

    fn equiv_help(&self, m1: &mut Term, m2: &mut Term) -> Option<Path> {
        if m1.untyped_eq(m2) {
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
            if m1.untyped_eq(m2) {
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
        if head1 == head2 {
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

struct Infer<'a> {
    env: &'a Env,
    local_env: &'a mut LocalEnv,
    eq_set: EqSet,
}

impl<'a> Infer<'a> {
    fn check_type(mut self, m: &mut Term, target: &mut Type) -> anyhow::Result<()> {
        self.env.check_kind(self.local_env, target, &Kind::base())?;
        self.check_type_help(m, target)?;
        let unifier = self.eq_set.solve()?;
        unifier.apply_term(m)?;
        unifier.apply_type(target)?;
        Ok(())
    }

    fn check_type_help(&mut self, m: &mut Term, target: &Type) -> anyhow::Result<()> {
        match m {
            Term::Local(name) => {
                for (local, ty) in &self.local_env.locals {
                    if local == name {
                        self.eq_set.unify(ty.clone(), target.clone());
                        return Ok(());
                    }
                }
                bail!("unknown local variable");
            }
            Term::Hole(name) => {
                for (local, ty) in &self.local_env.holes {
                    if local == name {
                        self.eq_set.unify(ty.clone(), target.clone());
                        return Ok(());
                    }
                }
                bail!("unknown meta variable");
            }
            Term::Var(_) => {
                bail!("term not locally closed");
            }
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                self.env
                    .check_kind(self.local_env, &inner.binder_type, &Kind::base())?;
                let x = Name::fresh();
                let t = inner.binder_type.clone();
                self.local_env.locals.push((x, t));
                inner.body.open(&mk_local(x));
                let body_ty = mk_fresh_type_hole();
                self.check_type_help(&mut inner.body, &body_ty)?;
                inner.body.close(x);
                self.local_env.locals.pop();
                self.eq_set.unify(
                    mk_type_arrow(inner.binder_type.clone(), body_ty),
                    target.clone(),
                );
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                let fun_ty = mk_fresh_type_hole();
                self.check_type_help(&mut inner.fun, &fun_ty)?;
                let arg_ty = mk_fresh_type_hole();
                self.check_type_help(&mut inner.arg, &arg_ty)?;
                self.eq_set
                    .unify(fun_ty, mk_type_arrow(arg_ty, target.clone()));
            }
            Term::Const(inner) => {
                let Some((tv, ty)) = self.env.consts.get(&inner.name) else {
                    bail!("constant not found");
                };
                if tv.len() != inner.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                for t in &inner.ty_args {
                    self.env.check_kind(self.local_env, t, &Kind::base())?;
                }
                let mut ty = ty.clone();
                ty.subst(&std::iter::zip(tv.iter().copied(), &inner.ty_args).collect::<Vec<_>>());
                self.eq_set.unify(ty, target.clone());
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
struct EqSet {
    equations: Vec<(Type, Type)>,
    parents: HashMap<Name, Type>,
}

impl EqSet {
    fn unify(&mut self, t1: Type, t2: Type) {
        self.equations.push((t1, t2));
    }

    fn find(&mut self, ty: Type) -> Type {
        let Type::Hole(name) = ty else {
            return ty;
        };
        let Some(ty) = self.parents.get(&name).cloned() else {
            return ty;
        };
        // During calling `find` parents[name] will NOT be updated
        // because a unification solution is not cyclic.
        let ty = self.find(ty);
        self.parents.insert(name, ty.clone());
        ty
    }

    fn solve(mut self) -> anyhow::Result<TypeUnifier> {
        while let Some((t1, t2)) = self.equations.pop() {
            let t1 = self.find(t1);
            let t2 = self.find(t2);
            if t1 == t2 {
                continue;
            }
            match (t1, t2) {
                (Type::Arrow(inner1), Type::Arrow(inner2)) => {
                    let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                    let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                    self.unify(inner1.dom, inner2.dom);
                    self.unify(inner1.cod, inner2.cod);
                }
                (Type::App(inner1), Type::App(inner2)) => {
                    // Since we have no higher-kinded polymorphism, holes will only be typed as `Type`,
                    // it is illegal to match the following two types:
                    //  ?M₁ t =?= ?M₂ t₁ t₂
                    // But such a case is checked and ruled out in the kind checking phase that runs before
                    // this unificaiton phase.
                    let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                    let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                    self.unify(inner1.fun, inner2.fun);
                    self.unify(inner1.arg, inner2.arg);
                }
                (Type::Hole(name), t) | (t, Type::Hole(name)) => {
                    self.parents.insert(name, t);
                }
                (t1, t2) => {
                    bail!("type mismatch: {t1} =/= {t2}");
                }
            }
        }
        Ok(TypeUnifier(self.parents))
    }
}

struct TypeUnifier(HashMap<Name, Type>);

impl TypeUnifier {
    fn apply_type(&self, t: &mut Type) -> anyhow::Result<()> {
        match t {
            Type::Const(_) => {}
            Type::Arrow(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_type(&mut inner.dom)?;
                self.apply_type(&mut inner.cod)?;
            }
            Type::App(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_type(&mut inner.fun)?;
                self.apply_type(&mut inner.arg)?;
            }
            Type::Local(_) => {}
            Type::Hole(name) => {
                let Some(ty) = self.0.get(name) else {
                    bail!("uninstantiated meta type variable");
                };
                *t = ty.clone();
                self.apply_type(t)?;
            }
        }
        Ok(())
    }

    fn apply_term(&self, m: &mut Term) -> anyhow::Result<()> {
        match m {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_type(&mut inner.binder_type)?;
                self.apply_term(&mut inner.body)?;
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_term(&mut inner.fun)?;
                self.apply_term(&mut inner.arg)?;
            }
            Term::Local(_) | Term::Hole(_) => {}
            Term::Const(inner) => {
                let inner = Arc::make_mut(inner);
                for ty_arg in &mut inner.ty_args {
                    self.apply_type(ty_arg)?;
                }
            }
        }
        Ok(())
    }
}
