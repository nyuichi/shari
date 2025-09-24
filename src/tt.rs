use regex::Regex;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::iter::zip;
use std::sync::LazyLock;
use std::sync::atomic::AtomicUsize;
use std::sync::{Arc, Mutex};
use std::{mem, vec};
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Name(usize);

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
    #[non_exhaustive]
    Const(Arc<TypeConst>),
    #[non_exhaustive]
    Arrow(Arc<TypeArrow>),
    #[non_exhaustive]
    App(Arc<TypeApp>),
    #[non_exhaustive]
    Local(Arc<TypeLocal>),
    #[non_exhaustive]
    Hole(Arc<TypeHole>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeConst {
    pub name: Name,
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeLocal {
    pub name: Name,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeHole {
    pub name: Name,
}

impl Default for Type {
    fn default() -> Self {
        mk_type_hole(Name::default())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const TYPE_PREC_ARROW: u8 = 0;
        const TYPE_PREC_APP: u8 = 1;
        const TYPE_PREC_ATOM: u8 = 2;

        fn fmt_type(ty: &Type, f: &mut std::fmt::Formatter<'_>, prec: u8) -> std::fmt::Result {
            match ty {
                Type::Const(inner) => write!(f, "{}", inner.name),
                Type::Arrow(inner) => {
                    let needs_paren = prec > TYPE_PREC_ARROW;
                    if needs_paren {
                        write!(f, "(")?;
                    }
                    fmt_type(&inner.dom, f, TYPE_PREC_APP)?;
                    write!(f, " → ")?;
                    fmt_type(&inner.cod, f, TYPE_PREC_ARROW)?;
                    if needs_paren {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
                Type::App(inner) => {
                    let needs_paren = prec > TYPE_PREC_APP;
                    if needs_paren {
                        write!(f, "(")?;
                    }
                    fmt_type(&inner.fun, f, TYPE_PREC_APP)?;
                    write!(f, " ")?;
                    fmt_type(&inner.arg, f, TYPE_PREC_ATOM)?;
                    if needs_paren {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
                Type::Local(inner) => write!(f, "${}", inner.name),
                Type::Hole(inner) => write!(f, "?{}", inner.name),
            }
        }

        fmt_type(self, f, TYPE_PREC_ARROW)
    }
}

#[inline]
pub fn mk_type_arrow(dom: Type, cod: Type) -> Type {
    Type::Arrow(Arc::new(TypeArrow { dom, cod }))
}

#[inline]
pub fn mk_fresh_type_hole() -> Type {
    mk_type_hole(Name::fresh_with_name("α"))
}

#[inline]
pub fn mk_type_hole(name: Name) -> Type {
    Type::Hole(Arc::new(TypeHole { name }))
}

#[inline]
pub fn mk_type_local(name: Name) -> Type {
    Type::Local(Arc::new(TypeLocal { name }))
}

#[inline]
pub fn mk_type_const(name: Name) -> Type {
    Type::Const(Arc::new(TypeConst { name }))
}

#[inline]
pub fn mk_type_app(fun: Type, arg: Type) -> Type {
    Type::App(Arc::new(TypeApp { fun, arg }))
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
            let cod = mem::take(self);
            *self = mk_type_arrow(item, cod);
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
            let fun = mem::take(self);
            *self = mk_type_app(fun, arg);
        }
    }

    #[allow(unused)]
    #[deprecated(note = "left for future use")]
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
                let name = x.name;
                if let Some((_, t)) = subst.iter().find(|(y, _)| *y == name) {
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
            Type::Local(t) => t.name == name,
            Type::Hole(_) => false,
        }
    }

    pub fn contains_hole(&self, name: Name) -> bool {
        match self {
            Type::Const(_) => false,
            Type::Arrow(t) => t.dom.contains_hole(name) || t.cod.contains_hole(name),
            Type::App(t) => t.fun.contains_hole(name) || t.arg.contains_hole(name),
            Type::Local(_) => false,
            Type::Hole(n) => n.name == name,
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
            Type::Hole(pattern) => {
                let pattern = pattern.name;
                if let Some((_, t)) = subst.iter().find(|&&(x, _)| x == pattern) {
                    self.matches_help(&t.clone(), subst)
                } else {
                    subst.push((pattern, self.clone()));
                    true
                }
            }
        }
    }

    fn holes(&self, buf: &mut Vec<Name>) {
        match self {
            Type::Const(_) => {}
            Type::Arrow(inner) => {
                inner.dom.holes(buf);
                inner.cod.holes(buf);
            }
            Type::App(inner) => {
                inner.fun.holes(buf);
                inner.arg.holes(buf);
            }
            Type::Local(_) => {}
            Type::Hole(name) => {
                buf.push(name.name);
            }
        }
    }

    pub fn inst(&mut self, subst: &[(Name, Type)]) {
        match self {
            Self::Const(_) => {}
            Self::Local(_) => {}
            Self::Hole(x) => {
                let name = x.name;
                if let Some((_, t)) = subst.iter().find(|(y, _)| *y == name) {
                    *self = t.clone();
                }
            }
            Self::Arrow(inner) => {
                let inner = Arc::make_mut(inner);
                inner.dom.inst(subst);
                inner.cod.inst(subst);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.inst(subst);
                inner.arg.inst(subst);
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

impl Display for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        for t in &self.args {
            write!(f, " {}", t)?;
        }
        Ok(())
    }
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

    pub fn holes(&self) -> Vec<Name> {
        let mut holes = vec![];
        for t in &self.args {
            t.holes(&mut holes);
        }
        holes
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
    pub name: Name,
    pub ty_args: Vec<Type>,
    pub args: Vec<Instance>,
}

impl Display for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instance::Local(c) => write!(f, "${}", c),
            Instance::Global(i) => {
                write!(f, "{}", i.name)?;
                if !i.ty_args.is_empty() {
                    write!(f, ".{{")?;
                    let mut first = true;
                    for t in &i.ty_args {
                        if !first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{t}")?;
                        first = false;
                    }
                    write!(f, "}}")?;
                }
                if !i.args.is_empty() {
                    write!(f, ".[")?;
                    let mut first = true;
                    for arg in &i.args {
                        if !first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{arg}")?;
                        first = false;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            Instance::Hole(name) => write!(f, "?{name}"),
        }
    }
}

pub fn mk_instance_local(class: Class) -> Instance {
    Instance::Local(class)
}

pub fn mk_instance_global(name: Name, ty_args: Vec<Type>, args: Vec<Instance>) -> Instance {
    Instance::Global(Arc::new(InstanceGlobal {
        name,
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

    pub fn is_hole(&self) -> bool {
        matches!(self, Instance::Hole(_))
    }
}

/// Locally nameless representation. See [Charguéraud, 2012].
/// Use syn's convention [https://docs.rs/syn/latest/syn/enum.Expr.html#syntax-tree-enums].
#[derive(Clone, Debug)]
pub enum Term {
    #[non_exhaustive]
    Var(Arc<TermVar>),
    #[non_exhaustive]
    Abs(Arc<TermAbs>),
    #[non_exhaustive]
    App(Arc<TermApp>),
    #[non_exhaustive]
    Local(Arc<TermLocal>),
    #[non_exhaustive]
    Const(Arc<TermConst>),
    #[non_exhaustive]
    Hole(Arc<TermHole>),
}

#[derive(Clone, Debug)]
pub struct TermVar {
    pub index: usize,
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
pub struct TermLocal {
    pub name: Name,
}

#[derive(Clone, Debug)]
pub struct TermConst {
    pub name: Name,
    pub ty_args: Vec<Type>,
    pub instances: Vec<Instance>,
}

#[derive(Clone, Debug)]
pub struct TermHole {
    pub name: Name,
}

impl From<TermConst> for Term {
    fn from(value: TermConst) -> Self {
        mk_const(value.name, value.ty_args, value.instances)
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
        mk_var(usize::MAX)
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const TERM_PREC_LAM: u8 = 0;
        const TERM_PREC_APP: u8 = 1;
        const TERM_PREC_ATOM: u8 = 2;

        fn fmt_term(term: &Term, f: &mut std::fmt::Formatter<'_>, prec: u8) -> std::fmt::Result {
            match term {
                Term::Var(inner) => write!(f, "#{}", inner.index),
                Term::Abs(inner) => {
                    let needs_paren = prec > TERM_PREC_LAM;
                    if needs_paren {
                        write!(f, "(")?;
                    }
                    write!(f, "λ{}:{}. ", inner.binder_name, inner.binder_type)?;
                    fmt_term(&inner.body, f, TERM_PREC_LAM)?;
                    if needs_paren {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
                Term::App(inner) => {
                    let needs_paren = prec > TERM_PREC_APP;
                    if needs_paren {
                        write!(f, "(")?;
                    }
                    fmt_term(&inner.fun, f, TERM_PREC_APP)?;
                    write!(f, " ")?;
                    fmt_term(&inner.arg, f, TERM_PREC_ATOM)?;
                    if needs_paren {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
                Term::Local(inner) => write!(f, "${}", inner.name),
                Term::Const(inner) => {
                    write!(f, "{}", inner.name)?;
                    if !inner.ty_args.is_empty() {
                        write!(f, ".{{")?;
                        for (idx, t) in inner.ty_args.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{t}")?;
                        }
                        write!(f, "}}")?;
                    }
                    if !inner.instances.is_empty() {
                        write!(f, ".[")?;
                        for (idx, i) in inner.instances.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{i}")?;
                        }
                        write!(f, "]")?;
                    }
                    Ok(())
                }
                Term::Hole(inner) => write!(f, "?{}", inner.name),
            }
        }

        fmt_term(self, f, TERM_PREC_LAM)
    }
}

#[inline]
pub fn mk_abs(binder_name: Name, binder_type: Type, body: Term) -> Term {
    Term::Abs(Arc::new(TermAbs {
        binder_type,
        binder_name,
        body,
    }))
}

#[inline]
pub fn mk_app(fun: Term, arg: Term) -> Term {
    Term::App(Arc::new(TermApp { fun, arg }))
}

#[inline]
pub fn mk_var(index: usize) -> Term {
    Term::Var(Arc::new(TermVar { index }))
}

#[inline]
pub fn mk_const(name: Name, ty_args: Vec<Type>, instances: Vec<Instance>) -> Term {
    Term::Const(Arc::new(TermConst {
        name,
        ty_args,
        instances,
    }))
}

#[inline]
pub fn mk_local(name: Name) -> Term {
    Term::Local(Arc::new(TermLocal { name }))
}

#[inline]
pub fn mk_fresh_hole() -> Term {
    mk_hole(Name::fresh())
}

#[inline]
pub fn mk_hole(name: Name) -> Term {
    Term::Hole(Arc::new(TermHole { name }))
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
    /// TODO:
    /// - open をもっと軽くする。Term の全ての variant に bound を持たせて、その値を見て不必要な clone を行わないようにする。
    /// - 結果的に &mut Term を mod の外で触らなくて良くなるはずなので、crate 全体では Term を clone しまくる実装になるはず。(全部 pass by value になる。) なので大工事になる。
    pub fn open(&mut self, x: &Term) {
        self.open_at(x, 0)
    }

    fn open_at(&mut self, x: &Term, level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(inner) => {
                if inner.index == level {
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
    /// TODO: close も　is_closed というフィールドを Term に持たせてそれを使うようにする。そもそも今関数は pub じゃなくてよくなるはず。
    #[allow(unused)]
    #[deprecated(note = "left for future use")]
    pub fn close(&mut self, name: Name) {
        assert!(self.is_lclosed());
        self.close_at(name, 0)
    }

    fn close_at(&mut self, name: Name, level: usize) {
        match self {
            Self::Local(inner) => {
                if inner.name == name {
                    *self = mk_var(level);
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
            Self::Local(inner) => !free_list.contains(&inner.name),
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
            Self::Local(inner) => free_list.contains(&inner.name),
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_supported_by(free_list),
            Self::App(inner) => {
                inner.fun.is_supported_by(free_list) && inner.arg.is_supported_by(free_list)
            }
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    #[allow(unused)]
    #[deprecated(note = "left for future use")]
    pub fn is_closed(&self) -> bool {
        self.is_supported_by(&[])
    }

    pub fn is_lclosed(&self) -> bool {
        self.is_lclosed_at(0)
    }

    fn is_lclosed_at(&self, level: usize) -> bool {
        match self {
            Self::Local(_) => true,
            Self::Var(inner) => inner.index < level,
            Self::Abs(inner) => inner.body.is_lclosed_at(level + 1),
            Self::App(inner) => inner.fun.is_lclosed_at(level) && inner.arg.is_lclosed_at(level),
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    #[allow(unused)]
    #[deprecated(note = "left for future use")]
    pub fn is_body(&self) -> bool {
        self.is_lclosed_at(1)
    }

    pub fn contains_var(&self, i: usize) -> bool {
        match self {
            Term::Var(inner) => i == inner.index,
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

    #[allow(unused)]
    #[deprecated(note = "left for future use")]
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
                if *a == arg.name {
                    return None;
                }
            }
            arg_locals.push(arg.name);
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
    #[allow(unused)]
    #[deprecated(note = "left for future use")]
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
            Self::Var(inner) => {
                let index = inner.index;
                if index < level {
                    return;
                }
                let offset = index - level;
                if offset < xs.len() {
                    *self = mk_local(xs[xs.len() - 1 - offset].name);
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
            Self::Local(inner) => {
                let name = inner.name;
                for (i, x) in xs.iter().rev().enumerate() {
                    if name == x.name {
                        *self = mk_var(level + i);
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

    pub fn count_forall(&self) -> usize {
        static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall").unwrap());

        let mut count = 0;
        let mut m = self;
        loop {
            let Term::App(app) = m else {
                break;
            };
            let app = app.as_ref();
            let Term::Const(head) = &app.fun else {
                break;
            };
            if head.name != *FORALL {
                break;
            }
            let Term::Abs(abs) = &app.arg else {
                break;
            };
            let body = &abs.as_ref().body;
            count += 1;
            m = body;
        }

        count
    }

    // TODO: proof.rsにstruct Prop { inner: Term }を用意して、Propにgeneralizeとかguardとかcount_forallとかを実装したい。
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

    pub fn ungeneralize1(&mut self) -> Option<Parameter> {
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

    pub fn unguard1(&mut self) -> Option<Term> {
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
            Term::Local(inner) => {
                for (x, m) in subst {
                    if inner.name == *x {
                        *self = m.clone();
                        break;
                    }
                }
            }
            Term::Const(_) => {}
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

    // TODO: こっちを Eq の impl にする。
    pub fn alpha_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1.index == index2.index,
            (Term::Abs(inner1), Term::Abs(inner2)) => {
                inner1.binder_type == inner2.binder_type && inner1.body.alpha_eq(&inner2.body)
            }
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.alpha_eq(&inner2.fun) && inner1.arg.alpha_eq(&inner2.arg)
            }
            (Term::Local(name1), Term::Local(name2)) => name1.name == name2.name,
            (Term::Const(inner1), Term::Const(inner2)) => inner1.alpha_eq(inner2),
            (Term::Hole(name1), Term::Hole(name2)) => name1.name == name2.name,
            _ => false,
        }
    }

    pub fn maybe_alpha_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1.index == index2.index,
            (Term::Abs(inner1), Term::Abs(inner2)) => inner1.body.maybe_alpha_eq(&inner2.body),
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.maybe_alpha_eq(&inner2.fun) && inner1.arg.maybe_alpha_eq(&inner2.arg)
            }
            (Term::Local(name1), Term::Local(name2)) => name1.name == name2.name,
            (Term::Const(inner1), Term::Const(inner2)) => inner1.name == inner2.name,
            (Term::Hole(name1), Term::Hole(name2)) => name1.name == name2.name,
            _ => false,
        }
    }

    fn beta_reduce(&mut self) -> bool {
        let Term::App(inner) = self else {
            return false;
        };
        let TermApp { fun, arg } = Arc::make_mut(inner);
        let Term::Abs(inner) = fun else {
            return false;
        };
        let TermAbs {
            binder_type: _,
            binder_name: _,
            body,
        } = Arc::make_mut(inner);
        body.open(arg);
        *self = mem::take(body);
        assert!(self.is_lclosed());
        true
    }

    pub fn whnf(&mut self) -> bool {
        let mut changed = false;
        loop {
            match self {
                Term::Var(_) | Term::Local(_) | Term::Const(_) | Term::Hole(_) | Term::Abs(_) => {
                    return changed;
                }
                Term::App(inner) => {
                    let inner = Arc::make_mut(inner);
                    if inner.fun.whnf() {
                        changed = true;
                    }
                    if self.beta_reduce() {
                        changed = true;
                        continue;
                    }
                    return changed;
                }
            }
        }
    }

    pub fn contains_local(&self, name: Name) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Abs(m) => m.body.contains_local(name),
            Term::App(m) => m.fun.contains_local(name) || m.arg.contains_local(name),
            Term::Local(inner) => inner.name == name,
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
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub target: Term,
    // equal to height(target)
    pub height: usize,
}

#[derive(Debug, Clone)]
pub struct Kappa;

#[derive(Debug, Clone)]
pub struct ClassInstance {
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
    pub kappa_table: &'a HashMap<Name, Kappa>,
    pub class_predicate_table: &'a HashMap<Name, ClassType>,
    pub class_instance_table: &'a HashMap<Name, ClassInstance>,
}

impl Env<'_> {
    pub fn infer_kind(&self, local_env: &LocalEnv, t: &Type) -> Kind {
        match t {
            Type::Const(name) => self
                .type_const_table
                .get(&name.name)
                .unwrap_or_else(|| panic!("unknown type constant: {:?}", name.name))
                .clone(),
            Type::Arrow(inner) => {
                let dom_kind = self.infer_kind(local_env, &inner.dom);
                if dom_kind != Kind::base() {
                    panic!(
                        "arrow domain must have base kind, but got {:?} for {:?}",
                        dom_kind, inner.dom
                    );
                }
                let cod_kind = self.infer_kind(local_env, &inner.cod);
                if cod_kind != Kind::base() {
                    panic!(
                        "arrow codomain must have base kind, but got {:?} for {:?}",
                        cod_kind, inner.cod
                    );
                }
                Kind::base()
            }
            Type::App(inner) => {
                let fun_kind = self.infer_kind(local_env, &inner.fun);
                if fun_kind.0 == 0 {
                    panic!("cannot apply a term of base kind: {:?}", inner.fun);
                }
                let arg_kind = self.infer_kind(local_env, &inner.arg);
                if arg_kind != Kind::base() {
                    panic!(
                        "type application argument must have base kind, but got {:?} for {:?}",
                        arg_kind, inner.arg
                    );
                }
                Kind(fun_kind.0 - 1)
            }
            Type::Local(x) => {
                for local_type in &local_env.local_types {
                    if *local_type == x.name {
                        return Kind::base();
                    }
                }
                panic!("unbound local type: {:?}", x.name);
            }
            Type::Hole(_) => panic!("cannot infer kind of a hole"),
        }
    }

    pub fn check_kind(&self, local_env: &LocalEnv, t: &Type, kind: Kind) {
        let inferred = self.infer_kind(local_env, t);
        if inferred != kind {
            panic!(
                "kind mismatch: expected {:?}, got {:?} for type {:?}",
                kind, inferred, t
            );
        }
    }

    pub fn check_wft(&self, local_env: &LocalEnv, t: &Type) {
        self.check_kind(local_env, t, Kind::base());
    }

    pub fn check_wfc(&self, local_env: &LocalEnv, c: &Class) {
        let class_type = self
            .class_predicate_table
            .get(&c.name)
            .unwrap_or_else(|| panic!("unknown class predicate: {:?}", c.name));
        if class_type.arity != c.args.len() {
            panic!(
                "class {:?} expects {} arguments but got {}",
                c.name,
                class_type.arity,
                c.args.len()
            );
        }
        for arg in &c.args {
            self.check_wft(local_env, arg);
        }
    }

    pub fn infer_class(&self, local_env: &LocalEnv, i: &Instance) -> Class {
        match i {
            Instance::Local(i) => {
                for local_class in &local_env.local_classes {
                    if local_class == i {
                        return i.clone();
                    }
                }
                panic!("unknown local class instance: {:?}", i);
            }
            Instance::Global(i) => {
                let InstanceGlobal {
                    name,
                    ty_args,
                    args,
                } = &**i;
                let ClassInstance {
                    local_types,
                    local_classes,
                    target,
                    method_table: _,
                } = self
                    .class_instance_table
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown class instance: {:?}", name));
                if local_types.len() != ty_args.len() {
                    panic!(
                        "class instance {:?} expects {} type arguments but got {}",
                        name,
                        local_types.len(),
                        ty_args.len()
                    );
                }
                for ty_arg in ty_args {
                    self.check_wft(local_env, ty_arg);
                }
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, ty_args) {
                    type_subst.push((x, t.clone()));
                }
                if local_classes.len() != args.len() {
                    panic!(
                        "class instance {:?} expects {} class arguments but got {}",
                        name,
                        local_classes.len(),
                        args.len()
                    );
                }
                for (local_class, arg) in zip(local_classes, args) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    self.check_class(local_env, arg, &local_class);
                }
                let mut target = target.clone();
                target.subst(&type_subst);
                target
            }
            Instance::Hole(_) => panic!("cannot infer class of a hole"),
        }
    }

    // t is trusted
    pub fn check_class(&self, local_env: &LocalEnv, i: &Instance, class: &Class) {
        let inferred = self.infer_class(local_env, i);
        if inferred != *class {
            panic!("class mismatch: expected {:?}, got {:?}", class, inferred);
        }
    }

    pub fn infer_type(&self, local_env: &mut LocalEnv, m: &Term) -> Type {
        match m {
            Term::Var(_) => panic!("cannot infer type of a raw variable"),
            Term::Abs(m) => {
                self.check_wft(local_env, &m.binder_type);
                let x = Parameter {
                    name: Name::fresh_from(m.binder_name),
                    ty: m.binder_type.clone(),
                };
                let mut n = m.body.clone();
                n.open(&mk_local(x.name));
                local_env.locals.push(x);
                let target = self.infer_type(local_env, &n);
                let x = local_env.locals.pop().unwrap();
                mk_type_arrow(x.ty, target)
            }
            Term::App(m) => {
                let fun_ty = self.infer_type(local_env, &m.fun);
                match fun_ty {
                    Type::Arrow(fun_ty) => {
                        self.check_type(local_env, &m.arg, &fun_ty.dom);
                        fun_ty.cod.clone()
                    }
                    _ => panic!(
                        "expected a function type but got {:?} for term {:?}",
                        fun_ty, m.fun
                    ),
                }
            }
            Term::Local(inner) => {
                for y in local_env.locals.iter().rev() {
                    if inner.name == y.name {
                        return y.ty.clone();
                    }
                }
                panic!("unbound local term: {:?}", inner.name);
            }
            Term::Const(m) => {
                let Const {
                    local_types,
                    local_classes,
                    ty,
                } = self
                    .const_table
                    .get(&m.name)
                    .unwrap_or_else(|| panic!("unknown constant: {:?}", m.name));
                if local_types.len() != m.ty_args.len() {
                    panic!(
                        "constant {:?} expects {} type arguments but got {}",
                        m.name,
                        local_types.len(),
                        m.ty_args.len()
                    );
                }
                for ty_arg in &m.ty_args {
                    self.check_wft(local_env, ty_arg);
                }
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, &m.ty_args) {
                    type_subst.push((x, t.clone()));
                }
                if local_classes.len() != m.instances.len() {
                    panic!(
                        "constant {:?} expects {} class arguments but got {}",
                        m.name,
                        local_classes.len(),
                        m.instances.len()
                    );
                }
                for (local_class, instance) in zip(local_classes, &m.instances) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    self.check_wfc(local_env, &local_class);
                    self.check_class(local_env, instance, &local_class);
                }
                let mut ty = ty.clone();
                ty.subst(&type_subst);
                ty
            }
            Term::Hole(_) => panic!("cannot infer type of a hole"),
        }
    }

    pub fn check_type(&self, local_env: &mut LocalEnv, m: &Term, target: &Type) {
        let inferred = self.infer_type(local_env, m);
        if inferred != *target {
            panic!(
                "type mismatch: expected {:?}, got {:?} for term {:?}",
                target, inferred, m
            );
        }
    }

    pub fn check_wff(&self, local_env: &mut LocalEnv, m: &Term) {
        self.check_type(local_env, m, &mk_type_prop());
    }

    // c.{u₁, ⋯, uₙ} := n
    // assert_eq!(m, c.{u₁, ⋯, uₙ})
    // self.delta_reduce(m);
    // assert_eq!(m, n)
    fn delta_reduce(&self, m: &mut Term) -> bool {
        let Term::Const(n) = m else {
            return false;
        };
        let Some(Delta {
            local_types,
            local_classes,
            target,
            height: _,
        }) = self.delta_table.get(&n.name)
        else {
            return false;
        };
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
        true
    }

    fn kappa_reduce(&self, m: &mut Term) -> bool {
        let Term::Const(n) = m else {
            return false;
        };
        if self.kappa_table.get(&n.name).is_none() {
            return false;
        }
        if n.instances.is_empty() {
            return false;
        }
        let Instance::Global(recv) = &n.instances[0] else {
            return false;
        };
        let InstanceGlobal {
            name,
            ty_args,
            args,
        } = &**recv;
        // assert_eq!(ty_args, &n.ty_args);
        // assert_eq!(&args[..], &n.instances[1..]);
        let Some(ClassInstance {
            local_types,
            local_classes,
            target: _,
            method_table,
        }) = self.class_instance_table.get(name)
        else {
            return false;
        };
        let Some(target) = method_table.get(&n.name) else {
            return false;
        };
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
        true
    }

    pub fn unfold_head(&self, m: &mut Term) -> bool {
        match m {
            Term::Var(_) | Term::Local(_) | Term::Abs(_) | Term::Hole(_) => false,
            Term::Const(_) => self.delta_reduce(m) || self.kappa_reduce(m),
            Term::App(m) => {
                let TermApp { fun, .. } = Arc::make_mut(m);
                self.unfold_head(fun)
            }
        }
    }

    pub fn delta_height(&self, name: Name) -> usize {
        match self.delta_table.get(&name) {
            Some(delta) => delta.height + 1,
            None => 0,
        }
    }

    // NB: does not take kappa-reductions into account.
    pub fn height(&self, m: &Term) -> usize {
        match m {
            Term::Var(_) => 0,
            Term::Abs(m) => self.height(&m.body),
            Term::App(m) => std::cmp::max(self.height(&m.fun), self.height(&m.arg)),
            Term::Local(_) => 0,
            Term::Const(m) => self.delta_height(m.name),
            Term::Hole(_) => 0,
        }
    }

    pub fn has_kappa(&self, name: Name) -> bool {
        self.kappa_table.contains_key(&name)
    }

    pub fn has_delta(&self, name: Name) -> bool {
        self.delta_table.contains_key(&name)
    }

    fn equiv_help(&self, m1: &mut Term, m2: &mut Term) -> bool {
        if m1.alpha_eq(m2) {
            return true;
        }
        if let (Term::Abs(inner1), Term::Abs(inner2)) = (&mut *m1, &mut *m2) {
            let inner1 = Arc::make_mut(inner1);
            let inner2 = Arc::make_mut(inner2);
            let x = Name::fresh();
            let local = mk_local(x);
            inner1.body.open(&local);
            inner2.body.open(&local);
            return self.equiv_help(&mut inner1.body, &mut inner2.body);
        }

        let reduced1 = m1.whnf();
        let reduced2 = m2.whnf();
        if reduced1 || reduced2 {
            if m1.alpha_eq(m2) {
                return true;
            }
            if let (Term::Abs(inner1), Term::Abs(inner2)) = (&mut *m1, &mut *m2) {
                let inner1 = Arc::make_mut(inner1);
                let inner2 = Arc::make_mut(inner2);
                let x = Name::fresh();
                let local = mk_local(x);
                inner1.body.open(&local);
                inner2.body.open(&local);
                // TODO: use loop
                return self.equiv_help(&mut inner1.body, &mut inner2.body);
            }
        }

        if matches!(m1, Term::Abs(_)) {
            return self.equiv_help(m2, m1);
        }
        if matches!(m2, Term::Abs(_)) {
            // m1 must be unfoldable
            if !self.unfold_head(m1) {
                return false;
            }
            return self.equiv_help(m1, m2);
        }

        let head1 = m1.head();
        let head2 = m2.head();
        if let (Term::Local(head1), Term::Local(head2)) = (head1, head2) {
            if head1.name != head2.name {
                return false;
            }
            let args1 = m1.args();
            let args2 = m2.args();
            if args1.len() != args2.len() {
                return false;
            }
            for (a1, a2) in std::iter::zip(args1, args2) {
                let mut a1 = a1.clone();
                let mut a2 = a2.clone();
                if !self.equiv_help(&mut a1, &mut a2) {
                    return false;
                }
            }
            return true;
        }
        if matches!(head1, Term::Local(_)) {
            return self.equiv_help(m2, m1);
        }
        if matches!(head2, Term::Local(_)) {
            // m1 must be unfoldable
            if !self.unfold_head(m1) {
                return false;
            }
            return self.equiv_help(m1, m2);
        }

        let (Term::Const(head1_inner), Term::Const(head2_inner)) = (head1, head2) else {
            panic!("holes found");
        };
        // optimization
        if head1_inner.alpha_eq(head2_inner) {
            let args1 = m1.args();
            let args2 = m2.args();
            if args1.len() == args2.len() {
                let mut all_equiv = true;
                for (a1, a2) in std::iter::zip(args1, args2) {
                    let mut a1 = a1.clone();
                    let mut a2 = a2.clone();
                    if !self.equiv_help(&mut a1, &mut a2) {
                        all_equiv = false;
                        break;
                    }
                }
                if all_equiv {
                    return true;
                }
            }
        }

        if self.has_kappa(head1_inner.name) || self.has_kappa(head2_inner.name) {
            if self.unfold_head(m1) {
                return self.equiv_help(m1, m2);
            }
            if self.unfold_head(m2) {
                return self.equiv_help(m1, m2);
            }
            return false;
        }

        let height1 = self.delta_height(head1_inner.name);
        let height2 = self.delta_height(head2_inner.name);
        if height1 == 0 && height2 == 0 {
            return false;
        }

        match height1.cmp(&height2) {
            std::cmp::Ordering::Less => {
                if !self.unfold_head(m2) {
                    return false;
                }
                self.equiv_help(m1, m2)
            }
            std::cmp::Ordering::Equal => {
                if !self.unfold_head(m1) {
                    return false;
                }
                if !self.unfold_head(m2) {
                    return false;
                }
                self.equiv_help(m1, m2)
            }
            std::cmp::Ordering::Greater => {
                if !self.unfold_head(m1) {
                    return false;
                }
                self.equiv_help(m1, m2)
            }
        }
    }

    /// Judgmental equality for the definitional equality.
    /// The type inhabitation problem of `m₁ ≡ m₂` is decidable.
    ///
    /// The formation rule is as follows:
    ///
    /// Γ ⊢ m₁ : τ    Γ ⊢ m₂ : τ
    /// -------------------------
    /// Γ ⊢ m₁ ≡ m₂ : τ
    ///
    /// The inference rules are as follows:
    ///
    /// ------------------
    /// Γ ⊢ refl m : m ≡ m
    ///
    /// Γ ⊢ h : m₁ ≡ m₂
    /// --------------------
    /// Γ ⊢ symm h : m₂ ≡ m₁
    ///
    /// Γ ⊢ h₁ : m₁ ≡ m₂   Γ ⊢ h₂ : m₂ ≡ m₃
    /// ------------------------------------
    /// Γ ⊢ trans h₁ h₂ : m₁ ≡ m₃
    ///
    /// Γ ⊢ h₁ : f₁ ≡ f₂   Γ ⊢ h₂ : a₁ ≡ a₂
    /// ------------------------------------
    /// Γ ⊢ congr_app h₁ h₂ : f₁ a₁ ≡ f₂ a₂
    ///
    /// Γ, x : τ ⊢ h : m₁ ≡ m₂
    /// ------------------------------------------------------------
    /// Γ ⊢ congr_abs (x : τ), h : (λ (x : τ), m₁) ≡ (λ (x : τ), m₂)
    ///
    ///
    /// --------------------------------------------------------
    /// Γ ⊢ beta_reduce ((λ x, m₁) m₂) : (λ x, m₁) m₂ ≡ [m₂/x]m₁
    ///
    ///
    /// --------------------------------------------------------------------------------------- (c.{u₁ ⋯ uₙ} :≡ m)
    /// Γ ⊢ delta_reduce c.{t₁ ⋯ tₙ}[i₁ ⋯ iₘ] : c.{t₁ ⋯ tₙ}[i₁ ⋯ iₘ] ≡ [i₁ ⋯ iₘ][t₁/u₁ ⋯ tₙ/uₙ]m
    ///
    /// Both terms must be ground
    pub fn equiv(&self, m1: &Term, m2: &Term) -> bool {
        let mut m1 = m1.clone();
        let mut m2 = m2.clone();
        self.equiv_help(&mut m1, &mut m2)
    }
}

// TODO: add more tests for Term::equiv
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    struct EnvFixture {
        type_const_table: HashMap<Name, Kind>,
        const_table: HashMap<Name, Const>,
        delta_table: HashMap<Name, Delta>,
        kappa_table: HashMap<Name, Kappa>,
        class_predicate_table: HashMap<Name, ClassType>,
        class_instance_table: HashMap<Name, ClassInstance>,
    }

    impl EnvFixture {
        fn new() -> Self {
            Self {
                type_const_table: HashMap::new(),
                const_table: HashMap::new(),
                delta_table: HashMap::new(),
                kappa_table: HashMap::new(),
                class_predicate_table: HashMap::new(),
                class_instance_table: HashMap::new(),
            }
        }

        fn with_delta(mut self, name: Name, delta: Delta) -> Self {
            self.delta_table.insert(name, delta);
            self
        }

        fn env(&self) -> Env<'_> {
            Env {
                type_const_table: &self.type_const_table,
                const_table: &self.const_table,
                delta_table: &self.delta_table,
                kappa_table: &self.kappa_table,
                class_predicate_table: &self.class_predicate_table,
                class_instance_table: &self.class_instance_table,
            }
        }
    }

    fn is_equiv(env: &Env<'_>, left: &Term, right: &Term) -> bool {
        env.equiv(left, right)
    }

    #[test]
    fn equiv_alpha_eq_constants() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let c = Name::intern("c").unwrap();
        let left = mk_const(c, vec![], vec![]);
        let right = mk_const(c, vec![], vec![]);

        assert!(is_equiv(&env, &left, &right));
    }

    #[test]
    fn equiv_beta_reduces_application() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let x = Name::intern("x").unwrap();
        let a = Name::intern("a").unwrap();
        let body = mk_var(0);
        let lambda = mk_abs(x, mk_type_prop(), body);
        let arg = mk_const(a, vec![], vec![]);
        let applied = mk_app(lambda, arg.clone());

        assert!(is_equiv(&env, &applied, &arg));
    }

    #[test]
    fn equiv_delta_unfolds_constant() {
        let c = Name::intern("c").unwrap();
        let d = Name::intern("d").unwrap();

        let delta = Delta {
            local_types: vec![],
            local_classes: vec![],
            target: mk_const(d, vec![], vec![]),
            height: 0,
        };

        let fixture = EnvFixture::new().with_delta(c, delta);
        let env = fixture.env();

        let defined = mk_const(c, vec![], vec![]);
        let body = mk_const(d, vec![], vec![]);

        assert!(is_equiv(&env, &defined, &body));
    }

    #[test]
    fn equiv_detects_constant_mismatch() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let c = Name::intern("c").unwrap();
        let d = Name::intern("d").unwrap();
        let left = mk_const(c, vec![], vec![]);
        let right = mk_const(d, vec![], vec![]);

        assert!(!is_equiv(&env, &left, &right));
    }

    #[test]
    fn equiv_detects_argument_mismatch() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let f = Name::intern("f").unwrap();
        let a = Name::intern("a").unwrap();
        let b = Name::intern("b").unwrap();

        let fun = mk_const(f, vec![], vec![]);
        let left = mk_app(fun.clone(), mk_const(a, vec![], vec![]));
        let right = mk_app(fun, mk_const(b, vec![], vec![]));

        assert!(!is_equiv(&env, &left, &right));
    }
}
