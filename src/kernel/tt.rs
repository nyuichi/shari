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
pub struct Name(usize);

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

    /// Panics if the name `value` has not been internalized before.
    pub fn get_unchecked(value: &str) -> Name {
        *NAME_TABLE.read().unwrap().get(value).unwrap()
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
    Mvar(Name),
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
        Type::Mvar(Default::default())
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
            Type::Mvar(inner) => {
                write!(f, "?{inner}")
            }
        }
    }
}

pub fn mk_type_arrow(dom: Type, mut cod: Type) -> Type {
    cod.discharge_rev([dom]);
    cod
}

pub fn mk_fresh_type_mvar() -> Type {
    Type::Mvar(Name::fresh())
}

pub fn mk_type_local(name: Name) -> Type {
    Type::Local(name)
}

pub fn mk_type_const(name: Name) -> Type {
    Type::Const(name)
}

/// See [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    /// t.discharge_rev([t1, t2]);
    /// assert_eq!(t, "t2 → t1 → t");
    fn discharge_rev(&mut self, cs: impl IntoIterator<Item = Type>) {
        for c in cs {
            *self = Type::Arrow(Arc::new(TypeArrow {
                dom: c,
                cod: mem::take(self),
            }));
        }
    }

    /// t.discharge([t1, t2]);
    /// assert_eq!(t, "t1 → t2 → t");
    pub fn discharge(&mut self, cs: impl IntoIterator<Item = Type>) {
        let mut iter = cs.into_iter();
        if let Some(item) = iter.next() {
            self.discharge(iter);
            *self = Type::Arrow(Arc::new(TypeArrow {
                dom: item,
                cod: mem::take(self),
            }));
        }
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
            Self::Mvar(_) => {}
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
            Type::Mvar(_) => false,
        }
    }
}

/// Locally nameless representation. See [Charguéraud, 2012].
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Term {
    Var(usize),
    Abs(Arc<TermAbs>),
    App(Arc<TermApp>),
    Local(Name),
    Const(Arc<TermConst>),
}

#[derive(Clone, Debug, Eq, Default, Ord, PartialOrd)]
pub struct TermAbs {
    pub binder_type: Type,
    // for pretty-printing
    pub binder_name: Name,
    pub body: Term,
}

impl PartialEq for TermAbs {
    /// Compares only [binder_type] and [body].
    fn eq(&self, other: &Self) -> bool {
        self.binder_type == other.binder_type && self.body == other.body
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct TermApp {
    pub fun: Term,
    pub arg: Term,
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Ord, PartialOrd)]
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
                        write!(f, "{t}")?;
                        if !first {
                            write!(f, ", ")?;
                        }
                        first = false;
                    }
                    write!(f, "}}")?;
                }
                Ok(())
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
        }
    }

    /// x # self <==> x ∉ FV(self)
    pub fn is_fresh(&self, name: Name) -> bool {
        match self {
            Self::Local(x) => x != &name,
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_fresh(name),
            Self::App(inner) => inner.fun.is_fresh(name) && inner.arg.is_fresh(name),
            Self::Const(_) => true,
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Local(_) => false,
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_closed(),
            Self::App(inner) => inner.fun.is_closed() && inner.arg.is_closed(),
            Self::Const(_) => true,
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
        }
    }

    pub fn binders(&self) -> impl Iterator<Item = &Type> {
        struct I<'a> {
            m: &'a Term,
        }
        impl<'a> Iterator for I<'a> {
            type Item = &'a Type;

            fn next(&mut self) -> Option<Self::Item> {
                if let Term::Abs(inner) = self.m {
                    self.m = &inner.body;
                    Some(&inner.binder_type)
                } else {
                    None
                }
            }
        }
        I { m: self }
    }

    /// may return locally open terms
    fn matrix(&self) -> &Term {
        let mut m = self;
        while let Term::Abs(inner) = m {
            m = &inner.body;
        }
        m
    }

    /// may return locally open terms
    pub fn head(&self) -> &Term {
        let mut m = self.matrix();
        while let Self::App(inner) = m {
            m = &inner.fun;
        }
        m
    }

    /// may return locally open terms
    pub fn args(&self) -> Vec<&Term> {
        let mut m = self.matrix();
        let mut args = vec![];
        while let Self::App(inner) = m {
            m = &inner.fun;
            args.push(&inner.arg);
        }
        args.reverse();
        args
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

    /// m.apply([l₁ ⋯ lₙ])
    /// assert(self = m lₙ ⋯ l₁)
    pub fn apply_rev(&mut self, mut args: Vec<Term>) {
        let mut m = mem::take(self);
        while let Some(arg) = args.pop() {
            m = mk_app(m, arg);
        }
        *self = m;
    }

    /// m = n l*
    /// m.unapply() // => l*
    /// assert(m = n)
    pub fn unapply(&mut self) -> Vec<Term> {
        let mut args = self.unapply_rev();
        args.reverse();
        args
    }

    /// m = n l₁ ⋯ lₙ
    /// m.unapply() // => [lₙ ⋯ l₁]
    /// assert(m = n)
    pub fn unapply_rev(&mut self) -> Vec<Term> {
        let mut args = vec![];
        let mut m = &mut *self;
        while let Self::App(inner) = m {
            let inner = Arc::make_mut(inner);
            args.push(mem::take(&mut inner.arg));
            m = &mut inner.fun;
        }
        *self = mem::take(m);
        args
    }

    // λ x₁ ⋯ xₙ, m ↦ [x₁, ⋯ , xₙ]
    pub fn undischarge(&mut self) -> Vec<(Name, Type)> {
        let mut xs = vec![];
        let mut m = &mut *self;
        while let Term::Abs(inner) = m {
            let TermAbs {
                binder_type,
                binder_name,
                body: n,
            } = Arc::make_mut(inner);
            xs.push((mem::take(binder_name), mem::take(binder_type)));
            m = n;
        }
        *self = mem::take(m);
        xs
    }

    // assert_eq!(self, "m");
    // self.discharge([x1, x2]);
    // assert_eq!(self, "λ x1 x2, m");
    pub fn discharge(&mut self, xs: Vec<(Name, Type)>) {
        let mut m = mem::take(self);
        for (name, ty) in xs.into_iter().rev() {
            m = mk_abs(name, ty, m);
        }
        *self = m;
    }

    pub fn abs(&mut self, name: Name, ty: Type, nickname: Name) {
        self.close(name);
        let m = mem::take(self);
        *self = mk_abs(nickname, ty, m);
    }

    pub fn instantiate(&mut self, subst: &[(Name, &Type)]) {
        match self {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.binder_type.subst(subst);
                inner.body.instantiate(subst);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.instantiate(subst);
                inner.arg.instantiate(subst);
            }
            Term::Local(_) => {}
            Term::Const(inner) => {
                for s in &mut Arc::make_mut(inner).ty_args {
                    s.subst(subst);
                }
            }
        }
    }

    fn untyped_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1 == index2,
            (Term::Abs(inner1), Term::Abs(inner2)) => inner1.body.untyped_eq(&inner2.body),
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.untyped_eq(&inner2.fun) && inner1.arg.untyped_eq(&inner2.arg)
            }
            (Term::Local(name1), Term::Local(name2)) => name1 == name2,
            (Term::Const(inner1), Term::Const(inner2)) => inner1.name == inner2.name,
            _ => false,
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

#[derive(Debug, Clone, PartialEq, Eq)]
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
    fn is_refl(&self) -> bool {
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
            Type::Mvar(_) => Ok(Kind::base()),
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
        let mut target = mk_fresh_type_mvar();
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
                if h1.right != h2.left {
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
                m1.abs(x, t.clone(), x);
                m2.abs(x, t.clone(), x);
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
                let Some(def) = self.defs.get(&name).cloned() else {
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
                target.instantiate(&subst);
                let c = mk_const(*name, ty_args.clone());
                Ok(Conv {
                    left: c,
                    right: target,
                })
            }
        }
    }

    fn beta_reduce(&self, m: &mut Term) -> Option<Path> {
        let path = mk_path_beta(m.clone());
        let Term::App(inner) = m else {
            return None;
        };
        let inner = Arc::make_mut(inner);
        let TermApp { mut fun, arg } = mem::take(inner);
        let Term::Abs(inner) = &mut fun else {
            return None;
        };
        let inner = Arc::make_mut(inner);
        let TermAbs {
            binder_type: _,
            binder_name: _,
            body,
        } = mem::take(inner);
        *m = body;
        m.open(&arg);
        Some(path)
    }

    fn whnf(&self, m: &mut Term) -> Path {
        match m {
            Term::Var(_) | Term::Local(_) | Term::Const(_) | Term::Abs(_) => {
                mk_path_refl(m.clone())
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                let p1 = self.whnf(&mut inner.fun);
                let p2 = self.whnf(&mut inner.arg);
                let h = mk_path_congr_app(p1, p2);
                let Term::Abs(_) = &mut inner.fun else {
                    return h;
                };
                let h_redex = self.beta_reduce(m).unwrap();
                let h = mk_path_trans(h, h_redex);
                let h_next = self.whnf(m);
                mk_path_trans(h, h_next)
            }
        }
    }

    fn delta_reduce(&self, m: &mut Term) -> Option<Path> {
        let Term::Const(inner) = m else {
            return None;
        };
        let TermConst { name, ty_args } = Arc::make_mut(inner);
        let Some(def) = self.defs.get(name).cloned() else {
            return None;
        };
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
        target.instantiate(&subst);
        let path = mk_path_delta(*name, mem::take(ty_args));
        *m = target;
        Some(path)
    }

    fn unfold_head(&self, m: &mut Term) -> Path {
        match m {
            Term::Var(_) | Term::Local(_) | Term::Abs(_) => mk_path_refl(m.clone()),
            Term::Const(_) => match self.delta_reduce(m) {
                Some(path) => path,
                None => mk_path_refl(m.clone()),
            },
            Term::App(inner) => {
                let TermApp { fun, arg } = Arc::make_mut(inner);
                let h_fun = self.unfold_head(fun);
                let h_arg = mk_path_refl(arg.clone());
                mk_path_congr_app(h_fun, h_arg)
            }
        }
    }

    fn def_hint(&self, name: Name) -> Option<usize> {
        let def = self.defs.get(&name)?;
        Some(def.hint)
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
        let h1 = self.whnf(m1);
        let h2 = mk_path_symm(self.whnf(m2));
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
        let head1 = m1.head();
        let head2 = m2.head();
        // optimization
        if head1.untyped_eq(head2) {
            let args1 = m1.args();
            let args2 = m2.args();
            if args1.len() == args2.len() {
                'args_eq: {
                    let mut h = mk_path_refl(head1.clone());
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
        let def1 = if let Term::Const(inner) = head1 {
            self.def_hint(inner.name)
        } else {
            None
        };
        let def2 = if let Term::Const(inner) = head2 {
            self.def_hint(inner.name)
        } else {
            None
        };
        if def1.is_some() || def2.is_some() {
            let height1 = def1.unwrap_or(0);
            let height2 = def2.unwrap_or(0);
            match height1.cmp(&height2) {
                std::cmp::Ordering::Less => {
                    let h3 = mk_path_symm(self.unfold_head(m2));
                    let h4 = self.equiv_help(m1, m2)?;
                    return Some(mk_path_trans(h1, mk_path_trans(h4, mk_path_trans(h3, h2))));
                }
                std::cmp::Ordering::Equal => {
                    let h3 = self.unfold_head(m1);
                    let h4 = mk_path_symm(self.unfold_head(m2));
                    let h5 = self.equiv_help(m1, m2)?;
                    return Some(mk_path_trans(
                        h1,
                        mk_path_trans(h3, mk_path_trans(h5, mk_path_trans(h4, h2))),
                    ));
                }
                std::cmp::Ordering::Greater => {
                    let h3 = self.unfold_head(m1);
                    let h4 = self.equiv_help(m1, m2)?;
                    return Some(mk_path_trans(h1, mk_path_trans(h3, mk_path_trans(h4, h2))));
                }
            }
        }
        None
    }

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
        self.env
            .check_kind(&self.local_env, target, &Kind::base())?;
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
            Term::Var(_) => {
                bail!("term not locally closed");
            }
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                self.env
                    .check_kind(&self.local_env, &inner.binder_type, &Kind::base())?;
                let x = Name::fresh();
                let t = inner.binder_type.clone();
                self.local_env.locals.push((x, t));
                inner.body.open(&mk_local(x));
                let body_ty = mk_fresh_type_mvar();
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
                let fun_ty = mk_fresh_type_mvar();
                self.check_type_help(&mut inner.fun, &fun_ty)?;
                let arg_ty = mk_fresh_type_mvar();
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
                    self.env.check_kind(&self.local_env, t, &Kind::base())?;
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
        let Type::Mvar(name) = ty else {
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

    fn solve(mut self) -> anyhow::Result<Unifier> {
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
                    // Since we have no higher-kinded polymorphism, mvars will only be typed as `Type`,
                    // it is illegal to match the following two types:
                    //  ?M₁ t =?= ?M₂ t₁ t₂
                    // But such a case is checked and ruled out in the kind checking phase that runs before
                    // this unificaiton phase.
                    let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                    let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                    self.unify(inner1.fun, inner2.fun);
                    self.unify(inner1.arg, inner2.arg);
                }
                (Type::Mvar(name), t) | (t, Type::Mvar(name)) => {
                    self.parents.insert(name, t);
                }
                (t1, t2) => {
                    bail!("type mismatch: {t1} =/= {t2}");
                }
            }
        }
        Ok(Unifier(self.parents))
    }
}

struct Unifier(HashMap<Name, Type>);

impl Unifier {
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
            Type::Mvar(name) => {
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
            Term::Local(_) => {}
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
