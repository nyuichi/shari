//! [Type] and [Term] may be ill-formed.

// TODO: quasiquote and pattern match
// TODO: handle type variables in local env

use anyhow::{bail, Context};
use core::ops::Range;
use once_cell::sync::Lazy;
use regex::Regex;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::mem;
use std::str::FromStr;
use std::sync::{Arc, RwLock};
use thiserror::Error;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Name {
    inner: String,
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

#[derive(Error, Debug, Clone)]
#[error("invalid name")]
pub struct InvalidNameError;

impl TryFrom<String> for Name {
    type Error = InvalidNameError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        static RE: Lazy<Regex> = Lazy::new(|| {
            regex::Regex::new(r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*").unwrap()
        });
        if RE.is_match(&value) {
            Ok(Name { inner: value })
        } else {
            Err(InvalidNameError)
        }
    }
}

impl TryFrom<&str> for Name {
    type Error = InvalidNameError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        value.to_owned().try_into()
    }
}

impl Borrow<str> for Name {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Name {
    // TODO: fixme
    fn fresh() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNTER: Lazy<AtomicUsize> = Lazy::new(Default::default);
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        Name {
            inner: format!("{id}"),
        }
    }

    pub fn as_str(&self) -> &str {
        &self.inner
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Type {
    Const(Name),
    Arrow(Arc<(Type, Type)>),
    Var(Name),
}

impl Default for Type {
    fn default() -> Self {
        Type::prop()
    }
}

impl FromStr for Type {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let env = Env::get();
        let mut lex = Lex::new(s);
        let mut parser = Parser::new(&mut lex, &env);
        parser.ty()
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Env::get().notations.pp.fmt_type_help(self, 0, f)
    }
}

/// See [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    pub fn prop() -> Type {
        Type::Const(Name {
            inner: "Prop".to_owned(),
        })
    }

    pub fn target(&self) -> &Type {
        let mut t = self;
        while let Self::Arrow(p) = t {
            let (_, t2) = &**p;
            t = t2;
        }
        t
    }

    pub fn args(&self) -> Vec<&Type> {
        let mut ts = vec![];
        let mut t = self;
        while let Self::Arrow(p) = t {
            let (t1, t2) = &**p;
            ts.push(t1);
            t = t2;
        }
        ts
    }

    /// (t₁ → … → tₙ → t) ↦ [t₁, …, tₙ] (self becomes t)
    pub fn undischarge(&mut self) -> Vec<Type> {
        let mut ts = vec![];
        let mut t = &mut *self;
        while let Self::Arrow(p) = t {
            let (t1, t2) = Arc::make_mut(p);
            ts.push(mem::take(t1));
            t = t2;
        }
        *self = mem::take(t);
        ts
    }

    /// [t₁, …, tₙ] ↦ (t₁ → … → tₙ → self)
    pub fn discharge(&mut self, ts: Vec<Type>) {
        let mut t = mem::take(self);
        for u in ts.into_iter().rev() {
            t = Self::Arrow(Arc::new((u, t)));
        }
        *self = t;
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Type::Const(_) => true,
            Type::Arrow(p) => p.0.is_closed() && p.1.is_closed(),
            Type::Var(_) => false,
        }
    }

    fn instantiate(&mut self, mvar: &str, t: &Type) {
        match self {
            Self::Const(_) => {}
            Self::Var(x) => {
                if x.as_str() == mvar {
                    *self = t.clone();
                }
            }
            Self::Arrow(p) => {
                let p = Arc::make_mut(p);
                p.0.instantiate(mvar, t);
                p.1.instantiate(mvar, t);
            }
        }
    }
}

/// locally nameless representation
/// See [Charguéraud, 2012].
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Term {
    Var(usize),
    Abs(Arc<Abs>),
    App(Arc<(Term, Term)>),
    Local(Name),
    Const(Arc<(Name, Vec<Type>)>),
    /// Mvar is always closed.
    Mvar(Name),
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct Abs {
    pub binder: Type,
    pub body: Term,
}

impl Default for Term {
    fn default() -> Self {
        Term::Var(usize::MAX)
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Env::get().notations.pp.fmt_term(self, f)
    }
}

impl FromStr for Term {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let env = Env::get();
        let mut lex = Lex::new(s);
        let mut parser = Parser::new(&mut lex, &env);
        parser.term()
    }
}

impl Term {
    /// self.open(x) == [x/0]self
    pub fn open(&mut self, name: &Name) {
        assert!(self.is_contextual());
        self.open_at(name, 0)
    }

    fn open_at(&mut self, name: &Name, level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(i) => {
                if *i == level {
                    *self = Self::Local(name.clone());
                }
            }
            Self::Abs(a) => {
                Arc::make_mut(a).body.open_at(name, level + 1);
            }
            Self::App(p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.open_at(name, level);
                m2.open_at(name, level);
            }
            Self::Mvar(_) => {}
            Self::Const(_) => {}
        }
    }

    /// self.close(x) == [0/x]self
    pub fn close(&mut self, name: &str) {
        assert!(self.is_lclosed());
        self.close_at(name, 0)
    }

    fn close_at(&mut self, name: &str, level: usize) {
        match self {
            Self::Local(x) => {
                if name == x.as_str() {
                    *self = Self::Var(level);
                }
            }
            Self::Var(_) => {}
            Self::Abs(a) => {
                Arc::make_mut(a).body.close_at(name, level + 1);
            }
            Self::App(p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.close_at(name, level);
                m2.close_at(name, level);
            }
            Self::Const(_) => {}
            Self::Mvar(_) => {}
        }
    }

    /// x # self <==> x ∉ FV(self)
    pub fn is_fresh(&self, name: &str) -> bool {
        match self {
            Self::Local(x) => name != x.as_str(),
            Self::Var(_) => true,
            Self::Abs(a) => a.body.is_fresh(name),
            Self::App(p) => p.0.is_fresh(name) && p.1.is_fresh(name),
            Self::Const(_) => true,
            Self::Mvar(_) => true,
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Local(_) => false,
            Self::Var(_) => true,
            Self::Abs(a) => a.body.is_closed(),
            Self::App(p) => p.0.is_closed() && p.1.is_closed(),
            Self::Const(_) => true,
            Self::Mvar(_) => true,
        }
    }

    pub fn is_lclosed(&self) -> bool {
        self.is_lclosed_at(0)
    }

    fn is_lclosed_at(&self, level: usize) -> bool {
        match self {
            Self::Local(_) => true,
            Self::Var(i) => *i < level,
            Self::Abs(a) => a.body.is_lclosed_at(level + 1),
            Self::App(p) => p.0.is_lclosed_at(level) && p.1.is_lclosed_at(level),
            Self::Const(_) => true,
            Self::Mvar(_) => true,
        }
    }

    pub fn is_contextual(&self) -> bool {
        self.is_lclosed_at(1)
    }

    fn fill_at(&mut self, m: &Term, level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(i) => {
                if *i == level {
                    *self = m.clone();
                }
            }
            Self::App(p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.fill_at(m, level);
                m2.fill_at(m, level);
            }
            Self::Abs(a) => {
                Arc::make_mut(a).body.fill_at(m, level + 1);
            }
            Self::Const(_) => {}
            Self::Mvar(_) => {}
        }
    }

    pub fn fill(&mut self, m: &Term) {
        assert!(self.is_contextual());
        self.fill_at(m, 0);
    }

    fn subst(&mut self, name: &str, m: &Term) {
        match self {
            Self::Local(x) => {
                if name == x.as_str() {
                    *self = m.clone();
                }
            }
            Self::Var(_) => {}
            Self::App(p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.subst(name, m);
                m2.subst(name, m);
            }
            Self::Abs(a) => {
                Arc::make_mut(a).body.subst(name, m);
            }
            Self::Const(_) => {}
            Self::Mvar(_) => {}
        }
    }

    pub fn subst_mvar(&mut self, name: &str, m: &Term) {
        match self {
            Self::Local(_) => {}
            Self::Var(_) => {}
            Self::App(p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.subst_mvar(name, m);
                m2.subst_mvar(name, m);
            }
            Self::Abs(a) => {
                Arc::make_mut(a).body.subst_mvar(name, m);
            }
            Self::Const(_) => {}
            Self::Mvar(x) => {
                if x.as_str() == name {
                    *self = m.clone();
                }
            }
        }
    }

    // first-order pattern match.
    // other must be ground.
    // ignores types.
    pub fn match1<'a>(&self, other: &'a Term) -> Option<Subst<&'a Term>> {
        assert!(other.is_ground());
        let mut subst = Subst::new();
        if !subst.match1(self, other) {
            return None;
        }
        Some(subst)
    }

    pub fn binders(&self) -> impl Iterator<Item = &Type> {
        struct I<'a> {
            m: &'a Term,
        }
        impl<'a> Iterator for I<'a> {
            type Item = &'a Type;

            fn next(&mut self) -> Option<Self::Item> {
                if let Term::Abs(a) = self.m {
                    self.m = &a.body;
                    Some(&a.binder)
                } else {
                    None
                }
            }
        }
        I { m: self }
    }

    /// may return locally open terms
    pub fn matrix(&self) -> &Term {
        let mut m = self;
        while let Term::Abs(a) = m {
            m = &a.body;
        }
        m
    }

    /// may return locally open terms
    pub fn head(&self) -> &Term {
        let mut m = self.matrix();
        while let Self::App(p) = m {
            m = &p.0;
        }
        m
    }

    /// triple(λ (v:t)*, m l*) = (t*, m, l*)
    /// may return locally open terms
    pub fn triple(&self) -> (impl Iterator<Item = &Type>, &Term, Vec<&Term>) {
        let binders = self.binders();
        let mut m = self.matrix();
        let mut args = vec![];
        while let Self::App(p) = m {
            m = &p.0;
            args.push(&p.1);
        }
        args.reverse();
        let head = m;
        (binders, head, args)
    }

    /// may return locally open terms
    pub fn args(&self) -> Vec<&Term> {
        self.triple().2
    }

    pub fn is_neutral(&self) -> bool {
        match self {
            Self::Abs(_) => false,
            Self::App(p) => {
                let (m1, m2) = &**p;
                m1.is_neutral() && m2.is_normal()
            }
            Self::Var(_) | Self::Local(_) | Self::Const(_) | Self::Mvar(_) => true,
        }
    }

    /// `true` if the term is in β-normal form.
    pub fn is_normal(&self) -> bool {
        if let Self::Abs(a) = self {
            a.body.is_normal()
        } else {
            self.is_neutral()
        }
    }

    /// m is in head normal form if m has no β-redex at its head position.
    pub fn is_hnf(&self) -> bool {
        match self.head() {
            Self::Local(_) | Self::Var(_) | Self::Const(_) | Self::Mvar(_) => true,
            Self::Abs(_) => false,
            Self::App(_) => unreachable!(),
        }
    }

    /// does not check if a term inside an abstraction is in whnf
    pub fn is_whnf(&self) -> bool {
        match self {
            Self::Abs(_) => true,
            Self::Var(_) | Self::Local(_) | Self::Const(_) | Self::Mvar(_) | Self::App(_) => {
                self.is_hnf()
            }
        }
    }

    /// m = n l*
    /// m.unapply() // => l*
    /// assert(m = n)
    pub fn unapply(&mut self) -> Vec<Term> {
        let mut args = vec![];
        let mut m = &mut *self;
        while let Self::App(p) = m {
            let (m1, m2) = Arc::make_mut(p);
            args.push(mem::take(m2));
            m = m1;
        }
        *self = mem::take(m);
        args.reverse();
        args
    }

    pub fn apply(&mut self, args: impl IntoIterator<Item = Term>) {
        let mut m = mem::take(self);
        for arg in args {
            m = Term::App(Arc::new((m, arg)));
        }
        *self = m;
    }

    fn undischarge_locals(&mut self) -> Vec<(Name, Type)> {
        let mut binders = vec![];
        let mut m = &mut *self;
        while let Term::Abs(a) = m {
            let Abs { binder: t, body: n } = Arc::make_mut(a);
            let x = Name::fresh();
            n.open(&x);
            binders.push((x, mem::take(t)));
            m = n;
        }
        *self = mem::take(m);
        binders
    }

    fn discharge_locals<'a, T>(&'a mut self, binders: T)
    where
        T: IntoIterator<Item = (&'a Name, Type)>,
        <T as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        let mut m = mem::take(self);
        for (x, t) in binders.into_iter().rev() {
            m.close(x.as_str());
            m = Self::Abs(Arc::new(Abs { binder: t, body: m }));
        }
        *self = m;
    }

    fn undischarge(&mut self) -> Vec<Type> {
        let mut xs = vec![];
        let mut m = &mut *self;
        while let Term::Abs(a) = m {
            let Abs { binder: t, body: n } = Arc::make_mut(a);
            xs.push(mem::take(t));
            m = n;
        }
        *self = mem::take(m);
        xs
    }

    fn discharge(&mut self, xs: Vec<Type>) {
        let mut m = mem::take(self);
        for t in xs.into_iter().rev() {
            m = Self::Abs(Arc::new(Abs { binder: t, body: m }));
        }
        *self = m;
    }

    /// applicative-order (leftmost-innermost) reduction
    fn beta_reduce(&mut self) {
        match self {
            Self::Local(_) | Self::Var(_) | Self::Const(_) | Self::Mvar(_) => {}
            Self::App(p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.beta_reduce();
                m2.beta_reduce();
                if let Self::Abs(a) = m1 {
                    let a = Arc::make_mut(a);
                    a.body.fill(m2);
                    *self = mem::take(&mut a.body);
                    self.beta_reduce();
                }
            }
            Self::Abs(a) => Arc::make_mut(a).body.beta_reduce(),
        }
    }

    pub fn is_ground(&self) -> bool {
        match self {
            Self::Local(_) => true,
            Self::Var(_) => true,
            Self::Abs(a) => a.body.is_ground(),
            Self::App(p) => {
                let (m1, m2) = &**p;
                m1.is_ground() && m2.is_ground()
            }
            Self::Const(_) => true,
            Self::Mvar(_) => false,
        }
    }

    fn instantiate(&mut self, mvar: &str, t: &Type) {
        match self {
            Self::Abs(a) => {
                let a = Arc::make_mut(a);
                a.binder.instantiate(mvar, t);
                a.body.instantiate(mvar, t);
            }
            Self::App(p) => {
                let p = Arc::make_mut(p);
                p.0.instantiate(mvar, t);
                p.1.instantiate(mvar, t);
            }
            Self::Const(c) => {
                let c = Arc::make_mut(c);
                for u in &mut c.1 {
                    u.instantiate(mvar, t);
                }
            }
            Self::Local(_) | Self::Var(_) | Self::Mvar(_) => {}
        }
    }
}

#[derive(Debug)]
struct Env {
    consts: HashMap<Name, (Vec<Name>, Type)>,
    const_types: HashMap<Name, usize>,
    defs: HashMap<Name, (Vec<Name>, Term)>,
    type_defs: HashMap<Name, (Name, Name, Arc<Fact>)>,
    axioms: HashMap<Name, (Vec<Name>, Term)>,
    notations: NotationTable,
}

#[derive(Debug, Default)]
struct NotationTable {
    // symbol to name
    tt: TokenTable,
    // name to symbol
    pp: Printer,
}

// TODO: allow table lookup
static ENV: Lazy<RwLock<Env>> = Lazy::new(|| {
    let mut env = Env {
        consts: Default::default(),
        const_types: Default::default(),
        defs: Default::default(),
        type_defs: Default::default(),
        axioms: Default::default(),
        notations: Default::default(),
    };

    env.add_const_type("Prop", 0).unwrap();
    env.add_notation("=", Fixity::Infix, 50, "eq").unwrap();
    env.add_const(
        Name::try_from("eq").unwrap(),
        vec![Name::try_from("u").unwrap()],
        Type::Arrow(Arc::new((
            Type::Var(Name::try_from("u").unwrap()),
            Type::Arrow(Arc::new((
                Type::Var(Name::try_from("u").unwrap()),
                Type::prop(),
            ))),
        ))),
    )
    .unwrap();

    RwLock::new(env)
});

impl Env {
    fn get() -> std::sync::RwLockReadGuard<'static, Env> {
        ENV.read().unwrap()
    }

    fn get_mut() -> std::sync::RwLockWriteGuard<'static, Env> {
        ENV.write().unwrap()
    }

    fn token_table(&self) -> &TokenTable {
        &self.notations.tt
    }

    fn get_const_type(&self, name: &str) -> Option<usize> {
        self.const_types.get(name).copied()
    }

    fn add_const_type(&mut self, name: &str, arity: usize) -> anyhow::Result<()> {
        let Ok(name) = Name::try_from(name) else {
            bail!("invalid name: {name}");
        };
        if self.const_types.insert(name, arity).is_some() {
            bail!("constant type already defined");
        }
        Ok(())
    }

    fn get_const(&self, name: &str) -> Option<(&[Name], &Type)> {
        self.consts.get(name).map(|v| (v.0.as_slice(), &v.1))
    }

    fn add_const(&mut self, name: Name, type_vars: Vec<Name>, ty: Type) -> anyhow::Result<()> {
        if self.consts.insert(name, (type_vars, ty)).is_some() {
            bail!("constant already defined");
        }
        Ok(())
    }

    fn add_notation(
        &mut self,
        symbol: &str,
        fixity: Fixity,
        prec: usize,
        entity: &str,
    ) -> anyhow::Result<()> {
        let Ok(entity) = Name::try_from(entity) else {
            bail!("invalid name: {entity}");
        };
        let op = Operator {
            symbol: symbol.to_owned(),
            fixity,
            prec,
            entity: entity.clone(),
        };
        self.notations.tt.add(op.clone())?;
        self.notations.pp.add(op)?;
        Ok(())
    }
}

pub fn add_notation(symbol: &str, fixity: Fixity, prec: usize, entity: &str) -> anyhow::Result<()> {
    Env::get_mut().add_notation(symbol, fixity, prec, entity)
}

pub fn add_definition(
    name: &str,
    ty_vars: impl IntoIterator<Item = Name>,
    ty: Type,
    mut entity: Term,
) -> anyhow::Result<()> {
    let Ok(name) = Name::try_from(name) else {
        bail!("invalid name: {entity}");
    };
    let ty_vars: Vec<_> = ty_vars.into_iter().collect();
    if !ty_vars.is_empty() {
        // TODO
        todo!();
    }
    assert!(ty.is_closed(), "{ty}");
    let Ok(inferred_ty) = LocalEnv::new().infer(&mut entity) else {
        bail!("term not type-correct");
    };
    if inferred_ty != ty {
        bail!("invalid type");
    }
    // TODO check if consts in ty are well-formed.
    let mut env = Env::get_mut();
    env.add_const(name.clone(), ty_vars.clone(), ty)?;
    if env.defs.insert(name, (ty_vars, entity)).is_some() {
        bail!("multiple definitions");
    }
    Ok(())
}

#[derive(Clone, Debug, Default)]
pub struct Subst<T>(Vec<(Name, T)>);

impl<T> Subst<T> {
    fn new() -> Self {
        Self(vec![])
    }

    pub fn get(&self, name: &str) -> Option<&T> {
        for (k, v) in &self.0 {
            if k.as_str() == name {
                return Some(v);
            }
        }
        None
    }
}

impl Subst<Type> {
    fn apply_type(&self, t: &mut Type) {
        for (mvar, u) in &self.0 {
            t.instantiate(mvar.as_str(), u);
        }
    }

    fn apply_term(&self, m: &mut Term) {
        for (mvar, t) in &self.0 {
            m.instantiate(mvar.as_str(), t);
        }
    }

    fn unify(&mut self, t1: &mut Type, t2: &mut Type) -> anyhow::Result<()> {
        self.apply_type(t1);
        self.apply_type(t2);
        if t1 == t2 {
            return Ok(());
        }
        match (t1, t2) {
            (Type::Arrow(p1), Type::Arrow(p2)) => {
                let (t11, t12) = Arc::make_mut(p1);
                let (t21, t22) = Arc::make_mut(p2);
                self.unify(t11, t21)?;
                self.unify(t12, t22)?;
            }
            (Type::Var(i), t) | (t, Type::Var(i)) => {
                if !self.0.iter().any(|(j, _)| j == i) {
                    // TODO: occur check
                    self.0.push((i.clone(), t.clone()));
                } else {
                    let mut u = Type::Var(i.clone());
                    self.apply_type(&mut u);
                    self.unify(&mut u, t)?;
                }
            }
            (t1, t2) => {
                bail!("type mismatch: {t1} and {t2}");
            }
        }
        Ok(())
    }
}

impl<'a> Subst<&'a Term> {
    fn match1(&mut self, this: &Term, that: &'a Term) -> bool {
        match (this, that) {
            (Term::Var(i), Term::Var(j)) if i == j => true,
            (Term::Abs(a1), Term::Abs(a2)) => self.match1(&a1.body, &a2.body),
            (Term::App(p1), Term::App(p2)) => {
                self.match1(&p1.0, &p2.0) && self.match1(&p1.1, &p2.1)
            }
            (Term::Local(x), Term::Local(y)) if x == y => true,
            (Term::Const(c1), Term::Const(c2)) => c1.0 == c2.0,
            (Term::Mvar(name), m) => {
                self.0.push((name.clone(), m));
                true
            }
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LocalEnv {
    // ty_vars: Vec<Name>,
    locals: Vec<(Name, Type)>,
}

impl std::fmt::Display for LocalEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, (x, t)) in self.locals.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "({} : {})", x, t)?;
        }
        Ok(())
    }
}

impl LocalEnv {
    pub fn new() -> Self {
        LocalEnv { locals: vec![] }
    }

    fn get_local(&self, name: &str) -> Option<&Type> {
        for (x, t) in self.locals.iter().rev() {
            if x.as_str() == name {
                return Some(t);
            }
        }
        None
    }

    fn get_const(&self, name: &str) -> Option<(Vec<Name>, Type)> {
        if let Some(s) = Env::get().consts.get(name) {
            return Some(s.clone());
        }
        None
    }

    fn push_local(&mut self, name: Name, t: Type) {
        self.locals.push((name, t));
    }

    fn pop_local(&mut self) {
        if self.locals.pop().is_none() {
            panic!("logic flaw")
        }
    }

    fn infer_help<'a>(
        &self,
        m: &'a mut Term,
        var_stack: &mut Vec<&'a Type>,
        subst: &mut Subst<Type>,
    ) -> anyhow::Result<Type> {
        match m {
            Term::Local(name) => {
                if let Some(u) = self.get_local(name.as_str()) {
                    return Ok(u.clone());
                }
                bail!("local variable not found: {name}");
            }
            Term::Var(i) => {
                let i = *i;
                if i < var_stack.len() {
                    return Ok(var_stack[var_stack.len() - i - 1].clone());
                }
                bail!("term not locally closed");
            }
            Term::Abs(a) => {
                let a = Arc::make_mut(a);
                var_stack.push(&a.binder);
                let u = self.infer_help(&mut a.body, var_stack, subst)?;
                var_stack.pop();
                Ok(Type::Arrow(Arc::new((a.binder.clone(), u))))
            }
            Term::App(p) => {
                let p = Arc::make_mut(p);
                let mut t1 = self.infer_help(&mut p.0, var_stack, subst)?;
                let t2 = self.infer_help(&mut p.1, var_stack, subst)?;
                let mut t = Type::Arrow(Arc::new((t2, Type::Var(Name::fresh()))));
                subst.unify(&mut t1, &mut t)?;
                let Type::Arrow(mut p) = t else {
                    panic!("logic flaw");
                };
                Ok(mem::take(&mut Arc::make_mut(&mut p).1))
            }
            Term::Const(c) => {
                let c = Arc::make_mut(c);
                if let Some((tv, ty)) = self.get_const(c.0.as_str()) {
                    if tv.len() != c.1.len() {
                        bail!("number of type variables mismatch");
                    }
                    let mut new_tv: Vec<_> = std::iter::repeat_with(|| Type::Var(Name::fresh()))
                        .take(tv.len())
                        .collect();
                    let mut ty = ty.clone();
                    for (old, new) in std::iter::zip(tv, &new_tv) {
                        ty.instantiate(old.as_str(), new);
                    }
                    for (t1, t2) in std::iter::zip(&mut c.1, &mut new_tv) {
                        subst.unify(t1, t2)?;
                    }
                    return Ok(ty);
                }
                bail!("constant not found");
            }
            Term::Mvar(_) => {
                bail!("term not ground");
            }
        }
    }

    pub fn infer(&self, m: &mut Term) -> anyhow::Result<Type> {
        let mut subst = Subst::<Type>::default();
        let mut var_stack = vec![];
        let mut t = self.infer_help(m, &mut var_stack, &mut subst)?;
        assert!(var_stack.is_empty());
        subst.apply_type(&mut t);
        subst.apply_term(m);
        Ok(t)
    }

    fn infer_unchecked_help<'a>(&self, m: &'a Term, var_stack: &mut Vec<&'a Type>) -> Type {
        match m {
            Term::Local(name) => self.get_local(name.as_str()).unwrap().clone(),
            Term::Var(i) => var_stack[var_stack.len() - 1 - i].clone(),
            Term::Abs(a) => {
                let arg_ty = a.binder.clone();
                var_stack.push(&a.binder);
                let body_ty = self.infer_unchecked_help(&a.body, var_stack);
                var_stack.pop();
                Type::Arrow(Arc::new((arg_ty, body_ty)))
            }
            Term::App(p) => {
                let Type::Arrow(p) = self.infer_unchecked_help(&p.0, var_stack) else {
                    panic!("arrow type expected");
                };
                p.0.clone()
            }
            Term::Const(c) => {
                let (mvars, ty) = self.get_const(c.0.as_str()).unwrap();
                let mut ty = ty.clone();
                for (mvar, t) in std::iter::zip(mvars, &c.1) {
                    ty.instantiate(mvar.as_str(), t);
                }
                ty
            }
            Term::Mvar(_) => panic!("term not ground"),
        }
    }

    fn infer_unchecked(&self, m: &Term) -> Type {
        let mut var_stack = vec![];
        let t = self.infer_unchecked_help(m, &mut var_stack);
        assert!(var_stack.is_empty());
        t
    }

    // TODO: remove
    fn type_correct(&self, m: &Term) -> bool {
        let mut n = m.clone();
        let Ok(_) = self.infer(&mut n) else {
            return false;
        };
        &n == m
    }

    /// Check if the term is in η-long β-normal form.
    /// See Lectures on the Curry-Howard isomorphism, Chapter 4.
    /// https://math.stackexchange.com/q/3334730
    /// [m] must be ground and locally closed.
    fn is_canonical(&self, m: &Term) -> bool {
        assert!(m.is_lclosed());
        let mut var_stack = vec![];
        let r = self.is_canonical_help(m, &mut var_stack);
        assert!(var_stack.is_empty());
        r
    }

    fn is_canonical_help<'a>(&self, m: &'a Term, var_stack: &mut Vec<&'a Type>) -> bool {
        // TODO: avoid quadratic cost
        let t = self.infer_unchecked_help(m, var_stack);
        match t {
            Type::Arrow(_) => {
                if let Term::Abs(a) = m {
                    var_stack.push(&a.binder);
                    let r = self.is_canonical_help(&a.body, var_stack);
                    var_stack.pop();
                    r
                } else {
                    false
                }
            }
            Type::Const(_) => {
                let mut m = m;
                while let Term::App(p) = m {
                    if !self.is_canonical_help(&p.1, var_stack) {
                        return false;
                    }
                    m = &p.0;
                }
                match m {
                    Term::Var(_) | Term::Local(_) | Term::Const(_) | Term::Mvar(_) => true,
                    Term::Abs(_) => false,
                    Term::App(_) => unreachable!(),
                }
            }
            Type::Var(_) => {
                // type must be known
                false
            }
        }
    }

    /// [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_neutral(&self, m: &mut Term, var_stack: &mut Vec<Type>) {
        assert!(m.is_neutral());
        // [x M₁ ... Mₙ] := x [M₁] ... [Mₙ]
        let mut args = m.unapply();
        for arg in &mut args {
            self.eta_expand_normal(arg, var_stack);
        }
        m.apply(args);
        // TODO avoid quadratic cost
        let mut var_ref_stack = vec![];
        for ty_ref in &*var_stack {
            var_ref_stack.push(ty_ref);
        }
        let t = self.infer_unchecked_help(m, &mut var_ref_stack);
        assert_eq!(var_ref_stack.len(), var_stack.len());
        // [M] := λv₁ ⋯ vₙ. M v₁ ⋯ vₙ
        let vs: Vec<_> = t.args().into_iter().cloned().collect();
        m.apply((0..vs.len()).rev().map(Term::Var));
        m.discharge(vs);
    }

    /// 1. [λx.M] := λx.[M]
    /// 2. [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_normal(&self, m: &mut Term, var_stack: &mut Vec<Type>) {
        assert!(m.is_normal());
        let mut xs = m.undischarge();
        let num_xs = xs.len();
        var_stack.append(&mut xs);
        self.eta_expand_neutral(m, var_stack);
        xs.extend(var_stack.drain(var_stack.len() - num_xs..));
        m.discharge(xs);
    }

    /// [m] must be type-correct, ground, and locally closed.
    pub fn canonicalize(&self, m: &mut Term) {
        assert!(m.is_ground());
        assert!(m.is_lclosed());
        assert!(self.type_correct(m));
        m.beta_reduce();
        let mut var_stack = vec![];
        self.eta_expand_normal(m, &mut var_stack);
        assert!(var_stack.is_empty())
    }

    /// [m1] and [m2] must be type-correct and type-equal under the same environment.
    pub fn eq(&self, m1: &Term, m2: &Term) -> bool {
        let mut m1 = m1.clone();
        let mut m2 = m2.clone();
        self.canonicalize(&mut m1);
        self.canonicalize(&mut m2);
        m1 == m2
    }

    pub fn add(&mut self, name: Name, ty: Type) -> anyhow::Result<()> {
        match self.get_local(name.as_str()) {
            Some(t) => {
                if t == &ty {
                    Ok(())
                } else {
                    bail!("type mismatch in locals: ({name} : {ty}) and ({name} : {t})");
                }
            }
            None => {
                self.locals.push((name, ty));
                Ok(())
            }
        }
    }

    fn merge(&mut self, other: Self) -> anyhow::Result<()> {
        for (name, ty) in other.locals {
            self.add(name, ty)?;
        }
        Ok(())
    }
}

fn mk_const(name: &str, tv: impl IntoIterator<Item = Type>) -> Term {
    Term::Const(Arc::new((
        Name::try_from(name).expect("logic flaw"),
        tv.into_iter().collect(),
    )))
}

fn dest_call(m: &mut Term, f: &str) -> Option<Vec<Term>> {
    let mut args = vec![];
    let mut m = m;
    while let Term::App(p) = m {
        let p = Arc::make_mut(p);
        args.push(mem::take(&mut p.1));
        m = &mut p.0;
    }
    args.reverse();
    let Term::Const(c) = m else {
        return None;
    };
    if c.0.as_str() != f {
        return None;
    }
    Some(args)
}

fn dest_call2(m: &mut Term, f: &str) -> Option<(Term, Term)> {
    let v = dest_call(m, f)?;
    if v.len() != 2 {
        return None;
    }
    let mut iter = v.into_iter();
    let m1 = iter.next().unwrap();
    let m2 = iter.next().unwrap();
    Some((m1, m2))
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Fact {
    local_env: LocalEnv,
    ctx: Vec<Term>,
    target: Term,
}

impl std::fmt::Display for Fact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.local_env.locals.is_empty() {
            write!(f, "▶ ")?;
        } else {
            write!(f, "{} ▶ ", self.local_env)?;
        }
        for p in &self.ctx {
            write!(f, "({}) ", p)?;
        }
        write!(f, "⊢ {}", self.target)
    }
}

impl Fact {
    pub fn target(&self) -> &Term {
        &self.target
    }

    pub fn ctx(&self) -> &[Term] {
        &self.ctx
    }

    pub fn local_env(&self) -> &LocalEnv {
        &self.local_env
    }

    pub fn into_inner(self) -> (LocalEnv, Vec<Term>, Term) {
        (self.local_env, self.ctx, self.target)
    }
}

/// ```text
///
/// ----------------------
/// assume φ : [Γ ▸ φ ⊢ φ]
/// ```
pub fn assume(local_env: LocalEnv, mut target: Term) -> anyhow::Result<Fact> {
    // TODO: well-formedness check for local_env
    let ty = local_env.infer(&mut target)?;
    if ty != Type::prop() {
        bail!("expected Prop, but got {ty}");
    }
    Ok(Fact {
        local_env,
        ctx: vec![target.clone()],
        target,
    })
}

/// ```text
///
/// ---------------------------- (m₁ ≡ m₂)
/// eq_intro t : [Γ ▸ ⊢ m₁ = m₂]
/// ```
pub fn eq_intro(local_env: LocalEnv, mut m1: Term, mut m2: Term) -> anyhow::Result<Fact> {
    // TODO: well-formedness check for local_env
    let t1 = local_env.infer(&mut m1)?;
    let t2 = local_env.infer(&mut m2)?;
    if t1 != t2 {
        bail!("type mismatch: {t1} and {t2}");
    }
    if !local_env.eq(&m1, &m2) {
        bail!("terms not definitionally equal: {m1} and {m2}");
    }
    let mut target = mk_const("eq", [t1]);
    target.apply([m1, m2]);
    Ok(Fact {
        local_env,
        ctx: vec![],
        target,
    })
}

/// ```text
/// h₁ : [Γ ▸ Φ ⊢ m₁ = m₂]  h₂ : [Δ ▸ Ψ ⊢ C[m₂]]
/// -------------------------------------------- [indiscernibility of identicals]
/// eq_elim C[-] h₁ h₂ : [Γ ∪ Δ ▸ Φ ∪ Ψ ⊢ C[m₁]]
/// ```
pub fn eq_elim(c: Term, mut h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    if !c.is_contextual() {
        bail!("expected context, but got {c}");
    }
    let Some((m1, m2)) = dest_call2(&mut h1.target, "eq") else {
        bail!("expected equality");
    };
    let mut cm2 = c.clone();
    cm2.fill(&m2);
    let t = h2
        .local_env
        .infer(&mut cm2)
        .with_context(|| format!("context term is not type-correct: {c}"))?;
    if t != Type::prop() {
        bail!("expected Prop, but got {t}");
    }
    if h2.target != cm2 {
        bail!("terms not literally equal: {} and {}", h2.target, cm2);
    }
    let mut local_env = h1.local_env;
    local_env.merge(h2.local_env)?;
    let mut ctx: Vec<_> = h1.ctx.into_iter().chain(h2.ctx.into_iter()).collect();
    ctx.sort();
    ctx.dedup();
    let mut target = c;
    target.fill(&m1);
    local_env.infer(&mut target).expect("logic flaw");
    Ok(Fact {
        local_env,
        ctx,
        target,
    })
}

/// ```text
/// h₁ : [Γ ▸ Φ ⊢ φ]  h₂ : [Δ ▸ Ψ ⊢ ψ]
/// -------------------------------------------------------- [(external) propositional extensionality]
/// prop_ext h₁ h₂ : [Γ ∪ Δ ▸ (Φ - {ψ}) ∪ (Ψ - {φ}) ⊢ φ = ψ]
/// ```
pub fn prop_ext(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let mut local_env = h1.local_env;
    local_env.merge(h2.local_env)?;
    let mut ctx: Vec<_> = h1
        .ctx
        .into_iter()
        .filter(|p| p != &h2.target)
        .chain(h2.ctx.into_iter().filter(|p| p != &h1.target))
        .collect();
    ctx.sort();
    ctx.dedup();
    let mut target = mk_const("eq", [Type::prop()]);
    target.apply([h1.target, h2.target]);
    Ok(Fact {
        local_env,
        ctx,
        target,
    })
}

/// ```text
/// h : [Γ ▸ Φ ⊢ m₁ = m₂]
/// --------------------------------------------------------- (x ∉ FV Φ) [(external) function extensionality]
/// fun_ext x τ h : [Γ - {x : τ} ▸ Φ ⊢ (λ x, m₁) = (λ x, m₂)]
/// ```
pub fn fun_ext(x: &Name, t: Type, mut h: Fact) -> anyhow::Result<Fact> {
    let Some((mut m1, mut m2)) = dest_call2(&mut h.target, "eq") else {
        bail!("expected equality");
    };
    // this is optional
    if h.local_env.get_const(x.as_str()).is_some() {
        bail!("cannot quantify over constant variable: {x}");
    }
    if let Some(s) = h.local_env.get_local(x.as_str()) {
        if s != &t {
            bail!("variable type not compatible: expected ({x} : {t}), but got ({x} : {s})");
        }
    }
    if !h.ctx.iter().all(|m| m.is_fresh(x.as_str())) {
        bail!("eigenvariable condition fails");
    }
    let local_env = LocalEnv {
        locals: h
            .local_env
            .locals
            .into_iter()
            .filter(|p| &p.0 != x)
            .collect(),
    };
    m1.discharge_locals([(x, t.clone())]);
    m2.discharge_locals([(x, t)]);
    let t = local_env.infer_unchecked(&m1);
    let mut target = mk_const("eq", [t]);
    target.apply([m1, m2]);
    Ok(Fact {
        local_env,
        ctx: h.ctx,
        target,
    })
}

/// ```text
///
/// ---------------------------- (def foo := m) [definition]
/// by_def "foo": [ ▸ | foo = m]
/// ```
pub fn by_def(name: &Name) -> anyhow::Result<Fact> {
    let env = Env::get();
    match env.defs.get(name) {
        Some((ty_vars, entity)) => {
            // TODO: add ty_vars to local env
            let mut entity = entity.clone();
            let ty = LocalEnv::new().infer(&mut entity)?;
            let target = Term::App(Arc::new((
                Term::App(Arc::new((
                    Term::Const(Arc::new((Name::try_from("eq").unwrap(), vec![ty]))),
                    Term::Const(Arc::new((
                        name.clone(),
                        ty_vars.iter().map(|tv| Type::Var(tv.clone())).collect(),
                    ))),
                ))),
                entity,
            )));
            Ok(Fact {
                local_env: LocalEnv::new(),
                ctx: vec![],
                target,
            })
        }
        None => {
            bail!("definition not found")
        }
    }
}

#[derive(Debug, Clone)]
pub struct SourceInfo<'a> {
    line: usize,   // 1-origin
    column: usize, // 1-origin
    range: Range<usize>,
    input: &'a str,
}

impl<'a> SourceInfo<'a> {
    fn eof(input: &'a str) -> Self {
        let range = {
            let last = input.chars().count();
            last..last
        };
        let (line, column) = {
            let mut lines = input.lines();
            let last_line = lines.by_ref().last().unwrap();
            (lines.count() + 1, last_line.chars().count() + 1)
        };
        Self {
            range,
            input,
            line,
            column,
        }
    }

    fn as_str(&self) -> &str {
        self.input
            .get(self.range.clone())
            .expect("invalid token position")
    }
}

impl<'a> std::fmt::Display for SourceInfo<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}\n\n", self.line, self.column)?;
        writeln!(
            f,
            "{}",
            self.input
                .lines()
                .nth(self.line - 1)
                .expect("invalid line number")
        )?;
        writeln!(
            f,
            "{}{}",
            " ".repeat(self.column - 1),
            "^".repeat(
                self.input
                    .get(self.range.clone())
                    .unwrap_or("")
                    .chars()
                    .count()
            )
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    Ident,  // e.g. "foo", "α", "Prop"
    Symbol, // e.g. "+", ":", "λ", ",", "_"
}

#[derive(Debug, Clone)]
pub struct Token<'a> {
    kind: TokenKind,
    source_info: SourceInfo<'a>,
}

impl<'a> Token<'a> {
    fn is_ident(&self) -> bool {
        self.kind == TokenKind::Ident
    }

    fn is_symbol(&self) -> bool {
        self.kind == TokenKind::Symbol
    }

    fn as_str(&self) -> &str {
        self.source_info.as_str()
    }
}

impl<'a> std::fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?} {}\n{}", self.kind, self.as_str(), self.source_info)
    }
}

#[derive(Debug, Clone)]
pub struct Lex<'a> {
    input: &'a str,
    position: usize,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, Copy)]
struct LexState {
    position: usize,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, Error)]
#[error("unrecognizable character at line {line}, column {column}")]
pub struct LexError {
    line: usize,
    column: usize,
}

impl<'a> From<Lex<'a>> for LexError {
    fn from(lex: Lex<'a>) -> Self {
        Self {
            line: lex.line,
            column: lex.column,
        }
    }
}

impl<'a> Lex<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            position: 0,
            line: 1,
            column: 1,
        }
    }

    fn save(&self) -> LexState {
        LexState {
            position: self.position,
            line: self.line,
            column: self.column,
        }
    }

    fn restore(&mut self, state: LexState) {
        self.position = state.position;
        self.line = state.line;
        self.column = state.column;
    }

    fn advance(&mut self, bytes: usize) -> SourceInfo<'a> {
        let source_info = SourceInfo {
            range: self.position..self.position + bytes,
            line: self.line,
            column: self.column,
            input: self.input,
        };
        let text = &self.input[self.position..self.position + bytes];
        self.position += bytes;
        for c in text.chars() {
            if c == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
        source_info
    }
}

impl<'a> Iterator for Lex<'a> {
    type Item = std::result::Result<Token<'a>, LexError>;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq, Eq, Debug)]
        enum Kind {
            Space,
            Ident,
            Symbol,
            NumLit,
        }

        static RE: Lazy<Regex> = Lazy::new(|| {
            let s = &[
                (Kind::Space, r"\s+|--.*|/-"),
                (
                    Kind::Ident,
                    r"#?[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*",
                ),
                (
                    Kind::Symbol,
                    r"[(){}⟨⟩⟪⟫,]|[\p{Symbol}\p{Punctuation}&&[^(){}⟨⟩⟪⟫,]]+",
                ),
                (Kind::NumLit, r"0|[1-9][0-9]*"),
            ]
            .iter()
            .map(|(kind, re)| format!("(?P<{:?}>{})", kind, re))
            .collect::<Vec<_>>()
            .join("|");
            regex::Regex::new(&format!("^(?:{})", s)).unwrap()
        });

        static RE_BLOCK_COMMENT: Lazy<Regex> =
            Lazy::new(|| regex::Regex::new("^(?s:.*?)(?:(?P<start>/-)|(?P<end>-/))").unwrap());

        loop {
            if self.input.len() == self.position {
                return None;
            }
            let cap = match RE.captures(&self.input[self.position..]) {
                None => return Some(Err(LexError::from(self.clone()))),
                Some(cap) => cap,
            };

            // skip whitespaces
            if let Some(m) = cap.name(&format!("{:?}", Kind::Space)) {
                self.advance(m.range().count());
                if m.as_str() == "/-" {
                    let mut nest = 1;
                    while nest != 0 {
                        if self.input.len() == self.position {
                            return None;
                        }
                        let cap = match RE_BLOCK_COMMENT.captures(&self.input[self.position..]) {
                            None => return Some(Err(LexError::from(self.clone()))),
                            Some(cap) => cap,
                        };
                        if cap.name("start").is_some() {
                            nest += 1;
                            self.advance(cap.get(0).unwrap().range().count());
                        } else {
                            assert!(cap.name("end").is_some());
                            nest -= 1;
                            self.advance(cap.get(0).unwrap().range().count());
                        }
                    }
                }
                continue;
            }

            if cap.name(&format!("{:?}", Kind::NumLit)).is_some() {
                // TODO: support this
                return Some(Err(LexError::from(self.clone())));
            }

            // change the position of the cursor
            let source_info = self.advance(cap.get(0).unwrap().range().count());
            let text = source_info.as_str();

            let kind;
            if cap.name(&format!("{:?}", Kind::Ident)).is_some() {
                match text {
                    "λ" | "_" => {
                        kind = TokenKind::Symbol;
                    }
                    _ => {
                        kind = TokenKind::Ident;
                    }
                }
            } else {
                assert!(cap.name(&format!("{:?}", Kind::Symbol)).is_some());
                kind = TokenKind::Symbol;
            };
            return Some(Ok(Token { kind, source_info }));
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Fixity {
    /// alias to Infixl
    Infix,
    Infixl,
    Infixr,
    Nofix,
    Prefix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Operator {
    symbol: String,
    fixity: Fixity,
    prec: usize,
    entity: Name,
}

#[derive(Default, Debug)]
struct TokenTable {
    led: HashMap<String, Operator>,
    nud: HashMap<String, Operator>,
}

impl TokenTable {
    fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        match op.fixity {
            Fixity::Infix | Fixity::Infixl | Fixity::Infixr => {
                let sym = op.symbol.clone();
                if self.led.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
            Fixity::Nofix | Fixity::Prefix => {
                let sym = op.symbol.clone();
                if self.nud.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
        };
        Ok(())
    }
}

enum Led {
    App,
    User(Operator),
}

impl Led {
    fn prec(&self) -> usize {
        match self {
            Self::App => 1024,
            Self::User(op) => op.prec,
        }
    }
}

enum Nud {
    Mvar,
    Var,
    Abs,
    Forall,
    Exists,
    Paren,
    Bracket,
    User(Operator),
}

impl TokenTable {
    fn get_led(&self, token: &Token) -> Option<Led> {
        match token.kind {
            TokenKind::Ident => Some(Led::App),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match self.led.get(lit) {
                    Some(op) => Some(Led::User(op.clone())),
                    None => {
                        if self.get_nud(token).is_some() {
                            Some(Led::App)
                        } else {
                            None
                        }
                    }
                }
            }
        }
    }

    fn get_nud(&self, token: &Token) -> Option<Nud> {
        match token.kind {
            TokenKind::Ident => {
                if token.as_str().starts_with('#') {
                    Some(Nud::Mvar)
                } else {
                    Some(Nud::Var)
                }
            }
            TokenKind::Symbol => {
                let lit = token.as_str();
                match lit {
                    "(" => Some(Nud::Paren),
                    "⟨" => Some(Nud::Bracket),
                    "λ" => Some(Nud::Abs),
                    "∀" => Some(Nud::Forall),
                    "∃" => Some(Nud::Exists),
                    _ => self.nud.get(token.as_str()).map(|op| Nud::User(op.clone())),
                }
            }
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("{lex_error}")]
    Lex { lex_error: LexError },
    #[error("parse error: {message} at {source_info}")]
    Parse {
        message: String,
        source_info: String,
    },
    #[error("unexpected end of input at {source_info}")]
    Eof { source_info: String },
}

// Since LexError is not 'static we only want #[from] and don't need #[source],
// but this is impossible because #[from] attibute always implies #[source].
// So I am implementing it manually.
impl From<LexError> for ParseError {
    fn from(err: LexError) -> Self {
        Self::Lex { lex_error: err }
    }
}

pub struct Parser<'a, 'b> {
    lex: &'b mut Lex<'a>,
    env: &'b Env,
    locals: Vec<Name>,
}

impl<'a, 'b> Parser<'a, 'b> {
    fn new(lex: &'b mut Lex<'a>, env: &'b Env) -> Self {
        Self {
            lex,
            env,
            locals: vec![],
        }
    }

    fn fail<R>(token: Token<'a>, message: impl Into<String>) -> Result<R, ParseError> {
        Err(ParseError::Parse {
            message: message.into(),
            source_info: token.source_info.to_string(),
        })
    }

    fn eof_error(&self) -> ParseError {
        ParseError::Eof {
            source_info: SourceInfo::eof(self.lex.input).to_string(),
        }
    }

    fn optional<F, R>(&mut self, f: F) -> Option<R>
    where
        F: FnOnce(&mut Self) -> Result<R, ParseError>,
    {
        let state = self.lex.save();
        match f(self) {
            Ok(m) => Some(m),
            Err(_err) => {
                self.lex.restore(state);
                None
            }
        }
    }

    fn peek_opt(&mut self) -> Option<Token<'a>> {
        self.optional(|this| this.peek())
    }

    fn peek(&mut self) -> Result<Token<'a>, ParseError> {
        self.lex
            .clone()
            .next()
            .transpose()?
            .ok_or_else(|| self.eof_error())
    }

    fn advance(&mut self) {
        self.lex
            .next()
            .expect("unchecked advance")
            .expect("impossible lex error! probably due to unchecked advance");
    }

    pub fn eof(&mut self) -> Result<(), ParseError> {
        if let Some(token) = self.peek_opt() {
            Self::fail(token, "expected EOF but tokens remain")?;
        }
        Ok(())
    }

    pub fn eof_opt(&mut self) -> bool {
        self.peek_opt().is_none()
    }

    fn any_token(&mut self) -> Result<Token<'a>, ParseError> {
        self.lex
            .next()
            .transpose()
            .expect("lex error")
            .ok_or_else(|| self.eof_error())
    }

    fn ident(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_ident() {
            return Self::fail(token, "expected identifier");
        }
        Ok(token)
    }

    fn ident_opt(&mut self) -> Option<Token<'a>> {
        if let Some(token) = self.peek_opt() {
            if token.is_ident() {
                self.advance();
                return Some(token);
            }
        }
        None
    }

    fn symbol(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_symbol() {
            return Self::fail(token, "expected symbol");
        }
        Ok(token)
    }

    fn expect_symbol(&mut self, sym: &str) -> Result<(), ParseError> {
        let token = self.any_token()?;
        if token.kind == TokenKind::Symbol && token.as_str() == sym {
            return Ok(());
        }
        Self::fail(token, format!("expected symbol '{}'", sym))
    }

    fn expect_symbol_opt(&mut self, sym: &str) -> Option<Token<'a>> {
        if let Some(token) = self.peek_opt() {
            if token.kind == TokenKind::Symbol && token.as_str() == sym {
                self.advance();
                return Some(token);
            }
        }
        None
    }

    pub fn name(&mut self) -> Result<Name, ParseError> {
        Ok(Name::try_from(self.ident()?.as_str()).expect("logic flaw"))
    }

    fn name_opt(&mut self) -> Option<Name> {
        self.ident_opt()
            .map(|token| Name::try_from(token.as_str()).expect("logic flaw"))
    }

    fn type_primary(&mut self) -> Result<Type, ParseError> {
        if let Some(name) = self.name_opt() {
            match self.env.get_const_type(name.as_str()) {
                Some(arity) => {
                    if arity != 0 {
                        // TODO
                        todo!();
                    }
                    return Ok(Type::Const(name));
                }
                None => {
                    return Ok(Type::Var(name));
                }
            }
        }
        let token = self.any_token()?;
        if token.is_symbol() && token.as_str() == "(" {
            let t = self.ty()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else {
            todo!()
        }
    }

    pub fn ty(&mut self) -> Result<Type, ParseError> {
        let t = self.type_primary()?;
        if let Some(token) = self.peek_opt() {
            if token.is_symbol() && token.as_str() == "→" {
                self.advance();
                return Ok(Type::Arrow(Arc::new((t, self.ty()?))));
            }
        }
        Ok(t)
    }

    /// typed parameters e.g. `"(x y : T)"`
    fn parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError> {
        let mut idents = vec![];
        // needs at least one parameter
        idents.push(self.name()?);
        while let Some(name) = self.name_opt() {
            idents.push(name);
        }
        // TODO: allow declarations with no explict types
        self.expect_symbol(":")?;
        let t = self.ty()?;
        self.expect_symbol(")")?;
        Ok((idents, t))
    }

    fn parameters(&mut self) -> Result<Vec<(Name, Option<Type>)>, ParseError> {
        let mut params = vec![];
        loop {
            if let Some(token) = self.expect_symbol_opt("(") {
                let (names, t) = self.parameter(token)?;
                for name in names {
                    params.push((name, Some(t.clone())));
                }
            } else if let Some(name) = self.name_opt() {
                params.push((name, None));
            } else {
                break;
            }
        }
        Ok(params)
    }

    pub fn term(&mut self) -> Result<Term, ParseError> {
        self.subterm(0)
    }

    fn term_opt(&mut self) -> Option<Term> {
        self.optional(|this| this.term())
    }

    fn term_abs(&mut self, _token: Token) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, _) in &params {
            self.locals.push(name.clone());
        }
        let mut m = self.subterm(0)?;
        for _ in 0..params.len() {
            self.locals.pop();
        }
        for (name, t) in params.into_iter().rev() {
            let t = t.unwrap_or_else(|| Type::Var(Name::fresh()));
            m.discharge_locals([(&name, t)]);
        }
        Ok(m)
    }

    // TODO remove
    fn mk_const_unchecked(&self, name: &str) -> Term {
        let (ty_params, _) = self.env.get_const(name).expect("unknown constant");
        let mut ty_args = vec![];
        for _ in ty_params {
            ty_args.push(Type::Var(Name::fresh()));
        }
        Term::Const(Arc::new((
            Name::try_from(name).expect("invalid name"),
            ty_args,
        )))
    }

    fn term_forall(&mut self, _token: Token) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, _) in &params {
            self.locals.push(name.clone());
        }
        let mut m = self.subterm(0)?;
        for _ in 0..params.len() {
            self.locals.pop();
        }
        for (name, t) in params.into_iter().rev() {
            let t = t.unwrap_or_else(|| Type::Var(Name::fresh()));
            m.discharge_locals([(&name, t)]);
            let f = mem::take(&mut m);
            m = self.mk_const_unchecked("forall");
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_exists(&mut self, _token: Token) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, _) in &params {
            self.locals.push(name.clone());
        }
        let mut m = self.subterm(0)?;
        for _ in 0..params.len() {
            self.locals.pop();
        }
        for (name, t) in params.into_iter().rev() {
            let t = t.unwrap_or_else(|| Type::Var(Name::fresh()));
            m.discharge_locals([(&name, t)]);
            let f = mem::take(&mut m);
            m = self.mk_const_unchecked("exists");
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_var(&mut self, token: Token<'a>, entity: Option<Name>) -> Result<Term, ParseError> {
        let name = match entity {
            None => Name::try_from(token.as_str()).expect("logic flaw"),
            Some(s) => s,
        };
        for local in &self.locals {
            if local == &name {
                return Ok(Term::Local(name));
            }
        }
        let Some((tv, _)) = self.env.get_const(name.as_str()) else {
            return Self::fail(token, "constant not found");
        };
        // TODO: parse type parameters
        let mut type_args = vec![];
        for _ in tv {
            type_args.push(Type::Var(Name::fresh()));
        }
        Ok(Term::Const(Arc::new((name, type_args))))
    }

    fn term_mvar(&mut self, token: Token) -> Term {
        let name = Name::try_from(&token.as_str()[1..]).expect("logic flaw");
        Term::Mvar(name)
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError> {
        let token = self.any_token()?;
        // nud
        let nud = match self.env.token_table().get_nud(&token) {
            None => todo!("nud unknown: {}", token),
            Some(nud) => nud,
        };
        let mut left = match nud {
            Nud::Var => self.term_var(token, None)?,
            Nud::Mvar => self.term_mvar(token),
            Nud::Abs => self.term_abs(token)?,
            Nud::Paren => {
                let m = self.term()?;
                self.expect_symbol(")")?;
                m
            }
            Nud::Bracket => {
                let mut terms = vec![];
                while let Some(m) = self.term_opt() {
                    terms.push(m);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("⟩")?;
                // right associative encoding:
                // ⟨⟩ ⇒ star
                // ⟨m⟩ ⇒ m
                // ⟨m,n,l⟩ ⇒ ⟨m, ⟨n, l⟩⟩
                match terms.len() {
                    0 => self.mk_const_unchecked("star"),
                    1 => terms.pop().unwrap(),
                    _ => {
                        let mut m = terms.pop().unwrap();
                        for n in terms.into_iter().rev() {
                            let mut x = self.mk_const_unchecked("pair");
                            x.apply(vec![n, m]);
                            m = x;
                        }
                        m
                    }
                }
            }
            Nud::Forall => self.term_forall(token)?,
            Nud::Exists => self.term_exists(token)?,
            Nud::User(op) => match op.fixity {
                Fixity::Nofix => self.term_var(token, Some(op.entity))?,
                Fixity::Prefix => {
                    let mut fun = self.term_var(token, Some(op.entity))?;
                    let arg = self.subterm(op.prec)?;
                    fun.apply(vec![arg]);
                    fun
                }
                Fixity::Infix | Fixity::Infixl | Fixity::Infixr => unreachable!(),
            },
        };
        while let Some(token) = self.peek_opt() {
            let led = match self.env.token_table().get_led(&token) {
                None => break,
                Some(led) => led,
            };
            let prec = led.prec();
            if rbp >= prec {
                break;
            }
            match led {
                Led::App => {
                    let right = self.subterm(led.prec())?;
                    left.apply(vec![right])
                }
                Led::User(op) => {
                    let prec = match op.fixity {
                        Fixity::Infix | Fixity::Infixl => prec,
                        Fixity::Infixr => prec - 1,
                        Fixity::Nofix | Fixity::Prefix => unreachable!("op = {op:?}"),
                    };
                    self.advance();
                    let mut fun = self.term_var(token, Some(op.entity))?;
                    let right = self.subterm(prec)?;
                    fun.apply(vec![left, right]);
                    left = fun;
                }
            }
        }
        Ok(left)
    }
}

#[derive(Debug, Default)]
struct Printer {
    op_table: HashMap<Name, Operator>,
}

impl Printer {
    fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        let entity = op.entity.clone();
        if self.op_table.insert(entity, op).is_some() {
            bail!("notation already defined");
        }
        Ok(())
    }

    fn fmt_term_help(
        &self,
        m: &Term,
        prec: usize,
        mut allow_lambda: bool,
        local_names: &mut Vec<Name>,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        if !m.binders().any(|_| true) {
            let (_, head, mut args) = m.triple();
            if let Term::Const(c) = head {
                let name = &c.0;
                if let Some(op) = self.op_table.get(name) {
                    match op.fixity {
                        Fixity::Infix | Fixity::Infixl => {
                            if args.len() == 2 {
                                if prec >= op.prec {
                                    write!(f, "(")?;
                                    allow_lambda = true;
                                }
                                let m2 = args.pop().unwrap();
                                let m1 = args.pop().unwrap();
                                self.fmt_term_help(m1, op.prec - 1, false, local_names, f)?;
                                write!(f, " {} ", op.symbol)?;
                                self.fmt_term_help(m2, op.prec, allow_lambda, local_names, f)?;
                                if prec >= op.prec {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                        }
                        Fixity::Infixr => {
                            if args.len() == 2 {
                                if prec >= op.prec {
                                    write!(f, "(")?;
                                    allow_lambda = true;
                                }
                                let m2 = args.pop().unwrap();
                                let m1 = args.pop().unwrap();
                                self.fmt_term_help(m1, op.prec, false, local_names, f)?;
                                write!(f, " {} ", op.symbol)?;
                                self.fmt_term_help(m2, op.prec - 1, allow_lambda, local_names, f)?;
                                if prec >= op.prec {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                        }
                        Fixity::Nofix => {
                            if args.is_empty() {
                                write!(f, "{}", op.symbol)?;
                                return Ok(());
                            }
                        }
                        Fixity::Prefix => {
                            if args.len() == 1 {
                                if prec > op.prec {
                                    write!(f, "(")?;
                                    allow_lambda = true;
                                }
                                write!(f, "{}", op.symbol)?;
                                let m = args.pop().unwrap();
                                self.fmt_term_help(m, op.prec, allow_lambda, local_names, f)?;
                                if prec > op.prec {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                        }
                    }
                }
                match name.as_str() {
                    "forall" => {
                        if args.len() == 1 {
                            let mut arg = args.pop().unwrap();
                            if let Term::Abs(a) = &mut arg {
                                if !allow_lambda {
                                    write!(f, "(")?;
                                }
                                let x = Name::fresh();
                                write!(f, "∀ ({} : {}), ", x, a.binder)?;
                                local_names.push(x);
                                self.fmt_term_help(&a.body, 0, true, local_names, f)?;
                                local_names.pop();
                                if !allow_lambda {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                            args.push(arg);
                        }
                    }
                    "exists" => {
                        if args.len() == 1 {
                            let mut arg = args.pop().unwrap();
                            if let Term::Abs(a) = &mut arg {
                                if !allow_lambda {
                                    write!(f, "(")?;
                                }
                                let x = Name::fresh();
                                write!(f, "∃ ({} : {}), ", x, a.binder)?;
                                local_names.push(x);
                                self.fmt_term_help(&a.body, 0, true, local_names, f)?;
                                local_names.pop();
                                if !allow_lambda {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                            args.push(arg);
                        }
                    }
                    _ => {}
                }
            }
        }

        match m {
            Term::Var(i) => match local_names.get(*i) {
                Some(name) => write!(f, "{name}"),
                None => write!(f, "{i}"),
            },
            Term::Local(name) => write!(f, "{}", name),
            Term::Const(c) => {
                write!(f, "{}", c.0)?;
                if !c.1.is_empty() {
                    write!(
                        f,
                        ".{{{}}}",
                        c.1.iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                Ok(())
            }
            Term::Mvar(name) => write!(f, "#{}", name),
            Term::Abs(a) => {
                if !allow_lambda {
                    write!(f, "(")?;
                }
                let x = Name::fresh();
                write!(f, "λ ({} : {}), ", x, a.binder)?;
                local_names.push(x);
                self.fmt_term_help(&a.body, 0, true, local_names, f)?;
                local_names.pop();
                if !allow_lambda {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Term::App(p) => {
                if prec >= 1024 {
                    write!(f, "(")?;
                    allow_lambda = true;
                }
                self.fmt_term_help(&p.0, 1023, false, local_names, f)?;
                write!(f, " ")?;
                self.fmt_term_help(&p.1, 1024, allow_lambda, local_names, f)?;
                if prec >= 1024 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }

    fn fmt_term(&self, m: &Term, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut local_names = vec![];
        let res = self.fmt_term_help(m, 0, true, &mut local_names, f);
        assert!(local_names.is_empty());
        res
    }

    fn fmt_type_help(
        &self,
        t: &Type,
        prec: usize,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        match t {
            Type::Const(name) => write!(f, "{name}"),
            Type::Arrow(p) => {
                let (t1, t2) = &**p;
                if prec > 0 {
                    write!(f, "(")?;
                }
                self.fmt_type_help(t1, 1, f)?;
                write!(f, " → ")?;
                self.fmt_type_help(t2, 0, f)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::Var(mvar) => write!(f, "{mvar}"),
        }
    }
}
