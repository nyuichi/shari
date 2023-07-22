//! [Type] and [Term] may be ill-formed.

// TODO: quasiquote and pattern match

use anyhow::{anyhow, bail, Context};
use core::ops::Range;
use once_cell::sync::Lazy;
use regex::Regex;
use std::collections::{HashMap, VecDeque};
use std::mem;
use std::sync::Arc;
use thiserror::Error;

// TODO: Use string name
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MvarId(usize);

impl MvarId {
    // TODO: reclaim unused mvars
    pub fn fresh() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNTER: Lazy<AtomicUsize> = Lazy::new(Default::default);
        Self(COUNTER.fetch_add(1, Ordering::Relaxed))
    }

    pub fn id(&self) -> usize {
        self.0
    }
}

impl std::fmt::Display for MvarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id())
    }
}

#[derive(Debug, Default, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Name(String);

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for Name {
    fn from(value: &str) -> Self {
        // TODO: validation
        Self(value.to_owned())
    }
}

impl Name {
    // TODO: fixme
    fn fresh() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNTER: Lazy<AtomicUsize> = Lazy::new(Default::default);
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        Name(format!("#{id}"))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Type {
    Const(Name),
    Arrow(Arc<(Type, Type)>),
    // TODO: rename?
    Mvar(MvarId),
}

impl Default for Type {
    fn default() -> Self {
        Type::Const(Name::default())
    }
}

/// Following notations from [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    pub fn prop() -> Type {
        Type::Const(Name::from("Prop"))
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

    fn instantiate(&mut self, mid: &MvarId, t: &Type) {
        match self {
            Self::Const(_) => {}
            Self::Mvar(x) => {
                if x == mid {
                    *self = t.clone();
                }
            }
            Self::Arrow(p) => {
                let p = Arc::make_mut(p);
                p.0.instantiate(mid, t);
                p.1.instantiate(mid, t);
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
    Mvar(MvarId),
}

impl Default for Term {
    fn default() -> Self {
        Term::Var(usize::MAX)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct Abs {
    pub binder: Type,
    pub body: Term,
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
    pub fn close(&mut self, name: &Name) {
        assert!(self.is_lclosed());
        self.close_at(name, 0)
    }

    fn close_at(&mut self, name: &Name, level: usize) {
        match self {
            Self::Local(x) => {
                if name == x {
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
    pub fn is_fresh(&self, name: &Name) -> bool {
        match self {
            Self::Local(x) => name != x,
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

    fn subst(&mut self, name: &Name, m: &Term) {
        match self {
            Self::Local(x) => {
                if name == x {
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

    // /// triple(λ (v:t)*, m l*) = (t*, m, l*)
    // /// may return locally open terms
    // pub fn triple_mut(&mut self) -> (Vec<&mut Type>, &mut Term, Vec<&mut Term>) {
    //     let mut m = self;
    //     let mut binders = vec![];
    //     while let Self::Abs(a) = m {
    //         let a = Arc::make_mut(a);
    //         binders.push(&mut a.ty);
    //         m = &mut a.body;
    //     }
    //     let mut args: Vec<&mut Term> = vec![];
    //     while let Self::App(p) = m {
    //         let (m1, m2) = Arc::make_mut(p);
    //         args.push(m2);
    //         m = m1;
    //     }
    //     args.reverse();
    //     (binders, m, args)
    // }

    pub fn args_mut(&mut self) -> Vec<&mut Term> {
        let mut m = self;
        while let Self::Abs(a) = m {
            m = &mut Arc::make_mut(a).body;
        }
        let mut args: Vec<&mut Term> = vec![];
        while let Self::App(p) = m {
            let (m1, m2) = Arc::make_mut(p);
            args.push(m2);
            m = m1;
        }
        args.reverse();
        args
    }

    pub fn matrix_mut(&mut self) -> &mut Term {
        let mut m = self;
        while let Self::Abs(a) = m {
            m = &mut Arc::make_mut(a).body;
        }
        m
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

    pub fn apply(&mut self, ms: impl IntoIterator<Item = Term>) {
        for m in ms {
            *self = Term::App(Arc::new((*self, m)));
        }
    }

    pub fn undischarge(&mut self) -> Vec<(Name, Type)> {
        let mut binder = vec![];
        let mut m = &mut *self;
        while let Term::Abs(a) = m {
            let Abs { binder: t, body: n } = Arc::make_mut(a);
            let x = Name::fresh();
            n.open(&x);
            binder.push((x, mem::take(t)));
            m = n;
        }
        *self = mem::take(m);
        binder
    }

    pub fn discharge(&mut self, binder: Vec<(Name, Type)>) {
        let mut m = mem::take(self);
        for (x, t) in binder.into_iter().rev() {
            m.close(&x);
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

    fn instantiate(&mut self, mid: &MvarId, t: &Type) {
        match self {
            Self::Abs(a) => {
                let a = Arc::make_mut(a);
                a.binder.instantiate(mid, t);
                a.body.instantiate(mid, t);
            }
            Self::App(p) => {
                let p = Arc::make_mut(p);
                p.0.instantiate(mid, t);
                p.1.instantiate(mid, t);
            }
            Self::Const(c) => {
                let c = Arc::make_mut(c);
                for u in &mut c.1 {
                    u.instantiate(mid, t);
                }
            }
            Self::Local(_) | Self::Var(_) | Self::Mvar(_) => {}
        }
    }
}

#[derive(Debug)]
pub struct Env {
    name: Name,
    consts: HashMap<Name, (Vec<MvarId>, Type)>,
    const_types: HashMap<Name, usize>,
    defs: HashMap<Name, (Vec<MvarId>, Term)>,
    typedefs: HashMap<Name, (Name, Name, Arc<Fact>)>,
    axioms: HashMap<Name, (Vec<MvarId>, Term)>,
    notations: NotationTable,
}

#[derive(Debug, Default)]
struct NotationTable {
    // symbol to name
    tt: TokenTable,
    // name to symbol
    sugar: HashMap<Name, Operator>,
}

// TODO: allow table lookup
static ENV: Lazy<Arc<Env>> = Lazy::new(|| {
    let mut env = Env::new(Name::from("default"));
    env.add_notation("=", Fixity::Infix, 50, "eq").unwrap();
    env.add_notation("⊤", Fixity::Nofix, usize::MAX, "top")
        .unwrap();
    env.add_notation("∧", Fixity::Infixr, 35, "and").unwrap();
    env.add_notation("→", Fixity::Infixr, 25, "imp").unwrap();
    env.add_notation("⊥", Fixity::Nofix, usize::MAX, "bot")
        .unwrap();
    env.add_notation("∨", Fixity::Infixr, 30, "or").unwrap();
    env.add_notation("¬", Fixity::Prefix, 40, "not").unwrap();
    env.add_notation("↔", Fixity::Infix, 20, "iff").unwrap();
    Arc::new(env)
});

impl PartialEq for Env {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Eq for Env {}

impl Env {
    pub fn default() -> Arc<Env> {
        Arc::clone(&ENV)
    }

    fn new(name: Name) -> Env {
        Env {
            name,
            consts: Default::default(),
            const_types: Default::default(),
            defs: Default::default(),
            typedefs: Default::default(),
            axioms: Default::default(),
            notations: Default::default(),
        }
    }

    fn add_notation(
        &mut self,
        symbol: &str,
        fixity: Fixity,
        prec: usize,
        entity: &str,
    ) -> anyhow::Result<()> {
        let entity = Name::from(entity);
        self.notations
            .tt
            .add(symbol, fixity, prec, entity.clone())?;
        let op = Operator {
            symbol: symbol.to_owned(),
            fixity,
            prec,
            entity: entity.clone(),
        };
        self.notations
            .sugar
            .insert(entity.clone(), op)
            .ok_or_else(|| anyhow!("notation already defined: {entity}"))?;
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
        if m.binders().any(|_| true) {
            let (_, head, mut args) = m.triple();
            if let Term::Local(name) = head {
                if let Some(op) = self.notations.sugar.get(name) {
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
                        "{{{}}}",
                        c.1.iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                Ok(())
            }
            Term::Mvar(name) => write!(f, "?{}", name),
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
}

impl Type {
    fn fmt_type_help(&self, prec: usize, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Const(name) => write!(f, "{name}"),
            Self::Arrow(p) => {
                let (t1, t2) = &**p;
                if prec > 0 {
                    write!(f, "(")?;
                }
                t1.fmt_type_help(1, f)?;
                write!(f, " → ")?;
                t2.fmt_type_help(0, f)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Self::Mvar(mid) => write!(f, "?{mid}"),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.fmt_type_help(0, f)
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        ENV.fmt_term(self, f)
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
            "^".repeat(self.input.get(self.range.clone()).unwrap().chars().count())
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
    fn add(
        &mut self,
        symbol: &str,
        fixity: Fixity,
        prec: usize,
        entity: Name,
    ) -> anyhow::Result<()> {
        let op = Operator {
            symbol: symbol.to_owned(),
            fixity,
            prec,
            entity,
        };
        match fixity {
            Fixity::Infix | Fixity::Infixl | Fixity::Infixr => {
                if self.led.insert(symbol.to_owned(), op).is_some() {
                    bail!("symbol already defined: {symbol}")
                }
            }
            Fixity::Nofix | Fixity::Prefix => {
                if self.nud.insert(symbol.to_owned(), op).is_some() {
                    bail!("symbol already defined: {symbol}")
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
    Var,
    Abs,
    Forall,
    Exists,
    Paren,
    Bracket,
    Placeholder,
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
            TokenKind::Ident => Some(Nud::Var),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match lit {
                    "(" => Some(Nud::Paren),
                    "⟨" => Some(Nud::Bracket),
                    "λ" => Some(Nud::Abs),
                    "∀" => Some(Nud::Forall),
                    "∃" => Some(Nud::Exists),
                    "_" => Some(Nud::Placeholder),
                    _ => self.nud.get(token.as_str()).map(|op| Nud::User(op.clone())),
                }
            }
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseError<'a> {
    #[error("{lex_error}")]
    Lex { lex_error: LexError },
    #[error("parse error: {message} at {source_info}")]
    Parse {
        message: String,
        source_info: SourceInfo<'a>,
    },
    #[error("unexpected end of input at {source_info}")]
    Eof { source_info: SourceInfo<'a> },
}

// Since LexError is not 'static we only want #[from] and don't need #[source],
// but this is impossible because #[from] attibute always implies #[source].
// So I am implementing it manually.
impl<'a> From<LexError> for ParseError<'a> {
    fn from(err: LexError) -> Self {
        Self::Lex { lex_error: err }
    }
}

pub struct Parser<'a, 'b> {
    lex: &'b mut Lex<'a>,
    token_table: &'b TokenTable,
    placeholder: Name,
}

impl<'a, 'b> Parser<'a, 'b> {
    fn new(lex: &'b mut Lex<'a>, token_table: &'b TokenTable) -> Self {
        Self {
            lex,
            token_table,
            placeholder: Name::default(),
        }
    }

    fn fail<R>(token: Token<'a>, message: impl Into<String>) -> Result<R, ParseError> {
        Err(ParseError::Parse {
            message: message.into(),
            source_info: token.source_info,
        })
    }

    fn eof_error(&self) -> ParseError<'a> {
        ParseError::Eof {
            source_info: SourceInfo::eof(self.lex.input),
        }
    }

    fn optional<F, R>(&mut self, f: F) -> Option<R>
    where
        F: FnOnce(&mut Self) -> Result<R, ParseError<'a>>,
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

    fn peek(&mut self) -> Result<Token<'a>, ParseError<'a>> {
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

    pub fn eof(&mut self) -> Result<(), ParseError<'a>> {
        if let Some(token) = self.peek_opt() {
            Self::fail(token, "expected EOF but tokens remain")?;
        }
        Ok(())
    }

    pub fn eof_opt(&mut self) -> bool {
        self.peek_opt().is_none()
    }

    fn any_token(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        self.lex
            .next()
            .transpose()
            .expect("lex error")
            .ok_or_else(|| self.eof_error())
    }

    fn ident(&mut self) -> Result<Token<'a>, ParseError<'a>> {
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

    fn symbol(&mut self) -> Result<Token<'a>, ParseError<'a>> {
        let token = self.any_token()?;
        if !token.is_symbol() {
            return Self::fail(token, "expected symbol");
        }
        Ok(token)
    }

    fn expect_symbol(&mut self, sym: &str) -> Result<(), ParseError<'a>> {
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

    pub fn name(&mut self) -> Result<Name, ParseError<'a>> {
        Ok(Name(self.ident()?.as_str().to_owned()))
    }

    fn name_opt(&mut self) -> Option<Name> {
        self.ident_opt()
            .map(|token| Name(token.as_str().to_owned()))
    }

    fn type_primary(&mut self) -> Result<Type, ParseError<'a>> {
        if let Some(name) = self.name_opt() {
            return Ok(Type::Const(name));
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

    pub fn ty(&mut self) -> Result<Type, ParseError<'a>> {
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
    fn parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError<'a>> {
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

    fn parameters(&mut self) -> Result<Vec<(Name, Option<Type>)>, ParseError<'a>> {
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

    pub fn term(&mut self) -> Result<Term, ParseError<'a>> {
        self.placeholder = Name::fresh();
        let mut m = self.subterm(0)?;
        m.open(&self.placeholder);
        Ok(m)
    }

    fn term_opt(&mut self) -> Option<Term> {
        self.optional(|this| this.term())
    }

    fn term_abs(&mut self, _token: Token) -> Result<Term, ParseError<'a>> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        let mut m = self.subterm(0)?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, t) in params.into_iter().rev() {
            let t = t.unwrap_or_else(|| Type::Mvar(MvarId::fresh()));
            m.discharge(vec![(name, t)]);
        }
        Ok(m)
    }

    fn term_forall(&mut self, _token: Token) -> Result<Term, ParseError<'a>> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        let mut m = self.subterm(0)?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, t) in params.into_iter().rev() {
            let t = t.unwrap_or_else(|| Type::Mvar(MvarId::fresh()));
            m.discharge(vec![(name, t)]);
            let f = mem::take(&mut m);
            m = Term::Local(Name("forall".to_owned()));
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_exists(&mut self, _token: Token) -> Result<Term, ParseError<'a>> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        let mut m = self.subterm(0)?;
        if params.is_empty() {
            todo!("empty binding");
        }
        for (name, t) in params.into_iter().rev() {
            let t = t.unwrap_or_else(|| Type::Mvar(MvarId::fresh()));
            m.discharge(vec![(name, t)]);
            let f = mem::take(&mut m);
            m = Term::Local(Name("exists".to_owned()));
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_var(&mut self, token: Token, entity: Option<Name>) -> Term {
        let name = match entity {
            None => Name(token.as_str().to_owned()),
            Some(s) => s,
        };
        // TODO: parse as const
        Term::Local(name)
    }

    fn term_placeholder(&mut self, _token: Token) -> Term {
        Term::Local(self.placeholder.clone())
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError<'a>> {
        let token = self.any_token()?;
        // nud
        let nud = match self.token_table.get_nud(&token) {
            None => todo!("nud unknown: {}", token),
            Some(nud) => nud,
        };
        let mut left = match nud {
            Nud::Var => self.term_var(token, None),
            Nud::Placeholder => self.term_placeholder(token),
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
                    0 => Term::Local(Name("star".to_owned())),
                    1 => terms.pop().unwrap(),
                    _ => {
                        let mut m = terms.pop().unwrap();
                        for n in terms.into_iter().rev() {
                            let mut x = Term::Local(Name("tuple".to_owned()));
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
                Fixity::Nofix => self.term_var(token, Some(op.entity)),
                Fixity::Prefix => {
                    let mut fun = self.term_var(token, Some(op.entity));
                    let arg = self.subterm(op.prec)?;
                    fun.apply(vec![arg]);
                    fun
                }
                _ => unreachable!(),
            },
        };
        while let Some(token) = self.peek_opt() {
            let led = match self.token_table.get_led(&token) {
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
                        Fixity::Infixl => prec,
                        Fixity::Infixr => prec - 1,
                        _ => unreachable!(),
                    };
                    self.advance();
                    let mut fun = self.term_var(token, Some(op.entity));
                    let right = self.subterm(prec)?;
                    fun.apply(vec![left, right]);
                    left = fun;
                }
            }
        }
        Ok(left)
    }
}

impl std::str::FromStr for Term {
    // TODO: add ParseErrorOwned
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut lex = Lex::new(s);
        let mut parser = Parser::new(&mut lex, &ENV.notations.tt);
        parser.term().map_err(|_| ())
    }
}

#[derive(Clone, Debug, Default)]
struct Subst<T>(Vec<(MvarId, T)>);

impl Subst<Type> {
    fn apply_type(&self, t: &mut Type) {
        for (mid, u) in &self.0 {
            t.instantiate(mid, u);
        }
    }

    fn apply_term(&self, m: &mut Term) {
        for (mid, t) in &self.0 {
            m.instantiate(mid, t);
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
            (Type::Mvar(i), t) | (t, Type::Mvar(i)) => {
                if !self.0.iter().any(|(j, _)| j == i) {
                    // TODO: occur check
                    self.0.push((*i, t.clone()));
                } else {
                    let mut u = Type::Mvar(*i);
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LocalEnv {
    env: Arc<Env>,
    locals: Vec<(Name, Type)>,
}

impl std::fmt::Display for LocalEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ▶", self.env.name)?;
        if self.locals.is_empty() {
            write!(f, " ")?;
        } else {
            for (x, t) in &self.locals {
                write!(f, " ({} : {})", x, t)?;
            }
        }
        Ok(())
    }
}

impl LocalEnv {
    fn get_local(&self, name: &Name) -> Option<&Type> {
        for (x, t) in self.locals.iter().rev() {
            if x == name {
                return Some(t);
            }
        }
        None
    }

    fn get_const(&self, name: &Name) -> Option<&(Vec<MvarId>, Type)> {
        if let Some(s) = self.env.consts.get(name) {
            return Some(s);
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
                if let Some(u) = self.get_local(name) {
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
                let mut t = Type::Arrow(Arc::new((t2, Type::Mvar(MvarId::fresh()))));
                subst.unify(&mut t1, &mut t)?;
                let Type::Arrow(mut p) = t else {
                    panic!("logic flaw");
                };
                Ok(mem::take(&mut Arc::make_mut(&mut p).1))
            }
            Term::Const(c) => {
                let c = Arc::make_mut(c);
                if let Some((tv, ty)) = self.get_const(&c.0) {
                    if tv.len() != c.1.len() {
                        bail!("number of type variables mismatch");
                    }
                    let mut new_tv: Vec<_> = std::iter::repeat_with(|| Type::Mvar(MvarId::fresh()))
                        .take(tv.len())
                        .collect();
                    let mut ty = ty.clone();
                    for (old, new) in std::iter::zip(tv, &new_tv) {
                        ty.instantiate(old, new);
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

    pub fn infer_unchecked_help<'a>(&self, m: &'a Term, var_stack: &mut Vec<&'a Type>) -> Type {
        match m {
            Term::Local(name) => self.get_local(name).unwrap().clone(),
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
                let (mvars, ty) = self.get_const(&c.0).unwrap();
                let mut ty = ty.clone();
                for (mid, t) in std::iter::zip(mvars, &c.1) {
                    ty.instantiate(mid, t);
                }
                ty
            }
            Term::Mvar(_) => panic!("term not ground"),
        }
    }

    pub fn infer_unchecked(&self, m: &Term) -> Type {
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
        // TODO: avoid quadratic cost
        let t = self.infer_unchecked(m);
        match t {
            Type::Arrow(_) => {
                if let Term::Abs(a) = m {
                    self.is_canonical(&a.body)
                } else {
                    false
                }
            }
            Type::Const(_) => {
                let mut m = m;
                while let Term::App(p) = m {
                    if !self.is_canonical(&p.1) {
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
            Type::Mvar(_) => {
                // type must be known
                false
            }
        }
    }

    /// [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_neutral(&self, m: &mut Term) {
        assert!(m.is_neutral());
        // [x M₁ ... Mₙ] := x [M₁] ... [Mₙ]
        for arg in m.args_mut() {
            self.eta_expand_normal(arg);
        }
        // TODO avoid quadratic cost
        let t = self.infer_unchecked(m);
        // [M] := λv₁ v₂ ⋯. M v₁ v₂ ⋯
        let binders: Vec<_> = t
            .args()
            .into_iter()
            .map(|t| (Name::fresh(), t.clone()))
            .collect();
        m.apply(binders.iter().map(|(x, _)| Term::Local(x.to_owned())));
        m.discharge(binders);
    }

    /// 1. [λx.M] := λx.[M]
    /// 2. [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_normal(&self, m: &mut Term) {
        assert!(m.is_normal());
        self.eta_expand_neutral(m.matrix_mut());
    }

    /// [m] must be type-correct, ground, and locally closed.
    pub fn canonicalize(&self, m: &mut Term) {
        assert!(m.is_ground());
        assert!(m.is_lclosed());
        assert!(self.type_correct(m));
        m.beta_reduce();
        self.eta_expand_normal(m);
    }

    /// [m1] and [m2] must be type-correct and type-equal under the same environment.
    pub fn eq(&self, m1: &Term, m2: &Term) -> bool {
        let mut m1 = m1.clone();
        let mut m2 = m2.clone();
        self.canonicalize(&mut m1);
        self.canonicalize(&mut m2);
        m1 == m2
    }

    pub fn merge(&mut self, other: &mut Self) -> anyhow::Result<()> {
        if self.env.name != other.env.name {
            bail!(
                "environment mismatch: {} and {}",
                self.env.name,
                other.env.name
            );
        }
        for (name, ty) in &mut other.locals {
            let mut found = false;
            for (n, t) in &self.locals {
                if name == n {
                    if ty == t {
                        found = true;
                        break;
                    } else {
                        bail!("type mismatch in locals: ({name} : {ty}) and ({n} : {t})");
                    }
                }
            }
            if !found {
                self.locals.push((mem::take(name), mem::take(ty)));
            }
        }
        Ok(())
    }
}

fn mk_const(name: &str) -> Term {
    Term::Local(Name::from(name))
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
    let Term::Local(name) = m else {
        return None;
    };
    if name.as_str() != f {
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
        write!(f, "{} ▶ ", self.local_env.env.name)?;
        for (x, t) in &self.local_env.locals {
            write!(f, "({} : {}) ", x, t)?;
        }
        write!(f, "| ")?;
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
    let ty = local_env
        .infer(&mut target)
        .with_context(|| format!("infer: {local_env} ⊢ {target}"))?;
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
/// --------------------------
/// eq_intro t : [Γ ▸ ⊢ m = m]
/// ```
pub fn eq_intro(local_env: LocalEnv, mut m1: Term, mut m2: Term) -> anyhow::Result<Fact> {
    if !m1.is_ground() {
        bail!("term not ground: {m1}");
    }
    if !m2.is_ground() {
        bail!("term not ground: {m2}");
    }
    let t1 = local_env
        .infer(&mut m1)
        .with_context(|| format!("infer: {local_env} ⊢ {m1}"))?;
    let t2 = local_env
        .infer(&mut m2)
        .with_context(|| format!("infer: {local_env} ⊢ {m2}"))?;
    if t1 != t2 {
        bail!("type mismatch: {t1} and {t2}");
    }
    if !local_env.eq(&m1, &m2) {
        bail!("terms not definitionally equal: {m1} and {m2}");
    }
    let mut target = mk_const("eq");
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
pub fn eq_elim(c: &Term, h1: &Fact, h2: &Fact) -> anyhow::Result<Fact> {
    if !c.is_contextual() {
        bail!("expected context, but got {c}");
    }
    if !c.is_ground() {
        bail!("context not ground: {c}");
    }
    let Some((m1, m2)) = dest_call2(&mut h1.target.clone(), "eq") else {
        bail!("expected equality, but got {}", h1.target);
    };
    let mut cm2 = c.clone();
    cm2.fill(&m2);
    let t = h2
        .local_env
        .infer(&mut cm2)
        .with_context(|| format!("the context term is not type-correct: {c}"))?;
    if t != Type::prop() {
        bail!("expected Prop, but got {t}");
    }
    if !h2.local_env.eq(&h2.target, &cm2) {
        bail!("terms not definitionally equal: {} and {}", h2.target, cm2);
    }
    let mut local_env = h1.local_env.clone();
    local_env
        .merge(&mut h2.local_env.clone())
        .context("merge local environments")?;
    let mut ctx: Vec<_> = h1
        .ctx
        .iter()
        .cloned()
        .chain(h2.ctx.iter().cloned())
        .collect();
    ctx.sort();
    ctx.dedup();
    let mut target = c.clone();
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
pub fn prop_ext(h1: &Fact, h2: &Fact) -> anyhow::Result<Fact> {
    let mut local_env = h1.local_env.clone();
    local_env.merge(&mut h2.local_env.clone())?;
    let mut ctx: Vec<_> = h1
        .ctx
        .iter()
        .cloned()
        .filter(|p| p != &h2.target)
        .chain(h2.ctx.iter().cloned().filter(|p| p != &h1.target))
        .collect();
    ctx.sort();
    ctx.dedup();
    let mut target = mk_const("eq");
    target.apply([h1.target.clone(), h2.target.clone()]);
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
pub fn fun_ext(x: &Name, t: &Type, h: &Fact) -> anyhow::Result<Fact> {
    let Some((mut m1, mut m2)) = dest_call2(&mut h.target.clone(), "eq") else {
        bail!("expected equality, but got {}", h.target);
    };
    if h.local_env.get_const(x).is_some() {
        bail!("cannot quantify over constant variable: {x}");
    }
    if let Some(s) = h.local_env.get_local(x) {
        if s != t {
            bail!("variable type not compatible: expected ({x} : {t}), but got ({x} : {s})");
        }
    }
    if !h.ctx.iter().all(|m| m.is_fresh(x)) {
        bail!("eigenvariable condition fails");
    }
    let local_env = LocalEnv {
        env: Arc::clone(&h.local_env.env),
        locals: h
            .local_env
            .locals
            .iter()
            .cloned()
            .filter(|p| &p.0 != x)
            .collect(),
    };
    m1.discharge(vec![(x.clone(), t.clone())]);
    m2.discharge(vec![(x.clone(), t.clone())]);
    let mut target = mk_const("eq");
    target.apply([m1, m2]);
    Ok(Fact {
        local_env,
        ctx: h.ctx.clone(),
        target,
    })
}

/// A convenient representation of head normal form.
/// Recall that every (normal) term has form `λv*. m n*`.
#[derive(Clone)]
struct Triple {
    /// Outermost-first
    binders: Vec<Type>,
    /// Var, Const, or Mvar.
    /// Using locally nameless forms directly.
    head: Term,
    /// Huch calls these parts "arguments" [Huch, 2020](https://www21.in.tum.de/teaching/sar/SS20/5.pdf).
    /// See also Notation 2.29 in The Clausal Theory of Types [Wolfram, 2009].
    args: Vec<Term>,
}

// impl From<Term> for Triple {
//     fn from(mut m: Term) -> Self {
//         assert!(m.is_canonical());
//         let binder = m.unabstract();
//         let args = m.uncurry();
//         let head = m;
//         Self {
//             binders: binder,
//             head,
//             args,
//         }
//     }
// }

impl From<Triple> for Term {
    fn from(m: Triple) -> Self {
        let Triple {
            binders,
            head,
            args,
        } = m;
        let mut m = head;
        m.apply(args);
        for t in binders.into_iter().rev() {
            m = Self::Abs(Arc::new(Abs { binder: t, body: m }));
        }
        m
    }
}

impl Triple {
    /// See [Vukmirović+, 2020].
    pub fn is_flex(&self) -> bool {
        match self.head {
            Term::Mvar(_) => true,
            Term::Var(_) | Term::Local(_) | Term::Const(_) => false,
            Term::Abs(_) | Term::App(_) => unreachable!(),
        }
    }

    /// See [Vukmirović+, 2020].
    pub fn is_rigid(&self) -> bool {
        !self.is_flex()
    }
}

/// In Huet's original paper a disagreement set is just a finite set of pairs of terms.
/// For performance improvement, we classify pairs into rigid/rigid, flex/rigid, and flex/flex
/// at the preprocessing phase.
#[derive(Default)]
struct DisagreementSet {
    // rigid-rigid
    rr: Vec<(Triple, Triple)>,
    // flex-rigid
    fr: Vec<(Triple, Triple)>,
    // flex-flex
    ff: Vec<(Triple, Triple)>,
}

impl DisagreementSet {
    fn add(&mut self, m1: Triple, m2: Triple) {
        match (m1.is_rigid(), m2.is_rigid()) {
            (true, true) => self.rr.push((m1, m2)),
            (true, false) => self.fr.push((m2, m1)),
            (false, true) => self.fr.push((m1, m2)),
            (false, false) => self.ff.push((m1, m2)),
        }
    }

    /// decompose rigid-rigid pairs by chopping into smaller ones
    fn simplify(&mut self) -> bool {
        while let Some((h1, h2)) = self.rr.pop() {
            assert_eq!(h1.binders, h2.binders);
            if h1.head != h2.head {
                return false;
            }
            assert_eq!(h1.args.len(), h2.args.len());
            for (a1, a2) in h1.args.into_iter().zip(h2.args.into_iter()) {
                // TODO: fixme. a1 and a2 may be abstractions
                let a1 = Triple {
                    binders: h1.binders.clone(),
                    head: a1,
                    args: vec![],
                };
                let a2 = Triple {
                    binders: h2.binders.clone(),
                    head: a2,
                    args: vec![],
                };
                self.add(a1, a2);
            }
        }
        true
    }

    /// Suppose `f ≡ λx*. X t*` and `r ≡ λy*. x u*`.
    /// Imitation: X ↦ λz*. c (Y z*)* (when x = c)
    /// Projection: X ↦ λz*. zᵢ (Y z*)* (when τ(zᵢ) is compatible with τ(x))
    fn r#match(this: &Triple, that: &Triple) -> Vec<(MvarId, Term)> {
        assert!(this.is_flex());
        assert!(that.is_rigid());
        assert_eq!(this.binders, that.binders);
        let Term::Mvar(mid) = this.head else {
            panic!("self is not flex")
        };
        let mut heads = vec![];
        // λz*
        let mut binders = vec![];
        for arg in &this.args {
            binders.push(arg.ty());
        }
        // imitation
        match that.head {
            Term::Local(_) | Term::Const(_) => {
                heads.push(that.head.clone());
            }
            Term::Var(_) => {}
            Term::Abs(_) | Term::App(_) | Term::Mvar(_) => {
                panic!("logic flaw")
            }
        };
        // projection
        for (level, t) in binders.iter().rev().enumerate() {
            if t.target() == that.ty().target() {
                heads.push(Term::Var(level));
            }
        }
        let mut subst = vec![];
        for head in heads {
            let head_ty = match &head {
                Term::Local(_) | Term::Const(_) => head.ty(),
                Term::Var(i) => this.args[this.args.len() - i - 1].ty(),
                Term::Abs(_) | Term::App(_) | Term::Mvar(_) => panic!("logic flaw"),
            };
            let mut args = vec![];
            for _ in head_ty.args() {
                let mut y = Term::Mvar(MvarId::fresh());
                let mut zs = vec![];
                for i in 0..binders.len() {
                    zs.push(Term::Var(i));
                }
                y.apply(zs);
                args.push(y);
            }
            let mut m = Triple {
                binders: binders.clone(),
                head,
                args,
            };
            subst.push((mid, m.into()));
        }
        subst
    }

    fn solve(self) -> Vec<(MvarId, Term)> {
        let mut queue = VecDeque::new();
        queue.push_back((self, vec![]));
        while let Some((mut set, subst)) = queue.pop_front() {
            if !set.simplify() {
                continue;
            }
            if set.fr.is_empty() {
                return subst;
            }
            let (h1, h2) = &set.fr[0];
            for (mid, m) in h1.r#match(h2) {
                let mut new_set = DisagreementSet::default();
                for (m1, m2) in set.fr.iter().chain(set.ff.iter()) {
                    let mut m1 = Term::from(m1.clone());
                    m1.subst_mvar(mid, &m);
                    m1.canonicalize();
                    let mut m2 = Term::from(m2.clone());
                    m2.subst_mvar(mid, &m);
                    m2.canonicalize();
                    new_set.add(Triple::from(m1), Triple::from(m2));
                }
                let mut new_subst = subst.clone();
                new_subst.push((mid, m));
                queue.push_back((new_set, new_subst));
            }
        }
        todo!("no solution found");
    }
}
