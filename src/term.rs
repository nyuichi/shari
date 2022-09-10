use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet, VecDeque};
use std::mem;
use std::sync::Arc;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Name {
    Named(String),
    Anon(usize),
}

impl Default for Name {
    fn default() -> Self {
        Name::Anon(12345678)
    }
}

impl Name {
    // TODO: reclaim unused mvars
    pub fn fresh() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNTER: Lazy<AtomicUsize> = Lazy::new(Default::default);
        Self::Anon(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Scheme<T> {
    pub type_vars: Vec<Name>,
    pub main: T,
}

impl<T> Scheme<T> {
    pub fn arity(&self) -> usize {
        self.type_vars.len()
    }
}

#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct Sign {
    consts: HashMap<Name, Scheme<Type>>,
    types: HashSet<Name>, // TODO: support base types with arity of one or more
}

impl Sign {
    pub fn add_const(&mut self, name: Name, t: Scheme<Type>) {
        if self.consts.insert(name, t).is_some() {
            todo!()
        }
    }

    pub fn get_const(&self, name: &Name) -> Option<&Scheme<Type>> {
        self.consts.get(name)
    }

    pub fn add_type(&mut self, name: Name) {
        if !self.types.insert(name) {
            todo!()
        }
    }

    pub fn is_base(&self, name: &Name) -> bool {
        self.types.get(name).is_some()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Type {
    Fvar(Name),
    Arrow(Arc<(Type, Type)>),
}

impl Default for Type {
    fn default() -> Self {
        Type::Fvar(Name::default())
    }
}

/// Following notations from [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    pub fn depth(&self) -> usize {
        match self {
            Self::Arrow(p) => {
                let (t1, t2) = &**p;
                t1.depth().max(t2.depth()) + 1
            }
            _ => 0,
        }
    }

    pub fn rank(&self) -> usize {
        match self {
            Self::Arrow(p) => {
                let (t1, t2) = &**p;
                (t1.rank() + 1).max(t2.rank())
            }
            _ => 0,
        }
    }

    pub fn order(&self) -> usize {
        match self {
            Self::Arrow(p) => {
                let (t1, t2) = &**p;
                (t1.rank() + 1).max(t2.rank())
            }
            _ => 1,
        }
    }

    pub fn arity(&self) -> usize {
        let mut arity = 0;
        let mut t = self;
        while let Self::Arrow(p) = t {
            let (_, t2) = &**p;
            arity += 1;
            t = &t2;
        }
        arity
    }

    pub fn target(&self) -> &Type {
        let mut t = self;
        while let Self::Arrow(p) = t {
            let (_, t2) = &**p;
            t = &t2;
        }
        t
    }

    pub fn components(&self) -> Vec<&Type> {
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
    pub fn uncurry(&mut self) -> Vec<Type> {
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

    pub fn curry(&mut self, ts: Vec<Type>) {
        let mut t = mem::take(self);
        for u in ts.into_iter().rev() {
            t = Self::Arrow(Arc::new((u, t)));
        }
        *self = t;
    }
}

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

/// locally nameless representation
/// See [Charguéraud, 2012].
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Term {
    Fvar(Type, Name),
    Bvar(Type, usize),
    Abs(Type, Arc<Context>),
    App(Type, Arc<(Term, Term)>),
    Const(Type, Arc<(Name, Vec<Type>)>),
    /// Mvar is always closed.
    Mvar(Type, MvarId),
}

impl Default for Term {
    fn default() -> Self {
        Self::Bvar(Type::default(), 12345678)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct Context(pub Type, pub Term);

impl Context {
    pub fn fill(&mut self, m: &Term) {
        assert_eq!(self.0, *m.r#type());
        // TODO: traverse the whole term only once
        let x = Name::fresh();
        self.1.open(&x);
        self.1.subst(&x, m);
    }
}

impl Term {
    /// self.open(x) == [x/0]self
    pub fn open(&mut self, name: &Name) {
        assert!(self.is_body());
        self.open_at(name, 0)
    }

    fn open_at(&mut self, name: &Name, level: usize) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(t, i) => {
                if *i == level {
                    *self = Self::Fvar(mem::take(t), name.clone());
                }
            }
            Self::Abs(_, c) => {
                let Context(_, n) = Arc::make_mut(c);
                n.open_at(name, level + 1);
            }
            Self::App(_, p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.open_at(name, level);
                m2.open_at(name, level);
            }
            Self::Const(_, _) => {}
            Self::Mvar(_, _) => {}
        }
    }

    /// self.close(x) == [0/x]self
    pub fn close(&mut self, name: &Name) {
        assert!(self.is_lclosed());
        self.close_at(name, 0)
    }

    fn close_at(&mut self, name: &Name, level: usize) {
        match self {
            Self::Fvar(t, x) => {
                if name == x {
                    *self = Self::Bvar(mem::take(t), level);
                }
            }
            Self::Bvar(_, _) => {}
            Self::Abs(_, c) => {
                let Context(_, m) = Arc::make_mut(c);
                m.close_at(name, level + 1);
            }
            Self::App(_, p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.close_at(name, level);
                m2.close_at(name, level);
            }
            Self::Const(_, _) => {}
            Self::Mvar(_, _) => {}
        }
    }

    /// x # self <==> x ∉ FV(self)
    pub fn is_fresh(&self, name: &Name) -> bool {
        match self {
            Self::Fvar(_, x) => name != x,
            Self::Bvar(_, _) => true,
            Self::Abs(_, c) => {
                let Context(_, m) = &**c;
                m.is_closed()
            }
            Self::App(_, p) => {
                let (m1, m2) = &**p;
                m1.is_closed() && m2.is_closed()
            }
            Self::Const(_, _) => true,
            Self::Mvar(_, _) => true,
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Fvar(_, _) => false,
            Self::Bvar(_, _) => true,
            Self::Abs(_, c) => {
                let Context(_, m) = &**c;
                m.is_closed()
            }
            Self::App(_, p) => {
                let (m1, m2) = &**p;
                m1.is_closed() && m2.is_closed()
            }
            Self::Const(_, _) => true,
            Self::Mvar(_, _) => true,
        }
    }

    pub fn is_lclosed(&self) -> bool {
        self.is_lclosed_at(0)
    }

    fn is_lclosed_at(&self, level: usize) -> bool {
        match self {
            Self::Fvar(_, _) => true,
            Self::Bvar(_, i) => *i < level,
            Self::Abs(_, c) => {
                let Context(_, m) = &**c;
                m.is_lclosed_at(level + 1)
            }
            Self::App(_, p) => {
                let (m1, m2) = &**p;
                m1.is_lclosed_at(level) && m2.is_lclosed_at(level)
            }
            Self::Const(_, _) => true,
            Self::Mvar(_, _) => true,
        }
    }

    pub fn is_body(&self) -> bool {
        self.is_lclosed_at(1)
    }

    pub fn is_ground(&self) -> bool {
        match self {
            Self::Fvar(_, _) => true,
            Self::Bvar(_, _) => true,
            Self::Abs(_, c) => {
                let Context(_, m) = &**c;
                m.is_ground()
            }
            Self::App(_, p) => {
                let (m1, m2) = &**p;
                m1.is_ground() && m2.is_ground()
            }
            Self::Const(_, _) => true,
            Self::Mvar(_, _) => false,
        }
    }

    pub fn subst(&mut self, name: &Name, m: &Term) {
        match self {
            Self::Fvar(_, x) => {
                if name == x {
                    *self = m.clone();
                }
            }
            Self::Bvar(_, _) => {}
            Self::App(_, p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.subst(name, m);
                m2.subst(name, m);
            }
            Self::Abs(_, c) => {
                let Context(_, n) = Arc::make_mut(c);
                n.subst(name, m);
            }
            Self::Const(_, _) => {}
            Self::Mvar(_, _) => {}
        }
    }

    fn instantiate(&mut self, mid: MvarId, m: &Term) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(_, _) => {}
            Self::App(_, p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.instantiate(mid, m);
                m2.instantiate(mid, m);
            }
            Self::Abs(_, c) => {
                let Context(_, n) = Arc::make_mut(c);
                n.instantiate(mid, m);
            }
            Self::Const(_, _) => {}
            Self::Mvar(_, i) => {
                if *i == mid {
                    *self = m.clone();
                }
            }
        }
    }

    /// may return locally open terms
    pub fn head(&self) -> &Term {
        let mut m = self;
        while let Self::Abs(_, c) = m {
            let Context(_, n) = &**c;
            m = n;
        }
        while let Self::App(_, p) = m {
            let (m1, _) = &**p;
            m = m1;
        }
        m
    }

    /// triple(λ (v:t)*, m l*) = (t*, m, l*)
    /// may return locally open terms
    pub fn triple_mut(&mut self) -> (Vec<&mut Type>, &mut Term, Vec<&mut Term>) {
        let mut m = self;
        let mut binders = vec![];
        while let Self::Abs(_, c) = m {
            let Context(t, n) = Arc::make_mut(c);
            binders.push(t);
            m = n;
        }
        let mut args = vec![];
        while let Self::App(_, p) = m {
            let (m1, m2) = Arc::make_mut(p);
            args.push(m2);
            m = m1;
        }
        args.reverse();
        (binders, m, args)
    }

    pub fn arguments_mut(&mut self) -> Vec<&mut Term> {
        self.triple_mut().2
    }

    pub fn matrix_mut(&mut self) -> &mut Term {
        let mut m = self;
        while let Self::Abs(_, c) = m {
            let Context(_, n) = Arc::make_mut(c);
            m = n;
        }
        m
    }

    fn is_neutral(&self) -> bool {
        match self {
            Self::Abs(_, _) => false,
            Self::App(_, p) => {
                let (m1, m2) = &**p;
                m1.is_neutral() && m2.is_normal()
            }
            Self::Bvar(_, _) | Self::Fvar(_, _) | Self::Const(_, _) | Self::Mvar(_, _) => true,
        }
    }

    /// `true` if the term is in β-normal form.
    pub fn is_normal(&self) -> bool {
        if let Self::Abs(_, c) = self {
            let Context(_, m) = &**c;
            m.is_normal()
        } else {
            self.is_neutral()
        }
    }

    /// m is in head normal form if m has no β-redex at its head position.
    pub fn is_hnf(&self) -> bool {
        match self.head() {
            Self::Fvar(_, _) | Self::Bvar(_, _) | Self::Const(_, _) | Self::Mvar(_, _) => true,
            Self::Abs(_, _) => false,
            Self::App(_, _) => unreachable!(),
        }
    }

    /// does not check if a term inside an abstraction is in whnf
    pub fn is_whnf(&self) -> bool {
        match self {
            Self::Abs(_, _) => true,
            Self::Bvar(_, _)
            | Self::Fvar(_, _)
            | Self::Const(_, _)
            | Self::Mvar(_, _)
            | Self::App(_, _) => self.is_hnf(),
        }
    }

    /// m = n l*
    /// m.uncurry() // => l*
    /// assert(m = n)
    pub fn uncurry(&mut self) -> Vec<Term> {
        let mut args = vec![];
        let mut m = &mut *self;
        while let Self::App(_, p) = m {
            let (m1, m2) = Arc::make_mut(p);
            args.push(mem::take(m2));
            m = m1;
        }
        *self = mem::take(m);
        args.reverse();
        args
    }

    pub fn curry(&mut self, ms: Vec<Term>) {
        let mut head = mem::take(self);
        for m in ms {
            if let Type::Arrow(p) = head.r#type() {
                let (t1, t2) = &**p;
                assert_eq!(t1, m.r#type());
                head = Self::App(t2.clone(), Arc::new((head, m)));
            } else {
                panic!("invalid application: {:?} {:?}", self, m);
            }
        }
        *self = head;
    }

    pub fn unabstract(&mut self) -> Vec<(Name, Type)> {
        let mut binder = vec![];
        let mut m = &mut *self;
        while let Term::Abs(_, c) = m {
            let Context(t, n) = Arc::make_mut(c);
            let x = Name::fresh();
            n.open(&x);
            binder.push((x, mem::take(t)));
            m = n;
        }
        *self = mem::take(m);
        binder
    }

    pub fn r#abstract(&mut self, binder: Vec<(Name, Type)>) {
        let mut m = mem::take(self);
        for (x, t) in binder.into_iter().rev() {
            let mut u = m.r#type().clone();
            u.curry(vec![t.clone()]);
            m.close(&x);
            m = Self::Abs(u, Arc::new(Context(t, m)));
        }
        *self = m;
    }

    /// applicative-order (leftmost-innermost) reduction
    fn beta_reduce(&mut self) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(_, _) => {}
            Self::Const(_, _) => {}
            Self::Mvar(_, _) => {}
            Self::App(_, p) => {
                let (m1, m2) = Arc::make_mut(p);
                m1.beta_reduce();
                m2.beta_reduce();
                if let Self::Abs(_, c) = m1 {
                    let c = Arc::make_mut(c);
                    c.fill(m2);
                    let Context(_, m) = c;
                    *self = mem::take(m);
                    self.beta_reduce();
                }
            }
            Self::Abs(_, c) => {
                let Context(_, m) = Arc::make_mut(c);
                m.beta_reduce();
            }
        }
    }

    pub fn r#type(&self) -> &Type {
        match self {
            Self::Fvar(t, _)
            | Self::Bvar(t, _)
            | Self::Abs(t, _)
            | Self::App(t, _)
            | Self::Const(t, _)
            | Self::Mvar(t, _) => t,
        }
    }

    /// Check if the term is in η-long β-normal form.
    /// See Lectures on the Curry-Howard isomorphism, Chapter 4.
    /// https://math.stackexchange.com/q/3334730
    fn is_canonical(&self) -> bool {
        match self.r#type() {
            Type::Arrow(_) => {
                if let Self::Abs(_, c) = self {
                    let Context(_, m) = &**c;
                    m.is_canonical()
                } else {
                    false
                }
            }
            Type::Fvar(_) => {
                let mut m = self;
                while let Self::App(_, p) = m {
                    let (m1, m2) = &**p;
                    if !m2.is_canonical() {
                        return false;
                    }
                    m = m1;
                }
                match m {
                    Self::Fvar(_, _) | Self::Bvar(_, _) | Self::Const(_, _) | Self::Mvar(_, _) => {
                        true
                    }
                    Self::Abs(_, _) => false,
                    Self::App(_, _) => unreachable!(),
                }
            }
        }
    }

    /// [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_neutral(&mut self) {
        assert!(self.is_neutral());
        // [x M₁ ... Mₙ] := x [M₁] ... [Mₙ]
        for arg in self.arguments_mut() {
            arg.eta_expand_normal();
        }
        // [M] := λv₁ v₂ ⋯. M v₁ v₂ ⋯
        let binder: Vec<_> = self
            .r#type()
            .components()
            .into_iter()
            .map(|t| (Name::fresh(), t.clone()))
            .collect();
        self.curry(
            binder
                .iter()
                .map(|(x, t)| Term::Fvar(t.clone(), x.to_owned()))
                .collect(),
        );
        self.r#abstract(binder);
    }

    /// 1. [λx.M] := λx.[M]
    /// 2. [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_normal(&mut self) {
        assert!(self.is_normal());
        self.matrix_mut().eta_expand_neutral();
    }

    pub fn canonicalize(&mut self) {
        self.beta_reduce();
        self.eta_expand_normal();
    }

    /// self and other must be type-correct and type-equal under the same environment.
    pub fn def_eq(&mut self, other: &mut Self) -> bool {
        assert_eq!(self.r#type(), self.r#type());
        let mut m1 = self.clone();
        m1.canonicalize();
        let mut m2 = other.clone();
        m2.canonicalize();
        m1 == m2
    }
}

/// A convenient representation of head normal form.
/// Recall that every (normal) term has form `λv*. m n*`.
#[derive(Clone)]
struct Triple {
    /// Outermost-first
    binder: Vec<(Name, Type)>,
    /// Fvar, Const, or Mvar.
    // TODO: use locally nameless forms directly.
    head: Term,
    /// Huch calls these parts "arguments" [Huch, 2020](https://www21.in.tum.de/teaching/sar/SS20/5.pdf).
    /// See also Notation 2.29 in The Clausal Theory of Types [Wolfram, 2009].
    args: Vec<Term>,
}

impl From<Term> for Triple {
    fn from(mut m: Term) -> Self {
        assert!(m.is_canonical());
        let binder = m.unabstract();
        let args = m.uncurry();
        let head = m;
        Self { binder, head, args }
    }
}

impl From<Triple> for Term {
    fn from(m: Triple) -> Self {
        let Triple { binder, head, args } = m;
        let mut m = head;
        m.curry(args);
        m.r#abstract(binder);
        m
    }
}

impl Triple {
    /// See [Vukmirović+, 2020].
    pub fn is_flex(&self) -> bool {
        match self.head {
            Term::Mvar(_, _) => true,
            Term::Bvar(_, _) | Term::Fvar(_, _) | Term::Const(_, _) => false,
            Term::Abs(_, _) | Term::App(_, _) => unreachable!(),
        }
    }

    /// See [Vukmirović+, 2020].
    pub fn is_rigid(&self) -> bool {
        !self.is_flex()
    }

    /// Suppose `f ≡ λx*. X t*` and `r ≡ λy*. x u*`.
    /// Imitation: X ↦ λz*. x (Y z*)* (when x = c)
    /// Projection: X ↦ λz*. zᵢ (Y z*)* (when τ(zᵢ) is compatible with τ(x))
    fn r#match(&self, other: &Triple) -> Vec<(MvarId, Term)> {
        assert!(self.is_flex());
        assert!(self.is_rigid());
        let (t, mid) = if let Term::Mvar(t, mid) = &self.head {
            (t, *mid)
        } else {
            panic!("self is not flex")
        };
        let binder: Vec<_> = t
            .components()
            .into_iter()
            .map(|t| (Name::fresh(), t.clone()))
            .collect();
        let mut heads = vec![];
        // projection
        for (x, u) in &binder {
            if t.target() == u.target() {
                heads.push(Term::Fvar((*u).clone(), x.to_owned()));
            }
        }
        // imitation
        match other.head {
            Term::Fvar(_, _) | Term::Const(_, _) => {
                heads.push(other.head.clone());
            }
            _ => {}
        };
        let mut subst = vec![];
        for mut head in heads {
            head.curry(
                head.r#type()
                    .components()
                    .into_iter()
                    .map(|t| {
                        let mut t = t.clone();
                        t.curry(binder.iter().map(|(_, t)| (*t).clone()).collect());
                        let mut m = Term::Mvar(t, MvarId::fresh());
                        m.curry(
                            binder
                                .iter()
                                .map(|(x, t)| Term::Fvar(t.clone(), x.to_owned()))
                                .collect(),
                        );
                        m
                    })
                    .collect(),
            );
            head.r#abstract(binder.clone());
            subst.push((mid, head));
        }
        subst
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
            assert_eq!(h1.binder.len(), h2.binder.len());
            let has_same_heading = {
                let mut head2 = h2.head.clone();
                for ((x, t1), (y, t2)) in h1.binder.iter().zip(h2.binder.iter()) {
                    assert_eq!(t1, t2);
                    let m = Term::Fvar(t1.clone(), x.to_owned());
                    head2.subst(y, &m);
                }
                h1.head == head2
            };
            if has_same_heading {
                assert_eq!(h1.args.len(), h2.args.len());
                for (mut a1, mut a2) in h1.args.into_iter().zip(h2.args.into_iter()) {
                    a1.r#abstract(h1.binder.clone());
                    a2.r#abstract(h2.binder.clone());
                    self.add(Triple::from(a1), Triple::from(a2));
                }
            } else {
                return false;
            }
        }
        true
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
                    m1.instantiate(mid, &m);
                    m1.canonicalize();
                    let mut m2 = Term::from(m2.clone());
                    m2.instantiate(mid, &m);
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

impl Term {
    /// `self` and `other` must be type-correct and type-equal under the same environment.
    pub fn unify(&mut self, other: &mut Term) {
        assert_eq!(self.r#type(), other.r#type());
        let mut set = DisagreementSet::default();
        self.canonicalize();
        let h1 = Triple::from(self.clone());
        other.canonicalize();
        let h2 = Triple::from(mem::take(other));
        set.add(h1, h2);
        let subst = set.solve();
        for (mid, m) in subst {
            self.instantiate(mid, &m);
        }
        *other = self.clone();
    }
}
