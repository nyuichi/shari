use once_cell::sync::Lazy;
use std::collections::{HashMap, VecDeque};
use std::mem;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Name {
    Named(String),
    Anon(usize),
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
    // TODO: types: HashSet<Name>,
}

impl Sign {
    pub fn add_const(&mut self, name: Name, t: Scheme<Type>) {
        self.consts.insert(name, t).map(|_| todo!());
    }

    pub fn get_const(&self, name: &Name) -> Option<&Scheme<Type>> {
        self.consts.get(name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Fvar(Name),
    Arrow(Box<Type>, Box<Type>),
}

impl Default for Type {
    fn default() -> Self {
        Self::Fvar(Name::Anon(12345678))
    }
}

/// Following notations from [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    pub fn depth(&self) -> usize {
        match self {
            Self::Arrow(t1, t2) => t1.depth().max(t2.depth()) + 1,
            _ => 0,
        }
    }

    pub fn rank(&self) -> usize {
        match self {
            Self::Arrow(t1, t2) => (t1.rank() + 1).max(t2.rank()),
            _ => 0,
        }
    }

    pub fn order(&self) -> usize {
        match self {
            Self::Arrow(t1, t2) => (t1.rank() + 1).max(t2.rank()),
            _ => 1,
        }
    }

    pub fn arity(&self) -> usize {
        let mut arity = 0;
        let mut t = self;
        while let Self::Arrow(_, t2) = t {
            arity += 1;
            t = t2;
        }
        arity
    }

    pub fn target(&self) -> &Type {
        let mut t = self;
        while let Self::Arrow(_, t2) = t {
            t = t2;
        }
        t
    }

    pub fn components(&self) -> Vec<&Type> {
        let mut ts = vec![];
        let mut t = self;
        while let Self::Arrow(t1, t2) = t {
            ts.push(&**t1);
            t = &**t2;
        }
        ts
    }

    /// (t₁ → … → tₙ → t) ↦ [t₁, …, tₙ] (self becomes t)
    pub fn uncurry(&mut self) -> Vec<Type> {
        let mut ts = vec![];
        loop {
            match mem::take(self) {
                Self::Arrow(t1, t2) => {
                    ts.push(*t1);
                    *self = *t2;
                }
                t => {
                    *self = t;
                    break;
                }
            }
        }
        ts
    }

    pub fn curry(&mut self, ts: Vec<Type>) {
        for t in ts.into_iter().rev() {
            *self = Self::Arrow(Box::new(t), Box::new(mem::take(self)));
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct MvarId(usize);

impl std::fmt::Display for MvarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl MvarId {
    // TODO: reclaim unused mvars
    pub fn fresh() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNTER: Lazy<AtomicUsize> = Lazy::new(Default::default);
        Self(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

/// locally nameless representation
/// See [Charguéraud, 2012].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Fvar(Type, Name),
    Bvar(Type, usize),
    Abs(Type, Type, Box<Term>),
    App(Type, Box<Term>, Box<Term>),
    Const(Type, Name, Vec<Type>),
    /// Mvar is always closed.
    Mvar(Type, MvarId),
}

impl Default for Term {
    fn default() -> Self {
        Self::Bvar(Type::default(), 12345678)
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
            Self::Abs(_, _, n) => {
                n.open_at(name, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.open_at(name, level);
                m2.open_at(name, level);
            }
            Self::Const(_, _, _) => {}
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
            Self::Abs(_, _, m) => {
                m.close_at(name, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.close_at(name, level);
                m2.close_at(name, level);
            }
            Self::Const(_, _, _) => {}
            Self::Mvar(_, _) => {}
        }
    }

    #[doc(hidden)]
    pub fn mk_abs(&mut self, name: &Name, t: Type) {
        let u = self.r#type().clone();
        self.close(name);
        *self = Self::Abs(
            Type::Arrow(Box::new(t.clone()), Box::new(u)),
            t,
            Box::new(mem::take(self)),
        );
    }

    #[doc(hidden)]
    pub fn mk_app(&mut self, arg: Term) {
        if let Type::Arrow(t1, t2) = self.r#type() {
            assert_eq!(&**t1, arg.r#type());
            *self = Self::App((**t2).clone(), Box::new(mem::take(self)), Box::new(arg));
            return;
        }
        panic!("invalid application: {:?} {:?}", self, arg);
    }

    /// x # self <==> x ∉ FV(self)
    pub fn is_fresh(&self, name: &Name) -> bool {
        match self {
            Self::Fvar(_, x) => name != x,
            Self::Bvar(_, _) => true,
            Self::Abs(_, _, m) => m.is_closed(),
            Self::App(_, m1, m2) => m1.is_closed() && m2.is_closed(),
            Self::Const(_, _, _) => true,
            Self::Mvar(_, _) => true,
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Fvar(_, _) => false,
            Self::Bvar(_, _) => true,
            Self::Abs(_, _, m) => m.is_closed(),
            Self::App(_, m1, m2) => m1.is_closed() && m2.is_closed(),
            Self::Const(_, _, _) => true,
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
            Self::Abs(_, _, m) => m.is_lclosed_at(level + 1),
            Self::App(_, m1, m2) => m1.is_lclosed_at(level) && m2.is_lclosed_at(level),
            Self::Const(_, _, _) => true,
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
            Self::Abs(_, _, m) => m.is_ground(),
            Self::App(_, m1, m2) => m1.is_ground() && m2.is_ground(),
            Self::Const(_, _, _) => true,
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
            Self::App(_, m1, m2) => {
                m1.subst(name, m);
                m2.subst(name, m);
            }
            Self::Abs(_, _, n) => {
                n.subst(name, m);
            }
            Self::Const(_, _, _) => {}
            Self::Mvar(_, _) => {}
        }
    }

    fn instantiate(&mut self, mid: MvarId, m: &Term) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(_, _) => {}
            Self::App(_, m1, m2) => {
                m1.instantiate(mid, m);
                m2.instantiate(mid, m);
            }
            Self::Abs(_, _, n) => {
                n.instantiate(mid, m);
            }
            Self::Const(_, _, _) => {}
            Self::Mvar(_, i) => {
                if *i == mid {
                    *self = m.clone();
                }
            }
        }
    }

    /// m is in head position of n if n ≡ λv*. m l*
    /// May return a locally open term
    pub fn head(&self) -> &Self {
        let mut m = self;
        while let Self::Abs(_, _, n) = m {
            m = n;
        }
        while let Self::App(_, m1, _) = m {
            m = m1;
        }
        m
    }

    fn is_neutral(&self) -> bool {
        match self {
            Self::Abs(_, _, _) => false,
            Self::App(_, m1, m2) => m1.is_neutral() && m2.is_normal(),
            Self::Bvar(_, _) | Self::Fvar(_, _) | Self::Const(_, _, _) | Self::Mvar(_, _) => true,
        }
    }

    /// `true` if the term is in β-normal form.
    pub fn is_normal(&self) -> bool {
        if let Self::Abs(_, _, m) = self {
            m.is_normal()
        } else {
            self.is_neutral()
        }
    }

    /// m is in head normal form if m has no β-redex at its head position.
    pub fn is_hnf(&self) -> bool {
        match self.head() {
            Self::Fvar(_, _) | Self::Bvar(_, _) | Self::Const(_, _, _) | Self::Mvar(_, _) => true,
            Self::Abs(_, _, _) => false,
            Self::App(_, _, _) => unreachable!(),
        }
    }

    /// does not check if a term inside an abstraction is in whnf
    pub fn is_whnf(&self) -> bool {
        match self {
            Self::Abs(_, _, _) => true,
            Self::Bvar(_, _)
            | Self::Fvar(_, _)
            | Self::Const(_, _, _)
            | Self::Mvar(_, _)
            | Self::App(_, _, _) => self.is_hnf(),
        }
    }

    /// m = n l*
    /// m.uncurry() // => l*
    /// assert(m = n)
    pub fn uncurry(&mut self) -> Vec<Term> {
        let mut args = vec![];
        loop {
            match mem::take(self) {
                Self::App(_, m1, m2) => {
                    args.push(*m2);
                    *self = *m1;
                }
                m => {
                    *self = m;
                    break;
                }
            }
        }
        args.reverse();
        args
    }

    pub fn curry(&mut self, ms: Vec<Term>) {
        for m in ms {
            self.mk_app(m);
        }
    }

    /// self.open_subst(m) == [m/x][x/0]self (for fresh x) == [m/0]self
    fn open_subst(&mut self, m: &Term) {
        // TODO: traverse the whole term only once
        let x = Name::fresh();
        self.open(&x);
        self.subst(&x, m);
    }

    /// applicative-order (leftmost-innermost) reduction
    fn beta_reduce(&mut self) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(_, _) => {}
            Self::Const(_, _, _) => {}
            Self::Mvar(_, _) => {}
            Self::App(_, m1, m2) => {
                m1.beta_reduce();
                m2.beta_reduce();
                if let Self::Abs(_, _, m) = &mut **m1 {
                    m.open_subst(m2);
                    m.beta_reduce();
                    *self = mem::take(m);
                }
            }
            Self::Abs(_, _, m) => m.beta_reduce(),
        }
    }

    pub fn r#type(&self) -> &Type {
        match self {
            Self::Fvar(t, _)
            | Self::Bvar(t, _)
            | Self::Abs(t, _, _)
            | Self::App(t, _, _)
            | Self::Const(t, _, _)
            | Self::Mvar(t, _) => t,
        }
    }

    /// Check if the term is in η-long β-normal form.
    /// See Lectures on the Curry-Howard isomorphism, Chapter 4.
    /// https://math.stackexchange.com/q/3334730
    fn is_canonical(&mut self) -> bool {
        match self.r#type() {
            Type::Arrow(_, _) => {
                if let Self::Abs(_, _, m) = self {
                    let name = Name::fresh();
                    m.open(&name);
                    let r = m.is_canonical();
                    m.close(&name);
                    r
                } else {
                    false
                }
            }
            Type::Fvar(_) => {
                let mut m = self;
                while let Self::App(_, m1, m2) = m {
                    if !m2.is_canonical() {
                        return false;
                    }
                    m = m1;
                }
                match m {
                    Self::Fvar(_, _)
                    | Self::Bvar(_, _)
                    | Self::Const(_, _, _)
                    | Self::Mvar(_, _) => true,
                    Self::Abs(_, _, _) => false,
                    Self::App(_, _, _) => unreachable!(),
                }
            }
        }
    }

    /// [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_neutral(&mut self) {
        assert!(self.is_neutral());
        // [x M₁ ... Mₙ] := x [M₁] ... [Mₙ]
        let mut m = &mut *self;
        loop {
            match m {
                Self::Fvar(_, _) | Self::Bvar(_, _) | Self::Const(_, _, _) | Self::Mvar(_, _) => {
                    break;
                }
                Self::App(_, m1, m2) => {
                    m2.eta_expand_normal();
                    m = m1;
                }
                Self::Abs(_, _, _) => unreachable!(),
            }
        }
        // [M] := λv*. M v*
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
        for (name, t) in binder.into_iter().rev() {
            self.mk_abs(&name, t);
        }
    }

    /// 1. [λx.M] := λx.[M]
    /// 2. [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_normal(&mut self) {
        assert!(self.is_normal());
        match self {
            Self::Abs(_, _, m) => {
                let x = Name::fresh();
                m.open(&x);
                m.eta_expand_normal();
                m.close(&x);
            }
            Self::Bvar(_, _)
            | Self::Fvar(_, _)
            | Self::Const(_, _, _)
            | Self::Mvar(_, _)
            | Self::App(_, _, _) => {
                self.eta_expand_neutral();
            }
        }
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
struct Hnf {
    /// Outermost-first
    binder: Vec<(Name, Type)>,
    /// Fvar, Const, or Mvar.
    // TODO: use locally nameless forms directly.
    head: Term,
    /// Huch calls these parts "arguments" [Huch, 2020](https://www21.in.tum.de/teaching/sar/SS20/5.pdf).
    /// See also Notation 2.29 in The Clausal Theory of Types [Wolfram, 2009].
    args: Vec<Term>,
}

impl From<Term> for Hnf {
    fn from(mut m: Term) -> Self {
        assert!(m.is_canonical());
        let mut binder = vec![];
        let mut head = m;
        while let Term::Abs(_, t, mut m) = head {
            let x = Name::fresh();
            m.open(&x);
            binder.push((x, t));
            head = *m;
        }
        let args = head.uncurry();
        Self { binder, head, args }
    }
}

impl From<Hnf> for Term {
    fn from(m: Hnf) -> Self {
        let Hnf { binder, head, args } = m;
        let mut m = head;
        m.curry(args);
        for (x, t) in binder.into_iter().rev() {
            m.mk_abs(&x, t);
        }
        m
    }
}

impl Hnf {
    /// See [Vukmirović+, 2020].
    pub fn is_flex(&self) -> bool {
        match self.head {
            Term::Mvar(_, _) => true,
            Term::Bvar(_, _)
            | Term::Fvar(_, _)
            | Term::Const(_, _, _)
            | Term::Abs(_, _, _)
            | Term::App(_, _, _) => false,
        }
    }

    /// See [Vukmirović+, 2020].
    pub fn is_rigid(&self) -> bool {
        !self.is_flex()
    }

    fn matrix(&self) -> (&Term, &Vec<Term>) {
        (&self.head, &self.args)
    }

    /// Suppose `f ≡ λx*. X t*` and `r ≡ λy*. x u*`.
    /// Imitation: X ↦ λz*. x (Y z*)* (when x = c)
    /// Projection: X ↦ λz*. zᵢ (Y z*)* (when τ(zᵢ) is compatible with τ(x))
    fn r#match(&self, other: &Hnf) -> Vec<(MvarId, Term)> {
        assert!(self.is_flex());
        assert!(self.is_rigid());
        let (t, mid) = if let Term::Mvar(t, mid) = &self.head {
            (t, *mid)
        } else {
            panic!("self is not flex")
        };
        let zs: Vec<_> = t
            .components()
            .into_iter()
            .map(|t| (Name::fresh(), t.clone()))
            .collect();
        let mut heads = vec![];
        // projection
        for (x, u) in &zs {
            if t.target() == u.target() {
                heads.push(Term::Fvar((*u).clone(), x.to_owned()));
            }
        }
        // imitation
        match other.head {
            Term::Fvar(_, _) | Term::Const(_, _, _) => {
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
                        t.curry(zs.iter().map(|(_, t)| (*t).clone()).collect());
                        let mut m = Term::Mvar(t, MvarId::fresh());
                        m.curry(
                            zs.iter()
                                .map(|(x, t)| Term::Fvar(t.clone(), x.to_owned()))
                                .collect(),
                        );
                        m
                    })
                    .collect(),
            );
            for (x, t) in zs.iter().rev() {
                head.mk_abs(&x, (*t).clone());
            }
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
    rr: Vec<(Hnf, Hnf)>,
    // flex-rigid
    fr: Vec<(Hnf, Hnf)>,
    // flex-flex
    ff: Vec<(Hnf, Hnf)>,
}

impl DisagreementSet {
    fn add(&mut self, m1: Hnf, m2: Hnf) {
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
                    for (x, t) in h1.binder.clone().into_iter().rev() {
                        a1.mk_abs(&x, t);
                    }
                    for (y, t) in h2.binder.clone().into_iter().rev() {
                        a2.mk_abs(&y, t);
                    }
                    self.add(Hnf::from(a1), Hnf::from(a2));
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
                    new_set.add(Hnf::from(m1), Hnf::from(m2));
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
        let h1 = Hnf::from(self.clone());
        other.canonicalize();
        let h2 = Hnf::from(mem::take(other));
        set.add(h1, h2);
        let subst = set.solve();
        for (mid, m) in subst {
            self.instantiate(mid, &m);
        }
        *other = self.clone();
    }
}
