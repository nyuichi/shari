use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet, VecDeque};
use std::mem;

fn fresh() -> String {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: Lazy<AtomicUsize> = Lazy::new(Default::default);
    format!("#{}", COUNTER.fetch_add(1, Ordering::Relaxed))
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MvarId(usize);

impl MvarId {
    // TODO: reclaim unused mvars
    pub fn fresh() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNTER: Lazy<AtomicUsize> = Lazy::new(Default::default);
        Self(COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Base(String),
    Arrow(Box<Type>, Box<Type>),
    Mvar(MvarId),
}

impl Default for Type {
    fn default() -> Self {
        Self::Mvar(MvarId(12345678))
    }
}

/// Following the notations from [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
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

    pub fn is_ground(&self) -> bool {
        match self {
            Self::Arrow(t1, t2) => t1.is_ground() && t2.is_ground(),
            Type::Base(_) => true,
            Type::Mvar(_) => false,
        }
    }

    /// (t₁ → … → tₙ → t) ↦ [t₁, …, tₙ] (self becomes t)
    pub fn uncurry(&mut self) -> Vec<Type> {
        let mut ts = vec![];
        while let Self::Arrow(t1, t2) = mem::take(self) {
            ts.push(*t1);
            *self = *t2;
        }
        ts
    }

    pub fn curry(&mut self, ts: Vec<Type>) {
        for t in ts.into_iter().rev() {
            *self = Self::Arrow(Box::new(t), Box::new(mem::take(self)));
        }
    }

    pub fn subst_meta(&mut self, mid: MvarId, t: &Type) {
        match self {
            Self::Base(_) => {}
            Self::Mvar(i) => {
                if *i == mid {
                    *self = t.clone();
                }
            }
            Self::Arrow(t1, t2) => {
                t1.subst_meta(mid, t);
                t2.subst_meta(mid, t);
            }
        }
    }
}

/// locally nameless representation
/// See [Charguéraud, 2012].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Fvar(Type, String),
    Bvar(Type, usize),
    Abs(Type, Box<Term>),
    App(Type, Box<Term>, Box<Term>),
    Const(Type, String),
    /// Mvar is always closed.
    Mvar(Type, MvarId),
}

impl Default for Term {
    fn default() -> Self {
        Self::Bvar(Type::default(), 12345678)
    }
}

impl Term {
    pub fn r#type(&self) -> &Type {
        match self {
            Self::Fvar(t, _) => t,
            Self::Bvar(t, _) => t,
            Self::Abs(t, _) => t,
            Self::App(t, _, _) => t,
            Self::Const(t, _) => t,
            Self::Mvar(t, _) => t,
        }
    }

    /// `self` must satisfy `Term::is_body`.
    /// self.open(x) == [x/0]self
    pub fn open(&mut self, name: &str) {
        assert!(self.is_body());
        self.open_at(name, 0)
    }

    fn open_at(&mut self, name: &str, level: usize) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(t, i) => {
                if *i == level {
                    *self = Self::Fvar(mem::take(t), name.to_owned());
                }
            }
            Self::Abs(_, n) => {
                n.open_at(name, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.open_at(name, level);
                m2.open_at(name, level);
            }
            Self::Const(_, _) => {}
            Self::Mvar(_, _) => {}
        }
    }

    /// `self` must be locally closed.
    /// self.close(x) == [0/x]self
    pub fn close(&mut self, name: &str) {
        assert!(self.is_locally_closed());
        self.close_at(name, 0)
    }

    fn close_at(&mut self, name: &str, level: usize) {
        match self {
            Self::Fvar(t, ref x) => {
                if name == x {
                    *self = Self::Bvar(mem::take(t), level);
                }
            }
            Self::Bvar(_, _) => {}
            Self::Abs(_, m) => {
                m.close_at(name, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.close_at(name, level);
                m2.close_at(name, level);
            }
            Self::Const(_, _) => {}
            Self::Mvar(_, _) => {}
        }
    }

    fn mk_abs(&mut self, name: &str, t: Type) {
        let t = Type::Arrow(Box::new(t), Box::new(self.r#type().clone()));
        self.close(name);
        *self = Self::Abs(t, Box::new(mem::take(self)));
    }

    fn mk_app(&mut self, arg: Term, t: Type) {
        *self = Self::App(t, Box::new(mem::take(self)), Box::new(arg));
    }

    /// x # self <==> x ∉ FV(self)
    pub fn is_fresh(&self, name: &str) -> bool {
        match self {
            Self::Fvar(_, x) => name != x,
            Self::Bvar(_, _) => true,
            Self::Abs(_, m) => m.is_closed(),
            Self::App(_, m1, m2) => m1.is_closed() && m2.is_closed(),
            Self::Const(_, _) => true,
            Self::Mvar(_, _) => true,
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Fvar(_, _) => false,
            Self::Bvar(_, _) => true,
            Self::Abs(_, m) => m.is_closed(),
            Self::App(_, m1, m2) => m1.is_closed() && m2.is_closed(),
            Self::Const(_, _) => true,
            Self::Mvar(_, _) => true,
        }
    }

    pub fn is_locally_closed(&self) -> bool {
        self.is_locally_closed_at(0)
    }

    fn is_locally_closed_at(&self, level: usize) -> bool {
        match self {
            Self::Fvar(_, _) => true,
            Self::Bvar(_, i) => *i < level,
            Self::Abs(_, m) => m.is_locally_closed_at(level + 1),
            Self::App(_, m1, m2) => {
                m1.is_locally_closed_at(level) && m2.is_locally_closed_at(level)
            }
            Self::Const(_, _) => true,
            Self::Mvar(_, _) => true,
        }
    }

    pub fn is_body(&self) -> bool {
        self.is_locally_closed_at(1)
    }

    pub fn is_ground(&self) -> bool {
        match self {
            Self::Fvar(_, _) => true,
            Self::Bvar(_, _) => true,
            Self::Abs(_, m) => m.is_ground(),
            Self::App(_, m1, m2) => m1.is_ground() && m2.is_ground(),
            Self::Const(_, _) => true,
            Self::Mvar(_, _) => false,
        }
    }

    pub fn subst(&mut self, name: &str, m: &Term) {
        match self {
            Self::Fvar(_, ref x) => {
                if name == x {
                    *self = m.clone();
                }
            }
            Self::Bvar(_, _) => {}
            Self::App(_, m1, m2) => {
                m1.subst(name, m);
                m2.subst(name, m);
            }
            Self::Abs(_, n) => {
                n.subst(name, m);
            }
            Self::Const(_, _) => {}
            Self::Mvar(_, _) => {}
        }
    }

    pub fn subst_meta(&mut self, mid: MvarId, m: &Term) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(_, _) => {}
            Self::App(_, m1, m2) => {
                m1.subst_meta(mid, m);
                m2.subst_meta(mid, m);
            }
            Self::Abs(_, n) => {
                n.subst_meta(mid, m);
            }
            Self::Const(_, _) => {}
            Self::Mvar(_, i) => {
                if *i == mid {
                    *self = m.clone();
                }
            }
        }
    }

    fn subst_type_meta(&mut self, mid: MvarId, t: &Type) {
        match self {
            Self::Fvar(u, _) => u.subst_meta(mid, t),
            Self::Bvar(u, _) => u.subst_meta(mid, t),
            Self::Const(u, _) => u.subst_meta(mid, t),
            Self::Abs(u, m) => {
                u.subst_meta(mid, t);
                m.subst_type_meta(mid, t);
            }
            Self::App(u, m1, m2) => {
                u.subst_meta(mid, t);
                m1.subst_type_meta(mid, t);
                m2.subst_type_meta(mid, t);
            }
            Self::Mvar(u, _) => u.subst_meta(mid, t),
        }
    }

    /// m is in head position of n if n ≡ λv*. m l*
    /// May return a locally open term
    pub fn head(&self) -> &Self {
        let mut m = self;
        while let Self::Abs(_, n) = m {
            m = n;
        }
        while let Self::App(_, m1, _) = m {
            m = m1;
        }
        m
    }

    /// See [Vukmirović+, 2020].
    pub fn is_flex(&self) -> bool {
        match self.head() {
            Self::Mvar(_, _) => true,
            Self::Bvar(_, _)
            | Self::Fvar(_, _)
            | Self::Const(_, _)
            | Self::Abs(_, _)
            | Self::App(_, _, _) => false,
        }
    }

    /// See [Vukmirović+, 2020].
    pub fn is_rigid(&self) -> bool {
        !self.is_flex()
    }

    fn is_neutral(&self) -> bool {
        match self {
            Self::Abs(_, _) => false,
            Self::App(_, m1, m2) => m1.is_neutral() && m2.is_normal(),
            Self::Bvar(_, _) | Self::Fvar(_, _) | Self::Const(_, _) | Self::Mvar(_, _) => true,
        }
    }

    /// `true` if the term is in β-normal form.
    pub fn is_normal(&self) -> bool {
        if let Self::Abs(_, m) = self {
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
            Self::App(_, _, _) => unreachable!(),
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
            | Self::App(_, _, _) => self.is_hnf(),
        }
    }

    /// m = n l*
    /// m.uncurry() // => l*
    /// assert(m = n)
    pub fn uncurry(&mut self) -> Vec<Term> {
        let mut args = vec![];
        while let Self::App(_, m1, m2) = mem::take(self) {
            args.push(*m2);
            *self = *m1;
        }
        args.reverse();
        args
    }

    /// `self` and `ms` have to be fully typed.
    pub fn curry(&mut self, ms: Vec<Term>) {
        // assert!(self.is_well_typed());
        // assert!(ms.iter().all(Term::is_well_typed));
        for m in ms {
            let t = match self.r#type() {
                Type::Arrow(t1, t2) => {
                    assert_eq!(&**t1, m.r#type());
                    (**t2).clone()
                }
                _ => panic!("type mismatch at Term::curry"),
            };
            self.mk_app(m, t);
        }
    }

    /// Check if the term is in η-long β-normal form.
    /// `self` must be fully typed.
    /// See Lectures on the Curry-Howard isomorphism, Chapter 4.
    /// https://math.stackexchange.com/q/3334730
    pub fn is_canonical(&self) -> bool {
        // assert!(self.is_well_typed());
        match self.r#type() {
            Type::Arrow(_, _) => {
                if let Self::Abs(_, m) = self {
                    m.is_canonical()
                } else {
                    false
                }
            }
            Type::Base(_) | Type::Mvar(_) => {
                let mut m = self;
                while let Self::App(_, m1, m2) = m {
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
                    Self::App(_, _, _) => unreachable!(),
                }
            }
        }
    }

    /// self.open_subst(m) == [m/x][x/0]self (for fresh x) == [m/0]self
    fn open_subst(&mut self, m: &Term) {
        // TODO: traverse the whole term only once
        let x = fresh();
        self.open(&x);
        self.subst(&x, m);
    }

    /// applicative-order (leftmost-innermost) reduction
    fn beta_reduce(&mut self) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(_, _) => {}
            Self::Const(_, _) => {}
            Self::Mvar(_, _) => {}
            Self::App(_, m1, m2) => {
                m1.beta_reduce();
                m2.beta_reduce();
                if let Self::Abs(_, m) = &mut **m1 {
                    m.open_subst(m2);
                    m.beta_reduce();
                    *self = mem::take(m);
                }
            }
            Self::Abs(_, m) => m.beta_reduce(),
        }
    }

    /// [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_neutral(&mut self) {
        assert!(self.is_neutral());
        // [x M₁ ... Mₙ] := x [M₁] ... [Mₙ]
        let mut m = &mut *self;
        loop {
            match m {
                Self::Fvar(_, _) | Self::Bvar(_, _) | Self::Const(_, _) | Self::Mvar(_, _) => {
                    break;
                }
                Self::App(_, m1, m2) => {
                    m2.eta_expand_normal();
                    m = m1;
                }
                Self::Abs(_, _) => unreachable!(),
            }
        }
        // [M] := λv*. M v*
        let binder: Vec<_> = self
            .r#type()
            .components()
            .into_iter()
            .map(|t| (fresh(), t.clone()))
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

    /// self must be in β-normal form.
    /// 1. [λx.M] := λx.[M]
    /// 2. [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_normal(&mut self) {
        assert!(self.is_normal());
        match self {
            Self::Abs(_, m) => {
                let x = fresh();
                m.open(&x);
                m.eta_expand_normal();
                m.close(&x);
            }
            Self::Bvar(_, _)
            | Self::Fvar(_, _)
            | Self::Const(_, _)
            | Self::Mvar(_, _)
            | Self::App(_, _, _) => {
                self.eta_expand_neutral();
            }
        }
    }

    /// self must be fully typed
    pub fn canonicalize(&mut self) {
        // assert!(self.is_well_typed());
        self.beta_reduce();
        self.eta_expand_normal();
    }

    /// self and other must be fully typed
    pub fn def_eq(&self, other: &Self) -> bool {
        // assert!(self.is_well_typed());
        // assert!(other.is_well_typed());
        let mut m1 = self.clone();
        m1.canonicalize();
        let mut m2 = other.clone();
        m2.canonicalize();
        m1 == m2
    }
}

#[derive(Clone, Debug, Default)]
struct TypeSubst(Vec<(MvarId, Type)>);

impl TypeSubst {
    fn unify(&mut self, t1: &Type, t2: &Type) {
        if t1 == t2 {
            return;
        }
        match (t1, t2) {
            (Type::Arrow(t11, t12), Type::Arrow(t21, t22)) => {
                self.unify(t11, t21);
                self.unify(t12, t22);
            }
            (Type::Mvar(i), t) | (t, Type::Mvar(i)) => {
                if self.0.iter().find(|(j, _)| j == i).is_none() {
                    // TODO: occur check
                    self.0.push((*i, t.clone()));
                } else {
                    let mut u = Type::Mvar(*i);
                    u.apply_subst(&self);
                    self.unify(&u, t);
                }
            }
            (t1, t2) => {
                todo!("unify failed {:?} {:?}", t1, t2);
            }
        }
    }
}

impl Type {
    fn apply_subst(&mut self, subst: &TypeSubst) {
        for (i, u) in &subst.0 {
            self.subst_meta(*i, u);
        }
    }
}

impl Term {
    fn apply_type_subst(&mut self, subst: &TypeSubst) {
        for (i, t) in &subst.0 {
            self.subst_type_meta(*i, t);
        }
    }

    // TODO: split env into consts and freevars
    fn infer_help(&mut self, subst: &mut TypeSubst, env: &mut HashMap<String, Type>) {
        match self {
            Term::Fvar(t, name) | Term::Const(t, name) => {
                let u = env
                    .get(name)
                    .unwrap_or_else(|| todo!("constant or fvar not found {}", name));
                subst.unify(t, u);
            }
            Term::Mvar(_, _) => {}
            Term::Bvar(_, _) => todo!(),
            Term::Abs(t, m) => {
                let mid = MvarId::fresh();
                subst.unify(
                    t,
                    &Type::Arrow(Box::new(Type::Mvar(mid)), Box::new(m.r#type().clone())),
                );
                let name = fresh();
                env.insert(name.clone(), Type::Mvar(mid));
                m.open(&name);
                m.infer_help(subst, env);
                m.close(&name);
                env.remove(&name);
            }
            Term::App(t, m1, m2) => {
                subst.unify(
                    m1.r#type(),
                    &Type::Arrow(Box::new(m2.r#type().clone()), Box::new(t.clone())),
                );
                m1.infer_help(subst, env);
                m2.infer_help(subst, env);
            }
        }
    }

    pub fn infer(&mut self, env: &HashMap<String, Type>) {
        let mut subst = TypeSubst::default();
        self.infer_help(&mut subst, &mut env.clone());
        self.apply_type_subst(&subst);
    }
}

/// A convenient representation of head normal form.
/// Recall that every (normal) term has form `λv*. m n*`.
#[derive(Clone)]
struct Hnf {
    /// Outermost-first
    binder: Vec<(String, Type)>,
    /// Fvar, Const, or Mvar.
    // TODO: use locally nameless forms directly.
    head: Term,
    /// Huch calls these parts "arguments" [Huch, 2020](https://www21.in.tum.de/teaching/sar/SS20/5.pdf).
    /// See also Notation 2.29 in The Clausal Theory of Types [Wolfram, 2009].
    args: Vec<Term>,
}

impl From<Term> for Hnf {
    /// `m` has to be fully typed and canonicalized.
    fn from(m: Term) -> Self {
        assert!(m.is_canonical());
        let mut binder = vec![];
        let mut head = m;
        while let Term::Abs(t, mut m) = head {
            let x = fresh();
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
    fn matrix(&self) -> (&Term, &Vec<Term>) {
        (&self.head, &self.args)
    }

    /// `self` must be flex and `other` must be rigid.
    /// Suppose `f ≡ λx*. X t*` and `r ≡ λy*. x u*`.
    /// Imitation: X ↦ λz*. x (Y z*)* (when x = c)
    /// Projection: X ↦ λz*. zᵢ (Y z*)* (when τ(zᵢ) is compatible with τ(x))
    fn r#match(&self, other: &Hnf) -> Vec<(MvarId, Term)> {
        let (t, mid) = if let Term::Mvar(t, mid) = &self.head {
            (t, *mid)
        } else {
            panic!("self is not flex")
        };
        let zs: Vec<_> = self.args.iter().map(|m| (fresh(), m.r#type())).collect();
        let mut heads = vec![];
        // projection
        for (x, u) in &zs {
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
                        t.curry(zs.iter().map(|(_, t)| (*t).clone()).collect());
                        let mut m = Term::Mvar(t, MvarId::fresh());
                        m.curry(
                            zs.iter()
                                .map(|(x, t)| Term::Fvar((*t).clone(), x.to_owned()))
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
    /// `m1` and `m2` must be canonical.
    fn add(&mut self, m1: Hnf, m2: Hnf) {
        match (m1.head.is_rigid(), m2.head.is_rigid()) {
            (true, true) => self.rr.push((m1, m2)),
            (true, false) => self.fr.push((m2, m1)),
            (false, true) => self.fr.push((m1, m2)),
            (false, false) => self.ff.push((m1, m2)),
        }
    }

    /// decompose rigid-rigid pairs by chopping into smaller ones
    fn simplify(&mut self) {
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
                todo!("not unifiable");
            }
        }
    }

    fn solve(self) -> Vec<(MvarId, Term)> {
        let mut queue = VecDeque::new();
        queue.push_back((self, vec![]));
        while let Some((mut set, subst)) = queue.pop_front() {
            set.simplify();
            if set.fr.is_empty() {
                return subst;
            }
            let (h1, h2) = &set.fr[0];
            for (mid, m) in h1.r#match(h2) {
                let mut new_set = DisagreementSet::default();
                for (m1, m2) in set.fr.iter().chain(set.ff.iter()) {
                    let mut m1 = Term::from(m1.clone());
                    m1.subst_meta(mid, &m);
                    m1.canonicalize();
                    let mut m2 = Term::from(m2.clone());
                    m2.subst_meta(mid, &m);
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
    /// `self` and `other` must be fully-typed.
    fn unify(&mut self, other: &mut Term) {
        let mut set = DisagreementSet::default();
        self.canonicalize();
        let h1 = Hnf::from(self.clone());
        other.canonicalize();
        let h2 = Hnf::from(mem::take(other));
        set.add(h1, h2);
        let subst = set.solve();
        for (mid, m) in subst {
            self.subst_meta(mid, &m);
        }
        *other = self.clone();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer() {
        let env = vec![(
            "f".to_owned(),
            Type::Arrow(
                Type::Base("A".to_owned()).into(),
                Type::Base("B".to_owned()).into(),
            ),
        )]
        .into_iter()
        .collect();
        let mut m = Term::Fvar(Type::Mvar(MvarId::fresh()), "f".to_owned());
        m.mk_app(
            Term::Fvar(Type::Mvar(MvarId::fresh()).into(), "x".to_owned()),
            Type::Mvar(MvarId::fresh()),
        );
        m.mk_abs("x", Type::Mvar(MvarId::fresh()));
        m.infer(&env);
        assert_eq!(
            m.r#type(),
            &Type::Arrow(
                Type::Base("A".to_owned()).into(),
                Type::Base("B".to_owned()).into()
            )
        );
    }
}
