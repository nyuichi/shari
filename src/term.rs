use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet};

fn fresh() -> String {
    use std::sync::{Arc, Mutex};
    static COUNTER: Lazy<Arc<Mutex<usize>>> = Lazy::new(Default::default);
    let mut c = COUNTER.lock().unwrap();
    let r = *c;
    *c += 1;
    format!("#{}", r)
}

// TODO: reclaim unused mvars
pub fn fresh_mvar() -> usize {
    use std::sync::{Arc, Mutex};
    static COUNTER: Lazy<Arc<Mutex<usize>>> = Lazy::new(Default::default);
    let mut c = COUNTER.lock().unwrap();
    let r = *c;
    *c += 1;
    r
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Fvar(String),
    Bvar(usize),
    Arrow(Box<Type>, Box<Type>),
    Mvar(usize),
}

impl Default for Type {
    fn default() -> Self {
        Self::Bvar(0xdeadbeef)
    }
}

impl Type {
    fn instantiate(&mut self, mids: &[usize]) {
        match self {
            Self::Fvar(_) => {}
            Self::Bvar(i) => {
                *self = Self::Mvar(mids[*i]);
            }
            Self::Arrow(t1, t2) => {
                t1.instantiate(mids);
                t2.instantiate(mids);
            }
            Self::Mvar(_) => todo!("mvar in Type::instantiate"),
        }
    }

    pub fn uncurry(&self) -> (Vec<&Type>, &Type) {
        let mut ts = vec![];
        let mut t = self;
        while let Self::Arrow(t1, t2) = t {
            ts.push(&**t1);
            t = t2;
        }
        (ts, t)
    }

    pub fn subst_meta(&mut self, i: usize, t: &Type) {
        match self {
            Self::Fvar(_) => {}
            Self::Bvar(_) => {}
            Self::Mvar(j) => {
                if i == *j {
                    *self = t.clone();
                }
            }
            Self::Arrow(t1, t2) => {
                t1.subst_meta(i, t);
                t2.subst_meta(i, t);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeScheme(usize, Type);

impl TypeScheme {
    pub fn instantiate(&self) -> Type {
        let mut t = self.1.clone();
        if self.0 > 0 {
            t.instantiate(
                &std::iter::repeat_with(fresh_mvar)
                    .take(self.0)
                    .collect::<Vec<_>>(),
            );
        }
        t
    }
}

// locally nameless representation
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Fvar(Type, String),
    Bvar(Type, usize),
    Abs(Type, Box<Term>),
    App(Type, Box<Term>, Box<Term>),
}

impl Default for Term {
    fn default() -> Self {
        Self::Bvar(Type::default(), 0xdeadbeef)
    }
}

impl Term {
    pub fn r#type(&self) -> &Type {
        match self {
            Self::Fvar(t, _) => t,
            Self::Bvar(t, _) => t,
            Self::Abs(t, _) => t,
            Self::App(t, _, _) => t,
        }
    }

    /// self.open(x) == [x/0]self
    pub fn open(&mut self, name: &str) {
        self.open_at(name, 0)
    }

    fn open_at(&mut self, name: &str, level: usize) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(t, i) => {
                if *i == level {
                    *self = Self::Fvar(std::mem::take(t), name.to_owned());
                }
            }
            Self::Abs(_, n) => {
                n.open_at(name, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.open_at(name, level);
                m2.open_at(name, level);
            }
        }
    }

    /// self.close(x) == [0/x]self
    pub fn close(&mut self, name: &str) {
        self.close_at(name, 0)
    }

    fn close_at(&mut self, name: &str, level: usize) {
        match self {
            Self::Fvar(t, ref x) => {
                if name == x {
                    *self = Self::Bvar(std::mem::take(t), level);
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
        }
    }

    pub fn mk_abs(&mut self, name: &str, t: Type) {
        let t = Type::Arrow(Box::new(t), Box::new(self.r#type().clone()));
        self.close(name);
        *self = Self::Abs(t, Box::new(std::mem::take(self)));
    }

    pub fn mk_app(&mut self, arg: Term, t: Type) {
        *self = Self::App(t, Box::new(std::mem::take(self)), Box::new(arg));
    }

    pub fn is_fresh(&self, name: &str) -> bool {
        match self {
            Self::Fvar(_, x) => name != x,
            Self::Bvar(_, _) => true,
            Self::Abs(_, m) => m.is_closed(),
            Self::App(_, m1, m2) => m1.is_closed() && m2.is_closed(),
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Fvar(_, _) => false,
            Self::Bvar(_, _) => true,
            Self::Abs(_, m) => m.is_closed(),
            Self::App(_, m1, m2) => m1.is_closed() && m2.is_closed(),
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
        }
    }

    pub fn is_body(&self) -> bool {
        self.is_locally_closed_at(1)
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
        }
    }

    pub fn subst_type_meta(&mut self, i: usize, t: &Type) {
        match self {
            Self::Fvar(u, _) => u.subst_meta(i, t),
            Self::Bvar(u, _) => {
                u.subst_meta(i, t);
            }
            Self::Abs(u, m) => {
                u.subst_meta(i, t);
                m.subst_type_meta(i, t);
            }
            Self::App(u, m1, m2) => {
                u.subst_meta(i, t);
                m1.subst_type_meta(i, t);
                m2.subst_type_meta(i, t);
            }
        }
    }

    /// self.open_subst(m) == [m/x][x/0]self (for fresh x) == [m/0]self
    fn open_subst(&mut self, m: &Term) {
        let x = fresh();
        self.open(&x);
        self.subst(&x, m);
    }

    /// `t` in `λv*. t m*`
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

    fn is_neutral(&self) -> bool {
        match self {
            Self::Abs(_, _) => false,
            Self::App(_, m1, m2) => m1.is_neutral() && m2.is_normal(),
            Self::Bvar(_, _) | Self::Fvar(_, _) => true,
        }
    }

    /// `true` if the term is in a β-normal form.
    pub fn is_normal(&self) -> bool {
        if let Self::Abs(_, m) = self {
            m.is_normal()
        } else {
            self.is_neutral()
        }
    }

    /// does not check if a term inside an abstraction is in a whnf
    pub fn is_whnf(&self) -> bool {
        match self {
            Self::Abs(_, _) => true,
            Self::Bvar(_, _) | Self::Fvar(_, _) | Self::App(_, _, _) => match self.head() {
                Self::Bvar(_, _) | Self::Fvar(_, _) => true,
                Self::App(_, _, _) | Self::Abs(_, _) => false,
            },
        }
    }

    /// Check if the term is in a η-long β-normal form.
    /// `self` must be fully typed.
    /// See Lectures on the Curry-Howard isomorphism, Chapter 4.
    pub fn is_canonical(&self) -> bool {
        match self.r#type() {
            Type::Arrow(_, _) => {
                if let Self::Abs(_, m) = self {
                    m.is_canonical()
                } else {
                    false
                }
            }
            Type::Fvar(_) | Type::Bvar(_) | Type::Mvar(_) => {
                let mut m = self;
                while let Self::App(_, m1, m2) = m {
                    if !m2.is_canonical() {
                        return false;
                    }
                    m = m1;
                }
                match m {
                    Self::Fvar(_, _) | Self::Bvar(_, _) => true,
                    Self::Abs(_, _) => false,
                    Self::App(_, _, _) => unreachable!(),
                }
            }
        }
    }

    /// applicative-order (leftmost-innermost) reduction
    fn beta_reduce(&mut self) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(_, _) => {}
            Self::App(_, m1, m2) => {
                m1.beta_reduce();
                m2.beta_reduce();
                if let Self::Abs(_, m) = &mut **m1 {
                    m.open_subst(m2);
                    *self = std::mem::take(m);
                    self.beta_reduce();
                }
            }
            Self::Abs(_, m) => m.beta_reduce(),
        }
    }

    /// Type directed naive η expansion
    /// [M] := λv*. M v*
    fn naive_expand(&mut self) {
        let args: Vec<_> = self
            .r#type()
            .uncurry()
            .0
            .into_iter()
            .map(|t| (fresh(), t.clone()))
            .collect();

        for (name, t) in &args {
            let arg = Term::Fvar(t.clone(), name.to_owned());
            let t = match self.r#type() {
                Type::Arrow(_, t2) => (**t2).clone(),
                _ => unreachable!(),
            };
            self.mk_app(arg, t);
        }
        for (name, t) in args {
            self.mk_abs(&name, t);
        }
    }

    /// 1. [x M₁ ... Mₙ] := x [M₁] ... [Mₙ]
    /// 2. [(λx.M) M₁ ... Mₙ] := (λx.[M]) [M₁] ... [Mₙ]
    fn eta_expand_head(&mut self) {
        match self {
            Self::Fvar(_, _) | Self::Bvar(_, _) => {}
            Self::Abs(_, _) => {
                self.eta_expand();
            }
            Self::App(_, m1, m2) => {
                m1.eta_expand_head();
                m2.eta_expand();
            }
        }
    }

    /// Gives the long η form, which is formally defined as follows:
    /// 1. [λx.M] := λx.[M]
    /// 2. [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    /// 3. [(λx.M) M₁ ... Mₙ] := λv*. (λx.[M]) [M₁] ... [Mₙ] v*
    fn eta_expand(&mut self) {
        match self {
            Self::Abs(_, m) => {
                let x = fresh();
                m.open(&x);
                m.eta_expand();
                m.close(&x);
            }
            Self::Bvar(_, _) | Self::Fvar(_, _) | Self::App(_, _, _) => {
                self.eta_expand_head();
                self.naive_expand();
            }
        }
    }

    pub fn canonicalize(&mut self) {
        self.beta_reduce();
        self.eta_expand();
    }

    pub fn def_eq(&self, other: &Self) -> bool {
        let mut m1 = self.clone();
        let mut m2 = other.clone();
        m1.canonicalize();
        m2.canonicalize();
        m1 == m2
    }
}

#[derive(Clone, Debug, Default)]
struct TypeSubst(Vec<(usize, Type)>);

impl TypeSubst {
    // should we put this method in `impl Type` instead?
    fn apply_type(&self, t: &mut Type) {
        for (i, u) in &self.0 {
            t.subst_meta(*i, u);
        }
    }

    fn apply_term(&self, m: &mut Term) {
        for (i, t) in &self.0 {
            m.subst_type_meta(*i, t);
        }
    }

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
                    self.apply_type(&mut u);
                    self.unify(&u, t);
                }
            }
            (t1, t2) => {
                unimplemented!("unify {:?} {:?}", t1, t2);
            }
        }
    }

    // TODO: split env into consts and freevars
    fn infer(&mut self, m: &mut Term, env: &mut HashMap<String, TypeScheme>) {
        match m {
            Term::Fvar(t, name) => {
                let u = match env.get(name) {
                    None => unimplemented!("{}", name),
                    Some(s) => s.instantiate(),
                };
                self.unify(t, &u);
            }
            Term::Bvar(_, _) => unimplemented!(),
            Term::Abs(t, m) => {
                let mid = fresh_mvar();
                self.unify(
                    t,
                    &Type::Arrow(Box::new(Type::Mvar(mid)), Box::new(m.r#type().clone())),
                );
                let name = fresh();
                env.insert(name.clone(), TypeScheme(0, Type::Mvar(mid)));
                m.open(&name);
                self.infer(m, env);
                m.close(&name);
                env.remove(&name);
            }
            Term::App(t, m1, m2) => {
                self.unify(
                    m1.r#type(),
                    &Type::Arrow(Box::new(m2.r#type().clone()), Box::new(t.clone())),
                );
                self.infer(m1, env);
                self.infer(m2, env);
            }
        }
    }
}

impl Term {
    pub fn infer(&mut self, env: &HashMap<String, TypeScheme>) {
        let mut subst = TypeSubst::default();
        subst.infer(self, &mut env.clone());
        subst.apply_term(self);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer() {
        let env = vec![(
            "f".to_owned(),
            TypeScheme(
                0,
                Type::Arrow(
                    Type::Fvar("a".to_owned()).into(),
                    Type::Fvar("b".to_owned()).into(),
                ),
            ),
        )]
        .into_iter()
        .collect();
        let mut m = Term::Fvar(Type::Mvar(fresh_mvar()), "f".to_owned());
        m.mk_app(
            Term::Fvar(Type::Mvar(fresh_mvar()).into(), "x".to_owned()),
            Type::Mvar(fresh_mvar()),
        );
        m.mk_abs("x", Type::Mvar(fresh_mvar()));
        m.infer(&env);
        assert_eq!(
            m.r#type(),
            &Type::Arrow(
                Type::Fvar("a".to_owned()).into(),
                Type::Fvar("b".to_owned()).into()
            )
        );
    }
}
