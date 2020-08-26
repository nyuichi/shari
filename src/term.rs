use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet};

fn fresh() -> String {
    use std::sync::{Arc, Mutex};
    static COUNTER: Lazy<Arc<Mutex<usize>>> = Lazy::new(Default::default);
    let mut c = COUNTER.lock().unwrap();
    let r = *c;
    *c += 1;
    format!("g#{}", r)
}

fn fresh_tvar() -> usize {
    use std::sync::{Arc, Mutex};
    static COUNTER: Lazy<Arc<Mutex<usize>>> = Lazy::new(Default::default);
    let mut c = COUNTER.lock().unwrap();
    let r = *c;
    *c += 1;
    r
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Var(usize),
    Arrow(Box<Type>, Box<Type>),
    Base(String),
}

impl Type {
    pub fn subst(&mut self, i: usize, t: &Type) {
        match self {
            Self::Var(j) => {
                if i == *j {
                    *self = t.clone();
                }
            }
            Self::Arrow(t1, t2) => {
                t1.subst(i, t);
                t2.subst(i, t);
            }
            Self::Base(_) => {}
        }
    }

    fn apply_subst(&mut self, subst: &TypeSubst) {
        for (i, t) in &subst.0 {
            self.subst(*i, t);
        }
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

impl Term {
    pub fn r#type(&self) -> &Type {
        match self {
            Self::Fvar(t, _) => t,
            Self::Bvar(t, _) => t,
            Self::Abs(t, _) => t,
            Self::App(t, _, _) => t,
        }
    }

    /// self.open_subst(m) == [m/x][x/0]self (x#self) == [m/0]self
    pub fn open_subst(&mut self, m: &Term) {
        self.open_subst_at(m, 0)
    }

    fn open_subst_at(&mut self, m: &Term, level: usize) {
        match self {
            Self::Fvar(_, _) => {}
            Self::Bvar(_, i) => {
                if *i == level {
                    *self = m.clone();
                }
            }
            Self::Abs(_, n) => {
                n.open_subst_at(m, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.open_subst_at(m, level);
                m2.open_subst_at(m, level);
            }
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
                    *self = Self::Fvar(std::mem::replace(t, Type::Var(0)), name.to_owned());
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
                    *self = Self::Bvar(std::mem::replace(t, Type::Var(0)), level);
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

    pub fn into_abs(mut self, name: &str, t: Type) -> Self {
        let t = Type::Arrow(Box::new(t), Box::new(self.r#type().clone()));
        self.close(name);
        Self::Abs(t, Box::new(self))
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

    pub fn subst_type(&mut self, i: usize, t: &Type) {
        match self {
            Self::Fvar(u, _) => u.subst(i, t),
            Self::Bvar(u, _) => {
                u.subst(i, t);
            }
            Self::Abs(u, m) => {
                u.subst(i, t);
                m.subst_type(i, t);
            }
            Self::App(u, m1, m2) => {
                u.subst(i, t);
                m1.subst_type(i, t);
                m2.subst_type(i, t);
            }
        }
    }

    fn apply_subst_type(&mut self, subst: &TypeSubst) {
        for (i, t) in &subst.0 {
            self.subst_type(*i, t);
        }
    }

    pub fn head(&self) -> &Self {
        let mut m = self;
        while let Self::App(_, m1, _) = m {
            m = m1;
        }
        m
    }
}

#[derive(Clone, Debug, Default)]
struct TypeSubst(Vec<(usize, Type)>);

impl TypeSubst {
    fn unify(&mut self, t1: &Type, t2: &Type) {
        match (t1, t2) {
            (Type::Arrow(t11, t12), Type::Arrow(t21, t22)) => {
                self.unify(t11, t21);
                self.unify(t12, t22);
            }
            (Type::Base(name1), Type::Base(name2)) => {
                if name1 != name2 {
                    unimplemented!("unify {:?} {:?}", t1, t2);
                }
            }
            (Type::Var(i), t) | (t, Type::Var(i)) => {
                if &Type::Var(*i) == t {
                    return;
                }
                if self.0.iter().find(|(j, _)| j == i).is_none() {
                    // TODO: occur check
                    self.0.push((*i, t.clone()));
                } else {
                    let mut u = Type::Var(*i);
                    u.apply_subst(self);
                    self.unify(&u, t);
                }
            }
            (t1, t2) => {
                unimplemented!("unify {:?} {:?}", t1, t2);
            }
        }
    }

    fn infer(&mut self, m: &mut Term, env: &mut HashMap<String, (HashSet<usize>, Type)>) {
        match m {
            Term::Fvar(t, name) => {
                let u = match env.get(name) {
                    None => unimplemented!("{}", name),
                    Some((vars, t)) => {
                        // rename schematic type variables
                        let mut u = t.clone();
                        for s in vars {
                            u.subst(*s, &Type::Var(fresh_tvar()));
                        }
                        u
                    }
                };
                self.unify(t, &u);
            }
            Term::Bvar(_, _) => unimplemented!(),
            Term::Abs(t, m) => {
                let fresh_tv = fresh_tvar();
                self.unify(
                    t,
                    &Type::Arrow(Box::new(Type::Var(fresh_tv)), Box::new(m.r#type().clone())),
                );
                let name = fresh();
                env.insert(name.clone(), (Default::default(), Type::Var(fresh_tv)));
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
    pub fn infer(&mut self, env: &HashMap<String, (HashSet<usize>, Type)>) {
        let mut subst = TypeSubst::default();
        subst.infer(self, &mut env.clone());
        self.apply_subst_type(&subst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer() {
        let env = vec![(
            "f".to_owned(),
            (
                Default::default(),
                Type::Arrow(
                    Type::Base("a".to_owned()).into(),
                    Type::Base("b".to_owned()).into(),
                ),
            ),
        )]
        .into_iter()
        .collect();
        let mut m = Term::App(
            Type::Var(fresh_tvar()),
            Term::Fvar(Type::Var(fresh_tvar()), "f".to_owned()).into(),
            Term::Bvar(Type::Var(fresh_tvar()).into(), 0).into(),
        )
        .into_abs("x", Type::Var(fresh_tvar()));
        m.infer(&env);
        assert_eq!(
            m.r#type(),
            &Type::Arrow(
                Type::Base("a".to_owned()).into(),
                Type::Base("b".to_owned()).into()
            )
        );
    }
}
