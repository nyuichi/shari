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
    Var(Type, usize),    // bound variable
    Local(Type, String), // free variable
    Abs(Type, Box<Term>),
    App(Type, Box<Term>, Box<Term>),
}

impl Term {
    pub fn r#type(&self) -> &Type {
        match self {
            Self::Var(t, _) => t,
            Self::Local(t, _) => t,
            Self::Abs(t, _) => t,
            Self::App(t, _, _) => t,
        }
    }

    /// self.open(m) == [m/0]self
    pub fn open(&mut self, m: &Term) {
        self.open_at(m, 0)
    }

    fn open_at(&mut self, m: &Term, level: usize) {
        match self {
            Self::Var(_, i) => {
                if *i == level {
                    *self = m.clone();
                }
            }
            Self::Local(_, _) => {}
            Self::Abs(_, n) => {
                n.open_at(m, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.open_at(m, level);
                m2.open_at(m, level);
            }
        }
    }

    pub fn open_local(&mut self, local: &str) {
        self.open_local_at(local, 0)
    }

    fn open_local_at(&mut self, local: &str, level: usize) {
        match self {
            Self::Var(t, i) => {
                if *i == level {
                    *self = Self::Local(std::mem::replace(t, Type::Var(0)), local.to_owned());
                }
            }
            Self::Local(_, _) => {}
            Self::Abs(_, n) => {
                n.open_local_at(local, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.open_local_at(local, level);
                m2.open_local_at(local, level);
            }
        }
    }

    /// self.close_local(local) == [0/local]self
    pub fn close_local(&mut self, local: &str) {
        self.close_local_at(local, 0)
    }

    fn close_local_at(&mut self, local: &str, level: usize) {
        match self {
            Self::Var(_, _) => {}
            Self::Local(t, ref name) => {
                if name == local {
                    *self = Self::Var(std::mem::replace(t, Type::Var(0)), level);
                }
            }
            Self::Abs(_, m) => {
                m.close_local_at(local, level + 1);
            }
            Self::App(_, m1, m2) => {
                m1.close_local_at(local, level);
                m2.close_local_at(local, level);
            }
        }
    }

    pub fn into_abs(mut self, local: &str, t: Type) -> Self {
        let t = Type::Arrow(Box::new(t), Box::new(self.r#type().clone()));
        self.close_local(local);
        Self::Abs(t, Box::new(self))
    }

    pub fn is_fresh(&self, local: &str) -> bool {
        match self {
            Self::Var(_, _) => true,
            Self::Local(_, name) => name != local,
            Self::Abs(_, m) => m.is_closed(),
            Self::App(_, m1, m2) => m1.is_closed() && m2.is_closed(),
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Var(_, _) => true,
            Self::Local(_, _) => false,
            Self::Abs(_, m) => m.is_closed(),
            Self::App(_, m1, m2) => m1.is_closed() && m2.is_closed(),
        }
    }

    pub fn is_locally_closed(&self) -> bool {
        self.is_locally_closed_at(0)
    }

    fn is_locally_closed_at(&self, level: usize) -> bool {
        match self {
            Self::Var(_, i) => *i < level,
            Self::Local(_, _) => true,
            Self::Abs(_, m) => m.is_locally_closed_at(level + 1),
            Self::App(_, m1, m2) => {
                m1.is_locally_closed_at(level) && m2.is_locally_closed_at(level)
            }
        }
    }

    pub fn is_body(&self) -> bool {
        self.is_locally_closed_at(1)
    }

    pub fn subst(&mut self, local: &str, m: &Term) {
        match self {
            Self::Var(_, _) => {}
            Self::Local(_, ref name) => {
                if name == local {
                    *self = m.clone();
                }
            }
            Self::App(_, m1, m2) => {
                m1.subst(local, m);
                m2.subst(local, m);
            }
            Self::Abs(_, n) => {
                n.subst(local, m);
            }
        }
    }

    pub fn subst_type(&mut self, i: usize, t: &Type) {
        match self {
            Self::Var(u, _) => {
                u.subst(i, t);
            }
            Self::Local(u, _) => u.subst(i, t),
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
            Term::Var(_, _) => unimplemented!(),
            Term::Local(t, name) => {
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
            Term::Abs(t, m) => {
                let fresh_tv = fresh_tvar();
                self.unify(
                    t,
                    &Type::Arrow(Box::new(Type::Var(fresh_tv)), Box::new(m.r#type().clone())),
                );
                let name = fresh();
                env.insert(name.clone(), (Default::default(), Type::Var(fresh_tv)));
                m.open_local(&name);
                self.infer(m, env);
                m.close_local(&name);
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
            Term::Local(Type::Var(fresh_tvar()), "f".to_owned()).into(),
            Term::Var(Type::Var(fresh_tvar()).into(), 0).into(),
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
