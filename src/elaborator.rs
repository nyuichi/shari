use crate::parser;
use crate::term::{self, MvarId, Name, Scheme, Sign};
use std::collections::HashMap;

#[derive(Debug)]
struct Env<'a> {
    sign: &'a Sign,
    local_consts: &'a HashMap<Name, term::Type>,
    locals: Vec<(Name, Type)>,
}

impl<'a> Env<'a> {
    fn get_local(&self, name: &Name) -> Option<Type> {
        for (x, t) in self.locals.iter().rev() {
            if x == name {
                return Some(t.clone());
            }
        }
        if let Some(t) = self.local_consts.get(name) {
            return Some(Type::from(t.clone()));
        }
        None
    }

    fn get_const(&self, name: &Name) -> Option<Scheme<Type>> {
        if let Some(s) = self.sign.get_const(name) {
            return Some(s.clone().into());
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
}

impl From<parser::Name> for Name {
    fn from(name: parser::Name) -> Self {
        Name::Named(Box::new(name.0))
    }
}

impl From<Scheme<term::Type>> for Scheme<Type> {
    fn from(s: Scheme<term::Type>) -> Self {
        Self {
            type_vars: s.type_vars,
            main: Type::from(s.main),
        }
    }
}

impl Scheme<Type> {
    pub fn instantiate(&self, args: &[Type]) -> Type {
        assert_eq!(self.arity(), args.len());
        let mut t = self.main.clone();
        for (name, u) in self.type_vars.iter().zip(args.iter()) {
            t.subst(name, u);
        }
        t
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Var(Name),
    Arrow(Box<Type>, Box<Type>),
    Mvar(MvarId),
}

impl From<parser::Type> for Type {
    fn from(t: parser::Type) -> Self {
        match t {
            parser::Type::Var(name) => Type::Var(name.into()),
            parser::Type::Arrow(t1, t2) => {
                Type::Arrow(Box::new((*t1).into()), Box::new((*t2).into()))
            }
        }
    }
}

impl From<term::Type> for Type {
    fn from(t: term::Type) -> Self {
        match t {
            term::Type::Fvar(name) => Type::Var(name),
            term::Type::Arrow(p) => {
                let (t1, t2) = *p;
                Type::Arrow(Box::new(t1.into()), Box::new(t2.into()))
            }
        }
    }
}

impl Type {
    fn subst(&mut self, name: &Name, t: &Type) {
        match self {
            Self::Var(x) => {
                if x == name {
                    *self = t.clone();
                }
            }
            Self::Arrow(t1, t2) => {
                t1.subst(name, t);
                t2.subst(name, t);
            }
            Self::Mvar(_) => {}
        }
    }

    fn instantiate(&mut self, mid: &MvarId, t: &Type) {
        match self {
            Self::Var(_) => {}
            Self::Mvar(x) => {
                if x == mid {
                    *self = t.clone();
                }
            }
            Self::Arrow(t1, t2) => {
                t1.instantiate(mid, t);
                t2.instantiate(mid, t);
            }
        }
    }

    fn certify(self) -> term::Type {
        match self {
            Type::Var(name) => term::Type::Fvar(name),
            Type::Arrow(t1, t2) => {
                let mut t = t2.certify();
                t.curry(vec![t1.certify()]);
                t
            }
            Type::Mvar(_) => unreachable!("logic flaw: uninstantiated type meta variable found"),
        }
    }

    pub fn elaborate(self, _sign: &Sign) -> term::Type {
        // TODO: find undefined base types
        self.certify()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(Type, Name),
    Abs(Name, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
    Const(Type, Name, Vec<Type>),
}

impl From<parser::Term> for Term {
    fn from(m: parser::Term) -> Self {
        match m {
            parser::Term::Var(name) => Term::Var(Type::Mvar(MvarId::fresh()), name.into()),
            parser::Term::Abs(name, t, m) => {
                let t = match t {
                    Some(t) => Type::from(t),
                    None => Type::Mvar(MvarId::fresh()),
                };
                Term::Abs(name.into(), t, Box::new((*m).into()))
            }
            parser::Term::App(m1, m2) => Term::App(Box::new((*m1).into()), Box::new((*m2).into())),
        }
    }
}

impl Term {
    fn instantiate_type(&mut self, mid: &MvarId, t: &Type) {
        match self {
            Self::Abs(_, u, m) => {
                u.instantiate(mid, t);
                m.instantiate_type(mid, t);
            }
            Self::App(m1, m2) => {
                m1.instantiate_type(mid, t);
                m2.instantiate_type(mid, t);
            }
            Self::Const(u, _, ts) => {
                u.instantiate(mid, t);
                for u in ts {
                    u.instantiate(mid, t);
                }
            }
            Self::Var(u, _) => u.instantiate(mid, t),
        }
    }

    fn certify(self) -> term::Term {
        match self {
            Term::Var(t, name) => term::Term::Fvar(t.certify(), name),
            Term::Abs(name, t, m) => {
                let mut m = m.certify();
                m.mk_abs(&name, t.certify());
                m
            }
            Term::App(m1, m2) => {
                let mut m = m1.certify();
                m.mk_app(m2.certify());
                m
            }
            Term::Const(t, name, ts) => term::Term::Const(
                t.certify(),
                Box::new((name, ts.into_iter().map(Type::certify).collect())),
            ),
        }
    }

    pub fn elaborate(
        mut self,
        sign: &Sign,
        local_consts: &HashMap<Name, term::Type>,
    ) -> term::Term {
        let mut local_env = Env {
            sign,
            local_consts,
            locals: vec![],
        };
        self.infer(&mut local_env);
        // TODO: make sure no meta type var remains
        self.certify()
    }
}

#[derive(Clone, Debug, Default)]
struct TypeSubst(Vec<(MvarId, Type)>);

impl TypeSubst {
    fn unify(&mut self, t1: &mut Type, t2: &mut Type) {
        t1.apply_subst(self);
        t2.apply_subst(self);
        if t1 == t2 {
            return;
        }
        match (t1, t2) {
            (Type::Arrow(t11, t12), Type::Arrow(t21, t22)) => {
                self.unify(t11, t21);
                self.unify(t12, t22);
            }
            (&mut Type::Mvar(i), t) | (t, &mut Type::Mvar(i)) => {
                if self.0.iter().find(|(j, _)| *j == i).is_none() {
                    // TODO: occur check
                    self.0.push((i, t.clone()));
                } else {
                    let mut u = Type::Mvar(i);
                    u.apply_subst(&self);
                    self.unify(&mut u, t);
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
        for (mid, u) in &subst.0 {
            self.instantiate(mid, u);
        }
    }
}

impl Term {
    fn apply_type_subst(&mut self, subst: &TypeSubst) {
        for (mid, t) in &subst.0 {
            self.instantiate_type(mid, t);
        }
    }

    fn infer_help(&mut self, subst: &mut TypeSubst, env: &mut Env) -> Type {
        match self {
            Term::Var(t, name) => {
                if let Some(mut u) = env.get_local(name) {
                    subst.unify(t, &mut u);
                    return u;
                }
                if let Some(scheme) = env.get_const(name) {
                    let ts: Vec<_> = (0..scheme.arity())
                        .map(|_| Type::Mvar(MvarId::fresh()))
                        .collect();
                    let mut u = scheme.instantiate(&ts);
                    subst.unify(t, &mut u);
                    *self = Term::Const(u.clone(), name.clone(), ts);
                    return u;
                }
                todo!("variable not found {}", name)
            }
            Term::Const(_, _, _) => {
                unreachable!("logic flaw: const found before type inferenece done")
            }
            Term::Abs(name, t, m) => {
                env.push_local(name.clone(), t.clone());
                let u = m.infer_help(subst, env);
                env.pop_local();
                Type::Arrow(Box::new(t.clone()), Box::new(u))
            }
            Term::App(m1, m2) => {
                let mut t1 = m1.infer_help(subst, env);
                let t2 = m2.infer_help(subst, env);
                let tv = Type::Mvar(MvarId::fresh());
                subst.unify(
                    &mut t1,
                    &mut Type::Arrow(Box::new(t2), Box::new(tv.clone())),
                );
                tv
            }
        }
    }

    fn infer(&mut self, env: &mut Env) {
        let mut subst = TypeSubst::default();
        self.infer_help(&mut subst, env);
        self.apply_type_subst(&subst);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer() {
        let mut sign = Sign::default();
        let mut t = term::Type::Fvar(Name::Named(Box::new("B".to_owned())));
        t.curry(vec![term::Type::Fvar(Name::Named(Box::new(
            "A".to_owned(),
        )))]);
        sign.add_const(
            Name::Named(Box::new("f".to_owned())),
            Scheme::<term::Type> {
                type_vars: vec![],
                main: t,
            },
        );
        let m = parser::tests::parse_term("λ x, f x");
        println!("{:?}", m);
        let m = Term::from(m);
        let m = m.elaborate(&sign, &Default::default());
        println!("{:?}", m);
        // let mut m = Term::Const(Name::Named("f".to_owned()), vec![]);
        // m.mk_app(Term::Fvar(Name::Named("x".to_owned())));
        // m.mk_abs(&Name::Named("x".to_owned()), Type::Mvar(MvarId::fresh()));
        // m.infer(&mut env);
        // assert_eq!(
        //     m.synthesize(&mut env),
        //     Type::Arrow(
        //         Type::Base(Name::Named("A".to_owned())).into(),
        //         Type::Base(Name::Named("B".to_owned())).into()
        //     )
        // );
    }
}
