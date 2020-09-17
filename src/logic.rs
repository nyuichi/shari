use crate::term::{Name, Scheme, Sign, Term, Type};
use std::collections::{HashMap, HashSet};
use std::mem;

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct Spec {
    pub sign: Sign,
    pub defs: HashMap<Name, Scheme<Term>>,
    pub axioms: HashMap<Name, Scheme<Term>>,
    pub theorems: HashMap<Name, Scheme<Theorem>>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Theorem {
    spec: Spec,
    locals: HashMap<Name, Type>,
    assump: HashSet<Term>,
    target: Term,
}

impl std::fmt::Display for Theorem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "▶ ")?;
        for (x, t) in &self.locals {
            write!(f, "({} : {}) ", x, t)?;
        }
        write!(f, "| ")?;
        for p in &self.assump {
            write!(f, "({}) ", p)?;
        }
        write!(f, "⊢ {}", self.target)
    }
}

impl Theorem {
    pub fn target(&self) -> &Term {
        &self.target
    }

    fn merge(&mut self, spec: Spec, locals: HashMap<Name, Type>, assump: HashSet<Term>) {
        assert_eq!(self.spec, spec);
        for (name, t) in locals {
            match self.locals.get(&name) {
                Some(u) => assert_eq!(*u, t),
                None => {
                    let _ = self.locals.insert(name, t).unwrap();
                }
            }
        }
        for h in assump {
            self.assump.insert(h);
        }
    }

    pub fn assume(spec: Spec, locals: HashMap<Name, Type>, target: Term) -> Self {
        assert!(target.is_prop());
        Self {
            spec,
            locals,
            assump: vec![target.clone()].into_iter().collect(),
            target,
        }
    }

    pub fn eq_intro(
        spec: Spec,
        locals: HashMap<Name, Type>,
        assump: HashSet<Term>,
        m1: Term,
        m2: Term,
    ) -> Self {
        for h in &assump {
            assert!(h.is_prop());
        }
        assert_eq!(m1.r#type(), m2.r#type());
        assert!(Term::def_eq(&mut m1.clone(), &mut m2.clone()));
        Self {
            spec,
            locals,
            assump,
            target: Term::mk_eq(m1, m2),
        }
    }

    pub fn eq_elim(&mut self, h: Theorem, c: Term) {
        let (n1, n2) = match mem::take(&mut self.target).as_eq() {
            Some((n1, n2)) => (n1, n2),
            None => todo!(),
        };
        let mut m1 = c.clone();
        m1.fill(&n1);
        assert!(m1.is_prop());
        let mut m2 = c;
        m2.fill(&n2);
        assert!(m2.is_prop());
        assert_eq!(m2, h.target);
        self.merge(h.spec, h.locals, h.assump);
        self.target = m1;
    }

    pub fn imp_intro(&mut self, p: &Term) {
        let p = match self.assump.take(p) {
            Some(p) => p,
            None => todo!(),
        };
        self.target.mk_imp(p);
    }

    pub fn imp_elim(&mut self, h: Theorem) {
        let (p, q) = match mem::take(&mut self.target).as_imp() {
            Some((p, q)) => (p, q),
            None => todo!(),
        };
        assert_eq!(p, h.target);
        self.merge(h.spec, h.locals, h.assump);
        self.target = q;
    }

    pub fn forall_intro(&mut self, name: &Name) {
        for h in &self.assump {
            assert!(h.is_fresh(name));
        }
        let t = match self.locals.remove(name) {
            Some(t) => t,
            None => todo!(),
        };
        self.target.mk_forall(name, t);
    }

    pub fn forall_elim(&mut self, m: &Term) {
        let mut f = match mem::take(&mut self.target).as_forall() {
            Some(f) => f,
            None => todo!(),
        };
        f.fill(m);
        self.target = f;
    }
}

impl Term {
    fn is_prop(&self) -> bool {
        match self.r#type() {
            Type::Fvar(Name::Named(name)) => name == "Prop",
            _ => false,
        }
    }

    /// self must be context-like
    #[doc(hidden)]
    pub fn fill(&mut self, m: &Term) {
        if let Term::Abs(_, t, n) = self {
            assert_eq!(m.r#type(), t);
            let x = Name::fresh();
            n.open(&x);
            n.subst(&x, m);
            *self = mem::take(n);
            return;
        }
        todo!()
    }

    fn mk_eq(m1: Term, m2: Term) -> Self {
        assert_eq!(m1.r#type(), m2.r#type());
        let t = m1.r#type();
        let eq = Term::Const(
            Type::Arrow(
                Box::new(t.clone()),
                Box::new(Type::Arrow(
                    Box::new(t.clone()),
                    Box::new(Type::Fvar(Name::Named("Prop".to_owned()))),
                )),
            ),
            Name::Named("eq".to_owned()),
            vec![t.clone()],
        );
        let mut m = eq;
        m.mk_app(m1);
        m.mk_app(m2);
        m
    }

    pub fn as_eq(mut self) -> Option<(Term, Term)> {
        let mut args = self.uncurry();
        if args.len() == 2 {
            if let Term::Const(_, Name::Named(name), _) = &self {
                if name == "eq" {
                    let n2 = args.pop().unwrap();
                    let n1 = args.pop().unwrap();
                    return Some((n1, n2));
                }
            }
        }
        None
    }

    fn mk_forall(&mut self, name: &Name, t: Type) {
        assert!(self.is_prop());
        self.mk_abs(name, t.clone());
        let mut forall = Term::Const(
            Type::Arrow(
                Box::new(Type::Arrow(
                    Box::new(t.clone()),
                    Box::new(Type::Fvar(Name::Named("Prop".to_owned()))),
                )),
                Box::new(Type::Fvar(Name::Named("Prop".to_owned()))),
            ),
            Name::Named("forall".to_owned()),
            vec![t],
        );
        forall.mk_app(mem::take(self));
        *self = forall;
    }

    pub fn as_forall(mut self) -> Option<Term> {
        let mut args = self.uncurry();
        if args.len() == 1 {
            if let Term::Const(_, Name::Named(name), _) = &self {
                if name == "forall" {
                    let f = args.pop().unwrap();
                    return Some(f);
                }
            }
        }
        None
    }

    #[doc(hidden)]
    pub fn mk_imp(&mut self, p: Term) {
        assert!(self.is_prop());
        assert!(p.is_prop());
        let mut imp = Term::Const(
            Type::Arrow(
                Box::new(Type::Fvar(Name::Named("Prop".to_owned()))),
                Box::new(Type::Arrow(
                    Box::new(Type::Fvar(Name::Named("Prop".to_owned()))),
                    Box::new(Type::Fvar(Name::Named("Prop".to_owned()))),
                )),
            ),
            Name::Named("imp".to_owned()),
            vec![],
        );
        imp.mk_app(p);
        imp.mk_app(mem::take(self));
        *self = imp;
    }

    pub fn as_imp(mut self) -> Option<(Term, Term)> {
        let mut args = self.uncurry();
        if args.len() == 2 {
            if let Term::Const(_, Name::Named(name), _) = &self {
                if name == "imp" {
                    let q = args.pop().unwrap();
                    let p = args.pop().unwrap();
                    return Some((p, q));
                }
            }
        }
        None
    }
}
