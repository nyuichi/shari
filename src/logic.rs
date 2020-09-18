use crate::term::{Context, Name, Scheme, Sign, Term, Type};
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

    pub fn eq_elim(&mut self, h: Theorem, ctx: Context) {
        let (n1, n2) = match mem::take(&mut self.target).as_eq() {
            Some((n1, n2)) => (n1, n2),
            None => todo!(),
        };
        let mut c1 = ctx.clone();
        c1.fill(&n1);
        assert!(c1.1.is_prop());
        let mut c2 = ctx;
        c2.fill(&n2);
        assert!(c2.1.is_prop());
        assert_eq!(c2.1, h.target);
        self.merge(h.spec, h.locals, h.assump);
        self.target = c1.1;
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
        let mut ctx = match mem::take(&mut self.target).as_forall() {
            Some(f) => f,
            None => todo!(),
        };
        ctx.fill(m);
        self.target = ctx.1;
    }
}

impl Type {
    #[doc(hidden)]
    pub fn mk_prop() -> Type {
        Type::Fvar(Name::Named(Box::new("Prop".to_owned())))
    }
}

impl Term {
    fn is_prop(&self) -> bool {
        match self.r#type() {
            Type::Fvar(Name::Named(name)) => name.as_str() == "Prop",
            _ => false,
        }
    }

    fn mk_eq(m1: Term, m2: Term) -> Self {
        assert_eq!(m1.r#type(), m2.r#type());
        let a = m1.r#type().clone();
        let mut t = Type::mk_prop();
        t.curry(vec![a.clone(), a.clone()]);
        let eq = Term::Const(
            t,
            Box::new((Name::Named(Box::new("eq".to_owned())), vec![a])),
        );
        let mut m = eq;
        m.mk_app(m1);
        m.mk_app(m2);
        m
    }

    pub fn as_eq(mut self) -> Option<(Term, Term)> {
        let mut args = self.uncurry();
        if args.len() == 2 {
            if let Term::Const(_, p) = &self {
                if let (Name::Named(name), _) = &**p {
                    if name.as_str() == "eq" {
                        let n2 = args.pop().unwrap();
                        let n1 = args.pop().unwrap();
                        return Some((n1, n2));
                    }
                }
            }
        }
        None
    }

    fn mk_forall(&mut self, name: &Name, t: Type) {
        assert!(self.is_prop());
        self.mk_abs(name, t.clone());
        let mut pred_ty = Type::mk_prop();
        pred_ty.curry(vec![t.clone()]);
        let mut forall_ty = Type::mk_prop();
        forall_ty.curry(vec![pred_ty]);
        let mut forall = Term::Const(
            forall_ty,
            Box::new((Name::Named(Box::new("forall".to_owned())), vec![t])),
        );
        forall.mk_app(mem::take(self));
        *self = forall;
    }

    pub fn as_forall(mut self) -> Option<Context> {
        let mut args = self.uncurry();
        if args.len() == 1 {
            if let Term::Const(_, p) = &self {
                if let (Name::Named(name), _) = &**p {
                    if name.as_str() == "forall" {
                        let f = args.pop().unwrap();
                        if let Term::Abs(_, ctx) = f {
                            return Some(*ctx);
                        }
                    }
                }
            }
        }
        None
    }

    #[doc(hidden)]
    pub fn mk_imp(&mut self, p: Term) {
        assert!(self.is_prop());
        assert!(p.is_prop());
        let mut t = Type::mk_prop();
        t.curry(vec![Type::mk_prop(), Type::mk_prop()]);
        let mut imp = Term::Const(
            t,
            Box::new((Name::Named(Box::new("imp".to_owned())), vec![])),
        );
        imp.mk_app(p);
        imp.mk_app(mem::take(self));
        *self = imp;
    }

    pub fn as_imp(mut self) -> Option<(Term, Term)> {
        let mut args = self.uncurry();
        if args.len() == 2 {
            if let Term::Const(_, p) = &self {
                if let (Name::Named(name), _) = &**p {
                    if name.as_str() == "imp" {
                        let q = args.pop().unwrap();
                        let p = args.pop().unwrap();
                        return Some((p, q));
                    }
                }
            }
        }
        None
    }
}
