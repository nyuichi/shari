use crate::logic::{Spec, Theorem};
use crate::term::{Context, Name, Term, Type};
use std::collections::{HashMap, HashSet};
use std::mem;

#[derive(Clone, Debug)]
pub struct Sequent {
    spec: Spec,
    locals: HashMap<Name, Type>,
    assump: HashSet<Term>,
    target: Term,
}

impl std::fmt::Display for Sequent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

pub struct TacticState {
    goals: Vec<Sequent>,
    ops: Vec<Op>,
}

enum Op {
    Push {
        h: Theorem,
    },
    Assume {
        spec: Spec,
        locals: HashMap<Name, Type>,
        target: Term,
    },
    EqIntro {
        spec: Spec,
        locals: HashMap<Name, Type>,
        assump: HashSet<Term>,
        m1: Term,
        m2: Term,
    },
    EqElim {
        ctx: Context,
    },
    ImpIntro {
        p: Term,
    },
    ImpElim,
    ForallIntro {
        name: Name,
    },
    ForallElim {
        m: Term,
    },
}

impl TacticState {
    pub fn new(spec: Spec, p: Term) -> Self {
        let main_goal = Sequent {
            spec,
            locals: Default::default(),
            assump: Default::default(),
            target: p,
        };
        Self {
            goals: vec![main_goal],
            ops: vec![],
        }
    }

    pub fn goal(&self) -> &Sequent {
        self.goals.last().unwrap()
    }

    pub fn assume(&mut self) {
        let seq = self.goals.pop().unwrap();
        self.ops.push(Op::Assume {
            spec: seq.spec,
            locals: seq.locals,
            target: seq.target,
        });
    }

    pub fn eq_intro(&mut self) {
        let mut seq = self.goals.pop().unwrap();
        let (m1, m2) = seq.target.as_eq().unwrap();
        self.ops.push(Op::EqIntro {
            spec: seq.spec,
            locals: seq.locals,
            assump: seq.assump,
            m1: mem::take(m1),
            m2: mem::take(m2),
        });
    }

    pub fn imp_intro(&mut self) {
        let mut seq = self.goals.pop().unwrap();
        let (p1, p2) = seq.target.as_imp().unwrap();
        let (p1, p2) = (mem::take(p1), mem::take(p2));
        if !seq.assump.insert(p1.clone()) {
            todo!();
        }
        seq.target = p2;
        self.goals.push(seq);
        self.ops.push(Op::ImpIntro { p: p1 });
    }

    pub fn imp_elim(&mut self, p: Term) {
        let mut seq = self.goals.pop().unwrap();
        seq.target.mk_imp(p.clone());
        let mut seq2 = seq.clone();
        seq2.target = p;
        self.goals.push(seq2);
        self.goals.push(seq);
        self.ops.push(Op::ImpElim);
    }

    pub fn forall_intro(&mut self, name: Name) {
        let mut seq = self.goals.pop().unwrap();
        for p in &seq.assump {
            assert!(p.is_fresh(&name));
        }
        let Context(t, mut m) = mem::take(seq.target.as_forall().unwrap());
        m.open(&name);
        seq.target = m;
        if let Some(_) = seq.locals.insert(name.clone(), t) {
            todo!();
        }
        self.goals.push(seq);
        self.ops.push(Op::ForallIntro { name });
    }

    pub fn qed(mut self) -> Theorem {
        assert!(self.goals.is_empty());
        let mut stack = vec![];
        while let Some(op) = self.ops.pop() {
            match op {
                Op::Push { h } => {
                    stack.push(h);
                }
                Op::Assume {
                    spec,
                    locals,
                    target,
                } => {
                    stack.push(Theorem::assume(spec, locals, target));
                }
                Op::EqIntro {
                    spec,
                    locals,
                    assump,
                    m1,
                    m2,
                } => {
                    stack.push(Theorem::eq_intro(spec, locals, assump, m1, m2));
                }
                Op::EqElim { ctx } => {
                    let mut h1 = stack.pop().unwrap();
                    let h2 = stack.pop().unwrap();
                    h1.eq_elim(h2, ctx);
                    stack.push(h1);
                }
                Op::ImpIntro { p } => {
                    let mut h = stack.pop().unwrap();
                    h.imp_intro(&p);
                    stack.push(h);
                }
                Op::ImpElim => {
                    let mut h1 = stack.pop().unwrap();
                    let h2 = stack.pop().unwrap();
                    h1.imp_elim(h2);
                    stack.push(h1);
                }
                Op::ForallIntro { name } => {
                    let mut h = stack.pop().unwrap();
                    h.forall_intro(&name);
                    stack.push(h);
                }
                Op::ForallElim { m } => {
                    let mut h = stack.pop().unwrap();
                    h.forall_elim(&m);
                    stack.push(h);
                }
            }
        }
        assert_eq!(stack.len(), 1);
        stack.pop().unwrap()
    }
}
