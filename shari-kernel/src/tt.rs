//! [Type] and [Term] may be ill-formed.

use crate::env::{get_kind, get_type};

use anyhow::bail;
use once_cell::sync::Lazy;
use regex::Regex;
use std::collections::HashMap;
use std::fmt::Display;
use std::mem;
use std::sync::atomic::AtomicUsize;
use std::sync::{Arc, Mutex, RwLock};
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Name(usize);

static NAME_COUNTER: AtomicUsize = AtomicUsize::new(0);
static NAME_TABLE: Lazy<RwLock<HashMap<String, Name>>> = Lazy::new(Default::default);
static NAME_REV_TABLE: Lazy<Mutex<HashMap<Name, String>>> = Lazy::new(Default::default);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            NAME_REV_TABLE
                .lock()
                .unwrap()
                .get(self)
                .unwrap_or(&self.0.to_string())
        )
    }
}

#[derive(Error, Debug, Clone)]
#[error("invalid name")]
pub struct InvalidNameError;

impl TryFrom<&str> for Name {
    type Error = InvalidNameError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Name::intern(value)
    }
}

impl Name {
    pub fn fresh() -> Self {
        let id = NAME_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Name(id)
    }

    /// Panics if the name `value` has not been internalized before.
    pub fn get_unchecked(value: &str) -> Name {
        *NAME_TABLE.read().unwrap().get(value).unwrap()
    }

    pub fn intern(value: &str) -> Result<Name, InvalidNameError> {
        static RE: Lazy<Regex> = Lazy::new(|| {
            regex::Regex::new(r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*(\.[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*)*").unwrap()
        });
        if !RE.is_match(value) {
            return Err(InvalidNameError);
        }
        let mut name_table = NAME_TABLE.write().unwrap();
        if let Some(&name) = name_table.get(value) {
            return Ok(name);
        }
        let name = Name::fresh();
        name_table.insert(value.to_owned(), name);
        drop(name_table);
        // This can be put here outside the critical section of NAME_TABLE
        // because no one but this function knows of the value of `name`.
        NAME_REV_TABLE
            .lock()
            .unwrap()
            .insert(name, value.to_owned());
        Ok(name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Kind(pub usize);

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut arity = self.0;
        while arity > 0 {
            write!(f, "Type → ")?;
            arity -= 1;
        }
        write!(f, "Type")
    }
}

impl Kind {
    pub const fn base() -> Self {
        Kind(0)
    }

    pub fn is_base(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Type {
    Const(Name),
    Arrow(Arc<TypeArrow>),
    App(Arc<TypeApp>),
    Local(Name),
    Mvar(Name),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeArrow {
    pub dom: Type,
    pub cod: Type,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeApp {
    pub fun: Type,
    pub arg: Type,
}

impl Default for Type {
    fn default() -> Self {
        Type::Mvar(Default::default())
    }
}

pub fn mk_type_arrow(dom: Type, mut cod: Type) -> Type {
    cod.discharge_rev([dom]);
    cod
}

pub fn mk_fresh_type_mvar() -> Type {
    Type::Mvar(Name::fresh())
}

pub fn mk_type_local(name: Name) -> Type {
    Type::Local(name)
}

pub fn mk_type_const(name: Name) -> Type {
    Type::Const(name)
}

/// See [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    /// t.discharge_rev([t1, t2]);
    /// assert_eq!(t, "t2 → t1 → t");
    fn discharge_rev(&mut self, cs: impl IntoIterator<Item = Type>) {
        for c in cs {
            *self = Type::Arrow(Arc::new(TypeArrow {
                dom: c,
                cod: mem::take(self),
            }));
        }
    }

    /// t.discharge([t1, t2]);
    /// assert_eq!(t, "t1 → t2 → t");
    pub fn discharge(&mut self, cs: impl IntoIterator<Item = Type>) {
        let mut iter = cs.into_iter();
        if let Some(item) = iter.next() {
            self.discharge(iter);
            *self = Type::Arrow(Arc::new(TypeArrow {
                dom: item,
                cod: mem::take(self),
            }));
        }
    }

    pub fn apply(&mut self, args: impl IntoIterator<Item = Type>) {
        for arg in args {
            *self = Type::App(Arc::new(TypeApp {
                fun: mem::take(self),
                arg,
            }));
        }
    }

    /// Simultaneously substitute `t₁ ⋯ tₙ` for locals with names `x₁ ⋯ xₙ`.
    pub fn subst(&mut self, subst: &[(Name, &Type)]) {
        match self {
            Self::Const(_) => {}
            Self::Local(x) => {
                if let Some((_, t)) = subst.iter().copied().find(|(y, _)| y == x) {
                    *self = t.clone();
                }
            }
            Self::Mvar(_) => {}
            Self::Arrow(inner) => {
                let inner = Arc::make_mut(inner);
                inner.dom.subst(subst);
                inner.cod.subst(subst);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.subst(subst);
                inner.arg.subst(subst);
            }
        }
    }

    /// Infer the kind of [self]. This method also checks whether arities are consistent.
    fn infer(&self) -> anyhow::Result<Kind> {
        match self {
            Type::Const(name) => {
                let Some(kind) = get_kind(*name) else {
                    bail!("constant type not found");
                };
                Ok(kind)
            }
            Type::Arrow(inner) => {
                inner.dom.check(&Kind::base())?;
                inner.cod.check(&Kind::base())?;
                Ok(Kind::base())
            }
            Type::App(inner) => {
                let fun_kind = inner.fun.infer()?;
                if fun_kind.0 == 0 {
                    bail!("too many type arguments");
                }
                inner.arg.check(&Kind::base())?;
                Ok(Kind(fun_kind.0 - 1))
            }
            Type::Local(_) => Ok(Kind::base()),
            // no higher-kinded polymorphism
            Type::Mvar(_) => Ok(Kind::base()),
        }
    }

    /// Check whether arities are consistent.
    pub fn check(&self, kind: &Kind) -> anyhow::Result<()> {
        let my_kind = self.infer()?;
        if &my_kind != kind {
            bail!("expected {kind}, but got {my_kind}");
        }
        Ok(())
    }

    pub fn is_generic(&self, locals: &[Name]) -> bool {
        match self {
            Type::Const(_) => true,
            Type::Arrow(inner) => inner.dom.is_generic(locals) && inner.cod.is_generic(locals),
            Type::App(inner) => inner.fun.is_generic(locals) && inner.arg.is_generic(locals),
            Type::Local(name) => locals.contains(name),
            // no higher-kinded polymorphism
            Type::Mvar(_) => false,
        }
    }

    /// Returns [true] if [self] contains no meta variables.
    pub fn is_ground(&self) -> bool {
        match self {
            Type::Const(_) => true,
            Type::Arrow(inner) => inner.dom.is_ground() && inner.cod.is_ground(),
            Type::App(inner) => inner.fun.is_ground() && inner.arg.is_ground(),
            Type::Local(_) => true,
            Type::Mvar(_) => false,
        }
    }
}

/// Locally nameless representation. See [Charguéraud, 2012].
///
/// Variables are Church-style. A variable is given by a pair (x : τ) of a name x and a type τ.
/// Given τ₁ != τ₂, two variables (x : τ₁) and (x : τ₂) may occur in a single term and they have
/// to be treated as different variables. This greatly simplifies the treatment of typing contexts.
#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Term {
    Var(usize),
    Abs(Arc<TermAbs>),
    App(Arc<TermApp>),
    Local(Arc<TermLocal>),
    Const(Arc<TermConst>),
}

#[derive(Clone, Debug, Eq, Default, Ord, PartialOrd)]
pub struct TermAbs {
    pub binder_type: Type,
    // for pretty-printing
    pub binder_name: Name,
    pub body: Term,
}

impl PartialEq for TermAbs {
    /// Compares only [binder_type] and [body].
    fn eq(&self, other: &Self) -> bool {
        self.binder_type == other.binder_type && self.body == other.body
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct TermApp {
    pub fun: Term,
    pub arg: Term,
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct TermLocal {
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Ord, PartialOrd)]
pub struct TermConst {
    pub name: Name,
    pub ty_args: Vec<Type>,
}

impl From<TermLocal> for Term {
    fn from(value: TermLocal) -> Self {
        Term::Local(Arc::new(value))
    }
}

impl From<TermConst> for Term {
    fn from(value: TermConst) -> Self {
        Term::Const(Arc::new(value))
    }
}

impl Default for Term {
    fn default() -> Self {
        Term::Var(usize::MAX)
    }
}

pub fn mk_abs(binder_name: Name, binder_type: Type, body: Term) -> Term {
    Term::Abs(Arc::new(TermAbs {
        binder_type,
        binder_name,
        body,
    }))
}

pub fn mk_app(fun: Term, arg: Term) -> Term {
    Term::App(Arc::new(TermApp { fun, arg }))
}

pub fn mk_const(name: Name, ty_args: Vec<Type>) -> Term {
    Term::Const(Arc::new(TermConst { name, ty_args }))
}

pub fn mk_local(name: Name, ty: Type) -> Term {
    Term::Local(Arc::new(TermLocal { name, ty }))
}

impl Term {
    /// self.open(x) == [x/0]self
    pub fn open(&mut self, x: &Term) {
        self.open_at(x, 0)
    }

    fn open_at(&mut self, x: &Term, level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(i) => {
                if *i == level {
                    *self = x.clone();
                }
            }
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.open_at(x, level + 1);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.open_at(x, level);
                inner.arg.open_at(x, level);
            }
            Self::Const(_) => {}
        }
    }

    /// self.close(x) == [0/x]self
    pub fn close(&mut self, name: Name, ty: &Type) {
        assert!(self.is_lclosed());
        self.close_at(name, ty, 0)
    }

    fn close_at(&mut self, name: Name, ty: &Type, level: usize) {
        match self {
            Self::Local(inner) => {
                if inner.name == name && &inner.ty == ty {
                    *self = Self::Var(level);
                }
            }
            Self::Var(_) => {}
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.close_at(name, ty, level + 1);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.close_at(name, ty, level);
                inner.arg.close_at(name, ty, level);
            }
            Self::Const(_) => {}
        }
    }

    // fn open_shift(&mut self, x: &Term) {
    //     self.open_shift_at(x, 0)
    // }

    // fn open_shift_at(&mut self, x: &Term, shift: usize) {
    //     match self {
    //         Self::Local(_) => {}
    //         Self::Var(i) => {
    //             if *i == shift {
    //                 *self = x.clone();
    //                 self.shift(shift);
    //             }
    //         }
    //         Self::Abs(inner) => {
    //             Arc::make_mut(inner).body.open_shift_at(x, shift + 1);
    //         }
    //         Self::App(inner) => {
    //             let inner = Arc::make_mut(inner);
    //             inner.fun.open_shift_at(x, shift);
    //             inner.arg.open_shift_at(x, shift);
    //         }
    //         Self::Const(_) => {}
    //     }
    // }

    // fn shift(&mut self, shift: usize) {
    //     self.shift_at(0, shift)
    // }

    // fn shift_at(&mut self, level: usize, shift: usize) {
    //     match self {
    //         Self::Local(_) => {}
    //         Self::Var(x) => {
    //             if *x >= level {
    //                 *x += shift
    //             }
    //         }
    //         Self::Abs(inner) => {
    //             Arc::make_mut(inner).body.shift_at(level + 1, shift);
    //         }
    //         Self::App(inner) => {
    //             let inner = Arc::make_mut(inner);
    //             inner.fun.shift_at(level, shift);
    //             inner.arg.shift_at(level, shift);
    //         }
    //         Self::Const(_) => {}
    //     }
    // }

    pub fn unshift(&mut self) {
        self.unshift_at(0)
    }

    fn unshift_at(&mut self, level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(x) => {
                if *x >= level && *x >= 1 {
                    *x -= 1;
                }
            }
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.unshift_at(level + 1);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.unshift_at(level);
                inner.arg.unshift_at(level);
            }
            Self::Const(_) => {}
        }
    }

    /// x # self <==> x ∉ FV(self)
    pub fn is_fresh(&self, name: Name, ty: &Type) -> bool {
        match self {
            Self::Local(inner) => inner.name != name || inner.ty != *ty,
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_fresh(name, ty),
            Self::App(inner) => inner.fun.is_fresh(name, ty) && inner.arg.is_fresh(name, ty),
            Self::Const(_) => true,
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Local(_) => false,
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_closed(),
            Self::App(inner) => inner.fun.is_closed() && inner.arg.is_closed(),
            Self::Const(_) => true,
        }
    }

    fn is_lclosed(&self) -> bool {
        self.is_lclosed_at(0)
    }

    fn is_lclosed_at(&self, level: usize) -> bool {
        match self {
            Self::Local(_) => true,
            Self::Var(i) => *i < level,
            Self::Abs(inner) => inner.body.is_lclosed_at(level + 1),
            Self::App(inner) => inner.fun.is_lclosed_at(level) && inner.arg.is_lclosed_at(level),
            Self::Const(_) => true,
        }
    }

    pub fn is_body(&self) -> bool {
        self.is_lclosed_at(1)
    }

    pub(crate) fn has_var(&self, i: usize) -> bool {
        match self {
            &Term::Var(level) => i == level,
            Term::Abs(inner) => inner.body.has_var(i + 1),
            Term::App(inner) => inner.fun.has_var(i) || inner.arg.has_var(i),
            Term::Local(_) => false,
            Term::Const(_) => false,
        }
    }

    pub fn binders(&self) -> impl Iterator<Item = &Type> {
        struct I<'a> {
            m: &'a Term,
        }
        impl<'a> Iterator for I<'a> {
            type Item = &'a Type;

            fn next(&mut self) -> Option<Self::Item> {
                if let Term::Abs(inner) = self.m {
                    self.m = &inner.body;
                    Some(&inner.binder_type)
                } else {
                    None
                }
            }
        }
        I { m: self }
    }

    /// may return locally open terms
    fn matrix(&self) -> &Term {
        let mut m = self;
        while let Term::Abs(inner) = m {
            m = &inner.body;
        }
        m
    }

    /// may return locally open terms
    pub fn head(&self) -> &Term {
        let mut m = self.matrix();
        while let Self::App(inner) = m {
            m = &inner.fun;
        }
        m
    }

    /// may return locally open terms
    pub fn args(&self) -> Vec<&Term> {
        let mut m = self.matrix();
        let mut args = vec![];
        while let Self::App(inner) = m {
            m = &inner.fun;
            args.push(&inner.arg);
        }
        args.reverse();
        args
    }

    /// m.apply([l₁ ⋯ lₙ])
    /// assert(self = m l₁ ⋯ lₙ)
    pub fn apply(&mut self, args: impl IntoIterator<Item = Term>) {
        let mut m = mem::take(self);
        for arg in args {
            m = mk_app(m, arg);
        }
        *self = m;
    }

    /// m.apply([l₁ ⋯ lₙ])
    /// assert(self = m lₙ ⋯ l₁)
    pub fn apply_rev(&mut self, mut args: Vec<Term>) {
        let mut m = mem::take(self);
        while let Some(arg) = args.pop() {
            m = mk_app(m, arg);
        }
        *self = m;
    }

    /// m = n l*
    /// m.unapply() // => l*
    /// assert(m = n)
    pub fn unapply(&mut self) -> Vec<Term> {
        let mut args = self.unapply_rev();
        args.reverse();
        args
    }

    /// m = n l₁ ⋯ lₙ
    /// m.unapply() // => [lₙ ⋯ l₁]
    /// assert(m = n)
    pub fn unapply_rev(&mut self) -> Vec<Term> {
        let mut args = vec![];
        let mut m = &mut *self;
        while let Self::App(inner) = m {
            let inner = Arc::make_mut(inner);
            args.push(mem::take(&mut inner.arg));
            m = &mut inner.fun;
        }
        *self = mem::take(m);
        args
    }

    // // λ x₁ ⋯ xₙ, m ↦ [xₙ, ⋯ , x₁]
    // fn undischarge(&mut self) -> Vec<(Name, Type)> {
    //     let mut xs = vec![];
    //     let mut m = &mut *self;
    //     while let Term::Abs(inner) = m {
    //         let TermAbs {
    //             binder_type,
    //             binder_name,
    //             body: n,
    //         } = Arc::make_mut(inner);
    //         xs.push((mem::take(binder_name), mem::take(binder_type)));
    //         m = n;
    //     }
    //     *self = mem::take(m);
    //     xs.reverse();
    //     xs
    // }

    // // assert_eq!(self, "m");
    // // self.discharge([x1, x2]);
    // // assert_eq!(self, "λ x2 x1, m");
    // fn discharge(&mut self, xs: impl IntoIterator<Item = (Name, Type)>) {
    //     let mut m = mem::take(self);
    //     for (name, ty) in xs {
    //         m = mk_abs(name, ty, m);
    //     }
    //     *self = m;
    // }

    pub fn discharge_local(&mut self, name: Name, ty: Type, nickname: Name) {
        self.close(name, &ty);
        let m = mem::take(self);
        *self = mk_abs(nickname, ty, m);
    }

    /// Unification-based type inference.
    /// Errors if
    /// - types mismatch,
    /// - uninstantiated meta type variables remain,
    /// - self is not locally closed,
    /// - an unknown constant is found, or
    /// - kind checking failed.
    pub fn check(&mut self, target: &mut Type) -> anyhow::Result<()> {
        target.check(&Kind::base())?;
        let mut eq_set = EqSet::default();
        let mut var_stack = vec![];
        self.check_help(target, &mut var_stack, &mut eq_set)?;
        assert!(var_stack.is_empty());
        let unifier = eq_set.solve()?;
        unifier.apply_term(self)?;
        unifier.apply_type(target)?;
        Ok(())
    }

    fn check_help<'a>(
        &'a self,
        target: &Type,
        var_stack: &mut Vec<&'a Type>,
        eq_set: &mut EqSet,
    ) -> anyhow::Result<()> {
        match self {
            Term::Local(inner) => {
                inner.ty.check(&Kind::base())?;
                eq_set.unify(inner.ty.clone(), target.clone());
            }
            &Term::Var(i) => {
                if i >= var_stack.len() {
                    bail!("term not locally closed");
                }
                eq_set.unify(var_stack[var_stack.len() - i - 1].clone(), target.clone());
            }
            Term::Abs(inner) => {
                inner.binder_type.check(&Kind::base())?;
                var_stack.push(&inner.binder_type);
                let body_ty = mk_fresh_type_mvar();
                inner.body.check_help(&body_ty, var_stack, eq_set)?;
                var_stack.pop();
                eq_set.unify(
                    mk_type_arrow(inner.binder_type.clone(), body_ty),
                    target.clone(),
                );
            }
            Term::App(inner) => {
                let fun_ty = mk_fresh_type_mvar();
                inner.fun.check_help(&fun_ty, var_stack, eq_set)?;
                let arg_ty = mk_fresh_type_mvar();
                inner.arg.check_help(&arg_ty, var_stack, eq_set)?;
                eq_set.unify(fun_ty, mk_type_arrow(arg_ty, target.clone()));
            }
            Term::Const(inner) => {
                let Some((tv, mut ty)) = get_type(inner.name) else {
                    bail!("constant not found");
                };
                if tv.len() != inner.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                for t in &inner.ty_args {
                    t.check(&Kind::base())?;
                }
                ty.subst(&std::iter::zip(tv.iter().copied(), &inner.ty_args).collect::<Vec<_>>());
                eq_set.unify(ty, target.clone());
            }
        }
        Ok(())
    }

    pub fn infer(&mut self) -> anyhow::Result<Type> {
        let mut target = mk_fresh_type_mvar();
        self.check(&mut target)?;
        Ok(target)
    }

    pub fn is_generic(&self, locals: &[Name]) -> bool {
        match self {
            Term::Var(_) => true,
            Term::Abs(inner) => {
                inner.binder_type.is_generic(locals) && inner.body.is_generic(locals)
            }
            Term::App(inner) => inner.fun.is_generic(locals) && inner.arg.is_generic(locals),
            Term::Local(inner) => inner.ty.is_generic(locals),
            Term::Const(inner) => inner.ty_args.iter().all(|t| t.is_generic(locals)),
        }
    }

    pub fn instantiate(&mut self, subst: &[(Name, &Type)]) {
        match self {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.binder_type.subst(subst);
                inner.body.instantiate(subst);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.instantiate(subst);
                inner.arg.instantiate(subst);
            }
            Term::Local(inner) => Arc::make_mut(inner).ty.subst(subst),
            Term::Const(inner) => {
                for s in &mut Arc::make_mut(inner).ty_args {
                    s.subst(subst);
                }
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
struct EqSet {
    equations: Vec<(Type, Type)>,
    parents: HashMap<Name, Type>,
}

impl EqSet {
    fn unify(&mut self, t1: Type, t2: Type) {
        self.equations.push((t1, t2));
    }

    fn find(&mut self, ty: Type) -> Type {
        let Type::Mvar(name) = ty else {
            return ty;
        };
        let Some(ty) = self.parents.get(&name).cloned() else {
            return ty;
        };
        // During calling `find` parents[name] will NOT be updated
        // because a unification solution is not cyclic.
        let ty = self.find(ty);
        self.parents.insert(name, ty.clone());
        ty
    }

    fn solve(mut self) -> anyhow::Result<Unifier> {
        while let Some((t1, t2)) = self.equations.pop() {
            let t1 = self.find(t1);
            let t2 = self.find(t2);
            if t1 == t2 {
                continue;
            }
            match (t1, t2) {
                (Type::Arrow(inner1), Type::Arrow(inner2)) => {
                    let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                    let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                    self.unify(inner1.dom, inner2.dom);
                    self.unify(inner1.cod, inner2.cod);
                }
                (Type::App(inner1), Type::App(inner2)) => {
                    // Since we have no higher-kinded polymorphism, mvars will only be typed as `Type`,
                    // it is illegal to match the following two types:
                    //  ?M₁ t =?= ?M₂ t₁ t₂
                    // But such a case is checked and ruled out in the kind checking phase that runs before
                    // this unificaiton phase.
                    let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                    let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                    self.unify(inner1.fun, inner2.fun);
                    self.unify(inner1.arg, inner2.arg);
                }
                (Type::Mvar(name), t) | (t, Type::Mvar(name)) => {
                    self.parents.insert(name, t);
                }
                (_, _) => {
                    bail!("type mismatch");
                }
            }
        }
        Ok(Unifier(self.parents))
    }
}
struct Unifier(HashMap<Name, Type>);

impl Unifier {
    fn apply_type(&self, t: &mut Type) -> anyhow::Result<()> {
        match t {
            Type::Const(_) => {}
            Type::Arrow(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_type(&mut inner.dom)?;
                self.apply_type(&mut inner.cod)?;
            }
            Type::App(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_type(&mut inner.fun)?;
                self.apply_type(&mut inner.arg)?;
            }
            Type::Local(_) => {}
            Type::Mvar(name) => {
                let Some(ty) = self.0.get(name) else {
                    bail!("uninstantiated meta type variable");
                };
                *t = ty.clone();
                self.apply_type(t)?;
            }
        }
        Ok(())
    }

    fn apply_term(&self, m: &mut Term) -> anyhow::Result<()> {
        match m {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_type(&mut inner.binder_type)?;
                self.apply_term(&mut inner.body)?;
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_term(&mut inner.fun)?;
                self.apply_term(&mut inner.arg)?;
            }
            Term::Local(inner) => {
                let inner = Arc::make_mut(inner);
                self.apply_type(&mut inner.ty)?;
            }
            Term::Const(inner) => {
                let inner = Arc::make_mut(inner);
                for ty_arg in &mut inner.ty_args {
                    self.apply_type(ty_arg)?;
                }
            }
        }
        Ok(())
    }
}
