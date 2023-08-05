//! [Type] and [Term] may be ill-formed.

use anyhow::bail;
use core::ops::Range;
use once_cell::sync::Lazy;
use regex::Regex;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Display;
use std::mem;
use std::str::FromStr;
use std::sync::{Arc, RwLock};
use thiserror::Error;

// TODO internalization
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Name {
    inner: String,
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

#[derive(Error, Debug, Clone)]
#[error("invalid name")]
pub struct InvalidNameError;

impl TryFrom<String> for Name {
    type Error = InvalidNameError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        static RE: Lazy<Regex> = Lazy::new(|| {
            regex::Regex::new(r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*").unwrap()
        });
        if RE.is_match(&value) {
            Ok(Name { inner: value })
        } else {
            Err(InvalidNameError)
        }
    }
}

impl TryFrom<&str> for Name {
    type Error = InvalidNameError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        value.to_owned().try_into()
    }
}

impl Borrow<str> for Name {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Name {
    // TODO: fixme
    pub fn fresh() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static COUNTER: Lazy<AtomicUsize> = Lazy::new(Default::default);
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        Name {
            inner: format!("{id}"),
        }
    }

    pub fn as_str(&self) -> &str {
        &self.inner
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

impl FromStr for Type {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut lex = Lex::new(s);
        let mut parser = Parser::new(&mut lex);
        let ty = parser.ty()?;
        parser.eof()?;
        Ok(ty)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Env::get().notations.pp.fmt_type(self, f)
    }
}

fn mk_arrow(dom: Type, cod: Type) -> Type {
    Type::Arrow(Arc::new(TypeArrow { dom, cod }))
}

fn mk_tyapp(fun: Type, arg: Type) -> Type {
    Type::App(Arc::new(TypeApp { fun, arg }))
}

/// See [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    pub fn prop() -> Type {
        Type::Const(Name {
            inner: "Prop".to_owned(),
        })
    }

    /// If [self] is `t₁ → … → tₙ → t`, [args] returns `[t₁, …, tₙ]`.
    pub fn args(&self) -> Vec<&Type> {
        let mut ts = vec![];
        let mut t = self;
        while let Self::Arrow(inner) = t {
            ts.push(&inner.dom);
            t = &inner.cod;
        }
        ts
    }

    /// Substitute [t] for locals with name [name].
    fn subst(&mut self, name: &str, t: &Type) {
        match self {
            Self::Const(_) => {}
            Self::Local(x) => {
                if x.as_str() == name {
                    *self = t.clone();
                }
            }
            Self::Mvar(_) => {}
            Self::Arrow(inner) => {
                let inner = Arc::make_mut(inner);
                inner.dom.subst(name, t);
                inner.cod.subst(name, t);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.subst(name, t);
                inner.arg.subst(name, t);
            }
        }
    }

    /// Infer the kind of [self]. This method also checks whether arities are consistent.
    pub fn infer_kind(&self) -> anyhow::Result<Kind> {
        match self {
            Type::Const(name) => {
                let Some(kind) = get_kind(name.as_str()) else {
                    bail!("constant type not found");
                };
                Ok(kind)
            }
            Type::Arrow(inner) => {
                if !inner.dom.infer_kind()?.is_base() {
                    bail!("not a type");
                }
                if !inner.cod.infer_kind()?.is_base() {
                    bail!("not a type");
                }
                Ok(Kind::base())
            }
            Type::App(inner) => {
                let fun_kind = inner.fun.infer_kind()?;
                if fun_kind.is_base() {
                    bail!("not a type operator");
                }
                if !inner.arg.infer_kind()?.is_base() {
                    bail!("not a type");
                }
                Ok(Kind(fun_kind.0 - 1))
            }
            Type::Local(_) => Ok(Kind::base()),
            // no higher-kinded polymorphism
            Type::Mvar(_) => Ok(Kind::base()),
        }
    }

    /// Check whether arities are consistent.
    pub fn check_kind(&self, kind: &Kind) -> anyhow::Result<()> {
        let my_kind = self.infer_kind()?;
        if &my_kind != kind {
            bail!("expected {kind}, but got {my_kind}");
        }
        Ok(())
    }

    fn infer_kind_under(&self, locals: &[Name]) -> anyhow::Result<Kind> {
        match self {
            Type::Const(name) => {
                let Some(kind) = get_kind(name.as_str()) else {
                    bail!("constant type not found");
                };
                Ok(kind)
            }
            Type::Arrow(inner) => {
                if !inner.dom.infer_kind_under(locals)?.is_base() {
                    bail!("not a type");
                }
                if !inner.cod.infer_kind_under(locals)?.is_base() {
                    bail!("not a type");
                }
                Ok(Kind::base())
            }
            Type::App(inner) => {
                let fun_kind = inner.fun.infer_kind_under(locals)?;
                if fun_kind.is_base() {
                    bail!("not a type operator");
                }
                if !inner.arg.infer_kind_under(locals)?.is_base() {
                    bail!("not a type");
                }
                Ok(Kind(fun_kind.0 - 1))
            }
            Type::Local(name) => {
                if !locals.contains(name) {
                    bail!("unknown local");
                }
                Ok(Kind::base())
            }
            // no higher-kinded polymorphism
            Type::Mvar(_) => Ok(Kind::base()),
        }
    }

    /// Check whether arities are consistent.
    fn check_kind_under(&self, locals: &[Name], kind: &Kind) -> anyhow::Result<()> {
        let my_kind = self.infer_kind_under(locals)?;
        if &my_kind != kind {
            bail!("expected {kind}, but got {my_kind}");
        }
        Ok(())
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

    /// Instantiate meta variables with name [name] with [t].
    fn instantiate(&mut self, name: &str, t: &Type) {
        match self {
            Self::Const(_) | Self::Local(_) => {}
            Self::Mvar(x) => {
                if x.as_str() == name {
                    *self = t.clone();
                }
            }
            Self::Arrow(inner) => {
                let inner = Arc::make_mut(inner);
                inner.dom.instantiate(name, t);
                inner.cod.instantiate(name, t);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.instantiate(name, t);
                inner.arg.instantiate(name, t);
            }
        }
    }
}

#[test]
fn test_type_args() {
    let t: Type = "a → b → c".parse().unwrap();
    assert_eq!(t.args(), [&"a".parse().unwrap(), &"b".parse().unwrap()]);
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

impl Default for Term {
    fn default() -> Self {
        Term::Var(usize::MAX)
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Env::get().notations.pp.fmt_term(self, f)
    }
}

fn mk_abs(binder_name: Name, binder_type: Type, body: Term) -> Term {
    Term::Abs(Arc::new(TermAbs {
        binder_type,
        binder_name,
        body,
    }))
}

fn mk_app(fun: Term, arg: Term) -> Term {
    Term::App(Arc::new(TermApp { fun, arg }))
}

fn mk_const(name: Name, ty_args: Vec<Type>) -> Term {
    Term::Const(Arc::new(TermConst { name, ty_args }))
}

fn mk_local(name: Name, ty: Type) -> Term {
    Term::Local(Arc::new(TermLocal { name, ty }))
}

impl FromStr for Term {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut lex = Lex::new(s);
        let mut parser = Parser::new(&mut lex);
        let m = parser.term()?;
        parser.eof()?;
        Ok(m)
    }
}

impl Term {
    /// self.open(x) == [x/0]self
    pub fn open(&mut self, x: &Term) {
        assert!(self.is_body());
        self.open_at(x, 0)
    }

    pub fn open_at(&mut self, x: &Term, level: usize) {
        assert!(x.is_lclosed());
        self.open_at_help(x, level)
    }

    fn open_at_help(&mut self, x: &Term, level: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(i) => {
                if *i == level {
                    *self = x.clone();
                }
            }
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.open_at_help(x, level + 1);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.open_at_help(x, level);
                inner.arg.open_at_help(x, level);
            }
            Self::Const(_) => {}
        }
    }

    /// self.close(x) == [0/x]self
    pub fn close(&mut self, name: &str, ty: &Type) {
        assert!(self.is_lclosed());
        self.close_at(name, ty, 0)
    }

    fn close_at(&mut self, name: &str, ty: &Type, level: usize) {
        match self {
            Self::Local(inner) => {
                if inner.name.as_str() == name && &inner.ty == ty {
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

    /// x # self <==> x ∉ FV(self)
    pub fn is_fresh(&self, name: &str, ty: &Type) -> bool {
        match self {
            Self::Local(inner) => inner.name.as_str() != name || inner.ty != *ty,
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

    pub fn is_lclosed(&self) -> bool {
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

    fn has_var(&self, i: usize) -> bool {
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
    pub fn matrix(&self) -> &Term {
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

    /// triple(λ (v:t)*, m l*) = (t*, m, l*)
    /// may return locally open terms
    pub fn triple(&self) -> (impl Iterator<Item = &Type>, &Term, Vec<&Term>) {
        let binders = self.binders();
        let mut m = self.matrix();
        let mut args = vec![];
        while let Self::App(inner) = m {
            m = &inner.fun;
            args.push(&inner.arg);
        }
        args.reverse();
        let head = m;
        (binders, head, args)
    }

    /// may return locally open terms
    pub fn args(&self) -> Vec<&Term> {
        self.triple().2
    }

    pub fn is_neutral(&self) -> bool {
        match self {
            Self::Abs(_) => false,
            Self::App(inner) => inner.fun.is_neutral() && inner.arg.is_normal(),
            Self::Var(_) | Self::Local(_) | Self::Const(_) => true,
        }
    }

    /// `true` if the term is in β-normal form.
    pub fn is_normal(&self) -> bool {
        if let Self::Abs(inner) = self {
            inner.body.is_normal()
        } else {
            self.is_neutral()
        }
    }

    /// m is in head normal form if m has no β-redex at its head position.
    pub fn is_hnf(&self) -> bool {
        match self.head() {
            Self::Local(_) | Self::Var(_) | Self::Const(_) => true,
            Self::Abs(_) => false,
            Self::App(_) => unreachable!(),
        }
    }

    /// does not check if a term inside an abstraction is in whnf
    pub fn is_whnf(&self) -> bool {
        match self {
            Self::Abs(_) => true,
            Self::Var(_) | Self::Local(_) | Self::Const(_) | Self::App(_) => self.is_hnf(),
        }
    }

    /// m = n l*
    /// m.unapply() // => l*
    /// assert(m = n)
    pub fn unapply(&mut self) -> Vec<Term> {
        let mut args = vec![];
        let mut m = &mut *self;
        while let Self::App(inner) = m {
            let inner = Arc::make_mut(inner);
            args.push(mem::take(&mut inner.arg));
            m = &mut inner.fun;
        }
        *self = mem::take(m);
        args.reverse();
        args
    }

    pub fn apply(&mut self, args: impl IntoIterator<Item = Term>) {
        let mut m = mem::take(self);
        for arg in args {
            m = mk_app(m, arg);
        }
        *self = m;
    }

    // TODO: return Undischarge<'_> to avoid unnecessary allocation
    pub fn undischarge(&mut self) -> Vec<(Name, Type)> {
        let mut xs = vec![];
        let mut m = &mut *self;
        while let Term::Abs(inner) = m {
            let TermAbs {
                binder_type,
                binder_name,
                body: n,
            } = Arc::make_mut(inner);
            xs.push((mem::take(binder_name), mem::take(binder_type)));
            m = n;
        }
        *self = mem::take(m);
        xs
    }

    pub fn discharge(&mut self, xs: Vec<(Name, Type)>) {
        let mut m = mem::take(self);
        for (name, ty) in xs.into_iter().rev() {
            m = mk_abs(name, ty, m);
        }
        *self = m;
    }

    pub fn discharge_local(&mut self, name: Name, ty: Type) {
        self.close(name.as_str(), &ty);
        let m = mem::take(self);
        *self = mk_abs(name, ty, m);
    }

    pub fn reduce(&mut self) {
        self.delta_reduce();
        self.beta_reduce();
    }

    /// Unfold all definitions
    fn delta_reduce(&mut self) {
        match self {
            Self::Var(_) | Self::Local(_) => {}
            Self::Const(inner) => {
                if let Some(DeclDef {
                    local_types,
                    mut target,
                    ty: _,
                }) = get_def(inner.name.as_str())
                {
                    for (local, ty_arg) in std::iter::zip(&local_types, &inner.ty_args) {
                        target.instantiate_local(local.as_str(), ty_arg);
                    }
                    *self = target;
                    self.delta_reduce();
                }
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.delta_reduce();
                inner.arg.delta_reduce();
            }
            Self::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.body.delta_reduce();
            }
        }
    }

    /// Applicative-order (leftmost-innermost) β-reduction
    pub fn beta_reduce(&mut self) {
        match self {
            Self::Var(_) => {
                panic!("term not locally closed");
            }
            Self::Local(_) => {}
            Self::Const(_) => {}
            Self::App(inner) => {
                let TermApp { fun: m1, arg: m2 } = Arc::make_mut(inner);
                m1.beta_reduce();
                m2.beta_reduce();
                if let Self::Abs(inner) = m1 {
                    let inner = Arc::make_mut(inner);
                    inner.body.open(m2);
                    *self = mem::take(&mut inner.body);
                    self.beta_reduce();
                }
            }
            Self::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                let x = Name::fresh();
                let local = mk_local(x, mem::take(&mut inner.binder_type));
                inner.body.open(&local);
                inner.body.beta_reduce();
                let Term::Local(mut local) = local else {
                    unreachable!();
                };
                let TermLocal { name, ty } = mem::take(Arc::make_mut(&mut local));
                inner.body.close(name.as_str(), &ty);
                inner.binder_type = ty;
            }
        }
    }

    /// Unification-based type inference.
    /// This also performs kind checking.
    pub fn infer(&mut self, target: &mut Type) -> anyhow::Result<()> {
        let mut subst = Subst::<Type>::default();
        let mut var_stack = vec![];
        let mut t = self.infer_help(&mut var_stack, &mut subst)?;
        assert!(var_stack.is_empty());
        target.check_kind(&Kind::base())?;
        subst.unify(target, &mut t)?;
        subst.apply_type(&mut t);
        subst.apply_term(self);
        subst.apply_type(target);
        Ok(())
    }

    /// TODO: chagne return type to Result<()>
    fn infer_help<'a>(
        &'a self,
        var_stack: &mut Vec<&'a Type>,
        subst: &mut Subst<Type>,
    ) -> anyhow::Result<Type> {
        match self {
            Term::Local(inner) => {
                inner.ty.check_kind(&Kind::base())?;
                Ok(inner.ty.clone())
            }
            &Term::Var(i) => {
                if i >= var_stack.len() {
                    bail!("term not locally closed");
                }
                Ok(var_stack[var_stack.len() - i - 1].clone())
            }
            Term::Abs(inner) => {
                inner.binder_type.check_kind(&Kind::base())?;
                var_stack.push(&inner.binder_type);
                let u = inner.body.infer_help(var_stack, subst)?;
                var_stack.pop();
                Ok(mk_arrow(inner.binder_type.clone(), u))
            }
            Term::App(inner) => {
                let mut t1 = inner.fun.infer_help(var_stack, subst)?;
                let t2 = inner.arg.infer_help(var_stack, subst)?;
                let mut t = mk_arrow(t2, Type::Mvar(Name::fresh()));
                subst.unify(&mut t1, &mut t)?;
                let Type::Arrow(mut p) = t else {
                    panic!("logic flaw");
                };
                Ok(mem::take(&mut Arc::make_mut(&mut p).cod))
            }
            Term::Const(inner) => {
                let Some((tv, mut ty)) = get_type(inner.name.as_str()) else {
                    bail!("constant not found");
                };
                if tv.len() != inner.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                let mut new_tv: Vec<_> = std::iter::repeat_with(|| Type::Mvar(Name::fresh()))
                    .take(tv.len())
                    .collect();
                for (old, new) in std::iter::zip(&tv, &new_tv) {
                    ty.subst(old.as_str(), new);
                }
                let mut ty_args = inner.ty_args.clone();
                for (t1, t2) in std::iter::zip(&mut ty_args, &mut new_tv) {
                    t1.check_kind(&Kind::base())?;
                    subst.unify(t1, t2)?;
                }
                Ok(ty)
            }
        }
    }

    /// Similar to infer, but performs kind checking under given context.
    fn infer_under(&mut self, kind_ctx: &[Name]) -> anyhow::Result<Type> {
        let mut subst = Subst::<Type>::default();
        let mut var_stack = vec![];
        let mut t = self.infer_under_help(kind_ctx, &mut var_stack, &mut subst)?;
        assert!(var_stack.is_empty());
        subst.apply_type(&mut t);
        subst.apply_term(self);
        Ok(t)
    }

    fn infer_under_help<'a>(
        &'a self,
        kind_ctx: &[Name],
        var_stack: &mut Vec<&'a Type>,
        subst: &mut Subst<Type>,
    ) -> anyhow::Result<Type> {
        match self {
            Term::Local(inner) => {
                inner.ty.check_kind_under(kind_ctx, &Kind::base())?;
                Ok(inner.ty.clone())
            }
            Term::Var(i) => {
                let i = *i;
                if i < var_stack.len() {
                    return Ok(var_stack[var_stack.len() - i - 1].clone());
                }
                bail!("term not locally closed");
            }
            Term::Abs(inner) => {
                inner
                    .binder_type
                    .check_kind_under(kind_ctx, &Kind::base())?;
                var_stack.push(&inner.binder_type);
                let u = inner.body.infer_under_help(kind_ctx, var_stack, subst)?;
                var_stack.pop();
                Ok(mk_arrow(inner.binder_type.clone(), u))
            }
            Term::App(inner) => {
                let mut t1 = inner.fun.infer_under_help(kind_ctx, var_stack, subst)?;
                let t2 = inner.arg.infer_under_help(kind_ctx, var_stack, subst)?;
                let mut t = mk_arrow(t2, Type::Mvar(Name::fresh()));
                subst.unify(&mut t1, &mut t)?;
                let Type::Arrow(mut p) = t else {
                    panic!("logic flaw");
                };
                Ok(mem::take(&mut Arc::make_mut(&mut p).cod))
            }
            Term::Const(inner) => {
                if let Some((tv, mut ty)) = get_type(inner.name.as_str()) {
                    if tv.len() != inner.ty_args.len() {
                        bail!("number of type variables mismatch");
                    }
                    let mut new_tv: Vec<_> = std::iter::repeat_with(|| Type::Mvar(Name::fresh()))
                        .take(tv.len())
                        .collect();
                    for (old, new) in std::iter::zip(&tv, &new_tv) {
                        ty.subst(old.as_str(), new);
                    }
                    let mut ty_args = inner.ty_args.clone();
                    for (t1, t2) in std::iter::zip(&mut ty_args, &mut new_tv) {
                        t1.check_kind_under(kind_ctx, &Kind::base())?;
                        subst.unify(t1, t2)?;
                    }
                    return Ok(ty);
                }
                bail!("constant not found");
            }
        }
    }

    // type-correct implies locally closed
    pub fn is_type_correct(&self) -> bool {
        self.synthesize().is_ok()
    }

    /// Bidirectional type checking (check).
    /// This also performs kind checking.
    pub fn check(&self, target: &Type) -> anyhow::Result<()> {
        target.check_kind(&Kind::base())?;
        let mut var_stack = vec![];
        self.check_help(target, &mut var_stack)?;
        assert!(var_stack.is_empty());
        Ok(())
    }

    fn check_help<'a>(
        &'a self,
        target: &Type,
        var_stack: &mut Vec<&'a Type>,
    ) -> anyhow::Result<()> {
        match self {
            &Term::Var(i) => {
                if i >= var_stack.len() {
                    bail!("term not locally closed");
                }
                if var_stack[var_stack.len() - i - 1] != target {
                    bail!(
                        "unmatched types: '{}' and '{}'",
                        var_stack[var_stack.len() - i - 1],
                        target
                    );
                }
                Ok(())
            }
            Term::Abs(inner) => {
                inner.binder_type.check_kind(&Kind::base())?;
                let Type::Arrow(arr_inner) = target else {
                    bail!("expected an arrow type, but got {target}");
                };
                if arr_inner.dom != inner.binder_type {
                    bail!(
                        "unmatched types: '{}' and '{}'",
                        arr_inner.dom,
                        inner.binder_type
                    );
                }
                var_stack.push(&inner.binder_type);
                inner.body.check_help(&arr_inner.cod, var_stack)?;
                var_stack.pop();
                Ok(())
            }
            Term::App(inner) => {
                let arg_ty = inner.arg.synthesize_help(var_stack)?;
                let arr_ty = mk_arrow(arg_ty, target.clone());
                inner.fun.check_help(&arr_ty, var_stack)
            }
            Term::Local(inner) => {
                inner.ty.check_kind(&Kind::base())?;
                if &inner.ty != target {
                    bail!("unmatched types: '{}' and '{}'", inner.ty, target);
                }
                Ok(())
            }
            Term::Const(inner) => {
                let Some((ty_vars, mut ty)) = get_type(inner.name.as_str()) else {
                    bail!("constant not found: {}", inner.name);
                };
                if ty_vars.len() != inner.ty_args.len() {
                    bail!("type argument mismatch");
                }
                for ty_arg in &inner.ty_args {
                    ty_arg.check_kind(&Kind::base())?;
                }
                for (ty_var, ty_arg) in std::iter::zip(&ty_vars, &inner.ty_args) {
                    ty.subst(ty_var.as_str(), ty_arg);
                }
                if &ty != target {
                    bail!("type mismatch");
                }
                Ok(())
            }
        }
    }

    /// Bidirectional type checking (synthesize).
    /// This also performs kind checking.
    pub fn synthesize(&self) -> anyhow::Result<Type> {
        let mut var_stack = vec![];
        let ty = self.synthesize_help(&mut var_stack)?;
        assert!(var_stack.is_empty());
        Ok(ty)
    }

    fn synthesize_help<'a>(&'a self, var_stack: &mut Vec<&'a Type>) -> anyhow::Result<Type> {
        match self {
            &Term::Var(i) => {
                if i >= var_stack.len() {
                    bail!("term not locally closed");
                }
                Ok(var_stack[var_stack.len() - i - 1].clone())
            }
            Term::Abs(inner) => {
                inner.binder_type.check_kind(&Kind::base())?;
                var_stack.push(&inner.binder_type);
                let cod_ty = inner.body.synthesize_help(var_stack)?;
                var_stack.pop();
                let dom_ty = inner.binder_type.clone();
                Ok(mk_arrow(dom_ty, cod_ty))
            }
            Term::App(inner) => {
                let fun_ty = inner.fun.synthesize_help(var_stack)?;
                let Type::Arrow(mut arr_inner) = fun_ty else {
                    bail!("expected an arrow, but got {fun_ty}");
                };
                inner.arg.check_help(&arr_inner.dom, var_stack)?;
                Ok(mem::take(&mut Arc::make_mut(&mut arr_inner).cod))
            }
            Term::Local(inner) => {
                inner.ty.check_kind(&Kind::base())?;
                Ok(inner.ty.clone())
            }
            Term::Const(inner) => {
                let Some((ty_vars, mut ty)) = get_type(inner.name.as_str()) else {
                    bail!("constant not found");
                };
                if ty_vars.len() != inner.ty_args.len() {
                    bail!("type argument mismatch");
                }
                for (ty_var, ty_arg) in std::iter::zip(&ty_vars, &inner.ty_args) {
                    ty_arg.check_kind(&Kind::base())?;
                    ty.subst(ty_var.as_str(), ty_arg);
                }
                Ok(ty)
            }
        }
    }

    fn synthesize_unchecked(&self) -> Type {
        let mut var_stack = vec![];
        let t = self.synthesize_unchecked_help(&mut var_stack);
        assert!(var_stack.is_empty());
        t
    }

    fn synthesize_unchecked_help<'a>(&'a self, var_stack: &mut Vec<&'a Type>) -> Type {
        match self {
            Term::Var(i) => var_stack[var_stack.len() - 1 - i].clone(),
            Term::Abs(inner) => {
                var_stack.push(&inner.binder_type);
                let cod_ty = inner.body.synthesize_unchecked_help(var_stack);
                var_stack.pop();
                let dom_ty = inner.binder_type.clone();
                mk_arrow(dom_ty, cod_ty)
            }
            Term::App(inner) => {
                let t = inner.fun.synthesize_unchecked_help(var_stack);
                let Type::Arrow(inner) = t else {
                    panic!("expected an arrow, but got {t}");
                };
                inner.cod.clone()
            }
            Term::Local(inner) => inner.ty.clone(),
            Term::Const(inner) => {
                let (ty_vars, mut ty) = get_type(inner.name.as_str()).unwrap();
                for (ty_var, t) in std::iter::zip(&ty_vars, &inner.ty_args) {
                    ty.subst(ty_var.as_str(), t);
                }
                ty
            }
        }
    }

    /// Check if the term is in η-long β-normal form.
    /// See Lectures on the Curry-Howard isomorphism, Chapter 4.
    /// https://math.stackexchange.com/q/3334730
    /// [m] must be locally closed and type-correct.
    pub fn is_canonical(&self) -> bool {
        assert!(self.is_type_correct());
        let mut var_stack = vec![];
        let r = self.is_canonical_help(&mut var_stack);
        assert!(var_stack.is_empty());
        r
    }

    fn is_canonical_help<'a>(&'a self, var_stack: &mut Vec<&'a Type>) -> bool {
        // TODO: avoid quadratic cost
        let t = self.synthesize_unchecked_help(var_stack);
        match t {
            Type::Arrow(_) => {
                if let Term::Abs(inner) = self {
                    var_stack.push(&inner.binder_type);
                    let r = inner.body.is_canonical_help(var_stack);
                    var_stack.pop();
                    r
                } else {
                    false
                }
            }
            Type::App(_) | Type::Const(_) | Type::Mvar(_) | Type::Local(_) => {
                let mut m = self;
                while let Term::App(inner) = self {
                    if !inner.arg.is_canonical_help(var_stack) {
                        return false;
                    }
                    m = &inner.fun;
                }
                match m {
                    Term::Var(_) | Term::Local(_) | Term::Const(_) => true,
                    Term::Abs(_) => false,
                    Term::App(_) => unreachable!(),
                }
            }
        }
    }

    /// [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_neutral(&mut self, var_stack: &mut Vec<Type>) {
        assert!(self.is_neutral());
        // [x M₁ ... Mₙ] := x [M₁] ... [Mₙ]
        let mut args = self.unapply();
        for arg in &mut args {
            arg.eta_expand_normal(var_stack);
        }
        self.apply(args);
        // TODO avoid quadratic cost
        let mut var_ref_stack = vec![];
        for ty_ref in &*var_stack {
            var_ref_stack.push(ty_ref);
        }
        let t = self.synthesize_unchecked_help(&mut var_ref_stack);
        assert_eq!(var_ref_stack.len(), var_stack.len());
        // [M] := λv₁ ⋯ vₙ. M v₁ ⋯ vₙ
        let args = t.args();
        self.apply((0..args.len()).rev().map(Term::Var));
        let vs: Vec<_> = args
            .into_iter()
            .cloned()
            .map(|t| (Name::fresh(), t))
            .collect();
        self.discharge(vs);
    }

    /// 1. [λx.M] := λx.[M]
    /// 2. [x M₁ ... Mₙ] := λv*. x [M₁] ... [Mₙ] v*
    fn eta_expand_normal(&mut self, var_stack: &mut Vec<Type>) {
        assert!(self.is_normal());
        let mut xs = self.undischarge();
        let num_xs = xs.len();
        for (_, t) in &mut xs {
            var_stack.push(mem::take(t));
        }
        self.eta_expand_neutral(var_stack);
        for ((_, binder_type), t) in
            std::iter::zip(&mut xs, var_stack.drain(var_stack.len() - num_xs..))
        {
            *binder_type = t;
        }
        self.discharge(xs);
    }

    /// [m] must be type-correct
    pub fn canonicalize(&mut self) {
        assert!(self.is_type_correct());
        self.reduce();
        let mut var_stack = vec![];
        self.eta_expand_normal(&mut var_stack);
        assert!(var_stack.is_empty())
    }

    /// [m1] and [m2] must be type-correct and type-equal under the same environment.
    pub fn equiv(&self, other: &Term) -> bool {
        let mut m1 = self.clone();
        let mut m2 = other.clone();
        m1.canonicalize();
        m2.canonicalize();
        m1 == m2
    }

    // Returns `true` if `self` contains no type meta variables.
    pub fn is_fully_instantiated(&self) -> bool {
        match self {
            Term::Var(_) => true,
            Term::Abs(inner) => inner.binder_type.is_ground() && inner.body.is_fully_instantiated(),
            Term::App(inner) => {
                inner.fun.is_fully_instantiated() && inner.arg.is_fully_instantiated()
            }
            Term::Local(inner) => inner.ty.is_ground(),
            Term::Const(inner) => inner.ty_args.iter().all(Type::is_ground),
        }
    }

    pub fn instantiate(&mut self, name: &str, t: &Type) {
        match self {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.binder_type.instantiate(name, t);
                inner.body.instantiate(name, t);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.instantiate(name, t);
                inner.arg.instantiate(name, t);
            }
            Term::Local(inner) => Arc::make_mut(inner).ty.instantiate(name, t),
            Term::Const(inner) => {
                for s in &mut Arc::make_mut(inner).ty_args {
                    s.instantiate(name, t);
                }
            }
        }
    }

    pub fn instantiate_local(&mut self, name: &str, t: &Type) {
        match self {
            Term::Var(_) => {}
            Term::Abs(inner) => {
                let inner = Arc::make_mut(inner);
                inner.binder_type.subst(name, t);
                inner.body.instantiate_local(name, t);
            }
            Term::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.instantiate_local(name, t);
                inner.arg.instantiate_local(name, t);
            }
            Term::Local(inner) => Arc::make_mut(inner).ty.subst(name, t),
            Term::Const(inner) => {
                for s in &mut Arc::make_mut(inner).ty_args {
                    s.subst(name, t);
                }
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
struct Subst<T>(Vec<(Name, T)>);

impl Display for Subst<Type> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            return write!(f, "{{}}");
        }
        write!(f, "{{ {} ↦ {}", self.0[0].0, self.0[0].1)?;
        if self.0.len() > 1 {
            for (name, ty) in &self.0[1..] {
                write!(f, ", {} ↦ {}", name, ty)?;
            }
        }
        write!(f, " }}")?;
        Ok(())
    }
}

impl Subst<Type> {
    fn apply_type(&self, t: &mut Type) {
        for (name, u) in &self.0 {
            t.instantiate(name.as_str(), u);
        }
    }

    fn apply_term(&self, m: &mut Term) {
        for (name, t) in &self.0 {
            m.instantiate(name.as_str(), t);
        }
    }

    fn unify(&mut self, t1: &mut Type, t2: &mut Type) -> anyhow::Result<()> {
        self.apply_type(t1);
        self.apply_type(t2);
        if t1 == t2 {
            return Ok(());
        }
        match (t1, t2) {
            (Type::Arrow(inner1), Type::Arrow(inner2)) => {
                let TypeArrow { dom: t11, cod: t12 } = Arc::make_mut(inner1);
                let TypeArrow { dom: t21, cod: t22 } = Arc::make_mut(inner2);
                self.unify(t11, t21)?;
                self.unify(t12, t22)?;
            }
            (Type::Mvar(i), t) | (t, Type::Mvar(i)) => {
                if !self.0.iter().any(|(j, _)| j == i) {
                    // TODO: occur check
                    self.0.push((i.clone(), t.clone()));
                } else {
                    let mut u = Type::Mvar(i.clone());
                    self.apply_type(&mut u);
                    self.unify(&mut u, t)?;
                }
            }
            (Type::App(inner1), Type::App(inner2)) => {
                let inner1 = Arc::make_mut(inner1);
                let inner2 = Arc::make_mut(inner2);
                self.unify(&mut inner1.fun, &mut inner2.fun)?;
                self.unify(&mut inner1.arg, &mut inner2.arg)?;
            }
            (_, _) => {
                bail!("type mismatch");
            }
        }
        Ok(())
    }
}

// We include the parser and printer in the trusted kernel
// to take Pollack-inconsistency into account.

#[derive(Debug, Clone)]
pub struct SourceInfo<'a> {
    line: usize,   // 1-origin
    column: usize, // 1-origin
    range: Range<usize>,
    input: &'a str,
}

impl<'a> SourceInfo<'a> {
    fn eof(input: &'a str) -> Self {
        let range = {
            let last = input.chars().count();
            last..last
        };
        let (line, column) = {
            let mut lines = input.lines();
            let last_line = lines.by_ref().last().unwrap();
            (lines.count() + 1, last_line.chars().count() + 1)
        };
        Self {
            range,
            input,
            line,
            column,
        }
    }

    fn as_str(&self) -> &str {
        self.input
            .get(self.range.clone())
            .expect("invalid token position")
    }
}

impl<'a> Display for SourceInfo<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}\n\n", self.line, self.column)?;
        writeln!(
            f,
            "{}",
            self.input
                .lines()
                .nth(self.line - 1)
                .expect("invalid line number")
        )?;
        writeln!(
            f,
            "{}{}",
            " ".repeat(self.column - 1),
            "^".repeat(
                self.input
                    .get(self.range.clone())
                    .unwrap_or("")
                    .chars()
                    .count()
            )
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    Ident,  // e.g. "foo", "α", "Prop"
    Symbol, // e.g. "+", ":", "λ", ",", "_"
}

#[derive(Debug, Clone)]
pub struct Token<'a> {
    kind: TokenKind,
    source_info: SourceInfo<'a>,
}

impl<'a> Token<'a> {
    fn is_ident(&self) -> bool {
        self.kind == TokenKind::Ident
    }

    fn is_symbol(&self) -> bool {
        self.kind == TokenKind::Symbol
    }

    fn as_str(&self) -> &str {
        self.source_info.as_str()
    }
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?} {}\n{}", self.kind, self.as_str(), self.source_info)
    }
}

#[derive(Debug, Clone)]
pub struct Lex<'a> {
    input: &'a str,
    position: usize,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, Copy)]
struct LexState {
    position: usize,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, Error)]
#[error("unrecognizable character at line {line}, column {column}")]
pub struct LexError {
    line: usize,
    column: usize,
}

impl<'a> From<Lex<'a>> for LexError {
    fn from(lex: Lex<'a>) -> Self {
        Self {
            line: lex.line,
            column: lex.column,
        }
    }
}

impl<'a> Lex<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            position: 0,
            line: 1,
            column: 1,
        }
    }

    fn save(&self) -> LexState {
        LexState {
            position: self.position,
            line: self.line,
            column: self.column,
        }
    }

    fn restore(&mut self, state: LexState) {
        self.position = state.position;
        self.line = state.line;
        self.column = state.column;
    }

    fn advance(&mut self, bytes: usize) -> SourceInfo<'a> {
        let source_info = SourceInfo {
            range: self.position..self.position + bytes,
            line: self.line,
            column: self.column,
            input: self.input,
        };
        let text = &self.input[self.position..self.position + bytes];
        self.position += bytes;
        for c in text.chars() {
            if c == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
        source_info
    }
}

impl<'a> Iterator for Lex<'a> {
    type Item = std::result::Result<Token<'a>, LexError>;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq, Eq, Debug)]
        enum Kind {
            Space,
            Ident,
            Symbol,
            NumLit,
        }

        static RE: Lazy<Regex> = Lazy::new(|| {
            let s = &[
                (Kind::Space, r"\s+|--.*|/-"),
                (
                    Kind::Ident,
                    r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*",
                ),
                (
                    Kind::Symbol,
                    r"[(){}⟨⟩⟪⟫,]|[\p{Symbol}\p{Punctuation}&&[^(){}⟨⟩⟪⟫,]]+",
                ),
                (Kind::NumLit, r"0|[1-9][0-9]*"),
            ]
            .iter()
            .map(|(kind, re)| format!("(?P<{:?}>{})", kind, re))
            .collect::<Vec<_>>()
            .join("|");
            regex::Regex::new(&format!("^(?:{})", s)).unwrap()
        });

        static RE_BLOCK_COMMENT: Lazy<Regex> =
            Lazy::new(|| regex::Regex::new("^(?s:.*?)(?:(?P<start>/-)|(?P<end>-/))").unwrap());

        loop {
            if self.input.len() == self.position {
                return None;
            }
            let cap = match RE.captures(&self.input[self.position..]) {
                None => return Some(Err(LexError::from(self.clone()))),
                Some(cap) => cap,
            };

            // skip whitespaces
            if let Some(m) = cap.name(&format!("{:?}", Kind::Space)) {
                self.advance(m.range().count());
                if m.as_str() == "/-" {
                    let mut nest = 1;
                    while nest != 0 {
                        if self.input.len() == self.position {
                            return None;
                        }
                        let cap = match RE_BLOCK_COMMENT.captures(&self.input[self.position..]) {
                            None => return Some(Err(LexError::from(self.clone()))),
                            Some(cap) => cap,
                        };
                        if cap.name("start").is_some() {
                            nest += 1;
                            self.advance(cap.get(0).unwrap().range().count());
                        } else {
                            assert!(cap.name("end").is_some());
                            nest -= 1;
                            self.advance(cap.get(0).unwrap().range().count());
                        }
                    }
                }
                continue;
            }

            if cap.name(&format!("{:?}", Kind::NumLit)).is_some() {
                return Some(Err(LexError::from(self.clone())));
            }

            // change the position of the cursor
            let source_info = self.advance(cap.get(0).unwrap().range().count());
            let text = source_info.as_str();

            let kind;
            if cap.name(&format!("{:?}", Kind::Ident)).is_some() {
                match text {
                    "λ" | "_" => {
                        kind = TokenKind::Symbol;
                    }
                    _ => {
                        kind = TokenKind::Ident;
                    }
                }
            } else {
                assert!(cap.name(&format!("{:?}", Kind::Symbol)).is_some());
                kind = TokenKind::Symbol;
            };
            return Some(Ok(Token { kind, source_info }));
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Fixity {
    /// alias to Infixl
    Infix,
    Infixl,
    Infixr,
    Nofix,
    Prefix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Operator {
    symbol: String,
    fixity: Fixity,
    prec: usize,
    entity: Name,
}

#[derive(Default, Debug)]
struct TokenTable {
    led: HashMap<String, Operator>,
    nud: HashMap<String, Operator>,
}

impl TokenTable {
    fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        match op.fixity {
            Fixity::Infix | Fixity::Infixl | Fixity::Infixr => {
                let sym = op.symbol.clone();
                if self.led.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
            Fixity::Nofix | Fixity::Prefix => {
                let sym = op.symbol.clone();
                if self.nud.insert(sym, op).is_some() {
                    bail!("symbol already defined")
                }
            }
        };
        Ok(())
    }
}

enum Led {
    App,
    User(Operator),
}

impl Led {
    fn prec(&self) -> usize {
        match self {
            Self::App => 1024,
            Self::User(op) => op.prec,
        }
    }
}

enum Nud {
    Var,
    Abs,
    Forall,
    Exists,
    Paren,
    Bracket,
    User(Operator),
}

impl TokenTable {
    fn get_led(&self, token: &Token) -> Option<Led> {
        match token.kind {
            TokenKind::Ident => Some(Led::App),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match self.led.get(lit) {
                    Some(op) => Some(Led::User(op.clone())),
                    None => {
                        if self.get_nud(token).is_some() {
                            Some(Led::App)
                        } else {
                            None
                        }
                    }
                }
            }
        }
    }

    fn get_nud(&self, token: &Token) -> Option<Nud> {
        match token.kind {
            TokenKind::Ident => Some(Nud::Var),
            TokenKind::Symbol => {
                let lit = token.as_str();
                match lit {
                    "(" => Some(Nud::Paren),
                    "⟨" => Some(Nud::Bracket),
                    "λ" => Some(Nud::Abs),
                    "∀" => Some(Nud::Forall),
                    "∃" => Some(Nud::Exists),
                    _ => self.nud.get(token.as_str()).map(|op| Nud::User(op.clone())),
                }
            }
        }
    }
}

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("{lex_error}")]
    Lex { lex_error: LexError },
    #[error("parse error: {message} at {source_info}")]
    Parse {
        message: String,
        source_info: String,
    },
    #[error("unexpected end of input at {source_info}")]
    Eof { source_info: String },
}

// Since LexError is not 'static we only want #[from] and don't need #[source],
// but this is impossible because #[from] attibute always implies #[source].
// So I am implementing it manually.
impl From<LexError> for ParseError {
    fn from(err: LexError) -> Self {
        Self::Lex { lex_error: err }
    }
}

pub struct Parser<'a, 'b> {
    lex: &'b mut Lex<'a>,
    locals: Vec<(Name, Type)>,
}

impl<'a, 'b> Parser<'a, 'b> {
    fn new(lex: &'b mut Lex<'a>) -> Self {
        Self {
            lex,
            locals: vec![],
        }
    }

    fn fail<R>(token: Token<'a>, message: impl Into<String>) -> Result<R, ParseError> {
        Err(ParseError::Parse {
            message: message.into(),
            source_info: token.source_info.to_string(),
        })
    }

    fn eof_error(&self) -> ParseError {
        ParseError::Eof {
            source_info: SourceInfo::eof(self.lex.input).to_string(),
        }
    }

    fn optional<F, R>(&mut self, f: F) -> Option<R>
    where
        F: FnOnce(&mut Self) -> Result<R, ParseError>,
    {
        let state = self.lex.save();
        match f(self) {
            Ok(m) => Some(m),
            Err(_err) => {
                self.lex.restore(state);
                None
            }
        }
    }

    fn peek_opt(&mut self) -> Option<Token<'a>> {
        self.optional(|this| this.peek())
    }

    fn peek(&mut self) -> Result<Token<'a>, ParseError> {
        self.lex
            .clone()
            .next()
            .transpose()?
            .ok_or_else(|| self.eof_error())
    }

    fn advance(&mut self) {
        self.lex
            .next()
            .expect("unchecked advance")
            .expect("impossible lex error! probably due to unchecked advance");
    }

    pub fn eof(&mut self) -> Result<(), ParseError> {
        if let Some(token) = self.peek_opt() {
            Self::fail(token, "expected EOF but tokens remain")?;
        }
        Ok(())
    }

    fn any_token(&mut self) -> Result<Token<'a>, ParseError> {
        self.lex
            .next()
            .transpose()
            .expect("lex error")
            .ok_or_else(|| self.eof_error())
    }

    fn ident(&mut self) -> Result<Token<'a>, ParseError> {
        let token = self.any_token()?;
        if !token.is_ident() {
            return Self::fail(token, "expected identifier");
        }
        Ok(token)
    }

    fn ident_opt(&mut self) -> Option<Token<'a>> {
        if let Some(token) = self.peek_opt() {
            if token.is_ident() {
                self.advance();
                return Some(token);
            }
        }
        None
    }

    fn expect_symbol(&mut self, sym: &str) -> Result<(), ParseError> {
        let token = self.any_token()?;
        if token.kind == TokenKind::Symbol && token.as_str() == sym {
            return Ok(());
        }
        Self::fail(token, format!("expected symbol '{}'", sym))
    }

    fn expect_symbol_opt(&mut self, sym: &str) -> Option<Token<'a>> {
        if let Some(token) = self.peek_opt() {
            if token.kind == TokenKind::Symbol && token.as_str() == sym {
                self.advance();
                return Some(token);
            }
        }
        None
    }

    pub fn name(&mut self) -> Result<Name, ParseError> {
        Ok(Name::try_from(self.ident()?.as_str()).expect("logic flaw"))
    }

    fn name_opt(&mut self) -> Option<Name> {
        self.ident_opt()
            .map(|token| Name::try_from(token.as_str()).expect("logic flaw"))
    }

    fn type_primary(&mut self) -> Result<Type, ParseError> {
        let token = self.any_token()?;
        if token.is_ident() {
            let name: Name = token.as_str().try_into().expect("logic flaw");
            match get_kind(name.as_str()) {
                Some(_kind) => Ok(Type::Const(name)),
                None => Ok(Type::Local(name)),
            }
        } else if token.is_symbol() && token.as_str() == "(" {
            let t = self.ty()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else {
            Self::fail(token, "expected a primary type expression")
        }
    }

    pub fn ty(&mut self) -> Result<Type, ParseError> {
        self.subty(0)
    }

    fn subty(&mut self, rbp: usize) -> Result<Type, ParseError> {
        let mut t = self.type_primary()?;
        while let Some(token) = self.peek_opt() {
            if token.is_symbol() && token.as_str() == "→" {
                if rbp >= 25 {
                    break;
                }
                self.advance();
                t = mk_arrow(t, self.subty(24)?);
            } else if token.is_ident() || (token.is_symbol() && token.as_str() == "(") {
                t = mk_tyapp(t, self.subty(1024)?);
            } else {
                break;
            }
        }
        Ok(t)
    }

    /// typed parameters e.g. `"(x y : T)"`
    fn parameter(&mut self, _token: Token) -> Result<(Vec<Name>, Type), ParseError> {
        let mut idents = vec![];
        // needs at least one parameter
        idents.push(self.name()?);
        while let Some(name) = self.name_opt() {
            idents.push(name);
        }
        self.expect_symbol(":")?;
        let t = self.ty()?;
        self.expect_symbol(")")?;
        Ok((idents, t))
    }

    fn parameters(&mut self) -> Result<Vec<(Name, Option<Type>)>, ParseError> {
        let mut params = vec![];
        loop {
            if let Some(token) = self.expect_symbol_opt("(") {
                let (names, t) = self.parameter(token)?;
                for name in names {
                    params.push((name, Some(t.clone())));
                }
            } else if let Some(name) = self.name_opt() {
                params.push((name, None));
            } else {
                break;
            }
        }
        Ok(params)
    }

    pub fn term(&mut self) -> Result<Term, ParseError> {
        self.subterm(0)
    }

    fn term_opt(&mut self) -> Option<Term> {
        self.optional(|this| this.term())
    }

    fn term_abs(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => Type::Mvar(Name::fresh()),
            };
            binders.push((name, ty));
        }
        for (name, ty) in &binders {
            self.locals.push((name.clone(), ty.clone()));
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.discharge_local(name, t);
        }
        Ok(m)
    }

    // TODO remove
    fn mk_const_unchecked(&self, name: &str) -> Term {
        let (ty_params, _) = get_type(name).expect("unknown constant");
        let mut ty_args = vec![];
        for _ in ty_params {
            ty_args.push(Type::Mvar(Name::fresh()));
        }
        mk_const(Name::try_from(name).expect("invalid name"), ty_args)
    }

    fn term_forall(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => Type::Mvar(Name::fresh()),
            };
            binders.push((name, ty));
        }
        for (name, ty) in &binders {
            self.locals.push((name.clone(), ty.clone()));
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.discharge_local(name, t);
            let f = mem::take(&mut m);
            m = self.mk_const_unchecked("forall");
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_exists(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        let params = self.parameters()?;
        self.expect_symbol(",")?;
        if params.is_empty() {
            return Self::fail(token, "empty binding");
        }
        let mut binders = vec![];
        for (name, ty) in params {
            let ty = match ty {
                Some(ty) => ty,
                None => Type::Mvar(Name::fresh()),
            };
            binders.push((name, ty));
        }
        for (name, ty) in &binders {
            self.locals.push((name.clone(), ty.clone()));
        }
        let mut m = self.subterm(0)?;
        for _ in 0..binders.len() {
            self.locals.pop();
        }
        for (name, t) in binders.into_iter().rev() {
            m.discharge_local(name, t);
            let f = mem::take(&mut m);
            m = self.mk_const_unchecked("exists");
            m.apply(vec![f]);
        }
        Ok(m)
    }

    fn term_var(&mut self, token: Token<'a>, entity: Option<Name>) -> Result<Term, ParseError> {
        let name = match entity {
            None => Name::try_from(token.as_str()).expect("logic flaw"),
            Some(s) => s,
        };
        for (x, ty) in self.locals.iter().rev() {
            if x == &name {
                return Ok(Term::Local(Arc::new(TermLocal {
                    name: x.clone(),
                    ty: ty.clone(),
                })));
            }
        }
        if let Some((tv, _)) = get_type(name.as_str()) {
            // TODO: parse type parameters
            let mut ty_args = vec![];
            for _ in tv {
                ty_args.push(Type::Mvar(Name::fresh()));
            }
            return Ok(mk_const(name, ty_args));
        }
        Ok(Term::Local(Arc::new(TermLocal {
            name,
            ty: Type::Mvar(Name::fresh()),
        })))
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError> {
        let token = self.any_token()?;
        // nud
        let nud = match Env::get().token_table().get_nud(&token) {
            None => todo!("nud unknown: {}", token),
            Some(nud) => nud,
        };
        let mut left = match nud {
            Nud::Var => self.term_var(token, None)?,
            Nud::Abs => self.term_abs(token)?,
            Nud::Paren => {
                let m = self.term()?;
                self.expect_symbol(")")?;
                m
            }
            Nud::Bracket => {
                let mut terms = vec![];
                while let Some(m) = self.term_opt() {
                    terms.push(m);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("⟩")?;
                // right associative encoding:
                // ⟨⟩ ⇒ star
                // ⟨m⟩ ⇒ m
                // ⟨m,n,l⟩ ⇒ ⟨m, ⟨n, l⟩⟩
                match terms.len() {
                    0 => self.mk_const_unchecked("star"),
                    1 => terms.pop().unwrap(),
                    _ => {
                        let mut m = terms.pop().unwrap();
                        for n in terms.into_iter().rev() {
                            let mut x = self.mk_const_unchecked("pair");
                            x.apply(vec![n, m]);
                            m = x;
                        }
                        m
                    }
                }
            }
            Nud::Forall => self.term_forall(token)?,
            Nud::Exists => self.term_exists(token)?,
            Nud::User(op) => match op.fixity {
                Fixity::Nofix => self.term_var(token, Some(op.entity))?,
                Fixity::Prefix => {
                    let mut fun = self.term_var(token, Some(op.entity))?;
                    let arg = self.subterm(op.prec)?;
                    fun.apply(vec![arg]);
                    fun
                }
                Fixity::Infix | Fixity::Infixl | Fixity::Infixr => unreachable!(),
            },
        };
        while let Some(token) = self.peek_opt() {
            let led = match Env::get().token_table().get_led(&token) {
                None => break,
                Some(led) => led,
            };
            let prec = led.prec();
            if rbp >= prec {
                break;
            }
            match led {
                Led::App => {
                    let right = self.subterm(led.prec())?;
                    left.apply(vec![right]);
                }
                Led::User(op) => {
                    let prec = match op.fixity {
                        Fixity::Infix | Fixity::Infixl => prec,
                        Fixity::Infixr => prec - 1,
                        Fixity::Nofix | Fixity::Prefix => unreachable!("op = {op:?}"),
                    };
                    self.advance();
                    let mut fun = self.term_var(token, Some(op.entity))?;
                    let right = self.subterm(prec)?;
                    fun.apply(vec![left, right]);
                    left = fun;
                }
            }
        }
        Ok(left)
    }
}

#[derive(Debug, Default)]
struct PrettyPrinter {
    op_table: HashMap<Name, Operator>,
}

impl PrettyPrinter {
    fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        let entity = op.entity.clone();
        if self.op_table.insert(entity, op).is_some() {
            bail!("notation already defined");
        }
        Ok(())
    }

    fn fmt_term(&self, m: &Term, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut local_names = vec![];
        let res = self.fmt_term_help(m, 0, true, &mut local_names, f);
        assert!(local_names.is_empty());
        res
    }

    fn fmt_term_help(
        &self,
        m: &Term,
        prec: usize,
        mut allow_lambda: bool,
        local_names: &mut Vec<Name>,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        if !m.binders().any(|_| true) {
            let (_, head, mut args) = m.triple();
            if let Term::Const(inner) = head {
                let name = &inner.name;
                if let Some(op) = self.op_table.get(name) {
                    match op.fixity {
                        Fixity::Infix | Fixity::Infixl => {
                            if args.len() == 2 {
                                if prec >= op.prec {
                                    write!(f, "(")?;
                                    allow_lambda = true;
                                }
                                let m2 = args.pop().unwrap();
                                let m1 = args.pop().unwrap();
                                self.fmt_term_help(m1, op.prec - 1, false, local_names, f)?;
                                write!(f, " {} ", op.symbol)?;
                                self.fmt_term_help(m2, op.prec, allow_lambda, local_names, f)?;
                                if prec >= op.prec {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                        }
                        Fixity::Infixr => {
                            if args.len() == 2 {
                                if prec >= op.prec {
                                    write!(f, "(")?;
                                    allow_lambda = true;
                                }
                                let m2 = args.pop().unwrap();
                                let m1 = args.pop().unwrap();
                                self.fmt_term_help(m1, op.prec, false, local_names, f)?;
                                write!(f, " {} ", op.symbol)?;
                                self.fmt_term_help(m2, op.prec - 1, allow_lambda, local_names, f)?;
                                if prec >= op.prec {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                        }
                        Fixity::Nofix => {
                            if args.is_empty() {
                                write!(f, "{}", op.symbol)?;
                                return Ok(());
                            }
                        }
                        Fixity::Prefix => {
                            // TODO: buggy
                            if args.len() == 1 {
                                if prec > op.prec {
                                    write!(f, "(")?;
                                    allow_lambda = true;
                                }
                                write!(f, "{}", op.symbol)?;
                                let m = args.pop().unwrap();
                                self.fmt_term_help(m, op.prec, allow_lambda, local_names, f)?;
                                if prec > op.prec {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                        }
                    }
                }
                match name.as_str() {
                    "forall" => {
                        if args.len() == 1 {
                            let mut arg = args.pop().unwrap();
                            if let Term::Abs(inner) = &mut arg {
                                if !allow_lambda {
                                    write!(f, "(")?;
                                }
                                let mut x = inner.binder_name.clone();
                                'refresh: for refresh_index in 0.. {
                                    if refresh_index > 0 {
                                        x = Name::try_from(format!(
                                            "{}{refresh_index}",
                                            inner.binder_name.as_str()
                                        ))
                                        .unwrap();
                                    }
                                    for (i, local_name) in local_names.iter().rev().enumerate() {
                                        if local_name == &x && inner.body.has_var(i + 1) {
                                            continue 'refresh;
                                        }
                                    }
                                    break;
                                }
                                write!(f, "∀ ({} : {}), ", x, inner.binder_type)?;
                                local_names.push(x);
                                self.fmt_term_help(&inner.body, 0, true, local_names, f)?;
                                local_names.pop();
                                if !allow_lambda {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                            args.push(arg);
                        }
                    }
                    "exists" => {
                        if args.len() == 1 {
                            let mut arg = args.pop().unwrap();
                            if let Term::Abs(inner) = &mut arg {
                                if !allow_lambda {
                                    write!(f, "(")?;
                                }
                                let mut x = inner.binder_name.clone();
                                'refresh: for refresh_index in 0.. {
                                    if refresh_index > 0 {
                                        x = Name::try_from(format!(
                                            "{}{refresh_index}",
                                            inner.binder_name.as_str()
                                        ))
                                        .unwrap();
                                    }
                                    for (i, local_name) in local_names.iter().rev().enumerate() {
                                        if local_name == &x && inner.body.has_var(i + 1) {
                                            continue 'refresh;
                                        }
                                    }
                                    break;
                                }
                                write!(f, "∃ ({} : {}), ", x, inner.binder_type)?;
                                local_names.push(x);
                                self.fmt_term_help(&inner.body, 0, true, local_names, f)?;
                                local_names.pop();
                                if !allow_lambda {
                                    write!(f, ")")?;
                                }
                                return Ok(());
                            }
                            args.push(arg);
                        }
                    }
                    _ => {}
                }
            }
        }

        match m {
            &Term::Var(i) => match local_names.get(local_names.len() - i - 1) {
                Some(name) => write!(f, "{name}"),
                None => write!(f, "{i}"),
            },
            Term::Local(inner) => {
                // TODO: take prec into account
                // TODO: concise mode
                write!(f, "({} : {})", inner.name, inner.ty)
            }
            Term::Const(inner) => {
                write!(f, "{}", inner.name)?;
                if !inner.ty_args.is_empty() {
                    write!(
                        f,
                        ".{{{}}}",
                        inner
                            .ty_args
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                Ok(())
            }
            Term::Abs(inner) => {
                if !allow_lambda {
                    write!(f, "(")?;
                }
                let mut x = inner.binder_name.clone();
                'refresh: for refresh_index in 0.. {
                    if refresh_index > 0 {
                        x = Name::try_from(format!(
                            "{}{refresh_index}",
                            inner.binder_name.as_str()
                        ))
                        .unwrap();
                    }
                    for (i, local_name) in local_names.iter().rev().enumerate() {
                        if local_name == &x && inner.body.has_var(i + 1) {
                            continue 'refresh;
                        }
                    }
                    break;
                }
                write!(f, "λ ({} : {}), ", x, inner.binder_type)?;
                local_names.push(x);
                self.fmt_term_help(&inner.body, 0, true, local_names, f)?;
                local_names.pop();
                if !allow_lambda {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Term::App(inner) => {
                if prec >= 1024 {
                    write!(f, "(")?;
                    allow_lambda = true;
                }
                self.fmt_term_help(&inner.fun, 1023, false, local_names, f)?;
                write!(f, " ")?;
                self.fmt_term_help(&inner.arg, 1024, allow_lambda, local_names, f)?;
                if prec >= 1024 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }

    fn fmt_type(&self, t: &Type, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.fmt_type_help(t, 0, f)
    }

    fn fmt_type_help(
        &self,
        t: &Type,
        prec: usize,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        match t {
            Type::Const(name) => write!(f, "{name}"),
            Type::Arrow(inner) => {
                if prec >= 25 {
                    write!(f, "(")?;
                }
                self.fmt_type_help(&inner.dom, 25, f)?;
                write!(f, " → ")?;
                self.fmt_type_help(&inner.cod, 24, f)?;
                if prec >= 25 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::App(inner) => {
                if prec >= 1024 {
                    write!(f, "(")?;
                }
                self.fmt_type_help(&inner.fun, 1023, f)?;
                write!(f, " ")?;
                self.fmt_type_help(&inner.arg, 1024, f)?;
                if prec >= 1024 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::Mvar(name) => write!(f, "{name}"),
            Type::Local(name) => write!(f, "{name}"),
        }
    }
}

#[test]
fn test_parse_print() {
    insta::assert_display_snapshot!("λ (x : α), x".parse::<Term>().unwrap(), @"λ (x : α), x");
    insta::assert_display_snapshot!("λ (p q r : Prop), p q r".parse::<Term>().unwrap(), @"λ (p : Prop), λ (q : Prop), λ (r : Prop), p q r");
    insta::assert_display_snapshot!("λ (φ ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = (λ (f : Prop → Prop → Prop), f ⊤ ⊤)".parse::<Term>().unwrap(), @"λ (φ : Prop), λ (ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = λ (f : Prop → Prop → Prop), f ⊤ ⊤");
    insta::assert_display_snapshot!("λ (p q : Prop), p = (p ∧ q)".parse::<Term>().unwrap(), @"λ (p : Prop), λ (q : Prop), p = (p ∧ q)");
}

#[derive(Debug, Default)]
struct Env {
    decls: HashMap<Name, Decl>,
    type_decls: HashMap<Name, TypeDecl>,
    meta_decls: HashMap<Name, MetaDecl>,
    notations: NotationTable,
}

#[derive(Debug, Clone)]
enum Decl {
    Const(DeclConst),
    Def(DeclDef),
}

#[derive(Debug, Clone)]
struct DeclConst {
    local_types: Vec<Name>,
    ty: Type,
}

#[derive(Debug, Clone)]
struct DeclDef {
    local_types: Vec<Name>,
    target: Term,
    ty: Type,
}

#[derive(Debug, Clone)]
enum TypeDecl {
    Const(TypeDeclConst),
}

#[derive(Debug, Clone)]
struct TypeDeclConst {
    kind: Kind,
}

#[derive(Debug, Clone)]
enum MetaDecl {
    Axiom(MetaDeclAxiom),
    Lemma(MetaDeclLemma),
}

#[derive(Debug, Clone)]
struct MetaDeclAxiom {
    formula: Term,
}

#[derive(Debug, Clone)]
struct MetaDeclLemma {
    fact: Fact,
}

#[derive(Debug, Default)]
struct NotationTable {
    // symbol to name
    tt: TokenTable,
    // name to symbol
    pp: PrettyPrinter,
}

static ENV: Lazy<RwLock<Env>> = Lazy::new(|| {
    let mut env = Env::default();

    env.add_type_decl(
        "Prop".try_into().unwrap(),
        TypeDecl::Const(TypeDeclConst { kind: Kind::base() }),
    )
    .unwrap();

    env.add_decl(
        "eq".try_into().unwrap(),
        Decl::Const(DeclConst {
            local_types: vec!["u".try_into().unwrap()],
            ty: mk_arrow(
                Type::Local("u".try_into().unwrap()),
                mk_arrow(Type::Local("u".try_into().unwrap()), Type::prop()),
            ),
        }),
    )
    .unwrap();

    env.add_notation("=".to_owned(), Fixity::Infix, 50, "eq".try_into().unwrap())
        .unwrap();

    RwLock::new(env)
});

impl Env {
    fn get() -> std::sync::RwLockReadGuard<'static, Env> {
        ENV.try_read().unwrap()
    }

    fn get_mut() -> std::sync::RwLockWriteGuard<'static, Env> {
        ENV.try_write().unwrap()
    }

    fn token_table(&self) -> &TokenTable {
        &self.notations.tt
    }

    fn add_type_decl(&mut self, name: Name, decl: TypeDecl) -> anyhow::Result<()> {
        if self.type_decls.insert(name, decl).is_some() {
            bail!("type declaration with given name already defined");
        }
        Ok(())
    }

    fn add_decl(&mut self, name: Name, decl: Decl) -> anyhow::Result<()> {
        if self.decls.insert(name, decl).is_some() {
            bail!("declaration with given name already defined");
        }
        Ok(())
    }

    fn add_meta_decl(&mut self, name: Name, decl: MetaDecl) -> anyhow::Result<()> {
        if self.meta_decls.insert(name, decl).is_some() {
            bail!("meta declaration with given name already defined");
        }
        Ok(())
    }

    fn get_type_decl(&self, name: &str) -> Option<TypeDecl> {
        self.type_decls.get(name).cloned()
    }

    fn get_decl(&self, name: &str) -> Option<Decl> {
        self.decls.get(name).cloned()
    }

    fn get_meta_decl(&self, name: &str) -> Option<MetaDecl> {
        self.meta_decls.get(name).cloned()
    }

    fn add_notation(
        &mut self,
        symbol: String,
        fixity: Fixity,
        prec: usize,
        entity: Name,
    ) -> anyhow::Result<()> {
        let op = Operator {
            symbol,
            fixity,
            prec,
            entity,
        };
        self.notations.tt.add(op.clone())?;
        self.notations.pp.add(op)?;
        Ok(())
    }
}

pub fn add_notation(symbol: &str, fixity: Fixity, prec: usize, entity: &str) -> anyhow::Result<()> {
    let Ok(entity) = Name::try_from(entity) else {
        bail!("invalid name: {entity}");
    };
    Env::get_mut().add_notation(symbol.to_owned(), fixity, prec, entity)
}

pub fn add_const(name: Name, local_types: Vec<Name>, ty: Type) -> anyhow::Result<()> {
    for i in 0..local_types.len() {
        for j in i + 1..local_types.len() {
            if local_types[i] == local_types[j] {
                bail!("duplicate type variables");
            }
        }
    }
    ty.check_kind_under(local_types.as_slice(), &Kind::base())?;
    if !ty.is_ground() {
        bail!("type not fully instantiated");
    }
    Env::get_mut().add_decl(name, Decl::Const(DeclConst { local_types, ty }))
}

pub fn add_const_type(name: Name, kind: Kind) -> anyhow::Result<()> {
    Env::get_mut().add_type_decl(name, TypeDecl::Const(TypeDeclConst { kind }))
}

pub fn add_axiom(name: Name, mut p: Term) -> anyhow::Result<()> {
    p.infer(&mut Type::prop())?;
    if !p.is_fully_instantiated() {
        bail!("not fully instantiated");
    }
    if !p.is_closed() {
        bail!("formula not closed");
    }
    Env::get_mut().add_meta_decl(name, MetaDecl::Axiom(MetaDeclAxiom { formula: p }))
}

pub fn add_lemma(name: Name, fact: Fact) -> anyhow::Result<()> {
    if !fact.local_context().is_empty() {
        bail!("local context is not empty");
    }
    if !fact.target().is_closed() {
        bail!("formula not closed");
    }
    Env::get_mut().add_meta_decl(name, MetaDecl::Lemma(MetaDeclLemma { fact }))
}

pub fn add_definition(name: Name, local_types: Vec<Name>, mut target: Term) -> anyhow::Result<()> {
    for i in 0..local_types.len() {
        for j in i + 1..local_types.len() {
            if local_types[i] == local_types[j] {
                bail!("duplicate type variables");
            }
        }
    }
    let ty = target.infer_under(local_types.as_slice())?;
    if !target.is_fully_instantiated() {
        bail!("not fully instantiated");
    }
    if !target.is_closed() {
        bail!("term not closed");
    }
    Env::get_mut().add_decl(
        name,
        Decl::Def(DeclDef {
            local_types,
            target,
            ty,
        }),
    )
}

fn get_kind(name: &str) -> Option<Kind> {
    let decl = Env::get().get_type_decl(name)?;
    match decl {
        TypeDecl::Const(TypeDeclConst { kind }) => Some(kind),
    }
}

fn get_type(name: &str) -> Option<(Vec<Name>, Type)> {
    let decl = Env::get().get_decl(name)?;
    match decl {
        Decl::Const(DeclConst { local_types, ty }) => Some((local_types, ty)),
        Decl::Def(DeclDef {
            local_types,
            target: _,
            ty,
        }) => Some((local_types, ty)),
    }
}

fn get_def(name: &str) -> Option<DeclDef> {
    let decl = Env::get().get_decl(name)?;
    match decl {
        Decl::Const(_) => None,
        Decl::Def(decl_def) => Some(decl_def),
    }
}

pub fn get_fact(name: &str) -> Option<Fact> {
    let decl = Env::get().get_meta_decl(name)?;
    match decl {
        MetaDecl::Axiom(MetaDeclAxiom { formula }) => Some(Fact {
            local_context: vec![],
            target: formula,
        }),
        MetaDecl::Lemma(MetaDeclLemma { fact }) => Some(fact),
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Fact {
    local_context: Vec<Term>,
    target: Term,
}

impl Display for Fact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for p in &self.local_context {
            write!(f, "({}) ", p)?;
        }
        write!(f, "⊢ {}", self.target)
    }
}

impl Fact {
    pub fn target(&self) -> &Term {
        &self.target
    }

    pub fn local_context(&self) -> &Vec<Term> {
        &self.local_context
    }
}

fn mk_eq(ty: Type, m1: Term, m2: Term) -> Term {
    let mut m = mk_const("eq".try_into().unwrap(), vec![ty]);
    m.apply([m1, m2]);
    m
}

fn as_eq(m: &Term) -> (&Term, &Term) {
    let mut args = m.args();
    let m2 = args.pop().unwrap();
    let m1 = args.pop().unwrap();
    (m1, m2)
}

fn dest_eq(m: &mut Term) -> Option<(Term, Term)> {
    assert!(m.is_type_correct());
    let binders = m.undischarge();
    assert!(binders.is_empty());
    let mut args = m.unapply();
    let Term::Const(inner) = m else {
        return None;
    };
    if inner.name.as_str() != "eq" {
        return None;
    }
    assert_eq!(args.len(), 2);
    let m2 = args.pop().unwrap();
    let m1 = args.pop().unwrap();
    Some((m1, m2))
}

/// ```text
///
/// ------------------
/// assume φ : [φ ⊢ φ]
/// ```
pub fn assume(mut target: Term) -> anyhow::Result<Fact> {
    target.infer(&mut Type::prop())?;
    if !target.is_fully_instantiated() {
        bail!("not fully instantiated");
    }
    Ok(Fact {
        local_context: vec![target.clone()],
        target,
    })
}

#[test]
fn test_assume_ok() {
    // terms may contain local variables
    let p = mk_local("p".try_into().unwrap(), Type::prop());
    insta::assert_display_snapshot!(assume(p).unwrap(), @"((p : Prop)) ⊢ (p : Prop)");

    // infer as Prop
    let p = "p".parse().unwrap();
    insta::assert_display_snapshot!(assume(p).unwrap(), @"((p : Prop)) ⊢ (p : Prop)");

    // terms may contain type variables
    let p: Term = "(λ (x : α), x) = (λ x, x)".parse().unwrap();
    insta::assert_display_snapshot!(assume(p).unwrap(), @"((λ (x : α), x) = λ (x : α), x) ⊢ (λ (x : α), x) = λ (x : α), x");
}

#[test]
fn test_assume_err() {
    // not a proposition
    let p = mk_local(
        "p".try_into().unwrap(),
        mk_arrow(Type::prop(), Type::prop()),
    );
    insta::assert_display_snapshot!(assume(p).unwrap_err(), @"type mismatch");

    // ill-typed
    let p = "(λ (x : Prop), x) (λ y, y)".parse().unwrap();
    insta::assert_display_snapshot!(assume(p).unwrap_err(), @"type mismatch");

    // not fully instantiated
    let f = "(λ x, x) = (λ x, x)".parse().unwrap();
    insta::assert_display_snapshot!(assume(f).unwrap_err(), @"not fully instantiated");
}

/// ```text
///
/// ---------------------------- (m₁ ≡ m₂)
/// eq_intro m₁ m₂ : [⊢ m₁ = m₂]
/// ```
pub fn eq_intro(m1: Term, m2: Term) -> anyhow::Result<Fact> {
    let mut target: Term = mk_eq(Type::Mvar(Name::fresh()), m1, m2);
    target.infer(&mut Type::prop())?;
    if !target.is_fully_instantiated() {
        bail!("not fully instantiated");
    }
    let (m1, m2) = as_eq(&target);
    if !m1.equiv(m2) {
        bail!("terms not definitionally equal: {m1} and {m2}");
    }
    Ok(Fact {
        local_context: vec![],
        target,
    })
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ C[m₁]]
/// ------------------------------------- [indiscernibility of identicals]
/// eq_elim C[-] h₁ h₂ : [Φ ∪ Ψ ⊢ C[m₂]]
/// ```
pub fn eq_elim(c: Term, mut h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    if !c.is_body() {
        bail!("expected context, but got {c}");
    }
    let Some((m1, m2)) = dest_eq(&mut h1.target) else {
        bail!("expected equality");
    };
    let mut cm1 = c.clone();
    cm1.open(&m1);
    cm1.infer(&mut Type::prop())?;
    if !cm1.is_fully_instantiated() {
        bail!("not fully instantiated");
    }
    if h2.target != cm1 {
        bail!("terms not literally equal: {} and {}", h2.target, cm1);
    }
    let mut ctx: Vec<_> = h1
        .local_context
        .into_iter()
        .chain(h2.local_context.into_iter())
        .collect();
    ctx.sort();
    ctx.dedup();
    let mut target = c;
    target.open(&m2);
    target.infer(&mut Type::prop()).expect("logic flaw");
    assert!(target.is_fully_instantiated());
    Ok(Fact {
        local_context: ctx,
        target,
    })
}

/// ```text
/// h₁ : [Φ ⊢ φ]  h₂ : [Ψ ⊢ ψ]
/// ------------------------------------------------ [(external) propositional extensionality]
/// prop_ext h₁ h₂ : [(Φ - {ψ}) ∪ (Ψ - {φ}) ⊢ φ = ψ]
/// ```
pub fn prop_ext(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let mut ctx: Vec<_> = h1
        .local_context
        .into_iter()
        .filter(|p| p != &h2.target)
        .chain(h2.local_context.into_iter().filter(|p| p != &h1.target))
        .collect();
    ctx.sort();
    ctx.dedup();
    Ok(Fact {
        local_context: ctx,
        target: mk_eq(Type::prop(), h1.target, h2.target),
    })
}

/// ```text
/// h : [Φ ⊢ m₁ = m₂]
/// ------------------------------------------------------- (x ∉ FV Φ) [(external) function extensionality]
/// fun_ext x τ h : [Φ ⊢ (λ (x : τ), m₁) = (λ (x : τ), m₂)]
/// ```
pub fn fun_ext(x: &Name, t: Type, mut h: Fact) -> anyhow::Result<Fact> {
    t.check_kind(&Kind::base())?;
    let Some((mut m1, mut m2)) = dest_eq(&mut h.target) else {
        bail!("expected equality");
    };
    if !h.local_context.iter().all(|m| m.is_fresh(x.as_str(), &t)) {
        bail!("eigenvariable condition fails");
    }
    m1.discharge_local(x.clone(), t.clone());
    m2.discharge_local(x.clone(), t);
    let t = m1.synthesize_unchecked();
    Ok(Fact {
        local_context: h.local_context,
        target: mk_eq(t, m1, m2),
    })
}

/// ```text
/// h : [Φ ⊢ φ]
/// ------------------------------
/// inst u τ h : [[τ/u]Φ ⊢ [τ/u]φ]
/// ```
pub fn inst(name: &Name, ty: &Type, mut h: Fact) -> anyhow::Result<Fact> {
    ty.check_kind(&Kind::base())?;
    for p in &mut h.local_context {
        p.instantiate_local(name.as_str(), ty);
    }
    h.target.instantiate_local(name.as_str(), ty);
    Ok(h)
}
