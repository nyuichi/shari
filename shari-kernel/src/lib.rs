//! [Type] and [Term] may be ill-formed.

use anyhow::bail;
use core::ops::Range;
use once_cell::sync::Lazy;
use regex::Regex;
use std::collections::HashMap;
use std::fmt::Display;
use std::mem;
use std::str::FromStr;
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

    fn get_unchecked(value: &str) -> Name {
        *NAME_TABLE.read().unwrap().get(value).unwrap()
    }

    fn intern(value: &str) -> Result<Name, InvalidNameError> {
        static RE: Lazy<Regex> = Lazy::new(|| {
            regex::Regex::new(r"[\p{Cased_Letter}_][\p{Cased_Letter}\p{Number}_]*").unwrap()
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

// TODO TypeHead
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
    // Never be an `App`.
    pub head: Type,
    // Never be empty.
    pub args: Vec<Type>,
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
        let env = Env::get();
        let mut parser = Parser::new(&mut lex, &env, false);
        let ty = parser.ty()?;
        parser.eof()?;
        Ok(ty)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.fmt_help(f, 0)
    }
}

fn mk_type_arrow(dom: Type, mut cod: Type) -> Type {
    cod.discharge([dom]);
    cod
}

fn mk_fresh_type_mvar() -> Type {
    Type::Mvar(Name::fresh())
}

fn mk_type_local(name: Name) -> Type {
    Type::Local(name)
}

fn mk_type_const(name: Name) -> Type {
    Type::Const(name)
}

/// See [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    /// t.discharge([t1, t2]);
    /// assert_eq!(t, "t2 → t1 → t");
    fn discharge(&mut self, cs: impl IntoIterator<Item = Type>) {
        for c in cs {
            *self = Type::Arrow(Arc::new(TypeArrow {
                dom: c,
                cod: mem::take(self),
            }));
        }
    }

    fn apply(&mut self, args: impl IntoIterator<Item = Type>) {
        match self {
            Type::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.args.extend(args);
            }
            Type::Const(_) | Type::Arrow(_) | Type::Local(_) | Type::Mvar(_) => {
                *self = Type::App(Arc::new(TypeApp {
                    head: mem::take(self),
                    args: args.into_iter().collect(),
                }));
            }
        }
    }

    /// Substitute [t] for locals with name [name].
    fn subst(&mut self, name: Name, t: &Type) {
        match self {
            Self::Const(_) => {}
            Self::Local(x) => {
                if x == &name {
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
                inner.head.subst(name, t);
                for arg in &mut inner.args {
                    arg.subst(name, t);
                }
            }
        }
    }

    /// Infer the kind of [self]. This method also checks whether arities are consistent.
    fn infer_kind(&self) -> anyhow::Result<Kind> {
        match self {
            Type::Const(name) => {
                let Some(kind) = get_kind(*name) else {
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
                let head_kind = inner.head.infer_kind()?;
                if head_kind.0 < inner.args.len() {
                    bail!("too many type arguments");
                }
                for arg in &inner.args {
                    if !arg.infer_kind()?.is_base() {
                        bail!("not a type");
                    }
                }
                Ok(Kind(head_kind.0 - inner.args.len()))
            }
            Type::Local(_) => Ok(Kind::base()),
            // no higher-kinded polymorphism
            Type::Mvar(_) => Ok(Kind::base()),
        }
    }

    /// Check whether arities are consistent.
    fn check_kind(&self, kind: &Kind) -> anyhow::Result<()> {
        let my_kind = self.infer_kind()?;
        if &my_kind != kind {
            bail!("expected {kind}, but got {my_kind}");
        }
        Ok(())
    }

    fn infer_kind_under(&self, locals: &[Name]) -> anyhow::Result<Kind> {
        match self {
            Type::Const(name) => {
                let Some(kind) = get_kind(*name) else {
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
                let head_kind = inner.head.infer_kind_under(locals)?;
                if head_kind.0 < inner.args.len() {
                    bail!("too many type arguments");
                }
                for arg in &inner.args {
                    if !arg.infer_kind_under(locals)?.is_base() {
                        bail!("not a type");
                    }
                }
                Ok(Kind(head_kind.0 - inner.args.len()))
            }
            Type::Local(name) => {
                if !locals.contains(name) {
                    bail!("unknown local: {name}");
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
    fn is_ground(&self) -> bool {
        match self {
            Type::Const(_) => true,
            Type::Arrow(inner) => inner.dom.is_ground() && inner.cod.is_ground(),
            Type::App(inner) => inner.head.is_ground() && inner.args.iter().all(Type::is_ground),
            Type::Local(_) => true,
            Type::Mvar(_) => false,
        }
    }

    fn fmt_help(&self, f: &mut std::fmt::Formatter, prec: usize) -> std::fmt::Result {
        match self {
            Type::Const(name) => write!(f, "{name}"),
            Type::Arrow(inner) => {
                if prec >= 25 {
                    write!(f, "(")?;
                }
                inner.dom.fmt_help(f, 25)?;
                write!(f, " → ")?;
                inner.cod.fmt_help(f, 24)?;
                if prec >= 25 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::App(inner) => {
                if prec >= 1024 {
                    write!(f, "(")?;
                }
                inner.head.fmt_help(f, 1023)?;
                for arg in &inner.args {
                    write!(f, " ")?;
                    arg.fmt_help(f, 1024)?;
                }
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
        let env = Env::get();
        Printer::new(&env).fmt_term(self, f)
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
        let env = Env::get();
        let mut parser = Parser::new(&mut lex, &env, false);
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

    fn open_shift(&mut self, x: &Term) {
        self.open_shift_at(x, 0)
    }

    fn open_shift_at(&mut self, x: &Term, shift: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(i) => {
                if *i == shift {
                    *self = x.clone();
                    self.shift(shift);
                }
            }
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.open_shift_at(x, shift + 1);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.open_shift_at(x, shift);
                inner.arg.open_shift_at(x, shift);
            }
            Self::Const(_) => {}
        }
    }

    fn shift(&mut self, shift: usize) {
        self.shift_at(0, shift)
    }

    fn shift_at(&mut self, level: usize, shift: usize) {
        match self {
            Self::Local(_) => {}
            Self::Var(x) => {
                if *x >= level {
                    *x += shift
                }
            }
            Self::Abs(inner) => {
                Arc::make_mut(inner).body.shift_at(level + 1, shift);
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.shift_at(level, shift);
                inner.arg.shift_at(level, shift);
            }
            Self::Const(_) => {}
        }
    }

    /// x # self <==> x ∉ FV(self)
    fn is_fresh(&self, name: Name, ty: &Type) -> bool {
        match self {
            Self::Local(inner) => inner.name != name || inner.ty != *ty,
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_fresh(name, ty),
            Self::App(inner) => inner.fun.is_fresh(name, ty) && inner.arg.is_fresh(name, ty),
            Self::Const(_) => true,
        }
    }

    fn is_closed(&self) -> bool {
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

    fn is_body(&self) -> bool {
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
    fn matrix(&self) -> &Term {
        let mut m = self;
        while let Term::Abs(inner) = m {
            m = &inner.body;
        }
        m
    }

    /// triple(λ (v:t)*, m l*) = (t*, m, l*)
    /// may return locally open terms
    fn triple(&self) -> (impl Iterator<Item = &Type>, &Term, Vec<&Term>) {
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
    pub fn head(&self) -> &Term {
        self.triple().1
    }

    /// may return locally open terms
    pub fn args(&self) -> Vec<&Term> {
        self.triple().2
    }

    /// m = n l*
    /// m.unapply() // => l*
    /// assert(m = n)
    fn unapply(&mut self) -> Vec<Term> {
        let mut args = self.unapply_rev();
        args.reverse();
        args
    }

    /// m = n l₁ ⋯ lₙ
    /// m.unapply() // => [lₙ ⋯ l₁]
    /// assert(m = n)
    fn unapply_rev(&mut self) -> Vec<Term> {
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

    pub fn apply(&mut self, args: impl IntoIterator<Item = Term>) {
        let mut m = mem::take(self);
        for arg in args {
            m = mk_app(m, arg);
        }
        *self = m;
    }

    fn apply_rev(&mut self, mut args: Vec<Term>) {
        let mut m = mem::take(self);
        while let Some(arg) = args.pop() {
            m = mk_app(m, arg);
        }
        *self = m;
    }

    // λ x₁ ⋯ xₙ, m ↦ [xₙ, ⋯ , x₁]
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
        xs.reverse();
        xs
    }

    // assert_eq!(self, "m");
    // self.discharge([x1, x2]);
    // assert_eq!(self, "λ x2 x1, m");
    pub fn discharge(&mut self, xs: impl IntoIterator<Item = (Name, Type)>) {
        let mut m = mem::take(self);
        for (name, ty) in xs {
            m = mk_abs(name, ty, m);
        }
        *self = m;
    }

    pub fn discharge_local(&mut self, name: Name, ty: Type) {
        self.close(name, &ty);
        let m = mem::take(self);
        *self = mk_abs(name, ty, m);
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
                inner.body.close(name, &ty);
                inner.binder_type = ty;
            }
        }
    }

    /// Unification-based type inference.
    /// Errors if
    /// - types mismatch,
    /// - uninstantiated meta type variables remain,
    /// - self is not locally closed,
    /// - an unknown constant is found, or
    /// - kind checking failed.
    fn infer(&mut self, target: &mut Type) -> anyhow::Result<()> {
        target.check_kind(&Kind::base())?;
        let mut eq_set = EqSet::default();
        let mut var_stack = vec![];
        self.infer_help(target, &mut var_stack, &mut eq_set)?;
        assert!(var_stack.is_empty());
        let unifier = eq_set.solve()?;
        unifier.apply_term(self)?;
        unifier.apply_type(target)?;
        Ok(())
    }

    /// TODO: chagne return type to Result<()>
    fn infer_help<'a>(
        &'a self,
        target: &Type,
        var_stack: &mut Vec<&'a Type>,
        eq_set: &mut EqSet,
    ) -> anyhow::Result<()> {
        match self {
            Term::Local(inner) => {
                inner.ty.check_kind(&Kind::base())?;
                eq_set.unify(inner.ty.clone(), target.clone());
            }
            &Term::Var(i) => {
                if i >= var_stack.len() {
                    bail!("term not locally closed");
                }
                eq_set.unify(var_stack[var_stack.len() - i - 1].clone(), target.clone());
            }
            Term::Abs(inner) => {
                inner.binder_type.check_kind(&Kind::base())?;
                var_stack.push(&inner.binder_type);
                let body_ty = mk_fresh_type_mvar();
                inner.body.infer_help(&body_ty, var_stack, eq_set)?;
                var_stack.pop();
                eq_set.unify(
                    mk_type_arrow(inner.binder_type.clone(), body_ty),
                    target.clone(),
                );
            }
            Term::App(inner) => {
                let fun_ty = mk_fresh_type_mvar();
                inner.fun.infer_help(&fun_ty, var_stack, eq_set)?;
                let arg_ty = mk_fresh_type_mvar();
                inner.arg.infer_help(&arg_ty, var_stack, eq_set)?;
                eq_set.unify(fun_ty, mk_type_arrow(arg_ty, target.clone()));
            }
            Term::Const(inner) => {
                let Some((tv, mut ty)) = get_type(inner.name) else {
                    bail!("constant not found");
                };
                if tv.len() != inner.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                let new_tv: Vec<_> = std::iter::repeat_with(mk_fresh_type_mvar)
                    .take(tv.len())
                    .collect();
                for (old, new) in std::iter::zip(&tv, &new_tv) {
                    ty.subst(*old, new);
                }
                let ty_args = inner.ty_args.clone();
                for (t1, t2) in std::iter::zip(ty_args, new_tv) {
                    t1.check_kind(&Kind::base())?;
                    eq_set.unify(t1, t2);
                }
                eq_set.unify(ty, target.clone());
            }
        }
        Ok(())
    }

    /// Similar to infer, but performs kind checking under given context.
    fn infer_under(&mut self, target: &mut Type, kind_ctx: &[Name]) -> anyhow::Result<()> {
        let mut eq_set = EqSet::default();
        let mut var_stack = vec![];
        self.infer_under_help(target, kind_ctx, &mut var_stack, &mut eq_set)?;
        assert!(var_stack.is_empty());
        let unifier = eq_set.solve()?;
        unifier.apply_term(self)?;
        unifier.apply_type(target)?;
        Ok(())
    }

    fn infer_under_help<'a>(
        &'a self,
        target: &Type,
        kind_ctx: &[Name],
        var_stack: &mut Vec<&'a Type>,
        eq_set: &mut EqSet,
    ) -> anyhow::Result<()> {
        match self {
            Term::Local(inner) => {
                inner.ty.check_kind_under(kind_ctx, &Kind::base())?;
                eq_set.unify(inner.ty.clone(), target.clone());
            }
            &Term::Var(i) => {
                if i >= var_stack.len() {
                    bail!("term not locally closed");
                }
                eq_set.unify(var_stack[var_stack.len() - i - 1].clone(), target.clone());
            }
            Term::Abs(inner) => {
                inner
                    .binder_type
                    .check_kind_under(kind_ctx, &Kind::base())?;
                var_stack.push(&inner.binder_type);
                let body_ty = mk_fresh_type_mvar();
                inner
                    .body
                    .infer_under_help(&body_ty, kind_ctx, var_stack, eq_set)?;
                var_stack.pop();
                eq_set.unify(
                    mk_type_arrow(inner.binder_type.clone(), body_ty),
                    target.clone(),
                );
            }
            Term::App(inner) => {
                let fun_ty = mk_fresh_type_mvar();
                inner
                    .fun
                    .infer_under_help(&fun_ty, kind_ctx, var_stack, eq_set)?;
                let arg_ty = mk_fresh_type_mvar();
                inner
                    .arg
                    .infer_under_help(&arg_ty, kind_ctx, var_stack, eq_set)?;
                eq_set.unify(fun_ty, mk_type_arrow(arg_ty, target.clone()));
            }
            Term::Const(inner) => {
                let Some((tv, mut ty)) = get_type(inner.name) else {
                    bail!("constant not found");
                };
                if tv.len() != inner.ty_args.len() {
                    bail!("number of type variables mismatch");
                }
                let new_tv: Vec<_> = std::iter::repeat_with(mk_fresh_type_mvar)
                    .take(tv.len())
                    .collect();
                for (old, new) in std::iter::zip(&tv, &new_tv) {
                    ty.subst(*old, new);
                }
                let ty_args = inner.ty_args.clone();
                for (t1, t2) in std::iter::zip(ty_args, new_tv) {
                    t1.check_kind(&Kind::base())?;
                    eq_set.unify(t1, t2);
                }
                eq_set.unify(ty, target.clone());
            }
        }
        Ok(())
    }

    fn beta_reduce_whnf(&mut self) -> bool {
        let mut perform = false;
        match self {
            Self::Var(_) => {}
            Self::Local(_) => {}
            Self::Const(_) => {}
            Self::Abs(_) => {}
            Self::App(_) => {
                let mut args = self.unapply_rev();
                while let Self::Abs(inner) = self {
                    let Some(arg) = args.pop() else {
                        break;
                    };
                    let inner = Arc::make_mut(inner);
                    inner.body.open_shift(&arg);
                    perform = true;
                    *self = mem::take(&mut inner.body);
                }
                self.apply_rev(args);
                if perform {
                    self.beta_reduce_whnf();
                }
            }
        }
        perform
    }

    fn normalize_types(&mut self) -> bool {
        false
    }

    fn unfold_head(&mut self) {
        match self {
            Self::Var(_) | Self::Local(_) => {}
            Self::Const(inner) => {
                if let Some(DeclDef {
                    local_types,
                    mut target,
                    ty: _,
                }) = get_def(inner.name)
                {
                    for (local, ty_arg) in std::iter::zip(&local_types, &inner.ty_args) {
                        target.instantiate_local(*local, ty_arg);
                    }
                    *self = target;
                }
            }
            Self::App(inner) => {
                let inner = Arc::make_mut(inner);
                inner.fun.unfold_head();
            }
            Self::Abs(_) => {}
        }
    }

    /// [m1] and [m2] must be type-correct and type-equal under the same environment.
    /// TODO: optimize
    fn equiv(&self, other: &Term) -> bool {
        let mut m1 = self.clone();
        let mut m2 = other.clone();
        m1.normalize_types();
        m2.normalize_types();
        loop {
            if m1 == m2 {
                return true;
            }
            while let (Term::Abs(inner1), Term::Abs(inner2)) = (&mut m1, &mut m2) {
                m1 = mem::take(&mut Arc::make_mut(inner1).body);
                m2 = mem::take(&mut Arc::make_mut(inner2).body);
            }
            let p1 = m1.beta_reduce_whnf();
            let p2 = m2.beta_reduce_whnf();
            if p1 || p2 {
                if m1 == m2 {
                    return true;
                }
                while let (Term::Abs(inner1), Term::Abs(inner2)) = (&mut m1, &mut m2) {
                    m1 = mem::take(&mut Arc::make_mut(inner1).body);
                    m2 = mem::take(&mut Arc::make_mut(inner2).body);
                }
            }
            let h1 = m1.head();
            let h2 = m2.head();
            // optimization
            if h1 == h2 {
                let args1 = h1.args();
                let args2 = h2.args();
                if args1.len() == args2.len() {
                    'args_eq: {
                        for (a1, a2) in std::iter::zip(args1, args2) {
                            if !a1.equiv(a2) {
                                break 'args_eq;
                            }
                        }
                        return true;
                    }
                }
            }
            let def1 = if let Term::Const(inner) = h1 {
                get_def_index(inner.name)
            } else {
                None
            };
            let def2 = if let Term::Const(inner) = h2 {
                get_def_index(inner.name)
            } else {
                None
            };
            if def1.is_some() || def2.is_some() {
                let height1 = def1.unwrap_or(0);
                let height2 = def2.unwrap_or(0);
                match height1.cmp(&height2) {
                    std::cmp::Ordering::Less => {
                        m2.unfold_head();
                    }
                    std::cmp::Ordering::Equal => {
                        m1.unfold_head();
                        m2.unfold_head();
                    }
                    std::cmp::Ordering::Greater => {
                        m1.unfold_head();
                    }
                }
                m1.normalize_types();
                m2.normalize_types();
                continue;
            }
            if let Term::Abs(_) = m2 {
                (m1, m2) = (m2, m1)
            }
            if let Term::Abs(inner) = &mut m1 {
                m1 = mem::take(&mut Arc::make_mut(inner).body);
                m2.shift(1);
                m2.apply([Term::Var(0)]);
                m2 = mem::take(&mut m2);
                continue;
            }
            return false;
        }
    }

    fn instantiate_local(&mut self, name: Name, t: &Type) {
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
                    // so heads must be the same and args must be in the same length.
                    if inner1.head != inner2.head || inner1.args.len() != inner2.args.len() {
                        bail!("type mismatch");
                    }
                    let inner1 = Arc::try_unwrap(inner1).unwrap_or_else(|arc| (*arc).clone());
                    let inner2 = Arc::try_unwrap(inner2).unwrap_or_else(|arc| (*arc).clone());
                    for (arg1, arg2) in std::iter::zip(inner1.args, inner2.args) {
                        self.unify(arg1, arg2);
                    }
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
                self.apply_type(&mut inner.head)?;
                for arg in &mut inner.args {
                    self.apply_type(arg)?;
                }
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
    fn new(input: &'a str) -> Self {
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
                    r"[(){}⟨⟩⟪⟫,]|\.\{|\$\{|[\p{Symbol}\p{Punctuation}&&[^(){}⟨⟩⟪⟫,]]+",
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

#[derive(Default, Debug, Clone)]
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
    Brace,
    Hole,
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
                    "{" => Some(Nud::Brace),
                    "${" => Some(Nud::Hole),
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
    env: &'b Env,
    allow_holes: bool,
    holes: Vec<(Name, Type)>,
}

impl<'a, 'b> Parser<'a, 'b> {
    fn new(lex: &'b mut Lex<'a>, env: &'b Env, allow_holes: bool) -> Self {
        Self {
            lex,
            locals: vec![],
            env,
            allow_holes,
            holes: vec![],
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

    fn eof(&mut self) -> Result<(), ParseError> {
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

    fn name(&mut self) -> Result<Name, ParseError> {
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
            match self.env.get_kind(name) {
                Some(_kind) => Ok(mk_type_const(name)),
                None => Ok(mk_type_local(name)),
            }
        } else if token.is_symbol() && token.as_str() == "(" {
            let t = self.ty()?;
            self.expect_symbol(")")?;
            Ok(t)
        } else {
            Self::fail(token, "expected a primary type expression")
        }
    }

    fn ty(&mut self) -> Result<Type, ParseError> {
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
                t = mk_type_arrow(t, self.subty(24)?);
            } else if token.is_ident() || (token.is_symbol() && token.as_str() == "(") {
                t.apply([self.subty(1024)?]);
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

    fn term(&mut self) -> Result<Term, ParseError> {
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
                None => mk_fresh_type_mvar(),
            };
            binders.push((name, ty));
        }
        for (name, ty) in &binders {
            self.locals.push((*name, ty.clone()));
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
        let (ty_params, _) = self
            .env
            .get_type(name.try_into().unwrap())
            .expect("unknown constant");
        let mut ty_args = vec![];
        for _ in ty_params {
            ty_args.push(mk_fresh_type_mvar());
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
                None => mk_fresh_type_mvar(),
            };
            binders.push((name, ty));
        }
        for (name, ty) in &binders {
            self.locals.push((*name, ty.clone()));
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
                None => mk_fresh_type_mvar(),
            };
            binders.push((name, ty));
        }
        for (name, ty) in &binders {
            self.locals.push((*name, ty.clone()));
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

    fn term_setsep(&mut self, _token: Token<'a>) -> Result<Term, ParseError> {
        let name = self.name()?;
        self.expect_symbol("|")?;
        let t = mk_fresh_type_mvar();
        self.locals.push((name, t.clone()));
        let mut m = self.subterm(0)?;
        self.locals.pop();
        m.discharge_local(name, t);
        self.expect_symbol("}")?;
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
                    name: *x,
                    ty: ty.clone(),
                })));
            }
        }
        let Some((tv, _)) = self.env.get_type(name) else {
            return Ok(Term::Local(Arc::new(TermLocal {
                name,
                ty: mk_fresh_type_mvar(),
            })));
        };
        let mut ty_args = vec![];
        if let Some(_token) = self.expect_symbol_opt(".{") {
            if self.expect_symbol_opt("}").is_none() {
                loop {
                    ty_args.push(self.ty()?);
                    if self.expect_symbol_opt(",").is_none() {
                        break;
                    }
                }
                self.expect_symbol("}")?;
            }
        } else {
            for _ in tv {
                ty_args.push(mk_fresh_type_mvar());
            }
        }
        Ok(mk_const(name, ty_args))
    }

    fn term_hole(&mut self, token: Token<'a>) -> Result<Term, ParseError> {
        if !self.allow_holes {
            return Self::fail(token, "hole not allowed in this mode");
        }
        self.expect_symbol("}")?;
        let name = Name::fresh();
        let ty = mk_fresh_type_mvar();
        self.holes.push((name, ty.clone()));
        Ok(mk_local(name, ty))
    }

    fn subterm(&mut self, rbp: usize) -> Result<Term, ParseError> {
        let token = self.any_token()?;
        // nud
        let nud = match self.env.token_table().get_nud(&token) {
            None => todo!("nud unknown: {}", token),
            Some(nud) => nud,
        };
        let mut left = match nud {
            Nud::Var => self.term_var(token, None)?,
            Nud::Abs => self.term_abs(token)?,
            Nud::Paren => {
                let m = self.subterm(0)?;
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
            Nud::Brace => self.term_setsep(token)?,
            Nud::Hole => self.term_hole(token)?,
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
            let led = match self.env.token_table().get_led(&token) {
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

#[doc(hidden)]
pub trait Quote: Sized + 'static {
    fn quote<'a>(template: &str, args: impl IntoIterator<Item = &'a Self>) -> anyhow::Result<Self>;
}

impl Quote for Term {
    fn quote<'a>(template: &str, args: impl IntoIterator<Item = &'a Term>) -> anyhow::Result<Term> {
        let mut lex = Lex::new(template);
        let env = Env::get();
        let mut parser = Parser::new(&mut lex, &env, true);
        let mut m = parser.term()?;
        parser.eof()?;
        let args: Vec<_> = args.into_iter().collect();
        if args.len() != parser.holes.len() {
            bail!("number of holes mismatch");
        }
        for (i, (name, ty)) in parser.holes.into_iter().enumerate() {
            m.close_at(name, &ty, i);
        }
        for (i, arg) in args.into_iter().enumerate() {
            m.open_at(arg, i);
        }
        Ok(m)
    }
}

#[doc(hidden)]
pub fn quote<'a, T: Quote>(
    template: &str,
    args: impl IntoIterator<Item = &'a T>,
) -> anyhow::Result<T> {
    Quote::quote(template, args)
}

#[macro_export]
macro_rules! q {
    ($template:expr) => {
        $crate::quote($template, []).unwrap()
    };
    ($template:expr, $($args:expr),*) => {
        $crate::quote($template, [$($args),*]).unwrap()
    };
}

#[derive(Debug, Default, Clone)]
struct OpTable {
    op_table: HashMap<Name, Operator>,
}

impl OpTable {
    fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        let entity = op.entity;
        if self.op_table.insert(entity, op).is_some() {
            bail!("notation already defined");
        }
        Ok(())
    }

    fn get(&self, name: Name) -> Option<&Operator> {
        self.op_table.get(&name)
    }
}

struct Printer<'a> {
    env: &'a Env,
}

impl<'a> Printer<'a> {
    fn new(env: &'a Env) -> Self {
        Printer { env }
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
                let name = inner.name;
                if let Some(op) = self.env.op_table().get(name) {
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
                match name.to_string().as_str() {
                    "forall" => {
                        if args.len() == 1 {
                            let mut arg = args.pop().unwrap();
                            if let Term::Abs(inner) = &mut arg {
                                if !allow_lambda {
                                    write!(f, "(")?;
                                }
                                let mut x = inner.binder_name;
                                'refresh: for refresh_index in 0.. {
                                    if refresh_index > 0 {
                                        x = Name::try_from(
                                            format!("{}{refresh_index}", inner.binder_name)
                                                .as_str(),
                                        )
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
                                let mut x = inner.binder_name;
                                'refresh: for refresh_index in 0.. {
                                    if refresh_index > 0 {
                                        x = Name::try_from(
                                            format!("{}{refresh_index}", inner.binder_name)
                                                .as_str(),
                                        )
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
                let mut x = inner.binder_name;
                'refresh: for refresh_index in 0.. {
                    if refresh_index > 0 {
                        x = Name::try_from(
                            format!("{}{refresh_index}", inner.binder_name).as_str(),
                        )
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
}

#[test]
fn test_parse_print() {
    let ops = [
        Operator {
            symbol: "⊤".to_owned(),
            fixity: Fixity::Nofix,
            prec: usize::MAX,
            entity: "top".try_into().unwrap(),
        },
        Operator {
            symbol: "∧".to_owned(),
            fixity: Fixity::Infixr,
            prec: 35,
            entity: "and".try_into().unwrap(),
        },
        Operator {
            symbol: "¬".to_owned(),
            fixity: Fixity::Prefix,
            prec: 40,
            entity: "not".try_into().unwrap(),
        },
    ];

    let mut env = Env::get().clone();
    for op in ops {
        env.add_notation(op).unwrap();
    }

    env.add_term_decl(
        "top".try_into().unwrap(),
        TermDecl::Const(DeclConst {
            local_types: vec![],
            ty: mk_prop(),
        }),
    )
    .unwrap();

    env.add_term_decl(
        "not".try_into().unwrap(),
        TermDecl::Const(DeclConst {
            local_types: vec![],
            ty: mk_type_arrow(mk_prop(), mk_prop()),
        }),
    )
    .unwrap();

    env.add_term_decl(
        "and".try_into().unwrap(),
        TermDecl::Const(DeclConst {
            local_types: vec![],
            ty: mk_type_arrow(mk_prop(), mk_type_arrow(mk_prop(), mk_prop())),
        }),
    )
    .unwrap();

    struct Display<'a> {
        env: &'a Env,
        m: Term,
    }

    impl<'a> std::fmt::Display for Display<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            Printer::new(self.env).fmt_term(&self.m, f)
        }
    }

    let roundtrip = |s: &str| -> String {
        let mut lex = Lex::new(s);
        let mut parser = Parser::new(&mut lex, &env, false);
        let m = parser.term().unwrap();
        parser.eof().unwrap();
        Display { env: &env, m }.to_string()
    };

    insta::assert_snapshot!(roundtrip("λ (x : α), x"), @"λ (x : α), x");
    insta::assert_snapshot!(roundtrip("λ (p q r : Prop), p q r"), @"λ (p : Prop), λ (q : Prop), λ (r : Prop), p q r");
    insta::assert_snapshot!(roundtrip("λ (φ ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = (λ (f : Prop → Prop → Prop), f ⊤ ⊤)"), @"λ (φ : Prop), λ (ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = λ (f : Prop → Prop → Prop), f ⊤ ⊤");
    insta::assert_snapshot!(roundtrip("λ (p q : Prop), p = (p ∧ q)"), @"λ (p : Prop), λ (q : Prop), p = (p ∧ q)");
    insta::assert_snapshot!(roundtrip("λ (a b : Prop), (¬a) = b"), @"λ (a : Prop), λ (b : Prop), (¬a) = b");
    insta::assert_snapshot!(roundtrip("λ (a b : Prop), ¬a = b"), @"λ (a : Prop), λ (b : Prop), ¬a = b");
    insta::assert_snapshot!(roundtrip("λ (x : w), eq.{u → v} x"), @"λ (x : w), eq.{u → v} x");
}

pub fn mk_prop() -> Type {
    static PROP: Lazy<Type> = Lazy::new(|| mk_type_const(Name::intern("Prop").unwrap()));
    PROP.clone()
}

fn mk_eq(ty: Type, m1: Term, m2: Term) -> Term {
    let mut m = mk_const(Name::get_unchecked("eq"), vec![ty]);
    m.apply([m1, m2]);
    m
}

#[derive(Debug, Default, Clone)]
struct Env {
    decls: Vec<(Name, Decl)>,
    term_decls: HashMap<Name, usize>,
    type_decls: HashMap<Name, usize>,
    meta_decls: HashMap<Name, usize>,
    notations: NotationTable,
}

#[derive(Debug, Clone)]
pub enum Decl {
    Const(DeclConst),
    Def(DeclDef),
    TypeConst(DeclTypeConst),
    Axiom(DeclAxiom),
    Lemma(DeclLemma),
}

#[derive(Debug, Clone)]
pub struct DeclConst {
    pub local_types: Vec<Name>,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct DeclDef {
    pub local_types: Vec<Name>,
    pub target: Term,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct DeclTypeConst {
    pub kind: Kind,
}

#[derive(Debug, Clone)]
pub struct DeclAxiom {
    pub formula: Term,
}

#[derive(Debug, Clone)]
pub struct DeclLemma {
    pub fact: Fact,
}

#[derive(Debug, Default, Clone)]
struct NotationTable {
    // symbol to name
    tt: TokenTable,
    // name to symbol
    pp: OpTable,
}

#[derive(Debug, Clone)]
enum TermDecl {
    Const(DeclConst),
    Def(DeclDef),
}

#[derive(Debug, Clone)]
enum TypeDecl {
    Const(DeclTypeConst),
}

#[derive(Debug, Clone)]
enum MetaDecl {
    Axiom(DeclAxiom),
    Lemma(DeclLemma),
}

impl From<TermDecl> for Decl {
    fn from(value: TermDecl) -> Self {
        match value {
            TermDecl::Const(d) => Decl::Const(d),
            TermDecl::Def(d) => Decl::Def(d),
        }
    }
}

impl From<TypeDecl> for Decl {
    fn from(value: TypeDecl) -> Self {
        match value {
            TypeDecl::Const(d) => Decl::TypeConst(d),
        }
    }
}

impl From<MetaDecl> for Decl {
    fn from(value: MetaDecl) -> Self {
        match value {
            MetaDecl::Axiom(d) => Decl::Axiom(d),
            MetaDecl::Lemma(d) => Decl::Lemma(d),
        }
    }
}

impl TryFrom<Decl> for TermDecl {
    type Error = ();

    fn try_from(value: Decl) -> Result<Self, Self::Error> {
        match value {
            Decl::Const(d) => Ok(TermDecl::Const(d)),
            Decl::Def(d) => Ok(TermDecl::Def(d)),
            Decl::TypeConst(_) => Err(()),
            Decl::Axiom(_) => Err(()),
            Decl::Lemma(_) => Err(()),
        }
    }
}

impl TryFrom<Decl> for TypeDecl {
    type Error = ();

    fn try_from(value: Decl) -> Result<Self, Self::Error> {
        match value {
            Decl::Const(_) => Err(()),
            Decl::Def(_) => Err(()),
            Decl::TypeConst(d) => Ok(TypeDecl::Const(d)),
            Decl::Axiom(_) => Err(()),
            Decl::Lemma(_) => Err(()),
        }
    }
}

impl TryFrom<Decl> for MetaDecl {
    type Error = ();

    fn try_from(value: Decl) -> Result<Self, Self::Error> {
        match value {
            Decl::Const(_) => Err(()),
            Decl::Def(_) => Err(()),
            Decl::TypeConst(_) => Err(()),
            Decl::Axiom(d) => Ok(MetaDecl::Axiom(d)),
            Decl::Lemma(d) => Ok(MetaDecl::Lemma(d)),
        }
    }
}

static ENV: Lazy<RwLock<Env>> = Lazy::new(|| {
    let mut env = Env::default();

    env.add_type_decl(
        "Prop".try_into().unwrap(),
        TypeDecl::Const(DeclTypeConst { kind: Kind::base() }),
    )
    .unwrap();

    env.add_term_decl(
        "imp".try_into().unwrap(),
        TermDecl::Const(DeclConst {
            local_types: vec![],
            ty: mk_type_arrow(mk_prop(), mk_type_arrow(mk_prop(), mk_prop())),
        }),
    )
    .unwrap();

    env.add_term_decl(
        "forall".try_into().unwrap(),
        TermDecl::Const(DeclConst {
            local_types: vec!["u".try_into().unwrap()],
            ty: mk_type_arrow(
                mk_type_arrow(mk_type_local("u".try_into().unwrap()), mk_prop()),
                mk_prop(),
            ),
        }),
    )
    .unwrap();

    env.add_term_decl(
        "eq".try_into().unwrap(),
        TermDecl::Const(DeclConst {
            local_types: vec!["u".try_into().unwrap()],
            ty: mk_type_arrow(
                mk_type_local("u".try_into().unwrap()),
                mk_type_arrow(mk_type_local("u".try_into().unwrap()), mk_prop()),
            ),
        }),
    )
    .unwrap();

    env.add_notation(Operator {
        symbol: "→".to_owned(),
        fixity: Fixity::Infixr,
        prec: 25,
        entity: "imp".try_into().unwrap(),
    })
    .unwrap();
    env.add_notation(Operator {
        symbol: "=".to_owned(),
        fixity: Fixity::Infix,
        prec: 50,
        entity: "eq".try_into().unwrap(),
    })
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

    fn op_table(&self) -> &OpTable {
        &self.notations.pp
    }

    fn add_type_decl(&mut self, name: Name, decl: TypeDecl) -> anyhow::Result<()> {
        let index = self.decls.len();
        if self.type_decls.insert(name, index).is_some() {
            bail!("type declaration with given name already defined");
        }
        self.decls.push((name, decl.into()));
        Ok(())
    }

    fn add_term_decl(&mut self, name: Name, decl: TermDecl) -> anyhow::Result<()> {
        let index = self.decls.len();
        if self.term_decls.insert(name, index).is_some() {
            bail!("declaration with given name already defined");
        }
        self.decls.push((name, decl.into()));
        Ok(())
    }

    fn add_meta_decl(&mut self, name: Name, decl: MetaDecl) -> anyhow::Result<()> {
        let index = self.decls.len();
        if self.meta_decls.insert(name, index).is_some() {
            bail!("meta declaration with given name already defined");
        }
        self.decls.push((name, decl.into()));
        Ok(())
    }

    fn get_type_decl(&self, name: Name) -> Option<TypeDecl> {
        let &index = self.type_decls.get(&name)?;
        Some(self.decls[index].1.clone().try_into().unwrap())
    }

    fn get_term_decl(&self, name: Name) -> Option<TermDecl> {
        let &index = self.term_decls.get(&name)?;
        Some(self.decls[index].1.clone().try_into().unwrap())
    }

    fn get_term_decl_index(&self, name: Name) -> Option<(usize, TermDecl)> {
        let &index = self.term_decls.get(&name)?;
        Some((index, self.decls[index].1.clone().try_into().unwrap()))
    }

    fn get_meta_decl(&self, name: Name) -> Option<MetaDecl> {
        let &index = self.meta_decls.get(&name)?;
        Some(self.decls[index].1.clone().try_into().unwrap())
    }

    fn add_notation(&mut self, op: Operator) -> anyhow::Result<()> {
        self.notations.tt.add(op.clone())?;
        self.notations.pp.add(op)?;
        Ok(())
    }

    fn get_kind(&self, name: Name) -> Option<Kind> {
        let decl = self.get_type_decl(name)?;
        match decl {
            TypeDecl::Const(DeclTypeConst { kind }) => Some(kind),
        }
    }

    fn get_type(&self, name: Name) -> Option<(Vec<Name>, Type)> {
        let decl = self.get_term_decl(name)?;
        match decl {
            TermDecl::Const(DeclConst { local_types, ty }) => Some((local_types, ty)),
            TermDecl::Def(DeclDef {
                local_types,
                target: _,
                ty,
            }) => Some((local_types, ty)),
        }
    }
}

pub fn add_notation(symbol: &str, fixity: Fixity, prec: usize, entity: &str) -> anyhow::Result<()> {
    let Ok(entity) = Name::try_from(entity) else {
        bail!("invalid name: {entity}");
    };
    Env::get_mut().add_notation(Operator {
        symbol: symbol.to_owned(),
        fixity,
        prec,
        entity,
    })
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
    Env::get_mut().add_term_decl(name, TermDecl::Const(DeclConst { local_types, ty }))
}

pub fn add_const_type(name: Name, kind: Kind) -> anyhow::Result<()> {
    Env::get_mut().add_type_decl(name, TypeDecl::Const(DeclTypeConst { kind }))
}

pub fn add_axiom(name: Name, mut p: Term) -> anyhow::Result<()> {
    p.infer(&mut mk_prop())?;
    if !p.is_closed() {
        bail!("formula not closed");
    }
    Env::get_mut().add_meta_decl(name, MetaDecl::Axiom(DeclAxiom { formula: p }))
}

pub fn add_lemma(name: Name, fact: Fact) -> anyhow::Result<()> {
    if !fact.context().is_empty() {
        bail!("local context is not empty");
    }
    if !fact.target().is_closed() {
        bail!("formula not closed");
    }
    Env::get_mut().add_meta_decl(name, MetaDecl::Lemma(DeclLemma { fact }))
}

pub fn add_definition(name: Name, local_types: Vec<Name>, mut target: Term) -> anyhow::Result<()> {
    for i in 0..local_types.len() {
        for j in i + 1..local_types.len() {
            if local_types[i] == local_types[j] {
                bail!("duplicate type variables");
            }
        }
    }
    let mut ty = mk_fresh_type_mvar();
    target.infer_under(&mut ty, local_types.as_slice())?;
    if !target.is_closed() {
        bail!("term not closed");
    }
    Env::get_mut().add_term_decl(
        name,
        TermDecl::Def(DeclDef {
            local_types,
            target,
            ty,
        }),
    )
}

fn get_kind(name: Name) -> Option<Kind> {
    Env::get().get_kind(name)
}

fn get_type(name: Name) -> Option<(Vec<Name>, Type)> {
    Env::get().get_type(name)
}

fn get_def(name: Name) -> Option<DeclDef> {
    let decl = Env::get().get_term_decl(name)?;
    match decl {
        TermDecl::Const(_) => None,
        TermDecl::Def(decl_def) => Some(decl_def),
    }
}

fn get_def_index(name: Name) -> Option<usize> {
    let (index, decl) = Env::get().get_term_decl_index(name)?;
    match decl {
        TermDecl::Const(_) => None,
        TermDecl::Def(_) => Some(index),
    }
}

// TODO return also type parameters?
pub fn get_fact(name: Name) -> Option<Fact> {
    let decl = Env::get().get_meta_decl(name)?;
    match decl {
        MetaDecl::Axiom(DeclAxiom { formula }) => Some(Fact {
            context: vec![],
            target: formula,
        }),
        MetaDecl::Lemma(DeclLemma { fact }) => Some(fact),
    }
}

pub fn get_decls() -> Vec<(Name, Decl)> {
    Env::get().decls.clone()
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Fact {
    context: Vec<Term>,
    target: Term,
}

impl Display for Fact {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for p in &self.context {
            write!(f, "({}) ", p)?;
        }
        write!(f, "⊢ {}", self.target)
    }
}

impl Fact {
    pub fn target(&self) -> &Term {
        &self.target
    }

    pub fn context(&self) -> &Vec<Term> {
        &self.context
    }
}

static IMP: Lazy<Name> = Lazy::new(|| Name::intern("imp").unwrap());
static FORALL: Lazy<Name> = Lazy::new(|| Name::intern("forall").unwrap());
static EQ: Lazy<Name> = Lazy::new(|| Name::intern("eq").unwrap());

fn dest_eq(mut m: Term) -> anyhow::Result<(Type, Term, Term)> {
    if m.binders().count() != 0 {
        bail!("expected equality");
    }
    let Term::Const(inner) = m.head() else {
        bail!("expected equality");
    };
    if inner.name != *EQ {
        bail!("expected equality");
    }
    if inner.ty_args.len() != 1 {
        bail!("expected equality");
    }
    if m.args().len() != 2 {
        bail!("expected equality");
    }
    m.undischarge();
    let mut args = m.unapply();
    let Term::Const(mut inner) = m else {
        unreachable!();
    };
    let ty = Arc::make_mut(&mut inner).ty_args.pop().unwrap();
    let m2 = args.pop().unwrap();
    let m1 = args.pop().unwrap();
    Ok((ty, m1, m2))
}

/// ```text
///
/// ------------------
/// assume φ : [φ ⊢ φ]
/// ```
pub fn assume(mut target: Term) -> anyhow::Result<Fact> {
    target.infer(&mut mk_prop())?;
    Ok(Fact {
        context: vec![target.clone()],
        target,
    })
}

#[test]
fn test_assume_ok() {
    // terms may contain local variables
    let p = mk_local("p".try_into().unwrap(), mk_prop());
    insta::assert_display_snapshot!(assume(p).unwrap(), @"((p : Prop)) ⊢ (p : Prop)");

    // infer as Prop
    let p = q!("p");
    insta::assert_display_snapshot!(assume(p).unwrap(), @"((p : Prop)) ⊢ (p : Prop)");

    // terms may contain type variables
    let p: Term = q!("(λ (x : α), x) = (λ x, x)");
    insta::assert_display_snapshot!(assume(p).unwrap(), @"((λ (x : α), x) = λ (x : α), x) ⊢ (λ (x : α), x) = λ (x : α), x");
}

#[test]
fn test_assume_err() {
    // not a proposition
    let p = mk_local("p".try_into().unwrap(), mk_type_arrow(mk_prop(), mk_prop()));
    insta::assert_display_snapshot!(assume(p).unwrap_err(), @"type mismatch");

    // ill-typed
    let p = q!("(λ (x : Prop), x) (λ y, y)");
    insta::assert_display_snapshot!(assume(p).unwrap_err(), @"type mismatch");

    // not fully instantiated
    let f = q!("(λ x, x) = (λ x, x)");
    insta::assert_display_snapshot!(assume(f).unwrap_err(), @"uninstantiated meta type variable");
}

/// ```text
/// h : [Φ ⊢ ψ]
/// ---------------------------------
/// imp_intro φ h : [Φ - {φ} ⊢ φ → ψ]
/// ```
pub fn imp_intro(mut p: Term, h: Fact) -> anyhow::Result<Fact> {
    p.infer(&mut mk_prop())?;
    let mut context: Vec<_> = h.context.into_iter().filter(|q| &p != q).collect();
    context.sort();
    context.dedup();
    let mut target = mk_const(*IMP, vec![]);
    target.apply([p, h.target]);
    Ok(Fact { context, target })
}

/// ```text
/// h₁ : [Φ ⊢ φ → ψ]  h₂ : [Ψ ⊢ φ]
/// -------------------------------
/// imp_elim h₁ h₂ : [Φ ∪ Ψ ⊢ ψ]
/// ```
pub fn imp_elim(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let mut imp = h1.target;
    let mut args = imp.unapply();
    let Term::Const(inner) = imp else {
        bail!("not an implication");
    };
    if inner.name != *IMP {
        bail!("not an implication");
    }
    if args.len() != 2 {
        bail!("not an implication");
    }
    let target = args.pop().unwrap();
    let p = args.pop().unwrap();
    if p != h2.target {
        bail!("argument mismatch");
    }
    let mut context = h1.context;
    context.extend(h2.context);
    context.sort();
    context.dedup();
    Ok(Fact { context, target })
}

#[test]
fn test_imp_ok() {
    let p: Term = q!("p");
    let h = assume(p.clone()).unwrap();
    insta::assert_display_snapshot!(imp_intro(p, h).unwrap(), @"⊢ (p : Prop) → (p : Prop)");

    // weakening
    let p: Term = q!("p");
    insta::assert_display_snapshot!(imp_intro(p, reflexivity(mk_const(*IMP, vec![])).unwrap()).unwrap(), @"⊢ (p : Prop) → imp = imp");

    let h1 = assume(q!("p → q")).unwrap();
    let h2 = assume(q!("p")).unwrap();
    insta::assert_display_snapshot!(imp_elim(h1, h2).unwrap(), @"((p : Prop) → (q : Prop)) ((p : Prop)) ⊢ (q : Prop)");
}

#[test]
fn test_imp_err() {
    insta::assert_display_snapshot!(imp_intro(q!("(λ (x : Prop), x) (λ (x : Prop), x)"), assume(q!("p")).unwrap()).unwrap_err(), @"type mismatch");
    insta::assert_display_snapshot!(imp_intro(q!("p q"), assume(q!("p")).unwrap()).unwrap_err(), @"uninstantiated meta type variable");

    let h1 = assume(q!("p")).unwrap();
    let h2 = assume(q!("p")).unwrap();
    insta::assert_display_snapshot!(imp_elim(h1, h2).unwrap_err(), @"not an implication");
}

/// ```text
/// h : [Φ ⊢ φ]
/// --------------------------------------- ((x : τ) # Φ)
/// forall_intro x τ h : [Φ ⊢ ∀ (x : τ), φ]
/// ```
pub fn forall_intro(x: Name, t: Type, h: Fact) -> anyhow::Result<Fact> {
    t.check_kind(&Kind::base())?;
    if !h.context.iter().all(|m| m.is_fresh(x, &t)) {
        bail!("eigenvariable condition fails");
    }
    let mut m = h.target;
    m.discharge_local(x, t.clone());
    let mut target = mk_const(*FORALL, vec![t]);
    target.apply([m]);
    Ok(Fact {
        context: h.context,
        target,
    })
}

/// ```text
/// h : [Φ ⊢ ∀ (x : τ), φ]
/// ------------------------------
/// forall_elim m h : [Φ ⊢ [m/x]φ]
/// ```
pub fn forall_elim(mut m: Term, h: Fact) -> anyhow::Result<Fact> {
    let mut forall = h.target;
    let mut args = forall.unapply();
    let Term::Const(mut inner) = forall else {
        bail!("not a forall");
    };
    if inner.name != *FORALL {
        bail!("not a forall");
    }
    let mut domain_ty = Arc::make_mut(&mut inner).ty_args.pop().unwrap();
    if args.len() != 1 {
        bail!("not a forall");
    }
    let arg = args.pop().unwrap();
    let Term::Abs(mut inner) = arg else {
        bail!("forall must take an abstraction");
    };
    let mut target = mem::take(&mut Arc::make_mut(&mut inner).body);
    m.infer(&mut domain_ty)?;
    target.open(&m);
    Ok(Fact {
        context: h.context,
        target,
    })
}

#[test]
fn test_forall() {
    // err
    let p: Term = q!("p");
    let h = assume(p.clone()).unwrap();
    insta::assert_display_snapshot!(forall_intro("p".try_into().unwrap(), mk_prop(), h).unwrap_err(), @"eigenvariable condition fails");

    let p: Term = q!("p");
    let h = assume(p.clone()).unwrap();
    let h = imp_intro(p, h).unwrap();
    insta::assert_display_snapshot!(forall_intro("p".try_into().unwrap(), mk_prop(), h).unwrap(), @"⊢ ∀ (p : Prop), p → p");

    // weakening
    let h = reflexivity(q!("imp")).unwrap();
    insta::assert_display_snapshot!(forall_intro("p".try_into().unwrap(), mk_prop(), h).unwrap(), @"⊢ ∀ (p : Prop), imp = imp");

    let p: Term = q!("p");
    let h = assume(p.clone()).unwrap();
    let h = imp_intro(p, h).unwrap();
    let h = forall_intro("p".try_into().unwrap(), mk_prop(), h).unwrap();
    insta::assert_display_snapshot!(forall_elim(q!("q"), h).unwrap(), @"⊢ (q : Prop) → (q : Prop)");
}

/// ```text
///
/// -------------------------
/// reflexivity m : [⊢ m = m]
/// ```
pub fn reflexivity(mut m: Term) -> anyhow::Result<Fact> {
    let mut ty = mk_fresh_type_mvar();
    m.infer(&mut ty)?;
    let mut target = mk_const(*EQ, vec![ty]);
    target.apply([m.clone(), m]);
    Ok(Fact {
        context: vec![],
        target,
    })
}

/// ```text
/// h : [Φ ⊢ m₁ = m₂]
/// --------------------------
/// symmetry h : [Φ ⊢ m₂ = m₁]
/// ```
pub fn symmetry(h: Fact) -> anyhow::Result<Fact> {
    let (ty, m1, m2) = dest_eq(h.target)?;
    let mut target = mk_const(*EQ, vec![ty]);
    target.apply([m2, m1]);
    Ok(Fact {
        context: h.context,
        target,
    })
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ m₂ = m₃]
/// --------------------------------------
/// transitivity h₁ h₂ : [Φ ⊢ m₁ = m₃]
/// ```
pub fn transitivity(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let (ty, m1, m2) = dest_eq(h1.target)?;
    let (_, m3, m4) = dest_eq(h2.target)?;
    if m2 != m3 {
        bail!("transitivity mismatch");
    }
    let mut target = mk_const(*EQ, vec![ty]);
    target.apply([m1, m4]);
    let mut context = h1.context;
    context.extend(h2.context);
    context.sort();
    context.dedup();
    Ok(Fact { context, target })
}

/// ```text
///
/// -------------------------------- (m ≡ (λ x, m₁) m₂)
/// beta_reduce m : [⊢ m = [m₂/x]m₁]
/// ```
pub fn beta_reduce(mut m: Term) -> anyhow::Result<Fact> {
    let mut ty = mk_fresh_type_mvar();
    m.infer(&mut ty)?;
    let Term::App(inner) = &m else {
        bail!("not a beta redex");
    };
    let arg = &inner.arg;
    let Term::Abs(inner) = &inner.fun else {
        bail!("not a beta redex");
    };
    let mut n = inner.body.clone();
    n.open(arg);
    Ok(Fact {
        context: vec![],
        target: mk_eq(ty, m, n),
    })
}

/// ```text
///
/// --------------------------------- (m : u → v)
/// eta_expand m : [⊢ m = (λ x, m x)]
/// ```
pub fn eta_expand(mut m: Term) -> anyhow::Result<Fact> {
    let mut ty = mk_fresh_type_mvar();
    m.infer(&mut ty)?;
    let Type::Arrow(inner) = &ty else {
        bail!("not a function");
    };
    let dom_ty = inner.dom.clone();
    let mut n = m.clone();
    let x = Name::fresh();
    n.apply([mk_local(x, dom_ty.clone())]);
    n.discharge([(x, dom_ty)]);
    Ok(Fact {
        context: vec![],
        target: mk_eq(ty, m, n),
    })
}

/// ```text
///
/// -------------------------- (c := m)
/// delta_reduce c : [⊢ c = m]
/// ```
pub fn delta_reduce(name: Name) -> anyhow::Result<Fact> {
    let Some(def) = get_def(name) else {
        bail!("definition not found: {name}");
    };
    let DeclDef {
        local_types,
        target,
        ty,
    } = def;
    let mut ty_args = vec![];
    for x in local_types {
        ty_args.push(mk_type_local(x));
    }
    let m = mk_const(name, ty_args);
    Ok(Fact {
        context: vec![],
        target: mk_eq(ty, m, target),
    })
}

/// ```text
/// h₁ : [Φ ⊢ f₁ = f₂]  h₂ : [Ψ ⊢ a₁ = a₂]
/// -----------------------------------------
/// congr_app h₁ h₂ : [Φ ∪ Ψ ⊢ f₁ a₁ = f₂ a₂]
/// ```
pub fn congr_app(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let (t1, f1, f2) = dest_eq(h1.target)?;
    let (t2, a1, a2) = dest_eq(h2.target)?;
    let Type::Arrow(inner) = &t1 else {
        bail!("not a function");
    };
    if inner.dom != t2 {
        bail!("type mismatch");
    }
    let mut m1 = f1;
    let mut m2 = f2;
    m1.apply([a1]);
    m2.apply([a2]);
    let mut context = h1.context;
    context.extend(h2.context);
    context.sort();
    context.dedup();
    Ok(Fact {
        context,
        target: mk_eq(inner.cod.clone(), m1, m2),
    })
}

/// ```text
/// h : [Φ ⊢ m₁ = m₂]
/// ------------------------------------------------------- ((x : τ) # (Φ, m₁, m₂))
/// congr_abs τ h : [Φ ⊢ (λ (x : τ), m₁) = (λ (x : τ), m₂)]
/// ```
pub fn congr_abs(t: Type, h: Fact) -> anyhow::Result<Fact> {
    let (ty, mut m1, mut m2) = dest_eq(h.target)?;
    let x = Name::fresh();
    m1.discharge([(x, t.clone())]);
    m2.discharge([(x, t.clone())]);
    Ok(Fact {
        context: h.context,
        target: mk_eq(mk_type_arrow(t, ty), m1, m2),
    })
}

/// ```text
/// h₁ : [Φ ⊢ φ = ψ]  h₂ : [Ψ ⊢ φ]
/// ------------------------------
/// transport h₁ h₂ : [Φ ∪ Ψ ⊢ ψ]
/// ```
pub fn transport(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let (ty, p1, p2) = dest_eq(h1.target)?;
    if ty != mk_prop() {
        bail!("not a propositional equality");
    }
    if h2.target != p1 {
        bail!("proposition mismatch");
    }
    let mut context = h1.context;
    context.extend(h2.context);
    context.sort();
    context.dedup();
    Ok(Fact {
        context,
        target: p2,
    })
}

/// ```text
/// h : [Φ ⊢ φ]
/// ------------------------------
/// inst u τ h : [[τ/u]Φ ⊢ [τ/u]φ]
/// ```
pub fn inst(name: Name, ty: &Type, mut h: Fact) -> anyhow::Result<Fact> {
    ty.check_kind(&Kind::base())?;
    for p in &mut h.context {
        p.instantiate_local(name, ty);
    }
    h.target.instantiate_local(name, ty);
    Ok(h)
}

// TODO remove
pub fn eq_elim_old(c: Term, h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    if !c.is_body() {
        bail!("expected context, but got {c}");
    }
    let (_, m1, m2) = dest_eq(h1.target)?;
    let mut cm1 = c.clone();
    cm1.open(&m1);
    cm1.infer(&mut mk_prop())?;
    if h2.target != cm1 {
        bail!("terms not literally equal: {} and {}", h2.target, cm1);
    }
    let mut ctx: Vec<_> = h1
        .context
        .into_iter()
        .chain(h2.context.into_iter())
        .collect();
    ctx.sort();
    ctx.dedup();
    let mut target = c;
    target.open(&m2);
    target.infer(&mut mk_prop()).expect("logic flaw");
    Ok(Fact {
        context: ctx,
        target,
    })
}

// TODO remove
/// ```text
/// h : [Φ ⊢ φ]
/// -------------------- (φ ≡ ψ)
/// change ψ h : [Φ ⊢ ψ]
/// ```
pub fn change(mut target: Term, h: Fact) -> anyhow::Result<Fact> {
    target.infer(&mut mk_prop())?;
    if !target.equiv(&h.target) {
        bail!("terms not definitionally equal: {} and {target}", h.target);
    }
    Ok(Fact {
        context: h.context,
        target,
    })
}
