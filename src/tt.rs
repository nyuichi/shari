use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::iter::zip;
use std::sync::atomic::AtomicUsize;
use std::sync::{Arc, LazyLock, Mutex, Weak};
use std::vec;

use crate::{lex::Span, proof::mk_type_prop};

#[derive(Debug, Clone, Ord, PartialOrd, Default)]
pub struct Name(Arc<String>);

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash, Default)]
pub struct Path(Option<QualifiedName>);

// TODO: parseの中でrelative pathを処理するためにこの型が使われているが、この型はabsolute pathを表すものなので、parseの中で専用の型を使うべき。
#[derive(Debug, Clone, Ord, PartialOrd, Default)]
pub struct QualifiedName(Arc<QualifiedNameInner>);

#[derive(Debug, Clone, PartialEq, Eq, Ord, Hash, PartialOrd, Default)]
struct QualifiedNameInner {
    path: Path,
    name: Name,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Id(usize);

static NAME_TABLE: LazyLock<Mutex<HashMap<String, Weak<String>>>> = LazyLock::new(Default::default);
static QUALIFIED_NAME_TABLE: LazyLock<
    Mutex<HashMap<QualifiedNameInner, Weak<QualifiedNameInner>>>,
> = LazyLock::new(Default::default);

static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);
static ID_NAME_TABLE: LazyLock<Mutex<HashMap<Name, Id>>> = LazyLock::new(Default::default);
static ID_NAME_REV_TABLE: LazyLock<Mutex<HashMap<Id, Name>>> = LazyLock::new(Default::default);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Name {
    pub fn from_str(value: &str) -> Name {
        let mut table = NAME_TABLE.lock().unwrap();
        if let Some(existing) = table.get(value).and_then(|weak| weak.upgrade()) {
            return Name(existing);
        }

        let owned = Arc::new(value.to_owned());
        table.insert(value.to_owned(), Arc::downgrade(&owned));
        Name(owned)
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl PartialEq for Name {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Name {}

impl Hash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}

// TODO: .始まりの完全修飾で表示するようにする。QualifiedNameも同様。
impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names = self.names();
        if names.is_empty() {
            return Ok(());
        }
        write!(f, "{}", names[0])?;
        for name in &names[1..] {
            write!(f, ".{name}")?;
        }
        Ok(())
    }
}

impl Path {
    pub fn root() -> Path {
        Path(None)
    }

    // TODO: qualified_nameにリネーム
    pub fn as_qualified_name(&self) -> Option<&QualifiedName> {
        self.0.as_ref()
    }

    // TODO: from_qualified_name(QualifiedName) -> Pathを作ってこのメソッドは消す
    pub fn from_parts(parent: Path, name: Name) -> Path {
        Path(Some(QualifiedName::from_parts(parent, name)))
    }

    // TODO: 消す
    pub fn name(&self) -> Option<&Name> {
        self.0.as_ref().map(QualifiedName::name)
    }

    // TODO: 消す
    pub fn parent(&self) -> Option<&Path> {
        self.0.as_ref().map(QualifiedName::path)
    }

    // TODO: 消す
    pub fn to_parts(&self) -> Option<(&Path, &Name)> {
        self.0
            .as_ref()
            .map(|qualified_name| (qualified_name.path(), qualified_name.name()))
    }

    // TODO: 消す
    pub fn names(&self) -> Vec<Name> {
        self.0.as_ref().map_or_else(Vec::new, QualifiedName::names)
    }

    // TODO: 消す
    pub fn append(&self, suffix: &Path) -> Path {
        let mut path = self.clone();
        for name in suffix.names() {
            path = Path::from_parts(path, name);
        }
        path
    }

    // TODO: suffixはNameにする
    pub fn extend(&self, suffix: impl AsRef<str>) -> Path {
        let name = Name::from_str(suffix.as_ref());
        Path::from_parts(self.clone(), name)
    }
}

impl Display for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names = self.names();
        if names.is_empty() {
            return Ok(());
        }
        write!(f, "{}", names[0])?;
        for name in &names[1..] {
            write!(f, ".{name}")?;
        }
        Ok(())
    }
}

impl QualifiedName {
    pub fn from_parts(path: Path, name: Name) -> QualifiedName {
        let value = QualifiedNameInner { path, name };

        let mut table = QUALIFIED_NAME_TABLE.lock().unwrap();
        if let Some(existing) = table.get(&value).and_then(|weak| weak.upgrade()) {
            return QualifiedName(existing);
        }

        let owned = Arc::new(value.clone());
        table.insert(value, Arc::downgrade(&owned));
        QualifiedName(owned)
    }

    // TODO: これは消して Path::root().extend(Name::from(value)) に置き換えたい。ただ、parseでQualifiedNameを相対パス名にも流用しているせいで相対パスの作成にも使ってしまっているので、型の分離が終わってから着手する。
    pub fn from_str(value: &str) -> QualifiedName {
        Self::from_parts(Path::root(), Name::from_str(value))
    }

    pub fn name(&self) -> &Name {
        &self.0.name
    }

    pub fn path(&self) -> &Path {
        &self.0.path
    }

    // TODO: parse専用の型ができたら消す
    pub fn prefix(&self) -> Option<QualifiedName> {
        let name = self.path().name()?.clone();
        let parent = self.path().parent().cloned().unwrap_or_else(Path::root);
        Some(QualifiedName::from_parts(parent, name))
    }

    // TODO: parse専用の型ができたら消す
    pub fn names(&self) -> Vec<Name> {
        let mut names = vec![];
        names.extend(self.path().names());
        names.push(self.name().clone());
        names
    }

    pub fn to_path(&self) -> Path {
        self.path().extend(self.name().as_str())
    }

    // TODO: 消す
    pub fn append(&self, suffix: &QualifiedName) -> QualifiedName {
        let path = self.to_path().append(suffix.path());
        Self::from_parts(path, suffix.name().clone())
    }

    // TODO: このメソッドは消してself.to_path().extend(suffix)に置き換える
    pub fn extend(&self, suffix: impl AsRef<str>) -> QualifiedName {
        let name = Name::from_str(suffix.as_ref());
        Self::from_parts(self.to_path(), name)
    }
}

impl PartialEq for QualifiedName {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for QualifiedName {}

impl Hash for QualifiedName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}

impl Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = self.name() {
            if self.is_generated() {
                return write!(f, "{}{}", name, self.0);
            }
            return write!(f, "{}", name);
        }
        write!(f, "{}", self.0)
    }
}

impl Id {
    pub fn fresh() -> Self {
        let id = ID_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Id(id)
    }

    pub fn fresh_with_name(name: Name) -> Self {
        let new_id = Id::fresh();
        ID_NAME_REV_TABLE.lock().unwrap().insert(new_id, name);
        new_id
    }

    pub fn from_name(name: &Name) -> Id {
        let mut id_table = ID_NAME_TABLE.lock().unwrap();
        if let Some(&id) = id_table.get(name) {
            return id;
        }

        let id = Id::fresh();
        id_table.insert(name.clone(), id);
        drop(id_table);
        // This can be put here outside the critical section of ID_NAME_TABLE
        // because no one but this function knows of the value of `id`.
        ID_NAME_REV_TABLE.lock().unwrap().insert(id, name.clone());
        id
    }

    pub fn name(&self) -> Option<Name> {
        ID_NAME_REV_TABLE.lock().unwrap().get(self).cloned()
    }

    pub fn is_generated(&self) -> bool {
        if let Some(name) = self.name() {
            let Some(&id) = ID_NAME_TABLE.lock().unwrap().get(&name) else {
                return true;
            };
            return id != *self;
        }
        true
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

#[derive(Clone, Debug, Default)]
pub struct TypeMetadata {
    pub span: Option<Span>,
}

impl PartialEq for TypeMetadata {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for TypeMetadata {}

impl PartialOrd for TypeMetadata {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TypeMetadata {
    fn cmp(&self, _: &Self) -> Ordering {
        Ordering::Equal
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub enum Type {
    Const(Arc<TypeConst>),
    Arrow(Arc<TypeArrow>),
    App(Arc<TypeApp>),
    Local(Arc<TypeLocal>),
    Hole(Arc<TypeHole>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeConst {
    pub metadata: TypeMetadata,
    pub name: QualifiedName,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeArrow {
    pub metadata: TypeMetadata,
    pub dom: Type,
    pub cod: Type,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeApp {
    pub metadata: TypeMetadata,
    pub fun: Type,
    pub arg: Type,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeLocal {
    pub metadata: TypeMetadata,
    pub id: Id,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct TypeHole {
    pub metadata: TypeMetadata,
    pub id: Id,
}

impl Default for Type {
    fn default() -> Self {
        mk_type_hole(Id::default())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const TYPE_PREC_ARROW: u8 = 0;
        const TYPE_PREC_APP: u8 = 1;
        const TYPE_PREC_ATOM: u8 = 2;

        fn fmt_type(ty: &Type, f: &mut std::fmt::Formatter<'_>, prec: u8) -> std::fmt::Result {
            match ty {
                Type::Const(inner) => write!(f, "{}", inner.name),
                Type::Arrow(inner) => {
                    let needs_paren = prec > TYPE_PREC_ARROW;
                    if needs_paren {
                        write!(f, "(")?;
                    }
                    fmt_type(&inner.dom, f, TYPE_PREC_APP)?;
                    write!(f, " → ")?;
                    fmt_type(&inner.cod, f, TYPE_PREC_ARROW)?;
                    if needs_paren {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
                Type::App(inner) => {
                    let needs_paren = prec > TYPE_PREC_APP;
                    if needs_paren {
                        write!(f, "(")?;
                    }
                    fmt_type(&inner.fun, f, TYPE_PREC_APP)?;
                    write!(f, " ")?;
                    fmt_type(&inner.arg, f, TYPE_PREC_ATOM)?;
                    if needs_paren {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
                Type::Local(inner) => write!(f, "${}", inner.id),
                Type::Hole(inner) => write!(f, "?{}", inner.id),
            }
        }

        fmt_type(self, f, TYPE_PREC_ARROW)
    }
}

#[inline]
pub fn mk_type_arrow(dom: Type, cod: Type) -> Type {
    Type::Arrow(Arc::new(TypeArrow {
        metadata: TypeMetadata::default(),
        dom,
        cod,
    }))
}

#[inline]
pub fn mk_fresh_type_hole() -> Type {
    mk_type_hole(Id::fresh())
}

#[inline]
pub fn mk_type_hole(id: Id) -> Type {
    Type::Hole(Arc::new(TypeHole {
        metadata: TypeMetadata::default(),
        id,
    }))
}

#[inline]
pub fn mk_type_local(id: Id) -> Type {
    Type::Local(Arc::new(TypeLocal {
        metadata: TypeMetadata::default(),
        id,
    }))
}

#[inline]
pub fn mk_type_const(name: QualifiedName) -> Type {
    Type::Const(Arc::new(TypeConst {
        metadata: TypeMetadata::default(),
        name,
    }))
}

#[inline]
pub fn mk_type_app(fun: Type, arg: Type) -> Type {
    Type::App(Arc::new(TypeApp {
        metadata: TypeMetadata::default(),
        fun,
        arg,
    }))
}

/// See [Barendregt+, 06](https://ftp.science.ru.nl/CSI/CompMath.Found/I.pdf).
impl Type {
    pub fn metadata(&self) -> &TypeMetadata {
        match self {
            Type::Const(inner) => &inner.metadata,
            Type::Arrow(inner) => &inner.metadata,
            Type::App(inner) => &inner.metadata,
            Type::Local(inner) => &inner.metadata,
            Type::Hole(inner) => &inner.metadata,
        }
    }

    pub fn span(&self) -> Option<&Span> {
        self.metadata().span.as_ref()
    }

    pub fn with_span(self, span: Option<Span>) -> Type {
        match self {
            Type::Const(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Type::Const(Arc::new(inner))
            }
            Type::Arrow(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Type::Arrow(Arc::new(inner))
            }
            Type::App(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Type::App(Arc::new(inner))
            }
            Type::Local(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Type::Local(Arc::new(inner))
            }
            Type::Hole(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Type::Hole(Arc::new(inner))
            }
        }
    }

    /// t.arrow([t1, t2]) // => t1 → t2 → t
    pub fn arrow(&self, cs: impl IntoIterator<Item = Type>) -> Type {
        let mut cod = self.clone();
        let domains: Vec<Type> = cs.into_iter().collect(); // TODO: avoid calling collect
        for dom in domains.into_iter().rev() {
            cod = mk_type_arrow(dom, cod);
        }
        cod
    }

    /// Splits self into domains and the terminal codomain.
    pub fn unarrow(&self) -> (Vec<Type>, Type) {
        let mut doms = Vec::new();
        let mut current = self;
        while let Type::Arrow(inner) = current {
            doms.push(inner.dom.clone());
            current = &inner.cod;
        }
        (doms, current.clone())
    }

    pub fn components(&self) -> Vec<&Type> {
        let mut cs = vec![];
        let mut t = self;
        while let Type::Arrow(inner) = t {
            cs.push(&inner.dom);
            t = &inner.cod;
        }
        cs
    }

    pub fn apply(&self, args: impl IntoIterator<Item = Type>) -> Type {
        let mut fun = self.clone();
        for arg in args {
            fun = mk_type_app(fun, arg);
        }
        fun
    }

    /// Simultaneously substitute `t₁ ⋯ tₙ` for locals with names `x₁ ⋯ xₙ`.
    pub fn subst(&self, subst: &[(Id, Type)]) -> Type {
        match self {
            Type::Const(_) => self.clone(),
            Type::Local(x) => {
                let id = &x.id;
                subst
                    .iter()
                    .find(|(y, _)| y == id)
                    .map(|(_, t)| t.clone())
                    .unwrap_or_else(|| self.clone())
            }
            Type::Hole(_) => self.clone(),
            Type::Arrow(inner) => {
                let dom = inner.dom.subst(subst);
                let cod = inner.cod.subst(subst);
                if inner.dom.ptr_eq(&dom) && inner.cod.ptr_eq(&cod) {
                    self.clone()
                } else {
                    mk_type_arrow(dom, cod)
                }
            }
            Type::App(inner) => {
                let fun = inner.fun.subst(subst);
                let arg = inner.arg.subst(subst);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_type_app(fun, arg)
                }
            }
        }
    }

    /// Returns [true] if [self] contains no meta variables.
    pub fn is_ground(&self) -> bool {
        match self {
            Type::Const(_) => true,
            Type::Arrow(inner) => inner.dom.is_ground() && inner.cod.is_ground(),
            Type::App(inner) => inner.fun.is_ground() && inner.arg.is_ground(),
            Type::Local(_) => true,
            Type::Hole(_) => false,
        }
    }

    pub fn contains_local(&self, id: Id) -> bool {
        match self {
            Type::Const(_) => false,
            Type::Arrow(t) => t.dom.contains_local(id) || t.cod.contains_local(id),
            Type::App(t) => t.fun.contains_local(id) || t.arg.contains_local(id),
            Type::Local(t) => t.id == id,
            Type::Hole(_) => false,
        }
    }

    pub fn contains_hole(&self, hole_id: Id) -> bool {
        match self {
            Type::Const(_) => false,
            Type::Arrow(t) => t.dom.contains_hole(hole_id) || t.cod.contains_hole(hole_id),
            Type::App(t) => t.fun.contains_hole(hole_id) || t.arg.contains_hole(hole_id),
            Type::Local(_) => false,
            Type::Hole(n) => n.id == hole_id,
        }
    }

    pub fn replace_hole(&self, f: &impl Fn(Id) -> Option<Type>) -> Type {
        match self {
            Type::Const(_) => self.clone(),
            Type::Arrow(inner) => {
                let dom = inner.dom.replace_hole(f);
                let cod = inner.cod.replace_hole(f);
                if inner.dom.ptr_eq(&dom) && inner.cod.ptr_eq(&cod) {
                    self.clone()
                } else {
                    mk_type_arrow(dom, cod)
                }
            }
            Type::App(inner) => {
                let fun = inner.fun.replace_hole(f);
                let arg = inner.arg.replace_hole(f);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_type_app(fun, arg)
                }
            }
            Type::Local(_) => self.clone(),
            Type::Hole(hole) => {
                let hole_id = hole.id;
                if let Some(replacement) = f(hole_id) {
                    replacement.replace_hole(f)
                } else {
                    self.clone()
                }
            }
        }
    }

    pub fn target(&self) -> &Type {
        let mut t = self;
        while let Type::Arrow(inner) = t {
            t = &inner.cod;
        }
        t
    }

    pub fn head(&self) -> &Type {
        let mut t = self;
        while let Type::App(inner) = t {
            t = &inner.fun;
        }
        t
    }

    pub fn args(&self) -> Vec<&Type> {
        let mut t = self;
        let mut args = vec![];
        while let Type::App(inner) = t {
            args.push(&inner.arg);
            t = &inner.fun;
        }
        args.reverse();
        args
    }

    #[inline]
    fn ptr_eq(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Const(a), Type::Const(b)) => Arc::ptr_eq(a, b),
            (Type::Arrow(a), Type::Arrow(b)) => Arc::ptr_eq(a, b),
            (Type::App(a), Type::App(b)) => Arc::ptr_eq(a, b),
            (Type::Local(a), Type::Local(b)) => Arc::ptr_eq(a, b),
            (Type::Hole(a), Type::Hole(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }

    fn matches_help(&self, pattern: &Type, subst: &mut Vec<(Id, Type)>) -> bool {
        match pattern {
            Type::Const(_) => self == pattern,
            Type::Arrow(pattern) => {
                let Type::Arrow(target) = self else {
                    return false;
                };
                target.dom.matches_help(&pattern.dom, subst)
                    && target.cod.matches_help(&pattern.cod, subst)
            }
            Type::App(pattern) => {
                let Type::App(target) = self else {
                    return false;
                };
                target.fun.matches_help(&pattern.fun, subst)
                    && target.arg.matches_help(&pattern.arg, subst)
            }
            Type::Local(_) => self == pattern,
            Type::Hole(pattern) => {
                let pattern_id = pattern.id;
                if let Some((_, t)) = subst.iter().find(|&&(x, _)| x == pattern_id) {
                    self.matches_help(&t.clone(), subst)
                } else {
                    subst.push((pattern_id, self.clone()));
                    true
                }
            }
        }
    }

    fn holes(&self, buf: &mut Vec<Id>) {
        match self {
            Type::Const(_) => {}
            Type::Arrow(inner) => {
                inner.dom.holes(buf);
                inner.cod.holes(buf);
            }
            Type::App(inner) => {
                inner.fun.holes(buf);
                inner.arg.holes(buf);
            }
            Type::Local(_) => {}
            Type::Hole(hole) => {
                buf.push(hole.id);
            }
        }
    }

    pub fn inst(&self, subst: &[(Id, Type)]) -> Type {
        match self {
            Type::Const(_) => self.clone(),
            Type::Local(_) => self.clone(),
            Type::Hole(x) => {
                let id = x.id;
                subst
                    .iter()
                    .find(|(y, _)| *y == id)
                    .map(|(_, t)| t.clone())
                    .unwrap_or_else(|| self.clone())
            }
            Type::Arrow(inner) => {
                let dom = inner.dom.inst(subst);
                let cod = inner.cod.inst(subst);
                if inner.dom.ptr_eq(&dom) && inner.cod.ptr_eq(&cod) {
                    self.clone()
                } else {
                    mk_type_arrow(dom, cod)
                }
            }
            Type::App(inner) => {
                let fun = inner.fun.inst(subst);
                let arg = inner.arg.inst(subst);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_type_app(fun, arg)
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ClassType {
    pub arity: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Class {
    pub name: QualifiedName,
    pub args: Vec<Type>,
}

impl Display for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        for t in &self.args {
            write!(f, " {}", t)?;
        }
        Ok(())
    }
}

impl Class {
    pub fn subst(&self, subst: &[(Id, Type)]) -> Class {
        let mut changed = false;
        let args: Vec<Type> = self
            .args
            .iter()
            .map(|t| {
                let new_t = t.subst(subst);
                if !changed && !t.ptr_eq(&new_t) {
                    changed = true;
                }
                new_t
            })
            .collect();
        if changed {
            Class {
                name: self.name.clone(),
                args,
            }
        } else {
            self.clone()
        }
    }

    pub fn is_ground(&self) -> bool {
        self.args.iter().all(|t| t.is_ground())
    }

    pub fn matches(&self, pattern: &Class) -> Option<Vec<(Id, Type)>> {
        if self.name != pattern.name || self.args.len() != pattern.args.len() {
            return None;
        }
        let mut subst = vec![];
        for (t, p) in zip(&self.args, &pattern.args) {
            if !t.matches_help(p, &mut subst) {
                return None;
            }
        }
        Some(subst)
    }

    pub fn holes(&self) -> Vec<Id> {
        let mut holes = vec![];
        for t in &self.args {
            t.holes(&mut holes);
        }
        holes
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instance {
    Local(Arc<InstanceLocal>),
    Global(Arc<InstanceGlobal>),
    Hole(Arc<InstanceHole>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceLocal {
    pub class: Class,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceHole {
    pub id: Id,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceGlobal {
    pub name: QualifiedName,
    pub ty_args: Vec<Type>,
    pub args: Vec<Instance>,
}

impl Display for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instance::Local(c) => write!(f, "${}", c.class),
            Instance::Global(i) => {
                write!(f, "{}", i.name)?;
                if !i.ty_args.is_empty() {
                    write!(f, ".{{")?;
                    let mut first = true;
                    for t in &i.ty_args {
                        if !first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{t}")?;
                        first = false;
                    }
                    write!(f, "}}")?;
                }
                if !i.args.is_empty() {
                    write!(f, ".[")?;
                    let mut first = true;
                    for arg in &i.args {
                        if !first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{arg}")?;
                        first = false;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            Instance::Hole(hole) => write!(f, "?{}", hole.id),
        }
    }
}

pub fn mk_instance_local(class: Class) -> Instance {
    Instance::Local(Arc::new(InstanceLocal { class }))
}

pub fn mk_instance_global(
    name: QualifiedName,
    ty_args: Vec<Type>,
    args: Vec<Instance>,
) -> Instance {
    Instance::Global(Arc::new(InstanceGlobal {
        name,
        ty_args,
        args,
    }))
}

pub fn mk_instance_hole(id: Id) -> Instance {
    Instance::Hole(Arc::new(InstanceHole { id }))
}

impl Instance {
    fn replace_type(&self, f: &impl Fn(&Type) -> Type) -> Instance {
        match self {
            Instance::Local(c) => {
                let mut changed = false;
                let mut new_args = Vec::with_capacity(c.class.args.len());
                for t in &c.class.args {
                    let new_t = f(t);
                    if !changed && !t.ptr_eq(&new_t) {
                        changed = true;
                    }
                    new_args.push(new_t);
                }
                if !changed {
                    self.clone()
                } else {
                    mk_instance_local(Class {
                        name: c.class.name.clone(),
                        args: new_args,
                    })
                }
            }
            Instance::Global(i) => {
                let mut changed = false;
                let ty_args: Vec<Type> = i
                    .ty_args
                    .iter()
                    .map(|t| {
                        let new_t = f(t);
                        if !changed && !t.ptr_eq(&new_t) {
                            changed = true;
                        }
                        new_t
                    })
                    .collect();
                let args: Vec<Instance> = i.args.iter().map(|arg| arg.replace_type(f)).collect();
                if changed || args.iter().zip(&i.args).any(|(a, b)| !a.ptr_eq(b)) {
                    mk_instance_global(i.name.clone(), ty_args, args)
                } else {
                    self.clone()
                }
            }
            Instance::Hole(_) => self.clone(),
        }
    }

    pub fn contains_type_local(&self, id: Id) -> bool {
        match self {
            Instance::Local(class) => class.class.args.iter().any(|arg| arg.contains_local(id)),
            Instance::Global(instance) => {
                instance.ty_args.iter().any(|arg| arg.contains_local(id))
                    || instance.args.iter().any(|arg| arg.contains_type_local(id))
            }
            Instance::Hole(_) => false,
        }
    }

    pub fn is_type_ground(&self) -> bool {
        match self {
            Instance::Local(c) => c.class.is_ground(),
            Instance::Global(i) => {
                i.ty_args.iter().all(|t| t.is_ground()) && i.args.iter().all(|i| i.is_type_ground())
            }
            Instance::Hole(_) => true,
        }
    }

    pub fn is_instance_ground(&self) -> bool {
        match self {
            Instance::Local(_) => true,
            Instance::Global(inner) => inner.args.iter().all(Instance::is_instance_ground),
            Instance::Hole(_) => false,
        }
    }

    fn subst(&self, subst: &[(Class, Instance)]) -> Instance {
        match self {
            Instance::Local(c) => {
                for (u, i) in subst {
                    if &c.class == u {
                        return i.clone();
                    }
                }
                self.clone()
            }
            Instance::Global(i) => {
                let mut changed = false;
                let args: Vec<Instance> = i
                    .args
                    .iter()
                    .map(|arg| {
                        let new_arg = arg.subst(subst);
                        if !changed && !arg.ptr_eq(&new_arg) {
                            changed = true;
                        }
                        new_arg
                    })
                    .collect();
                if changed {
                    mk_instance_global(i.name.clone(), i.ty_args.clone(), args)
                } else {
                    self.clone()
                }
            }
            Instance::Hole(_) => self.clone(),
        }
    }

    fn ptr_eq(&self, other: &Instance) -> bool {
        match (self, other) {
            (Instance::Local(a), Instance::Local(b)) => Arc::ptr_eq(a, b),
            (Instance::Global(a), Instance::Global(b)) => Arc::ptr_eq(a, b),
            (Instance::Hole(a), Instance::Hole(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }

    pub fn is_hole(&self) -> bool {
        matches!(self, Instance::Hole(_))
    }
}

#[derive(Clone, Debug)]
pub struct TermMetadata {
    pub span: Option<Span>,
    pub is_closed: bool,
    pub bound: usize,
    pub has_const: bool,
    pub has_hole: bool,
}

impl PartialEq for TermMetadata {
    fn eq(&self, other: &Self) -> bool {
        self.is_closed == other.is_closed
            && self.bound == other.bound
            && self.has_const == other.has_const
            && self.has_hole == other.has_hole
    }
}

impl Eq for TermMetadata {}

impl Default for TermMetadata {
    fn default() -> Self {
        TermMetadata {
            span: None,
            is_closed: true,
            bound: 0,
            has_const: false,
            has_hole: false,
        }
    }
}

/// Locally nameless representation. See [Charguéraud, 2012].
/// Use syn's convention [https://docs.rs/syn/latest/syn/enum.Expr.html#syntax-tree-enums].
#[derive(Clone, Debug)]
pub enum Term {
    Var(Arc<TermVar>),
    Abs(Arc<TermAbs>),
    App(Arc<TermApp>),
    Local(Arc<TermLocal>),
    Const(Arc<TermConst>),
    Hole(Arc<TermHole>),
}

#[derive(Clone, Debug)]
pub struct TermVar {
    pub metadata: TermMetadata,
    pub index: usize,
}

#[derive(Clone, Debug, Default)]
pub struct TermAbs {
    pub metadata: TermMetadata,
    pub binder_type: Type,
    // for pretty-printing
    pub binder_name: Option<Name>,
    pub body: Term,
}

#[derive(Clone, Debug)]
pub struct TermApp {
    pub metadata: TermMetadata,
    pub fun: Term,
    pub arg: Term,
}

#[derive(Clone, Debug)]
pub struct TermLocal {
    pub metadata: TermMetadata,
    pub id: Id,
}

#[derive(Clone, Debug)]
pub struct TermConst {
    pub metadata: TermMetadata,
    pub name: QualifiedName,
    pub ty_args: Vec<Type>,
    pub instances: Vec<Instance>,
}

#[derive(Clone, Debug)]
pub struct TermHole {
    pub metadata: TermMetadata,
    pub id: Id,
}

impl TermConst {
    fn alpha_eq(&self, other: &TermConst) -> bool {
        if self.name != other.name || self.ty_args.len() != other.ty_args.len() {
            return false;
        }
        for (t, u) in zip(&self.ty_args, &other.ty_args) {
            if t != u {
                return false;
            }
        }
        // don't need to compare instances because of the coherency.
        true
    }
}

impl Default for Term {
    fn default() -> Self {
        mk_var(0)
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const TERM_PREC_LAM: u8 = 0;
        const TERM_PREC_APP: u8 = 1;
        const TERM_PREC_ATOM: u8 = 2;

        fn fmt_term(term: &Term, f: &mut std::fmt::Formatter<'_>, prec: u8) -> std::fmt::Result {
            match term {
                Term::Var(inner) => write!(f, "#{}", inner.index),
                Term::Abs(inner) => {
                    let needs_paren = prec > TERM_PREC_LAM;
                    if needs_paren {
                        write!(f, "(")?;
                    }
                    match &inner.binder_name {
                        Some(name) => write!(f, "λ{}:{}. ", name.as_str(), inner.binder_type)?,
                        None => write!(f, "λ_:{}. ", inner.binder_type)?,
                    }
                    fmt_term(&inner.body, f, TERM_PREC_LAM)?;
                    if needs_paren {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
                Term::App(inner) => {
                    let needs_paren = prec > TERM_PREC_APP;
                    if needs_paren {
                        write!(f, "(")?;
                    }
                    fmt_term(&inner.fun, f, TERM_PREC_APP)?;
                    write!(f, " ")?;
                    fmt_term(&inner.arg, f, TERM_PREC_ATOM)?;
                    if needs_paren {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
                Term::Local(inner) => write!(f, "${}", inner.id),
                Term::Const(inner) => {
                    write!(f, "{}", inner.name)?;
                    if !inner.ty_args.is_empty() {
                        write!(f, ".{{")?;
                        for (idx, t) in inner.ty_args.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{t}")?;
                        }
                        write!(f, "}}")?;
                    }
                    if !inner.instances.is_empty() {
                        write!(f, ".[")?;
                        for (idx, i) in inner.instances.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{i}")?;
                        }
                        write!(f, "]")?;
                    }
                    Ok(())
                }
                Term::Hole(inner) => write!(f, "?{}", inner.id),
            }
        }

        fmt_term(self, f, TERM_PREC_LAM)
    }
}

pub fn mk_abs(binder_name: Option<Name>, binder_type: Type, body: Term) -> Term {
    let mut body_meta = body.metadata().clone();
    body_meta.span = None;
    Term::Abs(Arc::new(TermAbs {
        metadata: body_meta,
        binder_type,
        binder_name,
        body,
    }))
}

pub fn mk_app(fun: Term, arg: Term) -> Term {
    let lhs = fun.metadata().clone();
    let rhs = arg.metadata().clone();
    let metadata = TermMetadata {
        span: None,
        is_closed: lhs.is_closed && rhs.is_closed,
        bound: lhs.bound.max(rhs.bound),
        has_const: lhs.has_const || rhs.has_const,
        has_hole: lhs.has_hole || rhs.has_hole,
    };
    Term::App(Arc::new(TermApp { metadata, fun, arg }))
}

pub fn mk_var(index: usize) -> Term {
    let metadata = TermMetadata {
        span: None,
        is_closed: true,
        bound: index + 1,
        has_const: false,
        has_hole: false,
    };
    Term::Var(Arc::new(TermVar { metadata, index }))
}

pub fn mk_const(name: QualifiedName, ty_args: Vec<Type>, instances: Vec<Instance>) -> Term {
    let metadata = TermMetadata {
        span: None,
        is_closed: true,
        bound: 0,
        has_const: true,
        has_hole: false,
    };
    Term::Const(Arc::new(TermConst {
        metadata,
        name,
        ty_args,
        instances,
    }))
}

pub fn mk_local(id: Id) -> Term {
    let metadata = TermMetadata {
        span: None,
        is_closed: false,
        bound: 0,
        has_const: false,
        has_hole: false,
    };
    Term::Local(Arc::new(TermLocal { metadata, id }))
}

pub fn mk_fresh_hole() -> Term {
    mk_hole(Id::fresh())
}

pub fn mk_hole(id: Id) -> Term {
    let metadata = TermMetadata {
        span: None,
        is_closed: true,
        bound: 0,
        has_const: false,
        has_hole: true,
    };
    Term::Hole(Arc::new(TermHole { metadata, id }))
}

#[derive(Debug, Clone)]
pub struct Ctor {
    pub head: Arc<TermConst>,
    pub args: Vec<Term>,
}

impl TryFrom<Term> for Ctor {
    type Error = ();

    fn try_from(value: Term) -> Result<Self, Self::Error> {
        match value {
            Term::Const(value) => Ok(Ctor {
                head: value,
                args: vec![],
            }),
            Term::App(value) => {
                let value = Arc::unwrap_or_clone(value);
                let mut ctor: Ctor = value.fun.try_into()?;
                ctor.args.push(value.arg);
                Ok(ctor)
            }
            Term::Var(_) | Term::Abs(_) | Term::Local(_) | Term::Hole(_) => Err(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Local {
    pub id: Id,
    pub ty: Type,
}

impl Term {
    #[inline]
    pub fn metadata(&self) -> &TermMetadata {
        match self {
            Term::Var(inner) => &inner.metadata,
            Term::Abs(inner) => &inner.metadata,
            Term::App(inner) => &inner.metadata,
            Term::Local(inner) => &inner.metadata,
            Term::Const(inner) => &inner.metadata,
            Term::Hole(inner) => &inner.metadata,
        }
    }

    pub fn span(&self) -> Option<&Span> {
        self.metadata().span.as_ref()
    }

    pub fn with_span(self, span: Option<Span>) -> Term {
        match self {
            Term::Var(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Term::Var(Arc::new(inner))
            }
            Term::Abs(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Term::Abs(Arc::new(inner))
            }
            Term::App(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Term::App(Arc::new(inner))
            }
            Term::Local(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Term::Local(Arc::new(inner))
            }
            Term::Const(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Term::Const(Arc::new(inner))
            }
            Term::Hole(inner) => {
                let mut inner = Arc::unwrap_or_clone(inner);
                inner.metadata.span = span;
                Term::Hole(Arc::new(inner))
            }
        }
    }

    fn ptr_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(a), Term::Var(b)) => Arc::ptr_eq(a, b),
            (Term::Abs(a), Term::Abs(b)) => Arc::ptr_eq(a, b),
            (Term::App(a), Term::App(b)) => Arc::ptr_eq(a, b),
            (Term::Local(a), Term::Local(b)) => Arc::ptr_eq(a, b),
            (Term::Const(a), Term::Const(b)) => Arc::ptr_eq(a, b),
            (Term::Hole(a), Term::Hole(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }

    /// self.open([x, y], k) == [x/k+1,y/k]self
    pub fn open(&self, xs: &[Term], level: usize) -> Term {
        if self.metadata().bound <= level {
            return self.clone();
        }
        match self {
            Self::Local(_) => self.clone(),
            Self::Var(inner) => {
                if inner.index >= level {
                    let i = inner.index - level;
                    if i < xs.len() {
                        return xs[xs.len() - i - 1].clone();
                    }
                }
                self.clone()
            }
            Self::Abs(inner) => {
                let body = inner.body.open(xs, level + 1);
                if inner.body.ptr_eq(&body) {
                    self.clone()
                } else {
                    mk_abs(inner.binder_name.clone(), inner.binder_type.clone(), body)
                }
            }
            Self::App(inner) => {
                let fun = inner.fun.open(xs, level);
                let arg = inner.arg.open(xs, level);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_app(fun, arg)
                }
            }
            Self::Const(_) => self.clone(),
            Self::Hole(_) => self.clone(),
        }
    }

    /// self.close([x, y], k) == [k+1/x, k/y]self
    pub fn close(&self, xs: &[Id], level: usize) -> Term {
        if self.metadata().is_closed {
            return self.clone();
        }
        match self {
            Self::Local(inner) => {
                let id = inner.id;
                for (i, &x) in xs.iter().rev().enumerate() {
                    if id == x {
                        return mk_var(level + i);
                    }
                }
                self.clone()
            }
            Self::Var(_) => self.clone(),
            Self::Abs(inner) => {
                let body = inner.body.close(xs, level + 1);
                if inner.body.ptr_eq(&body) {
                    self.clone()
                } else {
                    mk_abs(inner.binder_name.clone(), inner.binder_type.clone(), body)
                }
            }
            Self::App(inner) => {
                let fun = inner.fun.close(xs, level);
                let arg = inner.arg.close(xs, level);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_app(fun, arg)
                }
            }
            Self::Const(_) => self.clone(),
            Self::Hole(_) => self.clone(),
        }
    }

    pub fn replace_local(&self, f: &impl Fn(Id) -> Option<Term>) -> Term {
        if self.metadata().is_closed {
            return self.clone();
        }
        match self {
            Term::Var(_) => self.clone(),
            Term::Abs(inner) => {
                let body = inner.body.replace_local(f);
                if inner.body.ptr_eq(&body) {
                    self.clone()
                } else {
                    mk_abs(inner.binder_name.clone(), inner.binder_type.clone(), body)
                }
            }
            Term::App(inner) => {
                let fun = inner.fun.replace_local(f);
                let arg = inner.arg.replace_local(f);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_app(fun, arg)
                }
            }
            Term::Local(inner) => {
                if let Some(m) = f(inner.id) {
                    m
                } else {
                    self.clone()
                }
            }
            Term::Const(_) => self.clone(),
            Term::Hole(_) => self.clone(),
        }
    }

    pub fn replace_hole(&self, f: &impl Fn(Id) -> Option<Term>) -> Term {
        match self {
            Term::Var(_) => self.clone(),
            Term::Abs(inner) => {
                let body = inner.body.replace_hole(f);
                if inner.body.ptr_eq(&body) {
                    self.clone()
                } else {
                    mk_abs(inner.binder_name.clone(), inner.binder_type.clone(), body)
                }
            }
            Term::App(inner) => {
                let fun = inner.fun.replace_hole(f);
                let arg = inner.arg.replace_hole(f);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_app(fun, arg)
                }
            }
            Term::Local(_) => self.clone(),
            Term::Const(_) => self.clone(),
            Term::Hole(inner) => {
                if let Some(m) = f(inner.id) {
                    m
                } else {
                    self.clone()
                }
            }
        }
    }

    pub fn replace_instance(&self, f: &impl Fn(&Instance) -> Instance) -> Term {
        if !self.metadata().has_const {
            return self.clone();
        }
        match self {
            Term::Var(_) => self.clone(),
            Term::Abs(inner) => {
                let body = inner.body.replace_instance(f);
                if inner.body.ptr_eq(&body) {
                    self.clone()
                } else {
                    mk_abs(inner.binder_name.clone(), inner.binder_type.clone(), body)
                }
            }
            Term::App(inner) => {
                let fun = inner.fun.replace_instance(f);
                let arg = inner.arg.replace_instance(f);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_app(fun, arg)
                }
            }
            Term::Local(_) => self.clone(),
            Term::Const(inner) => {
                let mut changed = false;
                let instances: Vec<Instance> = inner
                    .instances
                    .iter()
                    .map(|instance| {
                        let new_instance = f(instance);
                        if !changed && !instance.ptr_eq(&new_instance) {
                            changed = true;
                        }
                        new_instance
                    })
                    .collect();
                if changed {
                    mk_const(inner.name.clone(), inner.ty_args.clone(), instances)
                } else {
                    self.clone()
                }
            }
            Term::Hole(_) => self.clone(),
        }
    }

    pub fn replace_type(&self, f: &impl Fn(&Type) -> Type) -> Term {
        match self {
            Term::Var(_) => self.clone(),
            Term::Abs(inner) => {
                let binder_type = f(&inner.binder_type);
                let body = inner.body.replace_type(f);
                if inner.binder_type.ptr_eq(&binder_type) && inner.body.ptr_eq(&body) {
                    self.clone()
                } else {
                    mk_abs(inner.binder_name.clone(), binder_type, body)
                }
            }
            Term::App(inner) => {
                let fun = inner.fun.replace_type(f);
                let arg = inner.arg.replace_type(f);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_app(fun, arg)
                }
            }
            Term::Local(_) => self.clone(),
            Term::Const(inner) => {
                let mut changed = false;
                let ty_args: Vec<Type> = inner
                    .ty_args
                    .iter()
                    .map(|t| {
                        let new_t = f(t);
                        if !changed && !t.ptr_eq(&new_t) {
                            changed = true;
                        }
                        new_t
                    })
                    .collect();
                let instances: Vec<Instance> = inner
                    .instances
                    .iter()
                    .map(|instance| {
                        let new_instance = instance.replace_type(f);
                        if !changed && !instance.ptr_eq(&new_instance) {
                            changed = true;
                        }
                        new_instance
                    })
                    .collect();
                if changed {
                    mk_const(inner.name.clone(), ty_args, instances)
                } else {
                    self.clone()
                }
            }
            Term::Hole(_) => self.clone(),
        }
    }

    pub fn subst_instance(&self, subst: &[(Class, Instance)]) -> Term {
        self.replace_instance(&|i| i.subst(subst))
    }

    pub fn subst_type(&self, subst: &[(Id, Type)]) -> Term {
        self.replace_type(&|t| t.subst(subst))
    }

    pub fn subst(&self, subst: &[(Id, Term)]) -> Term {
        self.replace_local(&|x| {
            for (y, m) in subst {
                if *y == x {
                    return Some(m.clone());
                }
            }
            None
        })
    }

    /// {x₁, ⋯, xₙ} # self <==> ∀ i, xᵢ ∉ FV(self)
    pub fn is_fresh(&self, free_list: &[Id]) -> bool {
        match self {
            Self::Local(inner) => !free_list.contains(&inner.id),
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_fresh(free_list),
            Self::App(inner) => inner.fun.is_fresh(free_list) && inner.arg.is_fresh(free_list),
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    /// FV(self) ⊆ {x₁, ⋯, xₙ}
    /// The term is borrowed from nominal set theory.
    pub fn is_supported_by(&self, free_list: &[Id]) -> bool {
        match self {
            Self::Local(inner) => free_list.contains(&inner.id),
            Self::Var(_) => true,
            Self::Abs(inner) => inner.body.is_supported_by(free_list),
            Self::App(inner) => {
                inner.fun.is_supported_by(free_list) && inner.arg.is_supported_by(free_list)
            }
            Self::Const(_) => true,
            Self::Hole(_) => true,
        }
    }

    pub fn contains_var(&self, i: usize) -> bool {
        if self.metadata().bound <= i {
            return false;
        }
        match self {
            Term::Var(inner) => i == inner.index,
            Term::Abs(inner) => inner.body.contains_var(i + 1),
            Term::App(inner) => inner.fun.contains_var(i) || inner.arg.contains_var(i),
            Term::Local(_) => false,
            Term::Const(_) => false,
            Term::Hole(_) => false,
        }
    }

    pub fn head(&self) -> &Term {
        if self.is_abs() {
            return self;
        }
        let mut m = self;
        while let Self::App(inner) = m {
            m = &inner.fun;
        }
        m
    }

    pub fn args(&self) -> Vec<&Term> {
        let mut m = self;
        let mut args = vec![];
        while let Self::App(inner) = m {
            m = &inner.fun;
            args.push(&inner.arg);
        }
        args.reverse();
        args
    }

    pub fn replace_head(&self, f: &impl Fn(&Term) -> Option<Term>) -> Option<Term> {
        match self {
            Term::Var(_) | Term::Abs(_) | Term::Local(_) | Term::Const(_) | Term::Hole(_) => {
                f(self)
            }
            Term::App(inner) => {
                let fun = inner.fun.replace_head(f)?;
                Some(mk_app(fun, inner.arg.clone()))
            }
        }
    }

    pub fn replace_args(&self, f: &impl Fn(&Term) -> Term) -> Term {
        match self {
            Term::Var(_) | Term::Abs(_) | Term::Local(_) | Term::Const(_) | Term::Hole(_) => {
                self.clone()
            }
            Term::App(inner) => {
                let fun = inner.fun.replace_args(f);
                let arg = f(&inner.arg);
                if inner.fun.ptr_eq(&fun) && inner.arg.ptr_eq(&arg) {
                    self.clone()
                } else {
                    mk_app(fun, arg)
                }
            }
        }
    }

    pub fn is_abs(&self) -> bool {
        matches!(self, Term::Abs(_))
    }

    pub fn is_hole(&self) -> bool {
        matches!(self, Term::Hole(_))
    }

    /// Checks if self ≡ (?M l₁ ⋯ lₙ) where l₁ ⋯ lₙ are pairwise distinct non-unfoldable locals.
    pub fn is_pattern(&self, local_env: &LocalEnv) -> Option<Vec<Id>> {
        let mut arg_locals = vec![];
        if !self.head().is_hole() {
            return None;
        }
        for arg in self.args() {
            let Term::Local(arg) = arg else {
                return None;
            };
            if local_env.get_local_delta(arg.id).is_some() {
                return None;
            }
            for a in &arg_locals {
                if *a == arg.id {
                    return None;
                }
            }
            arg_locals.push(arg.id);
        }
        Some(arg_locals)
    }

    pub fn is_quasi_pattern(&self, local_env: &LocalEnv) -> bool {
        if !self.head().is_hole() {
            return false;
        }
        for arg in self.args() {
            let Term::Local(arg) = arg else {
                return false;
            };
            if local_env.get_local_delta(arg.id).is_some() {
                return false;
            };
        }
        true
    }

    /// Returns the application `self l₁ ⋯ lₙ`.
    pub fn apply(&self, args: impl IntoIterator<Item = Term>) -> Term {
        let mut fun = self.clone();
        for arg in args {
            fun = mk_app(fun, arg);
        }
        fun
    }

    /// Returns the abstraction `λ xs, self`.
    pub fn abs(&self, xs: &[Local]) -> Term {
        let locals = xs.iter().map(|x| x.id).collect::<Vec<_>>();
        let mut m = self.close(&locals, 0);
        for x in xs.iter().rev() {
            m = mk_abs(x.id.name(), x.ty.clone(), m);
        }
        m
    }

    // checks if self has any (term-level) meta variable.
    pub fn is_ground(&self) -> bool {
        match self {
            Term::Var(_) => true,
            Term::Abs(m) => m.body.is_ground(),
            Term::App(m) => m.fun.is_ground() && m.arg.is_ground(),
            Term::Local(_) => true,
            Term::Const(_) => true,
            Term::Hole(_) => false,
        }
    }

    pub fn is_type_ground(&self) -> bool {
        match self {
            Term::Var(_) => true,
            Term::Abs(inner) => inner.binder_type.is_ground() && inner.body.is_type_ground(),
            Term::App(inner) => inner.fun.is_type_ground() && inner.arg.is_type_ground(),
            Term::Local(_) => true,
            Term::Const(inner) => {
                inner.ty_args.iter().all(Type::is_ground)
                    && inner.instances.iter().all(Instance::is_type_ground)
            }
            Term::Hole(_) => true,
        }
    }

    pub fn is_instance_ground(&self) -> bool {
        match self {
            Term::Var(_) => true,
            Term::Abs(inner) => inner.body.is_instance_ground(),
            Term::App(inner) => inner.fun.is_instance_ground() && inner.arg.is_instance_ground(),
            Term::Local(_) => true,
            Term::Const(inner) => inner.instances.iter().all(Instance::is_instance_ground),
            Term::Hole(_) => true,
        }
    }

    pub fn alpha_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1.index == index2.index,
            (Term::Abs(inner1), Term::Abs(inner2)) => {
                inner1.binder_type == inner2.binder_type && inner1.body.alpha_eq(&inner2.body)
            }
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.alpha_eq(&inner2.fun) && inner1.arg.alpha_eq(&inner2.arg)
            }
            (Term::Local(name1), Term::Local(name2)) => name1.id == name2.id,
            (Term::Const(inner1), Term::Const(inner2)) => inner1.alpha_eq(inner2),
            (Term::Hole(name1), Term::Hole(name2)) => name1.id == name2.id,
            _ => false,
        }
    }

    pub fn maybe_alpha_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1.index == index2.index,
            (Term::Abs(inner1), Term::Abs(inner2)) => inner1.body.maybe_alpha_eq(&inner2.body),
            (Term::App(inner1), Term::App(inner2)) => {
                inner1.fun.maybe_alpha_eq(&inner2.fun) && inner1.arg.maybe_alpha_eq(&inner2.arg)
            }
            (Term::Local(name1), Term::Local(name2)) => name1.id == name2.id,
            (Term::Const(inner1), Term::Const(inner2)) => inner1.name == inner2.name,
            (Term::Hole(name1), Term::Hole(name2)) => name1.id == name2.id,
            _ => false,
        }
    }

    /// Returns None if the term is already in whnf.
    pub fn whnf(&self) -> Option<Term> {
        match self {
            Term::Var(_) | Term::Local(_) | Term::Const(_) | Term::Hole(_) | Term::Abs(_) => None,
            Term::App(inner) => {
                let fun = inner.fun.whnf();
                if let Term::Abs(abs) = fun.as_ref().unwrap_or(&inner.fun) {
                    let body = abs.body.open(std::slice::from_ref(&inner.arg), 0);
                    return Some(body.whnf().unwrap_or(body));
                }
                fun.map(|fun| mk_app(fun, inner.arg.clone()))
            }
        }
    }

    pub fn contains_type_local(&self, id: Id) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Abs(inner) => {
                inner.binder_type.contains_local(id) || inner.body.contains_type_local(id)
            }
            Term::App(inner) => {
                inner.fun.contains_type_local(id) || inner.arg.contains_type_local(id)
            }
            Term::Local(_) => false,
            Term::Const(inner) => {
                inner.ty_args.iter().any(|ty| ty.contains_local(id))
                    || inner
                        .instances
                        .iter()
                        .any(|instance| instance.contains_type_local(id))
            }
            Term::Hole(_) => false,
        }
    }

    pub fn contains_local(&self, id: Id) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Abs(m) => m.body.contains_local(id),
            Term::App(m) => m.fun.contains_local(id) || m.arg.contains_local(id),
            Term::Local(inner) => inner.id == id,
            Term::Const(_) => false,
            Term::Hole(_) => false,
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct LocalEnv {
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub local_deltas: Vec<LocalDelta>,
    pub locals: Vec<Local>,
}

impl LocalEnv {
    pub fn get_local(&self, id: Id) -> Option<&Type> {
        self.locals.iter().rev().find_map(|local| {
            if local.id == id {
                Some(&local.ty)
            } else {
                None
            }
        })
    }

    pub fn get_local_delta(&self, id: Id) -> Option<&LocalDelta> {
        self.local_deltas.iter().rev().find(|delta| delta.id == id)
    }
}

#[derive(Debug, Clone)]
pub struct LocalDelta {
    pub id: Id,
    pub target: Term,
    pub height: usize,
}

#[derive(Debug, Clone)]
pub struct Const {
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Delta {
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub target: Term,
    // equal to height(target)
    pub height: usize,
}

#[derive(Debug, Clone)]
pub struct Kappa;

#[derive(Debug, Clone)]
pub struct ClassInstance {
    pub local_types: Vec<Id>,
    pub local_classes: Vec<Class>,
    pub target: Class,
    pub method_table: HashMap<QualifiedName, Term>,
}

#[derive(Debug, Clone)]
pub struct Env<'a> {
    pub type_const_table: &'a HashMap<QualifiedName, Kind>,
    pub const_table: &'a HashMap<QualifiedName, Const>,
    pub delta_table: &'a HashMap<QualifiedName, Delta>,
    pub kappa_table: &'a HashMap<QualifiedName, Kappa>,
    pub class_predicate_table: &'a HashMap<QualifiedName, ClassType>,
    pub class_instance_table: &'a HashMap<QualifiedName, ClassInstance>,
}

impl Env<'_> {
    pub fn infer_kind(&self, local_env: &LocalEnv, t: &Type) -> Kind {
        match t {
            Type::Const(name) => self
                .type_const_table
                .get(&name.name)
                .cloned()
                .unwrap_or_else(|| panic!("unknown type constant: {:?}", name.name)),
            Type::Arrow(inner) => {
                let dom_kind = self.infer_kind(local_env, &inner.dom);
                if dom_kind != Kind::base() {
                    panic!(
                        "arrow domain must have base kind, but got {:?} for {:?}",
                        dom_kind, inner.dom
                    );
                }
                let cod_kind = self.infer_kind(local_env, &inner.cod);
                if cod_kind != Kind::base() {
                    panic!(
                        "arrow codomain must have base kind, but got {:?} for {:?}",
                        cod_kind, inner.cod
                    );
                }
                Kind::base()
            }
            Type::App(inner) => {
                let fun_kind = self.infer_kind(local_env, &inner.fun);
                if fun_kind.0 == 0 {
                    panic!("cannot apply a term of base kind: {:?}", inner.fun);
                }
                let arg_kind = self.infer_kind(local_env, &inner.arg);
                if arg_kind != Kind::base() {
                    panic!(
                        "type application argument must have base kind, but got {:?} for {:?}",
                        arg_kind, inner.arg
                    );
                }
                Kind(fun_kind.0 - 1)
            }
            Type::Local(x) => {
                for local_type in &local_env.local_types {
                    if *local_type == x.id {
                        return Kind::base();
                    }
                }
                panic!("unbound local type: {:?}", x.id);
            }
            Type::Hole(_) => panic!("cannot infer kind of a hole"),
        }
    }

    pub fn check_kind(&self, local_env: &LocalEnv, t: &Type, kind: Kind) {
        let inferred = self.infer_kind(local_env, t);
        if inferred != kind {
            panic!(
                "kind mismatch: expected {:?}, got {:?} for type {:?}",
                kind, inferred, t
            );
        }
    }

    pub fn check_wft(&self, local_env: &LocalEnv, t: &Type) {
        self.check_kind(local_env, t, Kind::base());
    }

    pub fn check_wfc(&self, local_env: &LocalEnv, c: &Class) {
        let class_type = self
            .class_predicate_table
            .get(&c.name)
            .unwrap_or_else(|| panic!("unknown class predicate: {:?}", c.name));
        if class_type.arity != c.args.len() {
            panic!(
                "class {:?} expects {} arguments but got {}",
                c.name,
                class_type.arity,
                c.args.len()
            );
        }
        for arg in &c.args {
            self.check_wft(local_env, arg);
        }
    }

    pub fn infer_class(&self, local_env: &LocalEnv, i: &Instance) -> Class {
        match i {
            Instance::Local(i) => {
                for local_class in &local_env.local_classes {
                    if local_class == &i.class {
                        return i.class.clone();
                    }
                }
                panic!("unknown local class instance: {:?}", i);
            }
            Instance::Global(i) => {
                let InstanceGlobal {
                    name,
                    ty_args,
                    args,
                } = &**i;
                let ClassInstance {
                    local_types,
                    local_classes,
                    target,
                    method_table: _,
                } = self
                    .class_instance_table
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown class instance: {:?}", name));
                if local_types.len() != ty_args.len() {
                    panic!(
                        "class instance {:?} expects {} type arguments but got {}",
                        name,
                        local_types.len(),
                        ty_args.len()
                    );
                }
                for ty_arg in ty_args {
                    self.check_wft(local_env, ty_arg);
                }
                let mut type_subst = Vec::with_capacity(local_types.len());
                for (x, t) in zip(local_types, ty_args) {
                    type_subst.push((*x, t.clone()));
                }
                if local_classes.len() != args.len() {
                    panic!(
                        "class instance {:?} expects {} class arguments but got {}",
                        name,
                        local_classes.len(),
                        args.len()
                    );
                }
                for (local_class, arg) in zip(local_classes, args) {
                    let local_class = local_class.subst(&type_subst);
                    self.check_class(local_env, arg, &local_class);
                }
                target.subst(&type_subst)
            }
            Instance::Hole(_) => panic!("cannot infer class of a hole"),
        }
    }

    // t is trusted
    pub fn check_class(&self, local_env: &LocalEnv, i: &Instance, class: &Class) {
        let inferred = self.infer_class(local_env, i);
        if inferred != *class {
            panic!("class mismatch: expected {:?}, got {:?}", class, inferred);
        }
    }

    pub fn infer_type(&self, local_env: &mut LocalEnv, m: &Term) -> Type {
        match m {
            Term::Var(_) => panic!("cannot infer type of a raw variable"),
            Term::Abs(m) => {
                self.check_wft(local_env, &m.binder_type);
                let x = Local {
                    id: Id::fresh(),
                    ty: m.binder_type.clone(),
                };
                let n = m.body.open(&[mk_local(x.id)], 0);
                local_env.locals.push(x);
                let target = self.infer_type(local_env, &n);
                let x = local_env.locals.pop().unwrap();
                mk_type_arrow(x.ty, target)
            }
            Term::App(m) => {
                let fun_ty = self.infer_type(local_env, &m.fun);
                match fun_ty {
                    Type::Arrow(fun_ty) => {
                        self.check_type(local_env, &m.arg, &fun_ty.dom);
                        fun_ty.cod.clone()
                    }
                    _ => panic!(
                        "expected a function type but got {:?} for term {:?}",
                        fun_ty, m.fun
                    ),
                }
            }
            Term::Local(inner) => {
                for y in local_env.locals.iter().rev() {
                    if inner.id == y.id {
                        return y.ty.clone();
                    }
                }
                panic!("unbound local term: {:?}", inner.id);
            }
            Term::Const(m) => {
                let Const {
                    local_types,
                    local_classes,
                    ty,
                } = self
                    .const_table
                    .get(&m.name)
                    .unwrap_or_else(|| panic!("unknown constant: {:?}", m.name));
                if local_types.len() != m.ty_args.len() {
                    panic!(
                        "constant {:?} expects {} type arguments but got {}",
                        m.name,
                        local_types.len(),
                        m.ty_args.len()
                    );
                }
                for ty_arg in &m.ty_args {
                    self.check_wft(local_env, ty_arg);
                }
                let mut type_subst = Vec::with_capacity(local_types.len());
                for (x, t) in zip(local_types, &m.ty_args) {
                    type_subst.push((*x, t.clone()));
                }
                if local_classes.len() != m.instances.len() {
                    panic!(
                        "constant {:?} expects {} class arguments but got {}",
                        m.name,
                        local_classes.len(),
                        m.instances.len()
                    );
                }
                for (local_class, instance) in zip(local_classes, &m.instances) {
                    let local_class = local_class.subst(&type_subst);
                    self.check_wfc(local_env, &local_class);
                    self.check_class(local_env, instance, &local_class);
                }
                ty.subst(&type_subst)
            }
            Term::Hole(_) => panic!("cannot infer type of a hole"),
        }
    }

    pub fn check_type(&self, local_env: &mut LocalEnv, m: &Term, target: &Type) {
        let inferred = self.infer_type(local_env, m);
        if inferred != *target {
            panic!(
                "type mismatch: expected {:?}, got {:?} for term {:?}",
                target, inferred, m
            );
        }
    }

    pub fn check_wff(&self, local_env: &mut LocalEnv, m: &Term) {
        self.check_type(local_env, m, &mk_type_prop());
    }

    // c.{u₁, ⋯, uₙ} := n
    // assert_eq!(m, c.{u₁, ⋯, uₙ})
    // self.delta_reduce(m);
    // assert_eq!(m, n)
    fn delta_reduce(&self, m: &Term) -> Option<Term> {
        let Term::Const(n) = m else {
            return None;
        };
        let Delta {
            local_types,
            local_classes,
            target,
            height: _,
        } = self.delta_table.get(&n.name)?;
        let mut type_subst = Vec::with_capacity(local_types.len());
        for (x, t) in zip(local_types, &n.ty_args) {
            type_subst.push((*x, t.clone()));
        }
        let mut instance_subst = Vec::with_capacity(local_classes.len());
        for (local_class, instance) in zip(local_classes, &n.instances) {
            let local_class = local_class.subst(&type_subst);
            instance_subst.push((local_class, instance.clone()));
        }
        Some(
            target
                .subst_type(&type_subst)
                .subst_instance(&instance_subst),
        )
    }

    fn kappa_reduce(&self, m: &Term) -> Option<Term> {
        let Term::Const(n) = m else {
            return None;
        };
        self.kappa_table.get(&n.name)?;
        if n.instances.is_empty() {
            return None;
        }
        let Instance::Global(recv) = &n.instances[0] else {
            return None;
        };
        let InstanceGlobal {
            name,
            ty_args,
            args,
        } = &**recv;
        // assert_eq!(ty_args, &n.ty_args);
        // assert_eq!(&args[..], &n.instances[1..]);
        let ClassInstance {
            local_types,
            local_classes,
            target: _,
            method_table,
        } = self.class_instance_table.get(name)?;
        let target = method_table.get(&n.name)?;
        let mut type_subst = Vec::with_capacity(local_types.len());
        for (x, t) in zip(local_types, ty_args) {
            type_subst.push((*x, t.clone()));
        }
        let mut instance_subst = Vec::with_capacity(local_classes.len());
        for (local_class, instance) in zip(local_classes, args) {
            let local_class = local_class.subst(&type_subst);
            instance_subst.push((local_class, instance.clone()));
        }
        Some(
            target
                .subst_type(&type_subst)
                .subst_instance(&instance_subst),
        )
    }

    fn local_delta_reduce(&self, local_env: &LocalEnv, m: &Term) -> Option<Term> {
        match m {
            Term::Local(inner) => local_env
                .get_local_delta(inner.id)
                .map(|delta| delta.target.clone()),
            _ => None,
        }
    }

    pub fn unfold_head(&self, local_env: &LocalEnv, m: &Term) -> Option<Term> {
        m.replace_head(&|head| match head {
            Term::Local(_) => self.local_delta_reduce(local_env, head),
            Term::Const(_) => self.delta_reduce(head).or_else(|| self.kappa_reduce(head)),
            _ => None,
        })
    }

    pub fn local_delta_height(&self, local_env: &LocalEnv, id: Id) -> usize {
        local_env
            .get_local_delta(id)
            .map_or(0, |delta| delta.height + 1)
    }

    pub fn delta_height(&self, name: &QualifiedName) -> usize {
        self.delta_table
            .get(name)
            .map_or(0, |delta| delta.height + 1)
    }

    // NB: does not take kappa-reductions into account.
    pub fn height(&self, local_env: &LocalEnv, m: &Term) -> usize {
        match m {
            Term::Var(_) => 0,
            Term::Abs(m) => self.height(local_env, &m.body),
            Term::App(m) => std::cmp::max(
                self.height(local_env, &m.fun),
                self.height(local_env, &m.arg),
            ),
            Term::Local(inner) => self.local_delta_height(local_env, inner.id),
            Term::Const(inner) => self.delta_height(&inner.name),
            Term::Hole(_) => 0,
        }
    }

    pub fn has_kappa(&self, name: &QualifiedName) -> bool {
        self.kappa_table.contains_key(name)
    }

    fn is_kappa_redex(&self, m: &Term) -> bool {
        let Term::Const(n) = m else {
            return false;
        };
        self.kappa_table.contains_key(&n.name)
            && !n.instances.is_empty()
            && matches!(&n.instances[0], Instance::Global(_))
    }

    pub fn is_delta_redex(&self, local_env: &LocalEnv, m: &Term) -> bool {
        match m {
            Term::Local(inner) => self.local_delta_height(local_env, inner.id) > 0,
            Term::Const(inner) => self.delta_height(&inner.name) > 0,
            _ => false,
        }
    }

    pub fn is_opaque(&self, local_env: &LocalEnv, m: &Term) -> bool {
        matches!(m, Term::Const(_) | Term::Local(_))
            && !self.is_kappa_redex(m)
            && !self.is_delta_redex(local_env, m)
    }

    pub fn unfold_priority(&self, local_env: &LocalEnv, m: &Term) -> usize {
        if self.is_kappa_redex(m) {
            usize::MAX
        } else {
            self.height(local_env, m)
        }
    }

    /// Judgmental equality for the definitional equality.
    /// The type inhabitation problem of `m₁ ≡ m₂` is decidable.
    ///
    /// The formation rule is as follows:
    ///
    /// Γ ⊢ m₁ : τ    Γ ⊢ m₂ : τ
    /// -------------------------
    /// Γ ⊢ m₁ ≡ m₂ : τ
    ///
    /// The inference rules are as follows:
    ///
    /// ------------------
    /// Γ ⊢ refl m : m ≡ m
    ///
    /// Γ ⊢ h : m₁ ≡ m₂
    /// --------------------
    /// Γ ⊢ symm h : m₂ ≡ m₁
    ///
    /// Γ ⊢ h₁ : m₁ ≡ m₂   Γ ⊢ h₂ : m₂ ≡ m₃
    /// ------------------------------------
    /// Γ ⊢ trans h₁ h₂ : m₁ ≡ m₃
    ///
    /// Γ ⊢ h₁ : f₁ ≡ f₂   Γ ⊢ h₂ : a₁ ≡ a₂
    /// ------------------------------------
    /// Γ ⊢ congr_app h₁ h₂ : f₁ a₁ ≡ f₂ a₂
    ///
    /// Γ, x : τ ⊢ h : m₁ ≡ m₂
    /// ------------------------------------------------------------
    /// Γ ⊢ congr_abs (x : τ), h : (λ (x : τ), m₁) ≡ (λ (x : τ), m₂)
    ///
    ///
    /// --------------------------------------------------------
    /// Γ ⊢ beta_reduce ((λ x, m₁) m₂) : (λ x, m₁) m₂ ≡ [m₂/x]m₁
    ///
    ///
    /// --------------------------------------------------------------------------------------- (c.{u₁ ⋯ uₙ} :≡ m)
    /// Γ ⊢ delta_reduce c.{t₁ ⋯ tₙ}[i₁ ⋯ iₘ] : c.{t₁ ⋯ tₙ}[i₁ ⋯ iₘ] ≡ [i₁ ⋯ iₘ][t₁/u₁ ⋯ tₙ/uₙ]m
    ///
    /// Both terms must be ground
    pub fn equiv(&self, local_env: &LocalEnv, m1: &Term, m2: &Term) -> bool {
        if m1.alpha_eq(m2) {
            return true;
        }

        let mut m1 = m1.clone();
        let mut m2 = m2.clone();

        loop {
            if let (Term::Abs(inner1), Term::Abs(inner2)) = (&m1, &m2) {
                let x = Id::fresh();
                let local = mk_local(x);
                m1 = inner1.body.open(std::slice::from_ref(&local), 0);
                m2 = inner2.body.open(&[local], 0);
                if m1.alpha_eq(&m2) {
                    return true;
                }
                continue;
            }

            let new_m1 = m1.whnf();
            let reduced1 = new_m1.is_some();
            if let Some(new_m1) = new_m1 {
                m1 = new_m1;
            }
            let new_m2 = m2.whnf();
            let reduced2 = new_m2.is_some();
            if let Some(new_m2) = new_m2 {
                m2 = new_m2;
            }
            if reduced1 || reduced2 {
                if m1.alpha_eq(&m2) {
                    return true;
                }
                if let (Term::Abs(inner1), Term::Abs(inner2)) = (&m1, &m2) {
                    let x = Id::fresh();
                    let local = mk_local(x);
                    m1 = inner1.body.open(std::slice::from_ref(&local), 0);
                    m2 = inner2.body.open(&[local], 0);
                    if m1.alpha_eq(&m2) {
                        return true;
                    }
                    continue;
                }
            }

            if m1.is_abs() {
                std::mem::swap(&mut m1, &mut m2);
                continue;
            }
            if m2.is_abs() {
                if let Some(new_m1) = self.unfold_head(local_env, &m1) {
                    m1 = new_m1;
                    if m1.alpha_eq(&m2) {
                        return true;
                    }
                    continue;
                } else {
                    return false;
                }
            }

            let head1 = m1.head();
            let head2 = m2.head();

            if head1.alpha_eq(head2) {
                let args1 = m1.args();
                let args2 = m2.args();
                if args1.len() == args2.len() {
                    let mut all_equiv = true;
                    for (a1, a2) in std::iter::zip(args1, args2) {
                        if !self.equiv(local_env, a1, a2) {
                            all_equiv = false;
                            break;
                        }
                    }
                    if all_equiv {
                        return true;
                    }
                }
            }
            let priority1 = self.unfold_priority(local_env, head1);
            let priority2 = self.unfold_priority(local_env, head2);
            match priority1.cmp(&priority2) {
                std::cmp::Ordering::Less => {
                    if let Some(new_m2) = self.unfold_head(local_env, &m2) {
                        m2 = new_m2;
                        if m1.alpha_eq(&m2) {
                            return true;
                        }
                        continue;
                    } else {
                        return false;
                    }
                }
                std::cmp::Ordering::Equal => {
                    if let Some(new_m1) = self.unfold_head(local_env, &m1) {
                        m1 = new_m1;
                    } else {
                        return false;
                    }
                    if let Some(new_m2) = self.unfold_head(local_env, &m2) {
                        m2 = new_m2;
                    } else {
                        return false;
                    }
                    if m1.alpha_eq(&m2) {
                        return true;
                    }
                    continue;
                }
                std::cmp::Ordering::Greater => {
                    if let Some(new_m1) = self.unfold_head(local_env, &m1) {
                        m1 = new_m1;
                        if m1.alpha_eq(&m2) {
                            return true;
                        }
                        continue;
                    } else {
                        return false;
                    }
                }
            }
        }
    }
}

// TODO: add more tests for Term::equiv
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    struct EnvFixture {
        type_const_table: HashMap<QualifiedName, Kind>,
        const_table: HashMap<QualifiedName, Const>,
        delta_table: HashMap<QualifiedName, Delta>,
        kappa_table: HashMap<QualifiedName, Kappa>,
        class_predicate_table: HashMap<QualifiedName, ClassType>,
        class_instance_table: HashMap<QualifiedName, ClassInstance>,
    }

    impl EnvFixture {
        fn new() -> Self {
            Self {
                type_const_table: HashMap::new(),
                const_table: HashMap::new(),
                delta_table: HashMap::new(),
                kappa_table: HashMap::new(),
                class_predicate_table: HashMap::new(),
                class_instance_table: HashMap::new(),
            }
        }

        fn with_delta(mut self, name: QualifiedName, delta: Delta) -> Self {
            self.delta_table.insert(name, delta);
            self
        }

        fn with_const(mut self, name: QualifiedName, constant: Const) -> Self {
            self.const_table.insert(name, constant);
            self
        }

        fn env(&self) -> Env<'_> {
            Env {
                type_const_table: &self.type_const_table,
                const_table: &self.const_table,
                delta_table: &self.delta_table,
                kappa_table: &self.kappa_table,
                class_predicate_table: &self.class_predicate_table,
                class_instance_table: &self.class_instance_table,
            }
        }
    }

    fn empty_local_env() -> LocalEnv {
        LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![],
            locals: vec![],
        }
    }

    fn is_equiv(env: &Env<'_>, left: &Term, right: &Term) -> bool {
        env.equiv(&empty_local_env(), left, right)
    }

    fn local_id(value: &str) -> Id {
        Id::from_name(&Name::from_str(value))
    }

    #[test]
    fn equiv_alpha_eq_constants() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let c = QualifiedName::from_str("c");
        let left = mk_const(c.clone(), vec![], vec![]);
        let right = mk_const(c, vec![], vec![]);

        assert!(is_equiv(&env, &left, &right));
    }

    #[test]
    fn equiv_beta_reduces_application() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let x = Name::from_str("x");
        let a = QualifiedName::from_str("a");
        let body = mk_var(0);
        let lambda = mk_abs(Some(x), mk_type_prop(), body);
        let arg = mk_const(a.clone(), vec![], vec![]);
        let applied = mk_app(lambda, arg.clone());

        assert!(is_equiv(&env, &applied, &arg));
    }

    #[test]
    fn equiv_delta_unfolds_constant() {
        let c = QualifiedName::from_str("c");
        let d = QualifiedName::from_str("d");

        let delta = Delta {
            local_types: vec![],
            local_classes: vec![],
            target: mk_const(d.clone(), vec![], vec![]),
            height: 0,
        };

        let fixture = EnvFixture::new().with_delta(c.clone(), delta);
        let env = fixture.env();

        let defined = mk_const(c, vec![], vec![]);
        let body = mk_const(d, vec![], vec![]);

        assert!(is_equiv(&env, &defined, &body));
    }

    #[test]
    fn unfold_head_uses_local_delta_for_local() {
        let c_id = local_id("c");
        let d = QualifiedName::from_str("d");
        let fixture = EnvFixture::new();
        let env = fixture.env();
        let mut local_env = empty_local_env();
        local_env.locals.push(Local {
            id: c_id,
            ty: mk_type_prop(),
        });
        local_env.local_deltas.push(LocalDelta {
            id: c_id,
            target: mk_const(d.clone(), vec![], vec![]),
            height: 0,
        });

        let term = mk_local(c_id);
        let unfolded = env
            .unfold_head(&local_env, &term)
            .expect("local should unfold by local delta");
        assert!(unfolded.alpha_eq(&mk_const(d, vec![], vec![])));
    }

    #[test]
    fn local_delta_does_not_apply_to_global_const() {
        let c = QualifiedName::from_str("c");
        let a = QualifiedName::from_str("a");
        let b = QualifiedName::from_str("b");
        let fixture = EnvFixture::new().with_delta(
            c.clone(),
            Delta {
                local_types: vec![],
                local_classes: vec![],
                target: mk_const(a.clone(), vec![], vec![]),
                height: 0,
            },
        );
        let env = fixture.env();
        let mut local_env = empty_local_env();
        local_env.local_deltas.push(LocalDelta {
            id: local_id("c"),
            target: mk_const(b.clone(), vec![], vec![]),
            height: 0,
        });

        let term = mk_const(c, vec![], vec![]);
        let unfolded = env
            .unfold_head(&local_env, &term)
            .expect("constant should unfold by global delta");
        assert!(unfolded.alpha_eq(&mk_const(a, vec![], vec![])));
    }

    #[test]
    fn equiv_unfolds_mixed_local_heads() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let unfoldable_id = local_id("foo.l");
        let rigid_id = Id::from_name(&Name::from_str("x"));
        let local_env = LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            local_deltas: vec![LocalDelta {
                id: unfoldable_id,
                target: mk_local(rigid_id),
                height: 0,
            }],
            locals: vec![
                Local {
                    id: unfoldable_id,
                    ty: mk_type_prop(),
                },
                Local {
                    id: rigid_id,
                    ty: mk_type_prop(),
                },
            ],
        };

        assert!(env.equiv(&local_env, &mk_local(unfoldable_id), &mk_local(rigid_id)));
    }

    #[test]
    fn equiv_uses_local_delta() {
        let c_id = local_id("c");
        let d = QualifiedName::from_str("d");
        let fixture = EnvFixture::new();
        let env = fixture.env();
        let mut local_env = empty_local_env();
        local_env.locals.push(Local {
            id: c_id,
            ty: mk_type_prop(),
        });
        local_env.local_deltas.push(LocalDelta {
            id: c_id,
            target: mk_const(d.clone(), vec![], vec![]),
            height: 0,
        });

        let left = mk_local(c_id);
        let right = mk_const(d, vec![], vec![]);
        assert!(env.equiv(&local_env, &left, &right));
    }

    #[test]
    fn equiv_detects_constant_mismatch() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let c = QualifiedName::from_str("c");
        let d = QualifiedName::from_str("d");
        let left = mk_const(c, vec![], vec![]);
        let right = mk_const(d, vec![], vec![]);

        assert!(!is_equiv(&env, &left, &right));
    }

    #[test]
    fn equiv_detects_argument_mismatch() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let f = QualifiedName::from_str("f");
        let a = QualifiedName::from_str("a");
        let b = QualifiedName::from_str("b");

        let fun = mk_const(f, vec![], vec![]);
        let left = mk_app(fun.clone(), mk_const(a, vec![], vec![]));
        let right = mk_app(fun, mk_const(b, vec![], vec![]));

        assert!(!is_equiv(&env, &left, &right));
    }

    #[test]
    fn infer_type_local_uses_id_lookup() {
        let fixture = EnvFixture::new();
        let env = fixture.env();
        let id = local_id("foo.bar");
        let mut local_env = LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            locals: vec![Local {
                id,
                ty: mk_type_prop(),
            }],
            local_deltas: vec![],
        };

        let term = mk_local(id);
        let inferred = env.infer_type(&mut local_env, &term);
        assert_eq!(inferred, mk_type_prop());
    }

    #[test]
    fn equiv_local_compares_ids() {
        let fixture = EnvFixture::new();
        let env = fixture.env();

        let a_id = local_id("a");
        let b_id = local_id("b");
        let left = mk_local(a_id);
        let right = mk_local(a_id);
        let mismatch = mk_local(b_id);

        let local_env = empty_local_env();
        assert!(env.equiv(&local_env, &left, &right));
        assert!(!env.equiv(&local_env, &left, &mismatch));
    }

    #[test]
    fn local_and_const_are_not_equiv_without_unfold() {
        let fixture = EnvFixture::new().with_const(
            QualifiedName::from_str("c"),
            Const {
                local_types: vec![],
                local_classes: vec![],
                ty: mk_type_prop(),
            },
        );
        let env = fixture.env();
        let c = QualifiedName::from_str("c");
        let c_id = local_id("c");
        let mut local_env = empty_local_env();
        local_env.locals.push(Local {
            id: c_id,
            ty: mk_type_prop(),
        });

        let left = mk_local(c_id);
        let right = mk_const(c, vec![], vec![]);
        assert!(!env.equiv(&local_env, &left, &right));
    }

    #[test]
    fn infer_type_const_ignores_local_name_collision() {
        let c = QualifiedName::from_str("c");
        let fixture = EnvFixture::new().with_const(
            c.clone(),
            Const {
                local_types: vec![],
                local_classes: vec![],
                ty: mk_type_prop(),
            },
        );
        let env = fixture.env();
        let mut local_env = LocalEnv {
            local_types: vec![],
            local_classes: vec![],
            locals: vec![Local {
                id: local_id("c"),
                ty: mk_type_arrow(mk_type_prop(), mk_type_prop()),
            }],
            local_deltas: vec![],
        };

        let term = mk_const(c, vec![], vec![]);
        let inferred = env.infer_type(&mut local_env, &term);
        assert_eq!(inferred, mk_type_prop());
    }

    #[test]
    fn from_name_is_canonical_for_dotted_name() {
        let left = local_id("foo.bar");
        let right = local_id("foo.bar");
        assert_eq!(left, right);
    }

    #[test]
    fn name_returns_some_for_dotted_name_id() {
        let id = local_id("foo.bar");
        assert_eq!(id.name(), Some(Name::from_str("foo.bar")));
    }

    #[test]
    fn mk_local_for_dotted_name_id_is_not_closed() {
        let id = local_id("foo.bar");
        let local = mk_local(id);
        assert!(!local.metadata().is_closed);
    }

    #[test]
    fn path_root_is_canonical() {
        let left = Path::root();
        let right = Path::root();
        assert_eq!(left, right);
        assert!(left.parent().is_none());
        assert!(left.name().is_none());
    }

    #[test]
    fn path_from_parts_is_canonical() {
        let left = Path::from_parts(Path::root(), Name::from_str("foo"));
        let right = Path::from_parts(Path::root(), Name::from_str("foo"));
        assert_eq!(left, right);
    }

    #[test]
    fn path_from_parts_wraps_qualified_name() {
        let path = Path::from_parts(Path::root(), Name::from_str("foo"));
        let Path(Some(qualified_name)) = path else {
            panic!("path must not be root");
        };

        assert_eq!(qualified_name.path(), &Path::root());
        assert_eq!(qualified_name.name(), &Name::from_str("foo"));
    }

    #[test]
    fn path_as_qualified_name_matches_wrapped_value() {
        let path = Path::from_parts(Path::root(), Name::from_str("foo"));
        let Some(qualified_name) = path.as_qualified_name() else {
            panic!("path must provide a qualified name");
        };
        assert_eq!(qualified_name.path(), &Path::root());
        assert_eq!(qualified_name.name(), &Name::from_str("foo"));
        assert!(Path::root().as_qualified_name().is_none());
    }

    #[test]
    fn qualified_name_stores_path_and_name_separately() {
        let path = Path::from_parts(Path::root(), Name::from_str("foo"));
        let name = QualifiedName::from_parts(path.clone(), Name::from_str("bar"));
        assert_eq!(name.path(), &path);
        assert_eq!(name.name().as_str(), "bar");
        assert_eq!(name.to_string(), "foo.bar");
    }
}
