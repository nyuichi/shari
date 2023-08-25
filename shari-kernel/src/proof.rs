use std::{mem, sync::Arc};

use anyhow::bail;
use once_cell::sync::Lazy;

use crate::env::{get_def, DeclDef};
#[cfg(test)]
use crate::q;
use crate::tt::{mk_const, mk_type_arrow, mk_type_const, Kind, Name, Term, Type};

/// Judgmental equality for the definitional equality.
#[derive(Debug, Clone)]
pub struct Conv {
    left: Term,
    right: Term,
    ty: Type,
}

impl std::fmt::Display for Conv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ≡ {} : {}", self.left, self.right, self.ty)
    }
}

impl Conv {
    pub fn left(&self) -> &Term {
        &self.left
    }

    pub fn right(&self) -> &Term {
        &self.right
    }
}

/// ```text
///
/// -----------------------
/// reflexivity m : [m ≡ m]
/// ```
pub fn reflexivity(mut m: Term) -> anyhow::Result<Conv> {
    let ty = m.infer()?;
    Ok(Conv {
        left: m.clone(),
        right: m,
        ty,
    })
}

/// ```text
/// h : [m₁ ≡ m₂]
/// --------------------------
/// symmetry h : [m₂ ≡ m₁]
/// ```
pub fn symmetry(h: Conv) -> Conv {
    Conv {
        left: h.right,
        right: h.left,
        ty: h.ty,
    }
}

/// ```text
/// h₁ : [m₁ ≡ m₂]  h₂ : [m₂ ≡ m₃]
/// ------------------------------
/// transitivity h₁ h₂ : [m₁ ≡ m₃]
/// ```
pub fn transitivity(h1: Conv, h2: Conv) -> anyhow::Result<Conv> {
    if h1.ty != h2.ty {
        bail!("types mismatch");
    }
    if h1.right != h2.left {
        bail!("transitivity mismatch");
    }
    Ok(Conv {
        left: h1.left,
        right: h2.right,
        ty: h1.ty,
    })
}

/// ```text
/// h₁ : [f₁ ≡ f₂]  h₂ : [a₁ ≡ a₂]
/// ---------------------------------
/// congr_app h₁ h₂ : [f₁ a₁ ≡ f₂ a₂]
/// ```
pub fn congr_app(h1: Conv, h2: Conv) -> anyhow::Result<Conv> {
    let mut m1 = h1.left;
    let mut m2 = h1.right;
    m1.apply([h2.left]);
    m2.apply([h2.right]);
    let ty = m1.infer()?;
    Ok(Conv {
        left: m1,
        right: m2,
        ty,
    })
}

/// ```text
/// h : [m₁ ≡ m₂]
/// -----------------------------------------------------------
/// congr_abs x τ h : [(λ (x : τ), m₁) ≡ (λ (x : τ), m₂)]
/// ```
pub fn congr_abs(x: Name, t: Type, h: Conv) -> Conv {
    let mut m1 = h.left;
    let mut m2 = h.right;
    m1.discharge_local(x, t.clone());
    m2.discharge_local(x, t.clone());
    let ty = mk_type_arrow(t, h.ty);
    Conv {
        left: m1,
        right: m2,
        ty,
    }
}

/// ```text
///
/// ------------------------------------------------------
/// beta_reduce ((λ x, m₁) m₂) : [(λ x, m₁) m₂ ≡ [m₂/x]m₁]
/// ```
pub fn beta_reduce(mut m: Term) -> anyhow::Result<Conv> {
    let ty = m.infer()?;
    let Term::App(inner) = &m else {
        bail!("not a beta redex");
    };
    let arg = &inner.arg;
    let Term::Abs(inner) = &inner.fun else {
        bail!("not a beta redex");
    };
    let mut n = inner.body.clone();
    n.open(arg);
    Ok(Conv {
        left: m,
        right: n,
        ty,
    })
}

/// ```text
///
/// ---------------------------------------------------------- (c.{u₁ ⋯ uₙ} :≡ m)
/// delta_reduce c.{t₁ ⋯ tₙ} : [c.{t₁ ⋯ tₙ} ≡ [t₁/u₁ ⋯ tₙ/uₙ]m]
/// ```
pub fn delta_reduce(name: Name, ty_args: Vec<Type>) -> anyhow::Result<Conv> {
    let Some(def) = get_def(name) else {
        bail!("definition not found: {name}");
    };
    let DeclDef {
        local_types,
        mut target,
        mut ty,
    } = def;
    if local_types.len() != ty_args.len() {
        bail!("number of type arguments mismatch");
    }
    let mut subst = vec![];
    for (&x, t) in std::iter::zip(&local_types, &ty_args) {
        t.check(&Kind::base())?;
        subst.push((x, t));
    }
    target.instantiate(&subst);
    ty.subst(&subst);
    let c = mk_const(name, ty_args);
    Ok(Conv {
        left: c,
        right: target,
        ty,
    })
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Fact {
    context: Vec<Term>,
    target: Term,
}

impl std::fmt::Display for Fact {
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
    let mut args = m.unapply();
    let Term::Const(mut inner) = m else {
        unreachable!();
    };
    let ty = Arc::make_mut(&mut inner).ty_args.pop().unwrap();
    let m2 = args.pop().unwrap();
    let m1 = args.pop().unwrap();
    Ok((ty, m1, m2))
}

pub fn mk_prop() -> Type {
    static PROP: Lazy<Type> = Lazy::new(|| mk_type_const(Name::intern("Prop").unwrap()));
    PROP.clone()
}

/// ```text
///
/// ------------------
/// assume φ : [φ ⊢ φ]
/// ```
pub fn assume(mut target: Term) -> anyhow::Result<Fact> {
    target.check(&mut mk_prop())?;
    Ok(Fact {
        context: vec![target.clone()],
        target,
    })
}

#[test]
fn test_assume_ok() {
    use crate::tt::mk_local;

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
    use crate::tt::mk_local;

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
    p.check(&mut mk_prop())?;
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
        bail!("argument mismatch:\nexpected:\t{p}\ngot:\t\t{}", h2.target);
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
    insta::assert_display_snapshot!(imp_intro(p, eq_intro(mk_const(*IMP, vec![])).unwrap()).unwrap(), @"⊢ (p : Prop) → imp = imp");

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
    t.check(&Kind::base())?;
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
    m.check(&mut domain_ty)?;
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
    let h = eq_intro(q!("imp")).unwrap();
    insta::assert_display_snapshot!(forall_intro("p".try_into().unwrap(), mk_prop(), h).unwrap(), @"⊢ ∀ (p : Prop), imp = imp");

    let p: Term = q!("p");
    let h = assume(p.clone()).unwrap();
    let h = imp_intro(p, h).unwrap();
    let h = forall_intro("p".try_into().unwrap(), mk_prop(), h).unwrap();
    insta::assert_display_snapshot!(forall_elim(q!("q"), h).unwrap(), @"⊢ (q : Prop) → (q : Prop)");
}

/// ```text
///
/// ----------------------
/// eq_intro m : [⊢ m = m]
/// ```
pub fn eq_intro(mut m: Term) -> anyhow::Result<Fact> {
    let ty = m.infer()?;
    let mut target = mk_const(*EQ, vec![ty]);
    target.apply([m.clone(), m]);
    Ok(Fact {
        context: vec![],
        target,
    })
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ c m₁]
/// ------------------------------------ [indiscernibility of identicals]
/// eq_elim c h₁ h₂ : [Φ ∪ Ψ ⊢ c m₂]
/// ```
pub fn eq_elim(mut c: Term, h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let (ty, m1, m2) = dest_eq(h1.target)?;
    c.check(&mut mk_type_arrow(ty, mk_prop()))?;
    let mut cm1 = c.clone();
    cm1.apply([m1]);
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
    target.apply([m2]);
    Ok(Fact {
        context: ctx,
        target,
    })
}

/// ```text
/// h1 : [φ ≡ ψ]  h2 : [Φ ⊢ φ]
/// --------------------------
/// convert ψ h : [Φ ⊢ ψ]
/// ```
pub fn convert(h1: Conv, h2: Fact) -> anyhow::Result<Fact> {
    if h1.ty != mk_prop() {
        bail!("not a definitional equality between propositions");
    }
    if &h1.left != h2.target() {
        bail!("terms mismatch");
    }
    Ok(Fact {
        context: h2.context,
        target: h1.right,
    })
}

/// ```text
///
/// ---------------
/// axiom φ : [⊢ φ]
/// ```
pub fn axiom(mut p: Term) -> anyhow::Result<Fact> {
    p.check(&mut mk_prop())?;
    if !p.is_closed() {
        bail!("formula not closed");
    }
    Ok(Fact {
        context: vec![],
        target: p,
    })
}

/// This rule is not supposed to be used directly by users.
///
/// ```text
/// h : [Φ ⊢ φ]
/// ------------------------------------------
/// instantiate (u τ)* h : [[τ/u*]Φ ⊢ [τ/u*]φ]
/// ```
pub fn instantiate(subst: &[(Name, &Type)], mut h: Fact) -> anyhow::Result<Fact> {
    for (_, t) in subst {
        t.check(&Kind::base())?;
    }
    for p in &mut h.context {
        p.instantiate(subst);
    }
    h.target.instantiate(subst);
    Ok(h)
}
