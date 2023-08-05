mod term;

use anyhow::bail;
use std::sync::Arc;
use term::{
    add_definition, add_notation, assume, eq_elim, eq_intro, fun_ext, prop_ext, Fact, Fixity, Name,
    Term, TermLocal, Type,
};

fn lhs(m: &Term) -> anyhow::Result<&Term> {
    if !m.binders().all(|_| false) {
        bail!("not an application");
    }
    let args = m.args();
    if args.len() != 2 {
        bail!("not a binary application");
    }
    Ok(args[0])
}

fn rhs(m: &Term) -> anyhow::Result<&Term> {
    if !m.binders().all(|_| false) {
        bail!("not an application");
    }
    let args = m.args();
    if args.len() != 2 {
        bail!("not a binary application");
    }
    Ok(args[1])
}

fn arg(m: &Term) -> anyhow::Result<&Term> {
    if !m.binders().all(|_| false) {
        bail!("not an application");
    }
    let args = m.args();
    if args.len() != 1 {
        bail!("not a unary application");
    }
    Ok(args[0])
}

/// ```text
/// h : [Φ ⊢ φ]
/// ----------------------- (φ ≡ ψ)
/// change ψ h: [Φ ⊢ ψ]
/// ```
fn change(m: Term, h: Fact) -> anyhow::Result<Fact> {
    let n = h.target().clone();
    let h_eqv = eq_intro(n, m)?;
    eq_elim(Term::Var(0), h_eqv, h)
}

/// ```text
///
/// ---------------------
/// eq_refl m : [⊢ m = m]
/// ```
fn eq_refl(m: Term) -> anyhow::Result<Fact> {
    eq_intro(m.clone(), m)
}

/// ```text
/// h : [Φ ⊢ m₁ = m₂]
/// -------------------------
/// eq_symm h : [Φ ⊢ m₂ = m₁]
/// ```
fn eq_symm(h: Fact) -> anyhow::Result<Fact> {
    let m1 = lhs(h.target())?;
    let c = {
        let mut c: Term = "λ m1 x, eq x m1".parse().unwrap();
        c.undischarge();
        c.open_at(m1, 1);
        c
    };
    let ha = eq_refl(m1.clone())?;
    eq_elim(c, h, ha)
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ m₂ = m₃]
/// --------------------------------------
/// eq_trans h₁ h₂ : [Φ ⊢ m₁ = m₃]
/// ```
fn eq_trans(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let m3 = rhs(h2.target())?;
    let c = {
        let mut c: Term = "λ m3 x, eq x m3".parse().unwrap();
        c.undischarge();
        c.open_at(m3, 1);
        c
    };
    eq_elim(c, eq_symm(h1)?, h2)
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ m₁]
/// ----------------------------------
/// eq_mp h₁ h₂ : [Φ ∪ Ψ ⊢ m₂]
/// ```
fn eq_mp(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    eq_elim(Term::Var(0), h1, h2)
}

/// ```text
/// h : [Φ ⊢ f₁ = f₂]
/// ---------------------------------
/// congr_fun h a : [Φ ⊢ f₁ a = f₂ a]
/// ```
fn congr_fun(h: Fact, a: Term) -> anyhow::Result<Fact> {
    let f1 = lhs(h.target())?;
    let mut c: Term = "λ f1 a f, f1 a = f a".parse().unwrap();
    c.undischarge();
    c.open_at(f1, 2);
    c.open_at(&a, 1);
    let mut f1a = f1.clone();
    f1a.apply([a]);
    eq_elim(c, h, eq_refl(f1a)?)
}

/// ```text
/// h : [Φ ⊢ a₁ = a₂]
/// ---------------------------------
/// congr_arg f h : [Φ ⊢ f a₁ = f a₂]
/// ```
fn congr_arg(f: Term, h: Fact) -> anyhow::Result<Fact> {
    let a1 = lhs(h.target())?;
    let mut c: Term = "λ a1 f a, f a1 = f a".parse().unwrap();
    c.undischarge();
    c.open_at(a1, 2);
    c.open_at(&f, 1);
    let mut fa1 = f;
    fa1.apply([a1.clone()]);
    eq_elim(c, h, eq_refl(fa1)?)
}

/// ```text
/// h₁ : [Φ ⊢ f₁ = f₂]  h₂ : [Ψ ⊢ a₁ = a₂]
/// ---------------------------------------
/// congr h₁ h₂ : [Φ ∪ Ψ ⊢ f₁ a₁ = f₂ a₂]
/// ```
fn congr(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let f2 = rhs(h1.target())?.clone();
    let a1 = lhs(h2.target())?.clone();
    // h3: f₁ a₁ = f₂ a₁
    let h3 = congr_fun(h1, a1)?;
    // h4: f₂ a₁ = f₂ a₂
    let h4 = congr_arg(f2, h2)?;
    eq_trans(h3, h4)
}

fn init_logic() {
    add_notation("⊤", Fixity::Nofix, usize::MAX, "top").unwrap();
    add_notation("∧", Fixity::Infixr, 35, "and").unwrap();
    add_notation("→", Fixity::Infixr, 25, "imp").unwrap();
    add_notation("⊥", Fixity::Nofix, usize::MAX, "bot").unwrap();
    add_notation("∨", Fixity::Infixr, 30, "or").unwrap();
    add_notation("¬", Fixity::Prefix, 40, "not").unwrap();
    add_notation("↔", Fixity::Infix, 20, "iff").unwrap();

    // Equality-based representation by Andrews [Andrews, 1986]

    add_definition(
        "top".try_into().unwrap(),
        vec![],
        "(λ (x : Prop), x) = (λ x, x)".parse().unwrap(),
    )
    .unwrap();

    add_definition(
        "and".try_into().unwrap(),
        vec![],
        "λ (φ ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = (λ f, f ⊤ ⊤)"
            .parse()
            .unwrap(),
    )
    .unwrap();

    add_definition(
        "imp".try_into().unwrap(),
        vec![],
        "λ (φ ψ : Prop), φ = (φ ∧ ψ)".parse().unwrap(),
    )
    .unwrap();

    add_definition(
        "forall".try_into().unwrap(),
        vec!["u".try_into().unwrap()],
        "λ (P : u → Prop), P = (λ x, ⊤)".parse().unwrap(),
    )
    .unwrap();

    add_definition("bot".try_into().unwrap(), vec![], "∀ ξ, ξ".parse().unwrap()).unwrap();

    add_definition(
        "or".try_into().unwrap(),
        vec![],
        "λ (φ ψ : Prop), ∀ ξ, (φ → ξ) ∧ (ψ → ξ) → ξ"
            .parse()
            .unwrap(),
    )
    .unwrap();

    add_definition(
        "exists".try_into().unwrap(),
        vec!["u".try_into().unwrap()],
        "λ (P : u → Prop), ∀ ξ, (∀ x, P x → ξ) → ξ".parse().unwrap(),
    )
    .unwrap();

    add_definition(
        "not".try_into().unwrap(),
        vec![],
        "λ (φ : Prop), φ → ⊥".parse().unwrap(),
    )
    .unwrap();

    add_definition(
        "iff".try_into().unwrap(),
        vec![],
        "λ (φ ψ : Prop), (φ → ψ) ∧ (ψ → φ)".parse().unwrap(),
    )
    .unwrap();

    add_definition(
        "uexists".try_into().unwrap(),
        vec!["u".try_into().unwrap()],
        "λ (P : u → Prop), ∃ x, P x ∧ (∀ y, P y → x = y)"
            .parse()
            .unwrap(),
    )
    .unwrap();
}

/// ```text
///
/// ------------------
/// top_intro : [⊢ ⊤]
/// ```
fn top_intro() -> anyhow::Result<Fact> {
    let id = "λ (x : Prop), x".parse().unwrap();
    let h = eq_refl(id)?;
    let top = "top".parse().unwrap();
    change(top, h)
}

#[test]
fn test_top_intro() {
    insta::assert_display_snapshot!(top_intro().unwrap(), @"⊢ ⊤");
}

/// ```text
/// h : [Φ ⊢ φ]
/// -------------------- [reverse of material adequacy]
/// mar h : [Φ ⊢ φ = ⊤]
/// ```
fn mar(h: Fact) -> anyhow::Result<Fact> {
    prop_ext(h, top_intro()?)
}

#[test]
fn test_mar() {
    let p = "p".parse().unwrap();
    insta::assert_display_snapshot!(mar(assume(p).unwrap()).unwrap(), @"((p : Prop)) ⊢ (p : Prop) = ⊤");
}

/// ```text
/// h : [Φ ⊢ φ = ⊤]
/// ---------------- [material adequacy]
/// ma h : [Φ ⊢ φ]
/// ```
fn ma(h: Fact) -> anyhow::Result<Fact> {
    eq_mp(eq_symm(h)?, top_intro()?)
}

#[test]
fn test_ma() {
    let p = "p".parse().unwrap();
    insta::assert_display_snapshot!(ma(mar(assume(p).unwrap()).unwrap()).unwrap(), @"((p : Prop)) ⊢ (p : Prop)");
}

/// ```text
/// h₁ : [Φ ⊢ φ]  h₂ : [Ψ ⊢ ψ]
/// ---------------------------------
/// and_intro h₁ h₂ : [Φ ∪ Ψ ⊢ φ ∧ ψ]
/// ```
fn and_intro(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let p1 = h1.target();
    let p2 = h2.target();
    let mut p: Term = "λ p q, p ∧ q".parse().unwrap();
    p.undischarge();
    p.open_at(p1, 1);
    p.open_at(p2, 0);
    // h1: φ = ⊤
    let h1 = mar(h1)?;
    // h2: ψ = ⊤
    let h2 = mar(h2)?;
    let f = TermLocal {
        name: Name::fresh(),
        ty: "Prop → Prop → Prop".parse().unwrap(),
    };
    let h = congr(congr_arg(Term::Local(Arc::new(f.clone())), h1)?, h2)?;
    // h: (λ f, f φ ψ) = (λ f, f ⊤ ⊤)
    let h = fun_ext(&f.name, f.ty, h)?;
    change(p, h)
}

/// ```text
/// h : [Φ ⊢ φ ∧ ψ]
/// ---------------------
/// and_elim1 h : [Φ ⊢ φ]
/// ```
fn and_elim1(h: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h.target())?;
    let p2 = rhs(h.target())?;
    let mut p: Term = "λ (p q : Prop), (λ (f : Prop → Prop → Prop), f p q) = (λ f, f ⊤ ⊤)"
        .parse()
        .unwrap();
    p.undischarge();
    p.open_at(p1, 1);
    p.open_at(p2, 0);
    let mut q: Term = "λ p, p = ⊤".parse().unwrap();
    q.undischarge();
    q.open_at(p1, 0);
    // h: (λ f, f φ ψ) = (λ f, f ⊤ ⊤)
    let h = change(p, h)?;
    let f = "λ (p q : Prop), p".parse().unwrap();
    // h: (λ f, f φ ψ) (λ p q, p) = (λ f, f ⊤ ⊤) (λ p q, p)
    let h = congr_fun(h, f)?;
    // h: φ = ⊤
    let h = change(q, h)?;
    ma(h)
}

/// ```text
/// h : [Φ ⊢ φ ∧ ψ]
/// ---------------------
/// and_elim2 h : [Φ ⊢ ψ]
/// ```
fn and_elim2(h: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h.target())?;
    let p2 = rhs(h.target())?;
    let mut p: Term = "λ (p q : Prop), (λ (f : Prop → Prop → Prop), f p q) = (λ f, f ⊤ ⊤)"
        .parse()
        .unwrap();
    p.undischarge();
    p.open_at(p1, 1);
    p.open_at(p2, 0);
    let mut q: Term = "λ p, p = ⊤".parse().unwrap();
    q.undischarge();
    q.open_at(p2, 0);
    // h: (λ f, f φ ψ) = (λ f, f ⊤ ⊤)
    let h = change(p, h)?;
    let f = "λ (p q : Prop), q".parse().unwrap();
    // h: (λ f, f φ ψ) (λ p q, q) = (λ f, f ⊤ ⊤) (λ p q, q)
    let h = congr_fun(h, f)?;
    // h: ψ = ⊤
    let h = change(q, h)?;
    ma(h)
}

#[test]
fn test_and() {
    let p = "p".parse().unwrap();
    let q = "q".parse().unwrap();
    let h1 = assume(p).unwrap();
    let h2 = assume(q).unwrap();
    let h = and_intro(h1, h2).unwrap();
    insta::assert_display_snapshot!(h, @"((p : Prop)) ((q : Prop)) ⊢ (p : Prop) ∧ (q : Prop)");
    insta::assert_display_snapshot!(and_elim1(h.clone()).unwrap(), @"((p : Prop)) ((q : Prop)) ⊢ (p : Prop)");
    insta::assert_display_snapshot!(and_elim2(h).unwrap(), @"((p : Prop)) ((q : Prop)) ⊢ (q : Prop)");
}

/// ```text
/// h : [Φ ⊢ ψ]
/// ---------------------------------
/// imp_intro φ h : [Φ - {φ} ⊢ φ → ψ]
/// ```
fn imp_intro(p: Term, h: Fact) -> anyhow::Result<Fact> {
    let q = h.target();
    let mut a: Term = "λ p q, p ∧ q".parse().unwrap();
    a.undischarge();
    a.open_at(&p, 1);
    a.open(q);
    let mut b: Term = "λ p q, p → q".parse().unwrap();
    b.undischarge();
    b.open_at(&p, 1);
    b.open(q);
    // h1: φ ∧ ψ ⊢ φ ∧ ψ
    let h1 = assume(a)?;
    // h1: φ ∧ ψ ⊢ φ
    let h1 = and_elim1(h1)?;
    // hp: φ ⊢ φ
    let hp = assume(p)?;
    // h2: φ ⊢ φ ∧ ψ
    let h2 = and_intro(hp, h)?;
    // h: φ = φ ∧ ψ
    let h = prop_ext(h1, h2)?;
    change(b, h)
}

/// ```text
/// h₁ : [Φ ⊢ φ → ψ]  h₂ : [Φ ⊢ φ]
/// -------------------------------
/// imp_elim h₁ h₂ : [Φ ⊢ ψ]
/// ```
fn imp_elim(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let p = lhs(h1.target())?;
    let q = rhs(h1.target())?;
    let mut a: Term = "λ p q, p = (p ∧ q)".parse().unwrap();
    a.undischarge();
    a.open_at(p, 1);
    a.open(q);
    // h1: φ = (φ ∧ ψ)
    let h1 = change(a, h1)?;
    // h: φ ∧ ψ
    let h = eq_mp(h1, h2)?;
    and_elim2(h)
}

#[test]
fn test_imp() {
    let p: Term = "p".parse().unwrap();
    let h = assume(p.clone()).unwrap();
    insta::assert_display_snapshot!(imp_intro(p, h).unwrap(), @"⊢ (p : Prop) → (p : Prop)");

    // weakening
    let p: Term = "p".parse().unwrap();
    insta::assert_display_snapshot!(imp_intro(p, top_intro().unwrap()).unwrap(), @"⊢ (p : Prop) → ⊤");

    let p = "p".parse().unwrap();
    let q = "q".parse().unwrap();
    let h1 = assume(p).unwrap();
    let h2 = assume(q).unwrap();
    let h = and_intro(h1, h2).unwrap();
    let a = h.target().clone();
    // h: p ∧ q ⊢ p
    let h = and_elim1(h).unwrap();
    insta::assert_display_snapshot!(imp_intro(a, h).unwrap(), @"((p : Prop)) ((q : Prop)) ⊢ (p : Prop) ∧ (q : Prop) → (p : Prop)");

    let h1 = assume("p → q".parse().unwrap()).unwrap();
    let h2 = assume("p".parse().unwrap()).unwrap();
    insta::assert_display_snapshot!(imp_elim(h1, h2).unwrap(), @"((p : Prop) → (q : Prop)) ((p : Prop)) ⊢ (q : Prop)");
}

/// ```text
/// h : [Φ ⊢ ψ]
/// --------------------------------------- ((x : τ) # Φ)
/// forall_intro x τ h : [Φ ⊢ ∀ (x : τ), φ]
/// ```
fn forall_intro(x: &Name, t: Type, h: Fact) -> anyhow::Result<Fact> {
    let h = mar(h)?;
    // h: (λ x, φ) = (λ x, ⊤)
    let h = fun_ext(x, t, h)?;
    let p = lhs(h.target())?;
    let mut goal: Term = "λ P, forall P".parse().unwrap();
    goal.undischarge();
    goal.open(p);
    change(goal, h)
}

/// ```text
/// h : [Φ ⊢ ∀ (x : τ), φ]
/// ------------------------------
/// forall_elim m h : [Φ ⊢ [m/x]φ]
/// ```
fn forall_elim(m: Term, h: Fact) -> anyhow::Result<Fact> {
    let p = arg(h.target())?;
    let mut a: Term = "λ p, p = (λ x, ⊤)".parse().unwrap();
    a.undischarge();
    a.open(p);
    let Term::Abs(inner) = p else {
        bail!("not an abstraction");
    };
    let mut goal = inner.body.clone();
    goal.open(&m);
    // h: (λ x, φ) = (λ x, ⊤)
    let h = change(a, h)?;
    // h: (λ x, φ) m = (λ x, ⊤) m
    let h = congr_fun(h, m)?;
    let mut hr: Term = "λ p, p = ⊤".parse().unwrap();
    hr.undischarge();
    hr.open(&goal);
    // h: ([m/x]φ) = ⊤
    let h = change(hr, h)?;
    ma(h)
}

#[test]
fn test_forall() {
    // err
    let p: Term = "p".parse().unwrap();
    let h = assume(p.clone()).unwrap();
    insta::assert_display_snapshot!(forall_intro(&"p".try_into().unwrap(), Type::prop(), h).unwrap_err(), @"eigenvariable condition fails");

    let p: Term = "p".parse().unwrap();
    let h = assume(p.clone()).unwrap();
    let h = imp_intro(p, h).unwrap();
    insta::assert_display_snapshot!(forall_intro(&"p".try_into().unwrap(), Type::prop(), h).unwrap(), @"⊢ ∀ (p : Prop), p → p");

    // weakening
    let h = top_intro().unwrap();
    insta::assert_display_snapshot!(forall_intro(&"p".try_into().unwrap(), Type::prop(), h).unwrap(), @"⊢ ∀ (p : Prop), ⊤");

    let p: Term = "p".parse().unwrap();
    let h = assume(p.clone()).unwrap();
    let h = imp_intro(p, h).unwrap();
    let h = forall_intro(&"p".try_into().unwrap(), Type::prop(), h).unwrap();
    insta::assert_display_snapshot!(forall_elim("q".parse().unwrap(), h).unwrap(), @"⊢ (q : Prop) → (q : Prop)");
}

#[cfg(test)]
#[ctor::ctor]
fn init() {
    init_logic();
}

fn main() {
    init_logic();

    let id = "λ (x : Prop), x".parse::<Term>().unwrap();
    let idf = "(λ (f : Prop → Prop), f) (λ (x : Prop), x)"
        .parse::<Term>()
        .unwrap();
    let h1 = eq_intro(id, idf).unwrap();
    println!("h1: {h1}");
    let h2 = eq_symm(h1).unwrap();
    println!("h2: {h2}");

    let h = top_intro().unwrap();
    println!("{h}");

    let h3 = mar(h2).unwrap();
    println!("h3: {h3}");

    let h4 = ma(h3).unwrap();
    println!("h4: {h4}");

    let h5 = and_intro(
        eq_refl("λ (x : Prop), x".parse().unwrap()).unwrap(),
        top_intro().unwrap(),
    )
    .unwrap();
    println!("h5: {h5}");
}
