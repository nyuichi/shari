use anyhow::bail;
use shari_kernel::{
    add_axiom, add_const, add_const_type, add_definition, add_lemma, add_notation, assume, change,
    congr_app, eq_elim_old, forall_elim, forall_intro, get_decls, get_fact, imp_elim, imp_intro,
    inst, mk_prop, q, reflexivity, symmetry, transitivity, transport, Decl, DeclAxiom, DeclConst,
    DeclDef, DeclLemma, DeclTypeConst, Fact, Fixity, Kind, Name, Term, TermLocal, Type,
};
use std::sync::Arc;

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

fn apply(
    mut h: Fact,
    terms: impl IntoIterator<Item = Term>,
    facts: impl IntoIterator<Item = Fact>,
) -> anyhow::Result<Fact> {
    for m in terms {
        h = forall_elim(m, h)?;
    }
    for fact in facts {
        h = imp_elim(h, fact)?;
    }
    Ok(h)
}

fn take(name: Name, ty: Type) -> TermLocal {
    TermLocal { name, ty }
}

fn take_fresh(ty: Type) -> TermLocal {
    TermLocal {
        name: Name::fresh(),
        ty,
    }
}

/// ```text
///
/// ----------------------
/// eq_intro m : [⊢ m = m]
/// ```
fn eq_intro(m: Term) -> anyhow::Result<Fact> {
    reflexivity(m)
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ C m₁]
/// ----------------------------------- [indiscernibility of identicals]
/// eq_elim C h₁ h₂ : [Φ ∪ Ψ ⊢ C m₂]
/// ```
fn eq_elim(c: Term, h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    // ⊢ C m₁ = C m₂
    let h = congr_app(eq_intro(c)?, h1)?;
    transport(h, h2)
}

/// ```text
/// h : [Φ ⊢ m₁ = m₂]
/// -------------------------
/// eq_symm h : [Φ ⊢ m₂ = m₁]
/// ```
fn eq_symm(h: Fact) -> anyhow::Result<Fact> {
    symmetry(h)
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ m₂ = m₃]
/// --------------------------------------
/// eq_trans h₁ h₂ : [Φ ⊢ m₁ = m₃]
/// ```
fn eq_trans(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    transitivity(h1, h2)
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ m₁]
/// ----------------------------------
/// eq_mp h₁ h₂ : [Φ ∪ Ψ ⊢ m₂]
/// ```
fn eq_mp(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    transport(h1, h2)
}

/// ```text
/// h : [Φ ⊢ f₁ = f₂]
/// ---------------------------------
/// congr_fun h a : [Φ ⊢ f₁ a = f₂ a]
/// ```
fn congr_fun(h: Fact, a: Term) -> anyhow::Result<Fact> {
    congr_app(h, eq_intro(a)?)
}

/// ```text
/// h : [Φ ⊢ a₁ = a₂]
/// ---------------------------------
/// congr_arg f h : [Φ ⊢ f a₁ = f a₂]
/// ```
fn congr_arg(f: Term, h: Fact) -> anyhow::Result<Fact> {
    congr_app(eq_intro(f)?, h)
}

/// ```text
/// h₁ : [Φ ⊢ f₁ = f₂]  h₂ : [Ψ ⊢ a₁ = a₂]
/// ---------------------------------------
/// congr h₁ h₂ : [Φ ∪ Ψ ⊢ f₁ a₁ = f₂ a₂]
/// ```
fn congr(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    congr_app(h1, h2)
}

fn init_logic() {
    add_notation("⊤", Fixity::Nofix, usize::MAX, "top").unwrap();
    add_notation("∧", Fixity::Infixr, 35, "and").unwrap();
    add_notation("⊥", Fixity::Nofix, usize::MAX, "bot").unwrap();
    add_notation("∨", Fixity::Infixr, 30, "or").unwrap();
    add_notation("¬", Fixity::Prefix, 40, "not").unwrap();
    add_notation("↔", Fixity::Infix, 20, "iff").unwrap();
    add_notation("≠", Fixity::Infix, 50, "ne").unwrap();

    // A modified version of the equality-based representation by Andrews [Andrews, 1986]
    // This version is rather similar to Church encoding.
    // While the original version requires both prop_ext and fun_ext to define most of the connectives,
    // our version does not since imp and forall are builtin.

    add_definition(q!("top"), vec![], q!("(λ (x : Prop), x) = (λ x, x)")).unwrap();

    add_definition(
        q!("and"),
        vec![],
        q!("λ (φ ψ : Prop), ∀ ξ, (φ → ψ → ξ) → ξ"),
    )
    .unwrap();

    add_definition(q!("bot"), vec![], q!("∀ ξ, ξ")).unwrap();

    add_definition(
        q!("or"),
        vec![],
        q!("λ (φ ψ : Prop), ∀ ξ, (φ → ξ) ∧ (ψ → ξ) → ξ"),
    )
    .unwrap();

    add_definition(
        q!("exists"),
        vec![q!("u")],
        q!("λ (P : u → Prop), ∀ ξ, (∀ x, P x → ξ) → ξ"),
    )
    .unwrap();

    add_definition(q!("not"), vec![], q!("λ (φ : Prop), φ → ⊥")).unwrap();

    add_definition(q!("iff"), vec![], q!("λ (φ ψ : Prop), (φ → ψ) ∧ (ψ → φ)")).unwrap();

    add_definition(
        q!("uexists"),
        vec![q!("u")],
        q!("λ (P : u → Prop), ∃ x, P x ∧ (∀ y, P y → x = y)"),
    )
    .unwrap();

    add_definition(q!("ne"), vec![q!("u")], q!("λ (x y : u), ¬ x = y")).unwrap();

    // [⊢ ⊤]
    add_lemma(q!("trivial"), {
        let h = reflexivity(q!("λ (x : Prop), x")).unwrap();
        change(q!("top"), h).unwrap()
    })
    .unwrap();

    add_lemma(q!("and_intro"), {
        let hp = assume(q!("p")).unwrap();
        let hq = assume(q!("q")).unwrap();
        let h = and_intro(hp, hq).unwrap();
        let h = imp_intro(q!("q"), h).unwrap();
        let h = imp_intro(q!("p"), h).unwrap();
        let h = forall_intro(q!("q"), mk_prop(), h).unwrap();
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();

    add_lemma(q!("and_left"), {
        let h = assume(q!("p ∧ q")).unwrap();
        let h = and_left(h).unwrap();
        let h = imp_intro(q!("p ∧ q"), h).unwrap();
        let h = forall_intro(q!("q"), mk_prop(), h).unwrap();
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();

    add_lemma(q!("and_right"), {
        let h = assume(q!("p ∧ q")).unwrap();
        let h = and_right(h).unwrap();
        let h = imp_intro(q!("p ∧ q"), h).unwrap();
        let h = forall_intro(q!("q"), mk_prop(), h).unwrap();
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();

    add_lemma(q!("mp"), {
        let h1 = assume(q!("p → q")).unwrap();
        let h2 = assume(q!("p")).unwrap();
        let h = imp_elim(h1, h2).unwrap();
        let h = imp_intro(q!("p → q"), h).unwrap();
        let h = imp_intro(q!("p"), h).unwrap();
        let h = forall_intro(q!("q"), mk_prop(), h).unwrap();
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();

    add_lemma(q!("mt"), {
        let h_p_imp_q = assume(q!("p → q")).unwrap();
        let h_not_q = assume(q!("¬q")).unwrap();
        let h_q_imp_bot = change(q!("q → ⊥"), h_not_q).unwrap();
        let h_p = assume(q!("p")).unwrap();
        let h_q = apply(h_p_imp_q, [], [h_p]).unwrap();
        let h_bot = apply(h_q_imp_bot, [], [h_q]).unwrap();
        let h_not_p = change(q!("¬p"), imp_intro(q!("p"), h_bot).unwrap()).unwrap();
        let h_not_q_imp_not_p = imp_intro(q!("¬q"), h_not_p).unwrap();
        let h = imp_intro(q!("p → q"), h_not_q_imp_not_p).unwrap();
        forall_intro(
            q!("p"),
            mk_prop(),
            forall_intro(q!("q"), mk_prop(), h).unwrap(),
        )
        .unwrap()
    })
    .unwrap();

    add_lemma(q!("absurd"), {
        // ⊥ ⊢ ⊥
        let h = assume(q!("⊥")).unwrap();
        // ⊥ ⊢ ∀ p, p
        let h = change(q!("∀ p, p"), h).unwrap();
        // ⊥ ⊢ p
        let h = forall_elim(q!("p"), h).unwrap();
        // ⊢ ⊥ → p
        let h = imp_intro(q!("⊥"), h).unwrap();
        // ⊢ ∀ p, ⊥ → p
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();

    add_lemma(q!("contradiction"), {
        let h1 = assume(q!("p")).unwrap();
        let h2 = assume(q!("¬p")).unwrap();
        let h2 = change(q!("p → ⊥"), h2).unwrap();
        let h = mp(h2, h1).unwrap();
        let h = imp_intro(q!("¬p"), h).unwrap();
        let h = imp_intro(q!("p"), h).unwrap();
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();

    add_lemma(q!("not_is_fixpoint_free"), {
        let h = assume(q!("p = ¬p")).unwrap();
        // [p = ¬p, p ⊢ p]
        let p_holds = assume(q!("p")).unwrap();
        // [p = ¬p, p ⊢ ¬p]
        let not_p_holds = transport(h.clone(), p_holds.clone()).unwrap();
        // [p = ¬p, p ⊢ ⊥]
        let bot_holds = apply(
            get_fact(q!("contradiction")).unwrap(),
            [q!("p")],
            [p_holds, not_p_holds],
        )
        .unwrap();
        // [p = ¬p ⊢ ¬p]
        let not_p_holds = change(q!("¬p"), imp_intro(q!("p"), bot_holds).unwrap()).unwrap();
        // [p = ¬p ⊢ p]
        let p_holds = eq_mp(symmetry(h).unwrap(), not_p_holds.clone()).unwrap();
        // [p = ¬p ⊢ ⊥]
        let bot_holds = apply(
            get_fact(q!("contradiction")).unwrap(),
            [q!("p")],
            [p_holds, not_p_holds],
        )
        .unwrap();
        let h = imp_intro(q!("p = ¬p"), bot_holds).unwrap();
        let h = change(q!("p ≠ ¬p"), h).unwrap();
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();
}

/// ```text
///
/// ------------------
/// top_intro : [⊢ ⊤]
/// ```
fn top_intro() -> Fact {
    let id = q!("λ (x : Prop), x");
    let h = eq_intro(id).unwrap();
    let top = q!("top");
    change(top, h).unwrap()
}

#[test]
fn test_top_intro() {
    insta::assert_display_snapshot!(top_intro(), @"⊢ ⊤");
}

/// ```text
/// h₁ : [Φ ⊢ φ]  h₂ : [Ψ ⊢ ψ]
/// ---------------------------------
/// and_intro h₁ h₂ : [Φ ∪ Ψ ⊢ φ ∧ ψ]
/// ```
fn and_intro(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let p1 = h1.target();
    let p2 = h2.target();
    let g: Term = q!("${} ∧ ${}", p1, p2);
    let r = take_fresh(mk_prop());
    let p: Term = q!("${} → ${} → ${}", p1, p2, r);
    let h = assume(p.clone()).unwrap();
    let h = imp_elim(h, h1)?;
    let h = imp_elim(h, h2)?;
    let h = imp_intro(p, h).unwrap();
    let h = forall_intro(r.name, r.ty, h).unwrap();
    change(g, h)
}

/// ```text
/// h : [Φ ⊢ φ ∧ ψ]
/// --------------------
/// and_left h : [Φ ⊢ φ]
/// ```
fn and_left(h: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h.target())?.clone();
    let p2 = rhs(h.target())?.clone();
    let p: Term = q!("∀ r, (${} → ${} → r) → r", p1, p2);
    // h: ∀ r, (p → q → r) → r
    let h = change(p, h)?;
    let h = forall_elim(p1.clone(), h)?;
    let proj = assume(p1.clone()).unwrap();
    let proj = imp_intro(p2, proj).unwrap();
    let proj = imp_intro(p1, proj).unwrap();
    imp_elim(h, proj)
}

/// ```text
/// h : [Φ ⊢ φ ∧ ψ]
/// ---------------------
/// and_right h : [Φ ⊢ ψ]
/// ```
fn and_right(h: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h.target())?.clone();
    let p2 = rhs(h.target())?.clone();
    let p: Term = q!("∀ r, (${} → ${} → r) → r", p1, p2);
    // h: ∀ r, (p → q → r) → r
    let h = change(p, h)?;
    let h = forall_elim(p2.clone(), h)?;
    let proj = assume(p2.clone()).unwrap();
    let proj = imp_intro(p2, proj).unwrap();
    let proj = imp_intro(p1, proj).unwrap();
    imp_elim(h, proj)
}

#[test]
fn test_and() {
    let p = q!("p");
    let q = q!("q");
    let h1 = assume(p).unwrap();
    let h2 = assume(q).unwrap();
    let h = and_intro(h1, h2).unwrap();
    insta::assert_display_snapshot!(h, @"((p : Prop)) ((q : Prop)) ⊢ (p : Prop) ∧ (q : Prop)");
    insta::assert_display_snapshot!(and_left(h.clone()).unwrap(), @"((p : Prop)) ((q : Prop)) ⊢ (p : Prop)");
    insta::assert_display_snapshot!(and_right(h).unwrap(), @"((p : Prop)) ((q : Prop)) ⊢ (q : Prop)");
}

/// ```text
/// h : [Φ ⊢ φ]
/// ---------------------------
/// or_intro1 ψ h : [Φ ⊢ φ ∨ ψ]
/// ```
fn or_intro1(q: Term, h: Fact) -> anyhow::Result<Fact> {
    let p = h.target();
    let goal: Term = q!("${} ∨ ${}", p, q);
    let r = take_fresh(mk_prop());
    let c: Term = q!("(${} → ${}) ∧ (${} → ${})", p, r, q, r);
    // ha: (φ → ξ) ∧ (ψ → ξ) ⊢ (φ → ξ) ∧ (ψ → ξ)
    let ha = assume(c.clone()).unwrap();
    // ha: (φ → ξ) ∧ (ψ → ξ) ⊢ φ → ξ
    let ha = and_left(ha).unwrap();
    // ha: Φ, (φ → ξ) ∧ (ψ → ξ) ⊢ ξ
    let ha = imp_elim(ha, h)?;
    // ha: Φ ⊢ (φ → ξ) ∧ (ψ → ξ) → ξ
    let ha = imp_intro(c, ha).unwrap();
    // ha: Φ ⊢ ∀ ξ, (φ → ξ) ∧ (ψ → ξ) → ξ
    let ha = forall_intro(r.name, r.ty, ha).unwrap();
    change(goal, ha)
}

/// ```text
/// h : [Φ ⊢ ψ]
/// ---------------------------
/// or_intro2 φ h : [Φ ⊢ φ ∨ ψ]
/// ```
fn or_intro2(p: Term, h: Fact) -> anyhow::Result<Fact> {
    let q = h.target();
    let goal: Term = q!("${} ∨ ${}", p, q);
    let r = take_fresh(mk_prop());
    let c: Term = q!("(${} → ${}) ∧ (${} → ${})", p, r, q, r);
    // ha: (φ → ξ) ∧ (ψ → ξ) ⊢ (φ → ξ) ∧ (ψ → ξ)
    let ha = assume(c.clone()).unwrap();
    // ha: (φ → ξ) ∧ (ψ → ξ) ⊢ ψ → ξ
    let ha = and_right(ha).unwrap();
    // ha: Φ, (φ → ξ) ∧ (ψ → ξ) ⊢ ξ
    let ha = imp_elim(ha, h)?;
    // ha: Φ ⊢ (φ → ξ) ∧ (ψ → ξ) → ξ
    let ha = imp_intro(c, ha).unwrap();
    // ha: Φ ⊢ ∀ ξ, (φ → ξ) ∧ (ψ → ξ) → ξ
    let ha = forall_intro(r.name, r.ty, ha).unwrap();
    change(goal, ha)
}

/// ```text
/// h₁ : [Φ ⊢ φ ∨ ψ]  h₂ : [Ψ ⊢ ξ]  h₃ : [Ξ ⊢ ξ]
/// ---------------------------------------------
/// or_elim ψ h : [Φ ∪ (Ψ - {φ}) ∪ (Ξ - {ψ}) ⊢ ξ]
/// ```
fn or_elim(h1: Fact, h2: Fact, h3: Fact) -> anyhow::Result<Fact> {
    let p = lhs(h1.target())?.clone();
    let q = rhs(h1.target())?.clone();
    let r = h2.target().clone();
    let c: Term = q!("∀ r, (${} → r) ∧ (${} → r) → r", p, q);
    let h1 = change(c, h1)?;
    let h1 = forall_elim(r, h1)?;
    let h2 = imp_intro(p, h2)?;
    let h3 = imp_intro(q, h3)?;
    let ha = and_intro(h2, h3).unwrap();
    imp_elim(h1, ha)
}

/// TODO: refine
/// ```text
/// h : [Φ ⊢ φ m]
/// ---------------------------------------
/// exists_intro φ m h : [Φ ⊢ ∃ (x : τ), φ]
/// ```
fn exists_intro(p: Term, m: Term, h: Fact) -> anyhow::Result<Fact> {
    let goal: Term = q!("exists ${}", p);
    let r = take_fresh(mk_prop());
    let c: Term = q!("∀ x, ${} x → ${}", p, r);
    let q = q!("${} ${}", p, m);
    let h = change(q, h)?;
    let ha = assume(c.clone())?;
    let ha = forall_elim(m, ha)?;
    let h = imp_elim(ha, h)?;
    let h = imp_intro(c, h)?;
    let h = forall_intro(r.name, r.ty, h)?;
    change(goal, h)
}

/// ```text
/// h₁ : [Φ ⊢ ∃ (x : τ), φ]  h₂ : [Ψ ⊢ ψ]
/// ---------------------------------------------- ((y : τ) # (Ψ - {[y/x]φ}, ψ))
/// exists_elim y h₁ h₂ : [Φ ∪ (Ψ - {[y/x]φ}) ⊢ ψ]
/// ```
fn exists_elim(name: Name, h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let mut args = h1.target().args();
    if args.len() != 1 {
        bail!("not an exists");
    }
    // pred :≡ λ (x : τ), φ
    let pred = args.pop().unwrap();
    let Term::Abs(inner) = pred else {
        bail!("exists must take an abstraction");
    };
    // p :≡ [y/x]φ
    let mut p = inner.body.clone();
    let y = TermLocal {
        name,
        ty: inner.binder_type.clone(),
    };
    p.open(&y.clone().into());
    let q = h2.target().clone();
    let h2 = imp_intro(p.clone(), h2)?;
    let h2 = change(q!("${} ${} → ${}", pred, y, q), h2)?;
    let h2 = forall_intro(y.name, y.ty, h2)?;
    let h1 = change(q!("∀ r, (∀ x, ${} x → r) → r", pred), h1)?;
    apply(h1, [q], [h2])
}

/// TODO: refine
/// ```text
/// h₁ : [Φ ⊢ φ → ψ]  h₂ : [Φ ⊢ φ']
/// -------------------------------  (φ ≡ φ')
/// mp h₁ h₂ : [Φ ⊢ ψ]
/// ```
fn mp(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h1.target())?;
    let h2 = change(p1.clone(), h2)?;
    imp_elim(h1, h2)
}

fn beta_reduce(h: Fact) -> anyhow::Result<Fact> {
    let mut target = h.target().clone();
    target.beta_reduce();
    change(target, h)
}

/// ```text
/// h : [Φ ⊢ ⊥]
/// ------------------------------
/// not_intro φ h : [Φ - {φ} ⊢ ¬φ]
/// ```
fn not_intro(p: Term, h: Fact) -> anyhow::Result<Fact> {
    let goal: Term = q!("¬ ${}", p);
    let h = imp_intro(p, h)?;
    change(goal, h)
}

/// ```text
/// h : [Φ ⊢ ¬φ]
/// -------------------------
/// not_elim h : [Φ ⊢ φ → ⊥]
/// ```
fn not_elim(h: Fact) -> anyhow::Result<Fact> {
    let p = arg(h.target())?;
    let goal: Term = q!("${} → ⊥", p);
    change(goal, h)
}

fn imp_trans(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h1.target())?.clone();
    let h = assume(p1.clone())?;
    let h = imp_elim(h1, h)?;
    let h = imp_elim(h2, h)?;
    imp_intro(p1, h)
}

/// ```text
/// h₁ : [Φ ⊢ φ → ψ]  h₂ : [Ψ ⊢ ¬ψ]
/// -------------------------------
/// mt h₁ h₂ : [Φ ∪ Ψ ⊢ ¬φ]
/// ```
fn mt(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let h2 = not_elim(h2)?;
    let h = imp_trans(h1, h2)?;
    let p = lhs(h.target())?;
    let goal: Term = q!("¬ ${}", p);
    change(goal, h)
}

/// ```text
///
/// --------------------------
/// top_ne_bot : [⊢ ⊤ ≠ ⊥]
/// ```
fn top_ne_bot() -> Fact {
    let p: Term = q!("⊤ = ⊥");
    let h1 = assume(p.clone()).unwrap();
    let h = eq_mp(h1, top_intro()).unwrap();
    change(q!("⊤ ≠ ⊥"), not_intro(p, h).unwrap()).unwrap()
}

/// ```text
/// h₁ : [Φ ⊢ φ]  h₂ : [Ψ ⊢ ψ]
/// -------------------------------------------------
/// iff_intro h₁ h₂ : [(Φ - {ψ}) ∪ (Ψ - {φ}) ⊢ φ ↔ ψ]
/// ```
fn iff_intro(h1: Fact, h2: Fact) -> Fact {
    let p1 = h1.target().clone();
    let p2 = h2.target().clone();
    let g = q!("${} ↔ ${}", p1, p2);
    let h1 = imp_intro(p2, h1).unwrap();
    let h2 = imp_intro(p1, h2).unwrap();
    let h = and_intro(h2, h1).unwrap();
    change(g, h).unwrap()
}

/// ```text
/// h : [Φ ⊢ φ ↔ ψ]
/// -------------------------
/// iff_right h : [Φ ⊢ φ → ψ]
/// ```
fn iff_right(h: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h.target())?;
    let p2 = rhs(h.target())?;
    let h = change(q!("(${} → ${}) ∧ (${} → ${})", p1, p2, p2, p1), h)?;
    and_left(h)
}

/// ```text
/// h : [Φ ⊢ φ ↔ ψ]
/// ------------------------
/// iff_left h : [Φ ⊢ ψ → φ]
/// ```
fn iff_left(h: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h.target())?;
    let p2 = rhs(h.target())?;
    let h = change(q!("(${} → ${}) ∧ (${} → ${})", p1, p2, p2, p1), h)?;
    and_right(h)
}

fn init_function() {
    add_definition(
        q!("injective"),
        vec![q!("u"), q!("v")],
        q!("λ (f : u → v), ∀ x y, f x = f y → x = y"),
    )
    .unwrap();

    add_definition(
        q!("surjective"),
        vec![q!("u"), q!("v")],
        q!("λ (f : u → v), ∀ y, ∃ x, f x = y"),
    )
    .unwrap();

    add_lemma(q!("lawvere_fixpoint"), {
        let e = take(q!("e"), q!("u → u → v"));
        let f = take(q!("f"), q!("v → v"));
        let h = assume(q!("surjective ${}", e)).unwrap();
        let h = change(q!("∀ y, ∃ x, ${} x = y", e), h).unwrap();
        let h = apply(h, [q!("λ x, ${} (${} x x)", f, e)], []).unwrap();
        let x = take_fresh(q!("u"));
        let hh = assume(q!("${} ${} = (λ x, ${} (${} x x))", e, x, f, e)).unwrap();
        let hh = congr_fun(hh, x.clone().into()).unwrap();
        let hh = change(
            q!("${} ${} ${} = ${} (${} ${} ${})", e, x, x, f, e, x, x),
            hh,
        )
        .unwrap();
        let hh = change(q!("(λ y, y = ${} y) (${} ${} ${})", f, e, x, x), hh).unwrap();
        // hh: [e x = (λ x, f (e x x)) ⊢ ∃ y, y = f y]
        let hh = exists_intro(q!("λ y, y = ${} y", f), q!("${} ${} ${}", e, x, x), hh).unwrap();
        let h = exists_elim(x.name, h, hh).unwrap();
        let h = forall_intro(f.name, f.ty, h).unwrap();
        let h_exists_surj = assume(q!("∃ (e : u → u → v), surjective e")).unwrap();
        let h = exists_elim(e.name, h_exists_surj, h).unwrap();
        imp_intro(q!("∃ (e : u → u → v), surjective e"), h).unwrap()
    })
    .unwrap()
}

fn init_classical() {
    add_axiom(q!("prop_ext"), q!("∀ φ ψ, (φ ↔ ψ) ↔ (φ = ψ)")).unwrap();

    add_axiom(
        q!("fun_ext"),
        q!("∀ (f₁ f₂ : u → v), (∀ x, f₁ x = f₂ x) ↔ (f₁ = f₂)"),
    )
    .unwrap();

    // emulate the `inhabited` type class by dictionary passing
    add_const_type(q!("inhabited"), Kind(1)).unwrap();

    add_const(q!("inhabited_prop"), vec![], q!("inhabited Prop")).unwrap();

    add_const(
        q!("choice"),
        vec![q!("u")],
        q!("inhabited u → (u → Prop) → u"),
    )
    .unwrap();

    add_axiom(
        q!("choice_spec"),
        q!("∀ (h : inhabited u), ∀ (P : u → Prop), (∃ x, P x) → P (choice h P)"),
    )
    .unwrap();

    add_lemma(q!("em"), em()).unwrap();

    add_lemma(q!("ma"), {
        let h1 = assume(q!("p = ⊤")).unwrap();
        let h1 = ma(h1).unwrap();
        let h2 = assume(q!("p")).unwrap();
        let h2 = mar(h2);
        let h = prop_ext(iff_intro(h1, h2)).unwrap();
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();

    add_lemma(q!("nma"), {
        let h1 = {
            let h1 = assume(q!("p = ⊥")).unwrap();
            let h2 = assume(q!("p")).unwrap();
            let h = eq_mp(h1, h2).unwrap();
            let h = imp_intro(q!("p"), h).unwrap();
            // p = ⊥ ⊢ ¬p
            change(q!("¬p"), h).unwrap()
        };
        let h2 = {
            let h1 = {
                // ⊥ ⊢ ⊥
                let h = assume(q!("⊥")).unwrap();
                // ⊥ ⊢ p
                apply(get_fact(q!("absurd")).unwrap(), [q!("p")], [h]).unwrap()
            };
            let h2 = {
                // ¬p ⊢ ¬p
                let h1 = assume(q!("¬p")).unwrap();
                let h1 = change(q!("p → ⊥"), h1).unwrap();
                // p ⊢ p
                let h2 = assume(q!("p")).unwrap();
                // ¬p, p ⊢ ⊥
                imp_elim(h1, h2).unwrap()
            };
            // ¬p ⊢ p = ⊥
            prop_ext(iff_intro(h1, h2)).unwrap()
        };
        // ⊢ ¬p = (p = ⊥)
        let h = prop_ext(iff_intro(h1, h2)).unwrap();
        forall_intro(q!("p"), mk_prop(), h).unwrap()
    })
    .unwrap();
}

/// ```text
/// h : [Φ ⊢ φ ↔ ψ]
/// ------------------------ [propositional extensionality]
/// prop_ext h : [Φ ⊢ φ = ψ]
/// ```
fn prop_ext(h: Fact) -> anyhow::Result<Fact> {
    let p1 = lhs(h.target())?.clone();
    let p2 = rhs(h.target())?.clone();
    let prop_ext = apply(get_fact(q!("prop_ext")).unwrap(), [p1, p2], [])?;
    let prop_ext_right = iff_right(prop_ext).unwrap();
    apply(prop_ext_right, [], [h])
}

/// ```text
/// h : [Φ ⊢ m₁ = m₂]
/// ------------------------------------------------------- (x ∉ FV Φ) [function extensionality]
/// fun_ext x τ h : [Φ ⊢ (λ (x : τ), m₁) = (λ (x : τ), m₂)]
/// ```
pub fn fun_ext(x: Name, t: Type, h: Fact) -> anyhow::Result<Fact> {
    let m1 = lhs(h.target())?;
    let m2 = rhs(h.target())?;
    let Term::Const(inner) = h.target().head() else {
        bail!("not a constant");
    };
    if inner.ty_args.len() != 1 {
        bail!("number of type arguments mismatch");
    }
    let cod_ty = &inner.ty_args[0];
    let mut m1 = m1.clone();
    let mut m2 = m2.clone();
    m1.discharge_local(x, t.clone());
    m2.discharge_local(x, t.clone());
    let fun_ext = inst(
        q!("v"),
        cod_ty,
        inst(q!("u"), &t, get_fact(q!("fun_ext")).unwrap()).unwrap(),
    )
    .unwrap();
    let fun_ext = iff_right(apply(fun_ext, [m1.clone(), m2.clone()], []).unwrap()).unwrap();
    m1.apply([Term::Local(Arc::new(TermLocal {
        name: x,
        ty: t.clone(),
    }))]);
    m2.apply([Term::Local(Arc::new(TermLocal {
        name: x,
        ty: t.clone(),
    }))]);
    let h = change(q!("${} = ${}", m1, m2), h)?;
    let h = forall_intro(x, t, h).unwrap();
    apply(fun_ext, [], [h])
}

fn em() -> Fact {
    // Diaconescu's argument
    let p = take(q!("p"), q!("Prop"));
    // uu :≡ λ x, x = ⊤ ∨ p
    let uu: Term = q!("λ x, x = ⊤ ∨ ${}", p);
    // vv :≡ λ x, x = ⊥ ∨ p
    let vv: Term = q!("λ x, x = ⊥ ∨ ${}", p);
    // ex_uu : ⊢ ∃ x, uu x
    let ex_uu = {
        // h : ⊢ ⊤ = ⊤ ∨ p
        let h: Fact = or_intro1(q!("${}", p), eq_intro(q!("⊤")).unwrap()).unwrap();
        exists_intro(uu.clone(), q!("⊤"), h).unwrap()
    };
    // ex_vv : ⊢ ∃ x, vv x
    let ex_vv = {
        // h : ⊢ ⊥ = ⊥ ∨ p
        let h: Fact = or_intro1(q!("${}", p), eq_intro(q!("⊥")).unwrap()).unwrap();
        exists_intro(vv.clone(), q!("⊥"), h).unwrap()
    };
    let u: Term = q!("choice inhabited_prop ${}", uu);
    let v: Term = q!("choice inhabited_prop ${}", vv);
    // u_spec : ⊢ u = ⊤ ∨ p
    let u_spec = {
        let h = get_fact(q!("choice_spec")).unwrap();
        let h = inst(q!("u"), &mk_prop(), h).unwrap();
        let h = forall_elim(q!("inhabited_prop"), h).unwrap();
        let h = forall_elim(uu.clone(), h).unwrap();
        let h = mp(h, ex_uu).unwrap();
        beta_reduce(h).unwrap()
    };
    // u_spec : ⊢ v = ⊥ ∨ p
    let v_spec = {
        let h = get_fact(q!("choice_spec")).unwrap();
        let h = inst(q!("u"), &mk_prop(), h).unwrap();
        let h = forall_elim(q!("inhabited_prop"), h).unwrap();
        let h = forall_elim(vv.clone(), h).unwrap();
        let h = mp(h, ex_vv).unwrap();
        beta_reduce(h).unwrap()
    };
    // u_ne_v_or_p : u ≠ v ∨ p
    let u_ne_v_or_p = {
        // h1: (u = ⊤), (v = ⊥) ⊢ u ≠ v ∨ p
        let h1 = {
            let h1 = assume(q!("${} = ⊤", u)).unwrap();
            let mut c: Term = q!("λ p, p ≠ ⊥");
            c.undischarge();
            // h : [⊢ u ≠ ⊥]
            let h = eq_elim_old(c, eq_symm(h1).unwrap(), top_ne_bot()).unwrap();
            let h2 = assume(q!("${} = ⊥", v)).unwrap();
            let mut c: Term = q!("λ q, ${} ≠ q", u);
            c.undischarge();
            let h = eq_elim_old(c, eq_symm(h2).unwrap(), h).unwrap();
            or_intro1(q!("p"), h).unwrap()
        };
        // h2: p ⊢ u ≠ v ∨ p
        let h2 = {
            let h = assume(q!("p")).unwrap();
            or_intro2(q!("${} ≠ ${}", u, v), h).unwrap()
        };
        or_elim(u_spec, or_elim(v_spec, h1, h2.clone()).unwrap(), h2).unwrap()
    };
    // p_imp_u_eq_v : p → (u = v)
    let p_imp_u_eq_v = {
        let p_imp_uu_eq_vv = {
            // h1: p ⊢ x = ⊤ ∨ p
            let h1 = {
                let h = assume(q!("p")).unwrap();
                or_intro2(q!("x = ⊤"), h).unwrap()
            };
            // h2: p ⊢ x = ⊥ ∨ p
            let h2 = {
                let h = assume(q!("p")).unwrap();
                or_intro2(q!("x = ⊥"), h).unwrap()
            };
            let h = prop_ext(iff_intro(h1, h2)).unwrap();
            fun_ext(q!("x"), mk_prop(), h).unwrap()
        };
        let h = congr_arg(q!("choice inhabited_prop"), p_imp_uu_eq_vv).unwrap();
        imp_intro(q!("p"), h).unwrap()
    };
    // h1: u ≠ v ⊢ p ∨ ¬p
    let h1 = {
        let h = mt(
            p_imp_u_eq_v,
            change(
                q!("¬(${} = ${})", u, v),
                assume(q!("${} ≠ ${}", u, v)).unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        or_intro2(q!("p"), h).unwrap()
    };
    // h2: p ⊢ p ∨ ¬p
    let h2 = or_intro1(q!("¬p"), assume(q!("p")).unwrap()).unwrap();
    let h = or_elim(u_ne_v_or_p, h1, h2).unwrap();
    forall_intro(q!("p"), mk_prop(), h).unwrap()

    /*
    Λ p, {
      let U := `(λ x, x = ⊤ ∨ 'p),
      let V := `(λ x, x = ⊥ ∨ 'p),
      have ⟨∃ x, 'U x⟩ := {
        have h : ⟨⊤ = ⊤⟩ := eq_refl `⊤,
        have h : ⟨⊤ = ⊤ ∨ 'p⟩ := or_intro1 p h,
        exists_intro U `⊤ h
      },
      have ⟨∃ x, 'V x⟩ := {
        have ⟨⊥ = ⊥⟩ := eq_refl `⊥,
        have ⟨⊥ = ⊥ ∨ 'p⟩ := or_intro1 p ⟨⊥ = ⊥⟩,
        exists_intro V `⊥ ⟨⊥ = ⊥ ∨ 'p⟩
      },
      let u := `(choice.{Prop} inhabited_prop 'U),
      let v := `(choice.{Prop} inhabited_prop 'V),
      have u_spec : `('U 'u) := choice_spec.{Prop} inhabited_prop U ⟨∃ x, 'U x⟩,
      have v_spec : `('V 'v) := choice_spec.{Prop} inhabited_prop V ⟨∃ x, 'V x⟩,
      have u_ne_v_or_p : `(u ≠ v ∨ 'p) := {
        have hu : `('u = ⊤ ∨ 'p) := u_spec,
        have hv : `('v = ⊥ ∨ 'p) := v_spec,
        hu.case {
          h1 : `(u = ⊤) := {
            hv.case {
              h2 : `(v = ⊥) := {
                have h : `(⊤ ≠ ⊥) := top_ne_bot,
                have h : `(u ≠ ⊥) := eq_elim `(λ x, x ≠ ⊥) (eq_symm h1) h,
                have h : `(u ≠ v) := eq_elim `(λ x, 'u ≠ x) (eq_symm h2) h,
                or_intro p h
              },
              hp : p := {
                or_intro `('u ≠ 'v) hp
              }
            }
          },
          hp : p := {
            or_intro `('u ≠ 'v) hp
          }
        }
      },
    },
    have p_imp_u_eq_v : `('p → 'u = 'v) := λ (hp : p), {
      have U_eq_V : `('U = 'V) := fun_ext (Λ x, {
        have Ux : `('U 'x) := or_intro2 `('x = ⊤) hp,
        have Vx : `('V 'x) := or_intro2 `('x = ⊥) hp,
        have Ux_eq_Vx `('U 'x = 'V 'x) := proof_irrel Ux Vx,
        have h : `('U 'x ↔ 'V 'x) := iff_intro (λ _, Vx) (λ _, Ux),
        prop_ext h
      }),
      congr_arg `(choice.{Prop} inhabited_prop) U_eq_V
    },
    u_ne_v_or_p.case {
      h1 : `('u ≠ 'v) := {
        have h : `('u ≠ 'v → ¬ 'p) := mt p_imp_u_eq_v,
        or_intro2 p (h h1)
      },
      h2 : p := {
        or_intro1 `(¬ 'p) h2
      },
    }
    */
}

/// ```text
/// h : [Φ ⊢ φ]
/// -------------------- [reverse of material adequacy]
/// mar h : [Φ ⊢ φ = ⊤]
/// ```
fn mar(h: Fact) -> Fact {
    prop_ext(iff_intro(h, top_intro())).unwrap()
}

#[test]
fn test_mar() {
    let p = q!("p");
    insta::assert_display_snapshot!(mar(assume(p).unwrap()), @"((p : Prop)) ⊢ (p : Prop) = ⊤");
}

/// ```text
/// h : [Φ ⊢ φ = ⊤]
/// ---------------- [material adequacy]
/// ma h : [Φ ⊢ φ]
/// ```
fn ma(h: Fact) -> anyhow::Result<Fact> {
    eq_mp(eq_symm(h)?, top_intro())
}

#[test]
fn test_ma() {
    let p = q!("p");
    insta::assert_display_snapshot!(ma(mar(assume(p).unwrap())).unwrap(), @"((p : Prop)) ⊢ (p : Prop)");
}

fn init_set() {
    add_notation("∈", Fixity::Infix, 50, "mem").unwrap();
    add_notation("∉", Fixity::Infix, 50, "notmem").unwrap();
    add_notation("⊆", Fixity::Infix, 50, "subset").unwrap();
    add_notation("∩", Fixity::Infixl, 70, "cap").unwrap();
    add_notation("∪", Fixity::Infixl, 65, "cup").unwrap();
    add_notation("∖", Fixity::Infix, 70, "setminus").unwrap();
    add_notation("∅", Fixity::Nofix, usize::MAX, "empty").unwrap();

    // TODO: introduce type abbreviation Set u := u → Prop

    add_definition(
        q!("mem"),
        vec![q!("u")],
        q!("λ (x : u) (s : u → Prop), s x"),
    )
    .unwrap();

    add_definition(
        q!("notmem"),
        vec![q!("u")],
        q!("λ (x : u) (s : u → Prop), ¬(x ∈ s)"),
    )
    .unwrap();

    add_definition(q!("univ"), vec![q!("u")], q!("λ (x : u), ⊤")).unwrap();

    add_definition(q!("empty"), vec![q!("u")], q!("λ (x : u), ⊥")).unwrap();

    add_definition(
        q!("subset"),
        vec![q!("u")],
        q!("λ (s t : u → Prop), ∀ x, x ∈ s → x ∈ t"),
    )
    .unwrap();

    add_definition(
        q!("sep"),
        vec![q!("u")],
        q!("λ (s : u → Prop) (φ : u → Prop), λ x, x ∈ s ∧ φ x"),
    )
    .unwrap();

    add_definition(
        q!("cap"),
        vec![q!("u")],
        q!("λ (s t : u → Prop), { x | x ∈ s ∧ x ∈ t }"),
    )
    .unwrap();

    add_definition(
        q!("cup"),
        vec![q!("u")],
        q!("λ (s t : u → Prop), { x | x ∈ s ∨ x ∈ t }"),
    )
    .unwrap();

    add_definition(
        q!("bigcap"),
        vec![q!("u")],
        q!("λ (a : (u → Prop) → Prop), { x | ∀ s, s ∈ a → x ∈ s }"),
    )
    .unwrap();

    add_definition(
        q!("bigcup"),
        vec![q!("u")],
        q!("λ (a : (u → Prop) → Prop), { x | ∃ s, s ∈ a ∧ x ∈ s }"),
    )
    .unwrap();

    add_definition(
        q!("power"),
        vec![q!("u")],
        q!("λ (s : u → Prop), { t | t ⊆ s }"),
    )
    .unwrap();

    add_definition(
        q!("setminus"),
        vec![q!("u")],
        q!("λ (s t : u → Prop), { x | x ∈ s ∧ x ∉ t }"),
    )
    .unwrap();

    add_definition(
        q!("im"),
        vec![q!("u"), q!("v")],
        q!("λ (f : u → v) (s : u → Prop), { y | ∃ x, x ∈ s ∧ f x = y }"),
    )
    .unwrap();

    add_definition(
        q!("inj_on"),
        vec![q!("u"), q!("v")],
        q!("λ (s : u → Prop) (f : u → v), ∀ x y, x ∈ s ∧ y ∈ s → f x = f y → x = y"),
    )
    .unwrap();

    add_lemma(q!("cantor"), {
        let lawvere = inst(
            q!("v"),
            &mk_prop(),
            get_fact(q!("lawvere_fixpoint")).unwrap(),
        )
        .unwrap();
        let mt_lawvere = apply(
            get_fact(q!("mt")).unwrap(),
            [
                q!("∃ (e : u → u → Prop), surjective e"),
                q!("∀ (f : Prop → Prop), ∃ y, y = f y"),
            ],
            [lawvere],
        )
        .unwrap();
        // ⊢ ¬(∀ f, ∃ y, y = f y)
        let h = {
            let h = assume(q!("∀ (f : Prop → Prop), ∃ y, y = f y")).unwrap();
            let h = apply(h, [q!("not")], []).unwrap();
            let y = take(q!("y"), q!("Prop"));
            // y = f y ⊢ ⊥
            let h_contr = {
                let h_y_eq_not_y = assume(q!("${} = ¬ ${}", y, y)).unwrap();
                let h_y_ne_not_y = apply(
                    get_fact(q!("not_is_fixpoint_free")).unwrap(),
                    [q!("${}", y)],
                    [],
                )
                .unwrap();
                let h_not_y_eq_not_y = change(q!("¬(${} = ¬ ${})", y, y), h_y_ne_not_y).unwrap();
                apply(
                    get_fact(q!("contradiction")).unwrap(),
                    [q!("${} = ¬ ${}", y, y)],
                    [h_y_eq_not_y, h_not_y_eq_not_y],
                )
                .unwrap()
            };
            let h_contr = exists_elim(y.name, h, h_contr).unwrap();
            not_intro(q!("∀ (f : Prop → Prop), ∃ y, y = f y"), h_contr).unwrap()
        };
        apply(mt_lawvere, [], [h]).unwrap()
    })
    .unwrap();
}

fn init() {
    init_logic();
    init_function();
    init_classical();
    init_set();
}

#[cfg(test)]
#[ctor::ctor]
fn dev_init() {
    init()
}

fn main() {
    init();

    let decls = get_decls();
    for (name, decl) in decls {
        match decl {
            Decl::Const(DeclConst { local_types, ty }) => {
                if local_types.is_empty() {
                    println!("constant {name} : {ty}");
                } else {
                    let v: Vec<_> = local_types.iter().map(ToString::to_string).collect();
                    println!("constant {name}.{{{}}} : {ty}", v.join(", "));
                }
            }
            Decl::Def(DeclDef {
                local_types,
                target,
                ty,
            }) => {
                if local_types.is_empty() {
                    println!("def {name} : {ty} := {target}");
                } else {
                    let v: Vec<_> = local_types.iter().map(ToString::to_string).collect();
                    println!("def {name}.{{{}}} : {ty} := {target}", v.join(", "));
                }
            }
            Decl::TypeConst(DeclTypeConst { kind }) => {
                println!("type constant {name} : {kind}");
            }
            Decl::Axiom(DeclAxiom { formula }) => {
                println!("axiom {name} : {formula}");
            }
            Decl::Lemma(DeclLemma { fact }) => {
                let target = fact.target();
                println!("lemma {name} : {target}");
            }
        }
    }
}
