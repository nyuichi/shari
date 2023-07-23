mod term;

use std::{mem, sync::Arc};

use anyhow::bail;
use term::{
    add_definition, add_notation, by_def, eq_elim, eq_intro, prop_ext, Fact, Fixity, LocalEnv,
    Name, Term, Type,
};

/// ```text
///
/// ---------------------------
/// eq_refl Γ m : [Γ ▸ ⊢ m = m]
/// ```
fn eq_refl(local_env: LocalEnv, m: Term) -> anyhow::Result<Fact> {
    eq_intro(local_env, m.clone(), m)
}

/// ```text
/// h : [Γ ▸ Φ ⊢ m₁ = m₂]
/// -----------------------------
/// eq_symm h : [Γ ▸ Φ ⊢ m₂ = m₁]
/// ```
fn eq_symm(h: Fact) -> anyhow::Result<Fact> {
    let m2 = {
        let pat: Term = "eq #_ #m2".parse().unwrap();
        let Some(subst) = pat.match1(h.target()) else {
            bail!("expected equality, but got {}", h.target());
        };
        *subst.get("m2").unwrap()
    };
    let c = {
        let mut pat: Term = "λ x, eq #m2 x".parse().unwrap();
        pat.subst_mvar("m2", m2);
        let Term::Abs(mut p) = pat else {
            panic!();
        };
        mem::take(&mut Arc::make_mut(&mut p).body)
    };
    let ha = eq_refl(h.local_env().clone(), m2.clone())?;
    eq_elim(c, h, ha)
}

/// ```text
///
/// --------------------
/// top_intro : [ ▸ ⊢ ⊤]
/// ```
fn top_intro() -> anyhow::Result<Fact> {
    let id = "λ (x : Prop), x".parse().unwrap();
    let local_env = LocalEnv::new();
    let h = eq_refl(local_env, id)?;
    let c = {
        let pat: Term = "λ x, x".parse().unwrap();
        let Term::Abs(mut p) = pat else {
            panic!();
        };
        mem::take(&mut Arc::make_mut(&mut p).body)
    };
    let top_def = by_def(&Name::try_from("top").unwrap())?;
    eq_elim(c, top_def, h)
}

/// ```text
/// h : [Γ ▸ Φ ⊢ φ]
/// ---------------------- [material adequacy]
/// ma h : [Γ ▸ Φ ⊢ φ = ⊤]
/// ```
fn ma(h: Fact) -> anyhow::Result<Fact> {
    prop_ext(h, top_intro()?)
}

// /// ```text
// /// h : [Γ ▸ Φ ⊢ m₁ = m₂]
// /// -------------------------------------
// /// congr_fun f h : [Γ ▸ Φ ⊢ f m₁ = f m₂]
// /// ```
// fn congr_fun(f: &Term, h: &Fact) -> anyhow::Result<Fact> {
//     // qq! { let "eq m1 #m2" = target };
//     let (mut m1, mut m2) = {
//         let pat: Term = "eq #m1 #m2".parse().unwrap();
//         let Some(unif) = pat.matches(h.target()) else {
//             bail!("expected equality, but got {}", h.target());
//         };
//         let m1 = unif.get("m1").unwrap();
//         let m2 = unif.get("m2").unwrap();
//         (m1, m2)
//     };
//     // let c = qq!("eq (#f _) (#f #m2)").unwrap();
//     let c = {
//         let mut pat: Term = "eq (#f _) (#f #m2)".parse().unwrap();
//         pat.subst_mvar("f", f);
//         pat.subst_mvar("m2", m2);
//         pat
//     };
//     eq_elim(&c, h, &eq_refl(h.local_env().clone(), m2)?)
// }

fn main() {
    println!("{}", "λ (x : α → α), x".parse::<Term>().unwrap());
    let id = "λ (x : Prop), x".parse::<Term>().unwrap();
    let idf = "(λ (f : Prop → Prop), f) (λ (x : Prop), x)"
        .parse::<Term>()
        .unwrap();
    let local_env = LocalEnv::new();
    let h1 = eq_intro(local_env, id, idf).unwrap();
    println!("{h1}");
    let h2 = eq_symm(h1).unwrap();
    println!("{h2}");

    add_notation("⊤", Fixity::Nofix, usize::MAX, "top").unwrap();
    add_notation("∧", Fixity::Infixr, 35, "and").unwrap();
    add_notation("→", Fixity::Infixr, 25, "imp").unwrap();
    add_notation("⊥", Fixity::Nofix, usize::MAX, "bot").unwrap();
    add_notation("∨", Fixity::Infixr, 30, "or").unwrap();
    add_notation("¬", Fixity::Prefix, 40, "not").unwrap();
    add_notation("↔", Fixity::Infix, 20, "iff").unwrap();

    add_definition(
        "top",
        [],
        Type::prop(),
        "(λ (x : Prop), x) = (λ x, x)".parse().unwrap(),
    )
    .unwrap();

    let h = top_intro().unwrap();
    println!("{h}");

    let h3 = ma(h2).unwrap();
    println!("{h3}");

    add_definition(
        "and",
        [],
        "Prop → Prop → Prop".parse().unwrap(),
        "λ (φ ψ : Prop), (λf : Prop → Prop → Prop, f φ ψ) = (λ f, f ⊤ ⊤)"
            .parse()
            .unwrap(),
    )
    .unwrap();

    // def top : Prop := (λx : Prop, x) = (λx, x)
    // def and (φ ψ : Prop) : Prop := (λf : Prop → Prop → Prop, f φ ψ) = (λ f, f ⊤ ⊤)
    // def imp (φ ψ : Prop) : Prop := φ = φ ∧ ψ   -- Recall [x = x ∧ y] means [x ≤ y] in the preorder canonically induced by a lattice structure.
    // def forall (P : u → Prop) : Prop := P = (λ x, ⊤)
    // def bot : Prop := ∀ ξ, ξ
    // def or (φ ψ : Prop) : Prop := ∀ ξ, (φ → ξ) ∧ (ψ → ξ) → ξ
    // def exists (P : u → Prop) : Prop := ∀ ξ, (∀ x, P x → ξ) → ξ
    // def not (φ : Prop) : Prop := φ → ⊥
    // def iff (φ ψ : Prop) : Prop := (φ → ψ) ∧ (ψ → φ)
    // def uexists (P : u → Prop) : Prop := ∃ x, P x ∧ (∀ y, P y → x = y)
}
