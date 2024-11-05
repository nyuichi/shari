use crate::kernel::{
    proof::{
        mk_proof_assump, mk_proof_forall_intro, mk_proof_imp_intro, mk_type_prop, Context, Prop,
    },
    tt::{mk_local, LocalEnv, Name},
};
use crate::state::State;

mod cmd;
mod kernel;
mod lex;
mod parse;
mod print;
mod state;

fn main() -> anyhow::Result<()> {
    let mut state = State::new();

    state.run("infixr ⇒ : 25 := imp")?;
    state.run("infix = : 50 := eq")?;
    state.run("nofix ⊤ := top")?;
    state.run("infixr ∧ : 35 := and")?;
    state.run("nofix ⊥ := bot")?;
    state.run("infixr ∨ : 30 := or")?;
    state.run("prefix ¬ : 40 := not")?;
    state.run("infix ⇔ : 20 := iff")?;
    state.run("infix ≠ : 50 := ne")?;

    // Leibniz equality
    state.run("def eq.{u} (x : u) (y : u) : Prop := ∀ P, P x ⇒ P y")?;

    // The following definitions are attributed to [Andrews, 1986].
    state.run("def top : Prop := (λ (x : Prop), x) = (λ x, x)")?;
    state.run("def and (φ : Prop) (ψ : Prop) : Prop := ∀ ξ, (φ ⇒ ψ ⇒ ξ) ⇒ ξ")?;

    // The following definitions are due to Prawitz and Russell.
    state.run("def bot : Prop := ∀ ξ, ξ")?;
    state.run("def or (φ : Prop) (ψ : Prop) : Prop := ∀ ξ, (φ ⇒ ξ) ∧ (ψ ⇒ ξ) ⇒ ξ")?;
    state.run("def exists.{u} (P : u → Prop) : Prop := ∀ ξ, (∀ x, P x ⇒ ξ) ⇒ ξ")?;

    // Other connectives
    state.run("def not (φ : Prop) : Prop := φ ⇒ ⊥")?;
    state.run("def iff (φ : Prop) (ψ : Prop) : Prop := (φ ⇒ ψ) ∧ (ψ ⇒ φ)")?;
    state.run("def uexists.{u} (P : u → Prop) : Prop := ∃ x, P x ∧ (∀ y, P y ⇒ x = y)")?;
    state.run("def ne.{u} (x : u) (y : u) : Prop := ¬x = y")?;

    // Axioms of topos (cf. [Introduction to CATEGORY THEORY and CATEGORICAL LOGIC, T. Streicher, '03])
    state.run("axiom prop_ext (φ ψ : Prop) : (φ ⇔ ψ) ⇒ φ = ψ")?;
    state.run("axiom fun_ext.{u, v} (f₁ f₂ : u → v) : (∀ x, f₁ x = f₂ x) ⇒ f₁ = f₂")?;
    state.run("axiom auc.{u, v} (R : u → v → Prop) : (∀ x, ∃! y, R x y) ⇒ ∃! f, ∀ x, R x (f x)")?;

    // state.run(
    //     "meta def and.intro := λ h₁ h₂, {
    //         let φ := target h₁,
    //         let ψ := target h₂,
    //         let ξ := `{ξ},
    //         let h := assume `{ ${φ} ⇒ ${ψ} ⇒ ${ξ} },
    //         let h := imp.elim h h₁,
    //         let h := imp.elim h h₂,
    //         let h := imp.intro `{ ${φ} ⇒ ${ψ} ⇒ ${ξ} } h,
    //         let h := forall.intro mk_type_prop ξ h,
    //         change `{ ${φ} ∧ ${ψ} } h
    //     }",
    // )?;

    // state.run("meta type Proof")?;
    // state.run("meta type Term")?;
    // state.run("meta type Name")?;

    // // Definite description (cf. [Lambek & Scott, Theorem 5.9])
    // // h : [⋅ | ⋅ ⊢ ∃! (x : τ), φ]
    // // ------------------------------------------------------ [definite description]
    // // ⋅ ⊢ desc h : τ    desc.spec h : [ ⋅ | ⋅ ⊢ [desc h/x]φ]
    // state.run("meta const desc : Proof → Term")?;
    // state.run("meta const desc.spec : Proof → Proof")?;

    // state.run("meta const assump : Term → Proof")?;
    // state.run("meta const imp.intro : Term → Proof → Proof")?;
    // state.run("meta const imp.elim : Proof → Proof → Proof")?;
    // state.run("meta const forall.intro : Name → Type → Proof → Proof")?;
    // state.run("meta const forall.intro : Term → Proof → Proof")?;
    // state.run("meta const conv : Term → Proof → Proof")?;
    // state.run("meta const ref : Name → List Type → Proof")?;

    // state.run("meta const and.intro {φ ψ : Prop} : Proof φ → Proof ψ → Proof (φ ∧ ψ)")?;
    // state.run("meta const and.left {φ ψ : Prop} : Proof (φ ∧ ψ) → Proof φ")?;
    // state.run("meta const and.right {φ ψ : Prop} : Proof (φ ∧ ψ) → Proof ψ")?;
    // state.run("meta const eq.refl.{u} {m : Term u} : Proof (m = m)")?;
    // state.run(
    //     "meta const eq.subst.{u, v} {m₁ m₂ : Term u} {c : Term (u → v)} : Proof (m₁ = m₂) → Proof (c m₁) → Proof (c m₂)",
    // )?;

    // state.run(
    //     "lemma and.intro : ∀ (φ ψ : Prop), φ → ψ → φ ∧ ψ := {
    //         forall_intro mk_type_prop (λ φ, {
    //             forall_intro mk_type_prop (λ ψ, {
    //                 imp_intro φ {
    //                     imp_intro ψ {
    //                         let h := forall_intro mk_type_prop (λ ξ, {
    //                             imp_intro `{ $φ → $ψ → $ξ } {
    //                                 imp_elim (imp_elim (assume `{ $φ → $ψ → $ξ }) (assume φ)) (assume ψ)
    //                             }
    //                         }),
    //                         change `{ $φ ∧ $ψ } h
    //                     }
    //                 }
    //             })
    //         })
    //     }",
    // )?;

    // state.run("lemma tautology (φ : Prop) : φ → φ := imp_intro φ, (assump φ)")?;

    // println!("hoge");
    // state.run("lemma eq.refl.{u} (m : u) : m = m := conv (symm (trans (trans (congr_app (congr_app (delta eq.{u}), refl m), refl m), (beta (λ x y, ∀ P, P x → P y) m m)), (beta (λ y, ∀ P, P m → P y) m))), (forall_intro (P : u → Prop), (forall_elim (P m), tautology))")?;
    // state.run("lemma eq.def.{u} : eq.{u} = (λ x y, ∀ P, P x → P y) := ")?;
    // state.run("lemma eq.refl.{u} (m : u) : m = m := conv (symm (beta (beta (congr_app (congr_app (delta eq.{u}) , refl m), refl m)))), (forall_intro (P : u → Prop), (forall_elim (P m), tautology))")?;

    //    state.run("lemma eta.{u, v} (f : u → v) : f = (λ x, f x) := imp_elim (forall_elim (λ x, f x), (forall_elim f, fun_ext.{u, v})), (conv )")?;

    // p ::= already φ                -- assump
    //     | assume φ, p                   -- imp_intro
    //     | take (x : τ), p             -- forall_intro
    //     | suffices φ, p, p                      -- imp_elim
    //     | use φ, m, p                      -- forall_elim
    //     | show φ, p
    //     | c.{u₁, ⋯, uₙ}

    let proof_env = kernel::proof::Env::new_kernel();
    let p = mk_local(Name::intern("p").unwrap());

    /*
     * take p, assume p, already p
     * apply p q
     * instantiate p m
     */

    let h = mk_proof_forall_intro(
        Name::intern("p").unwrap(),
        mk_type_prop(),
        mk_proof_imp_intro(
            Prop { target: p.clone() },
            mk_proof_assump(Prop { target: p }),
        ),
    );
    let p = proof_env
        .infer_prop(&mut LocalEnv::default(), &mut Context::default(), h)
        .unwrap();
    println!("{p}");

    Ok(())
}
