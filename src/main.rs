use lex::Lex;
use parse::{ParseError, Parser};

mod cmd;
mod expr;
mod kernel;
mod lex;
mod parse;
mod print;

fn main() -> anyhow::Result<()> {
    let input = include_str!("main.shari");

    let mut state = cmd::Eval::new();

    let mut lex = Lex::new(input);

    loop {
        let cmd = match Parser::new(&mut lex, &state.tt, &state.ns).cmd() {
            Ok(cmd) => cmd,
            Err(ParseError::Eof { .. }) => {
                break;
            }
            Err(e) => {
                println!("parse error: {e}");
                break;
            }
        };
        state.run_cmd(cmd.clone())?;
        match cmd {
            cmd::Cmd::Def(cmd_def) => {
                println!("defined {}", cmd_def.name);
            }
            cmd::Cmd::Lemma(cmd_lemma) => {
                println!("proved {}", cmd_lemma.name);
            }
            _ => {}
        }
    }

    // state.run("def has_fp.{u} (f : u → u) : Prop := ∃ x, x = f x")?;
    // // fixed-point property
    // // emulate the `has_fpp` type class by dictionary passing
    // // ```text
    // // class has_fpp u :=
    // // (fpp : ∀ (f : u → u), has_fp f)
    // // ```
    // state.run("constant type has_fpp : Type → Type")?;
    // state.run("axiom fpp.{u} : ∀ (d : has_fpp.{u}), ∀ (f : u → u), has_fp f")?;

    // state.run("lemma lawvere_fixpoint.{u, v} : (∃ (e : u → u → v), surjective e) ⇒ ∀ (f : v → v), ∃ y, y = f y := ")?;

    // and.intro : Proof φ → Proof ψ → Proof (φ ∧ ψ)
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

    //    state.run("lemma eta.{u, v} (f : u → v) : f = (λ x, f x) := imp_elim (forall_elim (λ x, f x), (forall_elim f, fun_ext.{u, v})), (conv )")?;

    Ok(())
}

/// lawvere's fixed pont theorem
///
/// lemma not.no_fixpoint.{u} (φ : Prop) : φ ≠ ¬φ :=
/// imp_intro (φ = ¬φ), {
///   let φ, ¬φ := (show ⊥).contradiction φ,
///   let ((¬φ) = φ), ¬φ := (show φ).apply (eq.conv (¬φ) φ), -- yields ¬φ, which is automatically contracted with the one that comes from the contradiction tactic.
///   (show ((¬φ) = φ)).symmetry.from (assump (φ = ¬φ)),
///   (show ¬φ).from imp_intro φ, {
///      (show ⊥).contradiction φ,
///      (show ¬φ).apply (eq.conv φ ¬φ),
///      (show φ).from (assump φ),
///   },
/// }
///
/// lemma not.no_fixpoint.{u} (φ : Prop) : φ ≠ ¬φ :=
/// imp_intro (φ = ¬φ),
///   show ⊥.contradiction φ =: φ, ¬φ,
///   show φ.apply (eq.conv (¬φ) φ) =: ((¬φ) = φ), ¬φ   -- yields ¬φ, which is automatically contracted with the one that comes from the contradiction tactic.
///   show ((¬φ) = φ).symmetry.from (assump (φ = ¬φ)),
///   show ¬φ.from imp_intro φ,
///      show ⊥.contradiction φ =: φ, ¬φ,
///      show ¬φ.apply (eq.conv φ ¬φ),
///      show φ.from (assump φ)
///
/// lemma not.no_fixpoint.{u} (φ : Prop) : φ ≠ ¬φ :=
/// assume φ = ¬φ, show ⊥, {
///   let φ, ¬φ := ⟪⊥⟫.contradiction φ,
///   let (¬φ) = φ, ¬φ := ⟪φ⟫.apply eq.conv[¬φ, φ],    -- yields ¬φ, which is automatically contracted with the one that comes from the contradiction tactic.
///   ⟪(¬φ) = φ⟫.symmetry := ⟪φ = ¬φ⟫,
///   ⟪¬φ⟫ := assume φ, show ⊥, {
///      let φ, ¬φ := ⟪⊥⟫.contradiction φ,
///      let φ := ⟪¬φ⟫.apply (eq.conv[φ, ¬φ] ⟪φ = ¬φ⟫),   -- φ is automatically contracted.
///      ⟪φ⟫ := ⟪φ⟫
///   }
/// }
///
/// meta def bot.contradiction (φ : term Prop) : tactic (⊥ ← (φ, ¬φ))
/// meta def and.intro (φ ψ : term Prop) : proof ((φ, ψ) → φ ∧ ψ)
/// meta def symmetry.{u} {m₁ m₂ : term u} : tactic (m₁ = m₂ ← m₂ = m₁)
/// meta def symmetry.{u} {m₁ m₂ : term u} : proof (m₁ = m₂ → m₁ = m₂)
///
/// // built-in
/// Γ : typing context
/// Φ : hypotheses
///
/// -------------------------- (φ ∈ Φ)
/// Γ | Φ ⊢ ⟪φ⟫ : proof φ
///
/// Γ | Φ, φ ⊢ h : proof ψ
/// -----------------------------------
/// Γ | Φ ⊢ assume φ, h : proof (φ ⇒ ψ)
///
/// Γ | Φ ⊢ h₁ : proof (φ ⇒ ψ)    Γ | Φ ⊢ h₂ : proof φ
/// ---------------------------------------------------
/// Γ | Φ ⊢ h₁ h₂ : proof ψ
///
/// Γ, x : u | Φ ⊢ h : proof φ
/// ---------------------------------------------- (x # Φ)
/// Γ | Φ ⊢ take (x : u), h : proof (∀ (x : u), φ)
///
/// Γ | Φ ⊢ h : proof (∀ (x : u), φ)
/// -------------------------------- (Γ ⊢ m : u)
/// Γ | Φ ⊢ h[m] : proof [m/x]φ
///
/// Γ | Φ ⊢ h : proof φ
/// ------------------------------ (φ ≡ ψ)
/// Γ | Φ ⊢ change ψ, h : proof ψ
///
/// Γ | Φ ⊢ c : tactic φ ⊣
/// ---------------------------
/// Γ | Φ ⊢ show φ, c : proof φ
///
/// Γ | Φ ⊢ h : proof φ
/// ----------------------------
/// Γ | Φ ⊢ from h : tactic φ ⊣
///
/// Γ | Φ ⊢ c₁ : tactic φ₁ ⊣ Θ₁, φ₂    Γ | Φ ⊢ c₂ : tactic φ₂ ⊣ Θ₂
/// ---------------------------------------------------------------
/// Γ | Φ ⊢ let ⟪Θ₁⟫ ⟪φ₂⟫ := c₁, c₂ : tactic φ₁ ⊣ Θ₁, Θ₂
///
/// ----------------------------------- (φ ∈ Φ)
/// Γ | Φ ⊢ ⟪φ⟫.assumption : tactic φ ⊣
///
/// (no imp_intro)
///
/// --------------------------------------------
/// Γ | Φ ⊢ ⟪ψ⟫.suffices φ : tactic ψ ⊣ φ ⇒ ψ, φ
///
/// (no forall_intro)
///
/// --------------------------------------------------------
/// Γ | Φ ⊢ ⟪[m/x]φ⟫.generalize m x : tactic [m/x]φ ⊣ ∀ x, φ
///
/// -----------------------------------
/// Γ | Φ ⊢ ⟪φ⟫.change ψ : tactic φ ⊣ ψ
///
///
/// meta def and.intro (h₁ : proof φ) (h₂ : proof ψ) := {
///   let φ := target h₁,
///   let ψ := target h₂,
///   `{ take (ξ : Prop), assume ${φ} ⇒ ${ψ} ⇒ ξ, ⟪${φ} ⇒ ${ψ} ⇒ ξ⟫ ${h₁} ${h₂} }
/// }
///
/// lemma lawvere_fixpoint.{u, v} : (∃ (e : u → u → v), surjective e) ⇒ ∀ (f : v → v), ∃ y, y = f y :=
/// assume ∃ (e : u → u → v), surjective e,
/// take (f : v → v),
/// obtain e, surjective e := ⟪∃ (e : u → u → v), surjective e⟫,
/// obtain x, (λ x₁, f (e x₁ x₁)) = e x := (change ∀ (g : u → v), ∃ x, g = e x, ⟪surjective e⟫)[λ x, f (e x x)],
/// have f (e x x) = e x x := eq.congr_fun[x] ⟪(λ x₁, f (e x₁ x₁)) = e x⟫,
/// show ∃ y, y = f y, {
///   let e x x = f (e x x) := ⟪∃ y, y = f y⟫.construction (e x x),
///   ⟪(e x x) = f (e x x)⟫.symmetry := ⟪f (e x x) = e x x⟫
/// }
fn foo() {}
