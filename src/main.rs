mod term;

use anyhow::bail;
use term::{eq_elim, eq_intro, Fact, LocalEnv, Term};

/// ```text
///
/// ---------------------------
/// eq_refl Γ m : [Γ ▸ ⊢ m = m]
/// ```
fn eq_refl(local_env: LocalEnv, m: Term) -> anyhow::Result<Fact> {
    eq_intro(local_env, m.clone(), m)
}

// /// ```text
// /// h : [Γ ▸ Φ ⊢ m₁ = m₂]
// /// -------------------------------------
// /// congr_fun f h : [Γ ▸ Φ ⊢ f m₁ = f m₂]
// /// ```
// fn congr_fun(f: &Term, h: &Fact) -> anyhow::Result<Fact> {
//     // qq! { let "eq #m1 #m2" = target };
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
    println!("{}", "λ (x : ℕ → ℕ), x y".parse::<Term>().unwrap());
}
