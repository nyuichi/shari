mod term;

use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use anyhow::bail;
use once_cell::sync::Lazy;
use term::{
    add_axiom, add_const, add_notation, eq_elim, eq_intro, fun_ext, prop_ext, Fact, Fixity, Name,
    Term, TermApp, TermConst, TermLocal, Type,
};

static DEF_TABLE: Lazy<Mutex<HashMap<Name, Fact>>> = Lazy::new(Default::default);

fn add_definition(
    name: &str,
    ty_vars: impl IntoIterator<Item = Name>,
    mut entity: Term,
) -> anyhow::Result<()> {
    let Ok(name) = Name::try_from(name) else {
        bail!("invalid name: {entity}");
    };
    let ty_vars: Vec<_> = ty_vars.into_iter().collect();
    if !ty_vars.is_empty() {
        // TODO
        todo!();
        // check if ty_vars are pointwise distinct
    }
    let ty = entity.infer()?;
    add_const(name.clone(), ty_vars.clone(), ty.clone())?;
    let target = Term::App(Arc::new(TermApp {
        fun: Term::App(Arc::new(TermApp {
            fun: Term::Const(Arc::new(TermConst {
                name: Name::try_from("eq").unwrap(),
                ty_args: vec![ty],
            })),
            arg: Term::Const(Arc::new(TermConst {
                name: name.clone(),
                ty_args: ty_vars.into_iter().map(Type::Var).collect(),
            })),
        })),
        arg: entity,
    }));
    // TODO ty_vars = fv target
    let fact = add_axiom(target)?;
    if DEF_TABLE.lock().unwrap().insert(name, fact).is_some() {
        bail!("logic flaw");
    }
    Ok(())
}

fn by_def(name: &str) -> anyhow::Result<Fact> {
    Ok(DEF_TABLE.lock().unwrap().get(name).unwrap().clone())
}

// impl Term {
//     // first-order pattern match.
//     // ignores types.
//     fn match1<'a>(&self, other: &'a Term) -> Option<Subst<&'a Term>> {
//         let mut subst = Subst::new();
//         if !subst.match1(self, other) {
//             return None;
//         }
//         Some(subst)
//     }
// }

// impl<'a> Subst<&'a Term> {
//     fn match1(&mut self, this: &Term, that: &'a Term) -> bool {
//         match (this, that) {
//             (Term::Var(i), Term::Var(j)) if i == j => true,
//             (Term::Abs(a1), Term::Abs(a2)) => self.match1(&a1.body, &a2.body),
//             (Term::App(p1), Term::App(p2)) => {
//                 self.match1(&p1.0, &p2.0) && self.match1(&p1.1, &p2.1)
//             }
//             (Term::Local(x), Term::Local(y)) if x == y => true,
//             (Term::Const(c1), Term::Const(c2)) => c1.0 == c2.0,
//             (Term::Mvar(name), m) => {
//                 self.0.push((name.clone(), m));
//                 true
//             }
//             _ => false,
//         }
//     }
// }

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

/// ```text
/// h : [Φ ⊢ φ]
/// ----------------------- (φ ≡ ψ)
/// change ψ h: [Φ ⊢ ψ]
/// ```
fn change(m: Term, h: Fact) -> anyhow::Result<Fact> {
    let n = h.target().clone();
    let h_eqv = eq_intro(m, n)?;
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
    let m2 = rhs(h.target())?;
    let c = {
        let mut c: Term = "λ m2 x, eq m2 x".parse().unwrap();
        c.undischarge();
        c.open_at(m2, 1);
        c
    };
    let ha = eq_refl(m2.clone())?;
    eq_elim(c, h, ha)
}

/// ```text
/// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ m₁]
/// ----------------------------------
/// eq_mp h₁ h₂ : [Φ ∪ Ψ ⊢ m₂]
/// ```
fn eq_mp(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    eq_elim(Term::Var(0), eq_symm(h1)?, h2)
}

// /// ```text
// /// h₁ : [Φ ⊢ m₁ = m₂]  h₂ : [Ψ ⊢ n]
// /// --------------------------------- (f m₂ ≡ n)
// /// eq_subst f h₁ h₂ : [Φ ∪ Ψ ⊢ f m₁]
// /// ```
// fn eq_subst(f: Term, h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
//     let m2 = {
//         let pat: Term = "eq #_ #m2".parse().unwrap();
//         let Some(subst) = pat.match1(h1.target()) else {
//             bail!("expected equality, but got {}", h1.target());
//         };
//         *subst.get("m2").unwrap()
//     };
//     let mut fm2 = f.clone();
//     fm2.apply([m2.clone()]);
//     let h = eq_intro(h2.local_env().clone(), h2.target().clone(), fm2)?;
//     let h = eq_mp(h, h2)?;
//     let mut c = f;
//     c.apply([Term::Var(0)]);
//     eq_elim(c, h1, h)
// }

/// ```text
/// h₁ : [Φ ⊢ f₁ = f₂]  h₂ : [Ψ ⊢ a₁ = a₂]
/// ---------------------------------------
/// congr h₁ h₂ : [Φ ∪ Ψ ⊢ f₁ a₁ = f₂ a₂]
/// ```
fn congr(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let f2 = rhs(h1.target())?;
    let a1 = lhs(h2.target())?;
    let a2 = rhs(h2.target())?;
    let mut m = f2.clone();
    m.apply([a2.clone()]);
    // h : [.. ⊢ f₂ a₂ = f₂ a₂]
    let h = eq_refl(m)?;
    let mut c: Term = "λ f2 a2 a, f2 a = f2 a2".parse().unwrap();
    c.undischarge();
    c.open_at(f2, 2);
    c.open_at(a2, 1);
    let mut d: Term = "λ f2 a1 a2 f, f a1 = f2 a2".parse().unwrap();
    d.undischarge();
    d.open_at(f2, 3);
    d.open_at(a1, 2);
    d.open_at(a2, 1);
    // h : [.. ⊢ f₂ a₁ = f₂ a₂]
    let h = eq_elim(c, h2, h)?;
    eq_elim(d, h1, h)
}

/// ```text
/// h : [Φ ⊢ f₁ = f₂]
/// ---------------------------------
/// congr_fun h a : [Φ ⊢ f₁ a = f₂ a]
/// ```
fn congr_fun(h: Fact, a: Term) -> anyhow::Result<Fact> {
    congr(h, eq_refl(a)?)
}

/// ```text
/// h : [Φ ⊢ a₁ = a₂]
/// ---------------------------------
/// congr_arg f h : [Φ ⊢ f a₁ = f a₂]
/// ```
fn congr_arg(f: Term, h: Fact) -> anyhow::Result<Fact> {
    congr(eq_refl(f)?, h)
}

/// ```text
///
/// ------------------
/// top_intro : [⊢ ⊤]
/// ```
fn top_intro() -> anyhow::Result<Fact> {
    let id = "λ (x : Prop), x".parse().unwrap();
    let h = eq_refl(id)?;
    let c = {
        let mut c: Term = "λ x, x".parse().unwrap();
        c.undischarge();
        c
    };
    let top_def = by_def("top")?;
    eq_elim(c, top_def, h)
}

/// ```text
/// h : [Φ ⊢ φ]
/// -------------------- [reverse of material adequacy]
/// mar h : [Φ ⊢ φ = ⊤]
/// ```
fn mar(h: Fact) -> anyhow::Result<Fact> {
    prop_ext(h, top_intro()?)
}

/// ```text
/// h : [Φ ⊢ φ = ⊤]
/// ---------------- [material adequacy]
/// ma h : [Φ ⊢ φ]
/// ```
fn ma(h: Fact) -> anyhow::Result<Fact> {
    eq_elim(Term::Var(0), h, top_intro()?)
}

/// ```text
/// h₁ : [Φ ⊢ φ]  h₂ : [Ψ ⊢ ψ]
/// ---------------------------------
/// and_intro h₁ h₂ : [Φ ∪ Ψ ⊢ φ ∧ ψ]
/// ```
fn and_intro(h1: Fact, h2: Fact) -> anyhow::Result<Fact> {
    let p1 = h1.target().clone();
    let p2 = h2.target().clone();
    // h1: [Γ ▸ Φ ⊢ φ = ⊤]
    let h1 = mar(h1)?;
    // h2: [Δ ▸ Ψ ⊢ ψ = ⊤]
    let h2 = mar(h2)?;
    let fx = Name::fresh();
    let ft: Type = "Prop → Prop → Prop".parse().unwrap();
    let f = Term::Local(Arc::new(TermLocal {
        name: fx.clone(),
        ty: ft.clone(),
    }));
    let h = congr(congr_arg(f, h1)?, h2)?;
    // h: [.. ⊢ (λ f, f φ ψ) = (λ f, f ⊤ ⊤)]
    let h = fun_ext(&fx, ft, h)?;
    let mut g: Term = "λ (x y : Prop), (λ (f : Prop → Prop → Prop), f x y) = (λ f, f ⊤ ⊤)"
        .parse()
        .unwrap();
    g.apply([p1.clone(), p2.clone()]);
    // h: [.. ⊢ (λ x y, (λ f, f x y) = (λ f, f ⊤ ⊤)) φ ψ]
    let h = change(g, h)?;
    let mut c: Term = "λ p q r, r p q".parse().unwrap();
    c.undischarge();
    c.open_at(&p1, 2);
    c.open_at(&p2, 1);
    eq_elim(c, by_def("and")?, h)
}

fn main() {
    println!("{}", "λ (x : α → α), x".parse::<Term>().unwrap());
    let id = "λ (x : Prop), x".parse::<Term>().unwrap();
    let idf = "(λ (f : Prop → Prop), f) (λ (x : Prop), x)"
        .parse::<Term>()
        .unwrap();
    let h1 = eq_intro(id, idf).unwrap();
    println!("h1: {h1}");
    let h2 = eq_symm(h1).unwrap();
    println!("h2: {h2}");

    add_notation("⊤", Fixity::Nofix, usize::MAX, "top").unwrap();
    add_notation("∧", Fixity::Infixr, 35, "and").unwrap();
    add_notation("→", Fixity::Infixr, 25, "imp").unwrap();
    add_notation("⊥", Fixity::Nofix, usize::MAX, "bot").unwrap();
    add_notation("∨", Fixity::Infixr, 30, "or").unwrap();
    add_notation("¬", Fixity::Prefix, 40, "not").unwrap();
    add_notation("↔", Fixity::Infix, 20, "iff").unwrap();

    // Equality-based representation by Andrews [Andrews, 1986]

    add_definition("top", [], "(λ (x : Prop), x) = (λ x, x)".parse().unwrap()).unwrap();

    let h = top_intro().unwrap();
    println!("{h}");

    let h3 = mar(h2).unwrap();
    println!("h3: {h3}");

    let h4 = ma(h3).unwrap();
    println!("h4: {h4}");

    add_definition(
        "and",
        [],
        "λ (φ ψ : Prop), (λ (f : Prop → Prop → Prop), f φ ψ) = (λ f, f ⊤ ⊤)"
            .parse()
            .unwrap(),
    )
    .unwrap();

    let h5 = and_intro(
        eq_refl("λ (x : Prop), x".parse().unwrap()).unwrap(),
        top_intro().unwrap(),
    )
    .unwrap();
    println!("h5: {h5}");

    add_definition("imp", [], "λ (φ ψ : Prop), φ = φ ∧ ψ".parse().unwrap()).unwrap();

    add_definition(
        "forall",
        ["u".try_into().unwrap()],
        "λ (P : u → Prop), P = (λ x, ⊤)".parse().unwrap(),
    )
    .unwrap();

    add_definition("bot", [], "∀ ξ, ξ".parse().unwrap()).unwrap();

    add_definition(
        "or",
        [],
        "λ (φ ψ : Prop), ∀ ξ, (φ → ξ) ∧ (ψ → ξ) → ξ"
            .parse()
            .unwrap(),
    )
    .unwrap();

    add_definition(
        "exists",
        ["u".try_into().unwrap()],
        "λ (P : u → Prop), ∀ ξ, (∀ x, P x → ξ) → ξ".parse().unwrap(),
    )
    .unwrap();

    add_definition("not", [], "λ (φ : Prop), φ → ⊥".parse().unwrap()).unwrap();

    add_definition(
        "iff",
        [],
        "λ (φ ψ : Prop), (φ → ψ) ∧ (ψ → φ)".parse().unwrap(),
    )
    .unwrap();

    add_definition(
        "uexists",
        ["u".try_into().unwrap()],
        "λ (P : u → Prop), ∃ x, P x ∧ (∀ y, P y → x = y)"
            .parse()
            .unwrap(),
    )
    .unwrap();
}
