//! Prove by type synthesis.

use std::{collections::HashMap, mem, sync::Arc, vec};

use anyhow::bail;
use std::sync::LazyLock;

use super::tt::{
    self, mk_const, mk_type_arrow, mk_type_const, mk_type_local, Kind, LocalEnv, Name, Path, Term,
    Type,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Prop {
    pub target: Term,
}

impl std::fmt::Display for Prop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.target)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Proof {
    /// ```text
    ///
    /// ---------------------- (φ ∈ Φ)
    /// assump φ : [Γ | Φ ⊢ φ]
    /// ```
    Assump(Prop),
    /// ```text
    /// h : [Γ | Φ, φ ⊢ ψ]
    /// -------------------------------
    /// imp_intro φ h : [Γ | Φ ⊢ φ → ψ]
    /// ```
    ImpIntro(Box<(Prop, Proof)>),
    /// ```text
    /// h₁ : [Γ | Φ ⊢ φ → ψ]  h₂ : [Γ | Φ ⊢ φ]
    /// --------------------------------------
    /// imp_elim h₁ h₂ : [Γ | Φ ⊢ ψ]
    /// ```
    ImpElim(Box<(Proof, Proof)>),
    /// ```text
    /// h : [Γ, x : τ | Φ ⊢ φ]
    /// ------------------------------------------- ((x : τ) # Φ)
    /// forall_intro x τ h : [Γ | Φ ⊢ ∀ (x : τ), φ]
    /// ```
    ForallIntro(Box<(Name, Type, Proof)>),
    /// ```text
    /// h : [Γ | Φ ⊢ ∀ (x : τ), φ]
    /// ----------------------------------
    /// forall_elim m h : [Γ | Φ ⊢ [m/x]φ]
    /// ```
    ForallElim(Box<(Term, Proof)>),
    /// ```text
    /// h1 : [Γ ⊢ φ ≡ ψ : Prop]  h2 : [Γ | Φ ⊢ φ]
    /// -----------------------------------------
    /// conv ψ h : [Γ | Φ ⊢ ψ]
    /// ```
    Conv(Box<(Path, Proof)>),
    /// ```text
    ///
    /// ------------------------------- (c.{uᵢ} :⇔ φ)
    /// ref c (tᵢ) : [Γ | Φ ⊢ [τᵢ/uᵢ]φ]
    /// ```
    Ref(Box<(Name, Vec<Type>)>),
}

pub fn mk_proof_assump(p: Prop) -> Proof {
    Proof::Assump(p)
}

pub fn mk_proof_imp_intro(p: Prop, h: Proof) -> Proof {
    Proof::ImpIntro(Box::new((p, h)))
}

pub fn mk_proof_imp_elim(h1: Proof, h2: Proof) -> Proof {
    Proof::ImpElim(Box::new((h1, h2)))
}

pub fn mk_proof_forall_intro(x: Name, t: Type, h: Proof) -> Proof {
    Proof::ForallIntro(Box::new((x, t, h)))
}

pub fn mk_proof_forall_elim(m: Term, h: Proof) -> Proof {
    Proof::ForallElim(Box::new((m, h)))
}

pub fn mk_proof_conv(h1: Path, h2: Proof) -> Proof {
    Proof::Conv(Box::new((h1, h2)))
}

pub fn mk_proof_ref(name: Name, ty_args: Vec<Type>) -> Proof {
    Proof::Ref(Box::new((name, ty_args)))
}

static PROP: LazyLock<Name> = LazyLock::new(|| Name::intern("Prop").unwrap());
static IMP: LazyLock<Name> = LazyLock::new(|| Name::intern("imp").unwrap());
static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall").unwrap());

pub fn mk_type_prop() -> Type {
    static T_PROP: LazyLock<Type> = LazyLock::new(|| mk_type_const(*PROP));
    T_PROP.clone()
}

#[derive(Debug, Clone)]
pub struct Env {
    pub tt_env: tt::Env,
    // Proved or postulated facts
    pub facts: HashMap<Name, (Vec<Name>, Prop)>,
}

#[derive(Debug, Clone, Default)]
pub struct Context {
    pub props: Vec<Prop>,
}

impl Env {
    pub fn new_kernel() -> Env {
        let mut tt_env = tt::Env::default();

        // type Prop
        tt_env.type_consts.insert(*PROP, Kind::base());
        // const imp : Prop → Prop → Prop
        tt_env.consts.insert(
            *IMP,
            (
                vec![],
                mk_type_arrow(
                    mk_type_prop(),
                    mk_type_arrow(mk_type_prop(), mk_type_prop()),
                ),
            ),
        );
        // const forall.{u} : (u → Prop) → Prop
        let u = Name::intern("u").unwrap();
        tt_env.consts.insert(
            *FORALL,
            (
                vec![u],
                mk_type_arrow(
                    mk_type_arrow(mk_type_local(u), mk_type_prop()),
                    mk_type_prop(),
                ),
            ),
        );

        Env {
            tt_env,
            facts: Default::default(),
        }
    }

    pub fn infer_prop(
        &self,
        local_env: &mut LocalEnv,
        context: &mut Context,
        h: Proof,
    ) -> anyhow::Result<Prop> {
        match h {
            Proof::Assump(mut p) => {
                self.tt_env
                    .check_type(local_env, &mut p.target, &mut mk_type_prop())?;
                for c in &context.props {
                    if &p == c {
                        return Ok(p);
                    }
                }
                bail!("assumption not found");
            }
            Proof::ImpIntro(inner) => {
                let (mut p, h) = *inner;
                self.tt_env
                    .check_type(local_env, &mut p.target, &mut mk_type_prop())?;
                context.props.push(p);
                let h = self.infer_prop(local_env, context, h)?;
                let p = context.props.pop().unwrap();
                let mut target = mk_const(*IMP, vec![]);
                target.apply([p.target, h.target]);
                Ok(Prop { target })
            }
            Proof::ImpElim(inner) => {
                let (h1, h2) = *inner;
                let h1 = self.infer_prop(local_env, context, h1)?;
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
                self.check_prop(local_env, context, h2, &Prop { target: p })?;
                Ok(Prop { target })
            }
            Proof::ForallIntro(inner) => {
                let (x, t, h) = *inner;
                self.tt_env.check_kind(local_env, &t, &Kind::base())?;
                for c in &context.props {
                    if !c.target.is_fresh(x) {
                        bail!("eigenvariable condition fails");
                    }
                }
                local_env.locals.push((x, t));
                let h = self.infer_prop(local_env, context, h)?;
                let (x, t) = local_env.locals.pop().unwrap();
                let mut m = h.target;
                m.abs(x, t.clone(), x);
                let mut target = mk_const(*FORALL, vec![t]);
                target.apply([m]);
                Ok(Prop { target })
            }
            Proof::ForallElim(inner) => {
                let (mut m, h) = *inner;
                let h = self.infer_prop(local_env, context, h)?;
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
                self.tt_env.check_type(local_env, &mut m, &mut domain_ty)?;
                target.open(&m);
                Ok(Prop { target })
            }
            Proof::Conv(inner) => {
                let (h1, h2) = *inner;
                let h1 = self.tt_env.infer_conv(local_env, h1)?;
                if h1.ty != mk_type_prop() {
                    bail!("not a definitional equality between propositions");
                }
                self.check_prop(local_env, context, h2, &Prop { target: h1.left })?;
                Ok(Prop { target: h1.right })
            }
            Proof::Ref(inner) => {
                let (name, ty_args) = *inner;
                let Some((tv, mut target)) = self.facts.get(&name).cloned() else {
                    bail!("axiom not found");
                };
                if ty_args.len() != tv.len() {
                    bail!("wrong number of type arguments supplied");
                }
                for ty_arg in &ty_args {
                    self.tt_env.check_kind(local_env, ty_arg, &Kind::base())?;
                }
                let subst: Vec<_> = std::iter::zip(tv, ty_args.iter()).collect();
                target.target.instantiate(&subst);
                Ok(target)
            }
        }
    }

    pub fn check_prop(
        &self,
        local_env: &mut LocalEnv,
        context: &mut Context,
        h: Proof,
        prop: &Prop,
    ) -> anyhow::Result<()> {
        let p = self.infer_prop(local_env, context, h)?;
        if &p != prop {
            bail!("propositions mismatch");
        }
        Ok(())
    }
}

// #[cfg(test)]
// mod tests {
//     use super::tt::{mk_abs, mk_app, mk_fresh_type_mvar, mk_local, mk_var};
//     use super::*;

//     static P: Lazy<Name> = Lazy::new(|| Name::intern("p").unwrap());
//     static Q: Lazy<Name> = Lazy::new(|| Name::intern("q").unwrap());
//     static ALPHA: Lazy<Name> = Lazy::new(|| Name::intern("α").unwrap());
//     static X: Lazy<Name> = Lazy::new(|| Name::intern("x").unwrap());
//     static Y: Lazy<Name> = Lazy::new(|| Name::intern("y").unwrap());

//     #[test]
//     fn test_assume_ok() {
//         // terms may contain local variables
//         let p = mk_local(*P, mk_type_prop());
//         insta::assert_display_snapshot!(assume(p).unwrap(), @"(local p Prop) ⊢ (local p Prop)");

//         // infer as Prop
//         let p = mk_local(*P, mk_fresh_type_mvar());
//         insta::assert_display_snapshot!(assume(p).unwrap(), @"(local p Prop) ⊢ (local p Prop)");

//         // terms may contain type variables
//         // λ (x : α), x) = (λ x, x)
//         let p = mk_app(
//             mk_app(
//                 mk_const(*EQ, vec![mk_fresh_type_mvar()]),
//                 mk_abs(*X, mk_type_local(*ALPHA), mk_var(0)),
//             ),
//             mk_abs(*X, mk_fresh_type_mvar(), mk_var(0)),
//         );
//         insta::assert_display_snapshot!(assume(p).unwrap(), @"((eq.{(α → α)} (lam α (var 0))) (lam α (var 0))) ⊢ ((eq.{(α → α)} (lam α (var 0))) (lam α (var 0)))");
//     }

//     #[test]
//     fn test_assume_err() {
//         // not a proposition
//         let p = mk_local(*P, mk_type_arrow(mk_type_prop(), mk_type_prop()));
//         insta::assert_display_snapshot!(assume(p).unwrap_err(), @"type mismatch");

//         // ill-typed
//         // (λ (x : Prop), x) (λ y, y)
//         let p = mk_app(
//             mk_abs(*X, mk_type_prop(), mk_var(0)),
//             mk_abs(*Y, mk_fresh_type_mvar(), mk_var(0)),
//         );
//         insta::assert_display_snapshot!(assume(p).unwrap_err(), @"type mismatch");

//         // not fully instantiated
//         // (λ x, x) = (λ x, x)
//         let p = mk_app(
//             mk_app(
//                 mk_const(*EQ, vec![mk_fresh_type_mvar()]),
//                 mk_abs(*X, mk_fresh_type_mvar(), mk_var(0)),
//             ),
//             mk_abs(*X, mk_fresh_type_mvar(), mk_var(0)),
//         );
//         insta::assert_display_snapshot!(assume(p).unwrap_err(), @"uninstantiated meta type variable");
//     }
//     #[test]
//     fn test_imp_ok() {
//         let p = mk_local(*P, mk_fresh_type_mvar());
//         let h = assume(p.clone()).unwrap();
//         insta::assert_display_snapshot!(imp_intro(p, h).unwrap(), @"⊢ ((imp (local p Prop)) (local p Prop))");

//         // weakening
//         let p = mk_local(*P, mk_fresh_type_mvar());
//         insta::assert_display_snapshot!(imp_intro(p, eq_intro(mk_const(*IMP, vec![])).unwrap()).unwrap(), @"⊢ ((imp (local p Prop)) ((eq.{(Prop → (Prop → Prop))} imp) imp))");

//         // p → q
//         let p1 = mk_app(
//             mk_app(mk_const(*IMP, vec![]), mk_local(*P, mk_fresh_type_mvar())),
//             mk_local(*Q, mk_fresh_type_mvar()),
//         );
//         // p
//         let p2 = mk_local(*P, mk_fresh_type_mvar());
//         let h1 = assume(p1).unwrap();
//         let h2 = assume(p2).unwrap();
//         insta::assert_display_snapshot!(imp_elim(h1, h2).unwrap(), @"((imp (local p Prop)) (local q Prop)) (local p Prop) ⊢ (local q Prop)");
//     }

//     #[test]
//     fn test_imp_err() {
//         // (λ (x : Prop), x) (λ (x : Prop), x)
//         let p1 = mk_app(
//             mk_abs(*X, mk_type_prop(), mk_var(0)),
//             mk_abs(*X, mk_type_prop(), mk_var(0)),
//         );
//         // p
//         let p2 = mk_local(*P, mk_fresh_type_mvar());
//         // p q
//         let p3 = mk_app(
//             mk_local(*P, mk_fresh_type_mvar()),
//             mk_local(*Q, mk_fresh_type_mvar()),
//         );
//         // q
//         let p4 = mk_local(*Q, mk_fresh_type_mvar());

//         insta::assert_display_snapshot!(imp_intro(p1, assume(p2.clone()).unwrap()).unwrap_err(), @"type mismatch");
//         insta::assert_display_snapshot!(imp_intro(p3, assume(p2.clone()).unwrap()).unwrap_err(), @"uninstantiated meta type variable");

//         let h1 = assume(p2).unwrap();
//         let h2 = assume(p4).unwrap();
//         insta::assert_display_snapshot!(imp_elim(h1, h2).unwrap_err(), @"not an implication");
//     }

//     #[test]
//     fn test_forall() {
//         // err
//         let p: Term = mk_local(*P, mk_fresh_type_mvar());
//         let h = assume(p.clone()).unwrap();
//         insta::assert_display_snapshot!(forall_intro(*P, mk_type_prop(), h).unwrap_err(), @"eigenvariable condition fails");

//         let p: Term = mk_local(*P, mk_fresh_type_mvar());
//         let h = assume(p.clone()).unwrap();
//         let h = imp_intro(p, h).unwrap();
//         insta::assert_display_snapshot!(forall_intro(*P, mk_type_prop(), h).unwrap(), @"⊢ (forall.{Prop} (lam Prop ((imp (var 0)) (var 0))))");

//         // weakening
//         let h = eq_intro(mk_const(*IMP, vec![])).unwrap();
//         insta::assert_display_snapshot!(forall_intro(*P, mk_type_prop(), h).unwrap(), @"⊢ (forall.{Prop} (lam Prop ((eq.{(Prop → (Prop → Prop))} imp) imp)))");

//         let p: Term = mk_local(*P, mk_fresh_type_mvar());
//         let h = assume(p.clone()).unwrap();
//         let h = imp_intro(p, h).unwrap();
//         let h = forall_intro(*P, mk_type_prop(), h).unwrap();
//         insta::assert_display_snapshot!(forall_elim(mk_local(*Q, mk_fresh_type_mvar()), h).unwrap(), @"⊢ ((imp (local q Prop)) (local q Prop))");
//     }
// }
