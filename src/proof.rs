//! Prove by type synthesis.

use std::{collections::HashMap, sync::Arc, vec};

use anyhow::bail;
use std::sync::LazyLock;

use crate::tt::{
    self, mk_abs, mk_const, mk_type_arrow, mk_type_const, mk_type_local, Kind, LocalEnv, Name,
    Path, Term, TermAbs, Type,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Proof {
    /// ```text
    ///
    /// ---------------------- (φ ∈ Φ)
    /// Γ | Φ ⊢ assump φ : φ
    /// ```
    Assump(Term),
    /// ```text
    /// Γ | Φ, φ ⊢ h : ψ
    /// ------------------------------
    /// Γ | Φ ⊢ imp_intro φ, h : φ → ψ
    /// ```
    ImpIntro(Arc<(Term, Proof)>),
    /// ```text
    /// Γ | Φ ⊢ h₁ : φ → ψ    Γ | Φ ⊢ h₂ : φ
    /// -------------------------------------
    /// Γ | Φ ⊢ imp_elim h₁ h₂ : ψ
    /// ```
    ImpElim(Arc<(Proof, Proof)>),
    /// ```text
    /// Γ, x : τ | Φ ⊢ h : φ
    /// ---------------------------------------------- ((x : τ) # Φ)
    /// Γ | Φ ⊢ forall_intro (x : τ), h : ∀ (x : τ), φ
    /// ```
    ForallIntro(Arc<(Name, Type, Proof)>),
    /// ```text
    /// Γ | Φ ⊢ h : ∀ (x : τ), φ
    /// ----------------------------------
    /// Γ | Φ ⊢ forall_elim m, h : [m/x]φ]
    /// ```
    ForallElim(Arc<(Term, Proof)>),
    /// ```text
    /// Γ ⊢ p : φ ≡ ψ    Γ | Φ ⊢ h : φ
    /// -------------------------------
    /// Γ | Φ ⊢ conv p, h : ψ
    /// ```
    Conv(Arc<(Path, Proof)>),
    /// ```text
    ///
    /// -------------------------- (c.{uᵢ} :⇔ φ)
    /// Γ | Φ ⊢ c.{tᵢ} : [τᵢ/uᵢ]φ
    /// ```
    Ref(Arc<(Name, Vec<Type>)>),
}

impl std::fmt::Display for Proof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Proof::Assump(prop) => write!(f, "(assump {prop})"),
            Proof::ImpIntro(inner) => write!(f, "(imp_intro {}, {})", inner.0, inner.1),
            Proof::ImpElim(inner) => write!(f, "(imp_elim {} {})", inner.0, inner.1),
            Proof::ForallIntro(inner) => {
                write!(f, "(forall_intro ({} : {}), {})", inner.0, inner.1, inner.2)
            }
            Proof::ForallElim(inner) => write!(f, "(forall_elim {}, {})", inner.0, inner.1),
            Proof::Conv(inner) => write!(f, "(conv {}, {})", inner.0, inner.1),
            Proof::Ref(inner) => {
                write!(f, "{}", inner.0)?;
                if !inner.1.is_empty() {
                    write!(f, ".{{")?;
                    let mut first = true;
                    for t in &inner.1 {
                        if !first {
                            write!(f, ", ")?;
                        }
                        write!(f, "{t}")?;
                        first = false;
                    }
                    write!(f, "}}")?;
                }
                Ok(())
            }
        }
    }
}

pub fn mk_proof_assump(p: Term) -> Proof {
    Proof::Assump(p)
}

pub fn mk_proof_imp_intro(p: Term, h: Proof) -> Proof {
    Proof::ImpIntro(Arc::new((p, h)))
}

pub fn mk_proof_imp_elim(h1: Proof, h2: Proof) -> Proof {
    Proof::ImpElim(Arc::new((h1, h2)))
}

pub fn mk_proof_forall_intro(x: Name, t: Type, h: Proof) -> Proof {
    Proof::ForallIntro(Arc::new((x, t, h)))
}

pub fn mk_proof_forall_elim(m: Term, h: Proof) -> Proof {
    Proof::ForallElim(Arc::new((m, h)))
}

pub fn mk_proof_conv(h1: Path, h2: Proof) -> Proof {
    Proof::Conv(Arc::new((h1, h2)))
}

pub fn mk_proof_ref(name: Name, ty_args: Vec<Type>) -> Proof {
    Proof::Ref(Arc::new((name, ty_args)))
}

static PROP: LazyLock<Name> = LazyLock::new(|| Name::intern("Prop").unwrap());
static IMP: LazyLock<Name> = LazyLock::new(|| Name::intern("imp").unwrap());
static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall").unwrap());

pub fn mk_type_prop() -> Type {
    static T_PROP: LazyLock<Type> = LazyLock::new(|| mk_type_const(*PROP));
    T_PROP.clone()
}

#[derive(Debug, Clone)]
pub struct Imp {
    pub lhs: Term,
    pub rhs: Term,
}

impl TryFrom<Term> for Imp {
    type Error = ();

    fn try_from(mut value: Term) -> Result<Self, Self::Error> {
        let mut args = value.unapply();
        let Term::Const(head) = value else {
            return Err(());
        };
        if head.name != *IMP {
            return Err(());
        }
        if args.len() != 2 {
            return Err(());
        }
        let rhs = args.pop().unwrap();
        let lhs = args.pop().unwrap();
        Ok(Self { lhs, rhs })
    }
}

impl From<Imp> for Term {
    fn from(value: Imp) -> Self {
        let mut m = mk_const(*IMP, vec![]);
        m.apply([value.lhs, value.rhs]);
        m
    }
}

#[derive(Debug, Clone)]
pub struct Forall {
    pub name: Name,
    pub ty: Type,
    // locally open
    pub body: Term,
}

impl TryFrom<Term> for Forall {
    type Error = ();

    fn try_from(mut value: Term) -> Result<Self, Self::Error> {
        let mut args = value.unapply();
        let Term::Const(mut head) = value else {
            return Err(());
        };
        if head.name != *FORALL {
            return Err(());
        }
        let domain_ty = Arc::make_mut(&mut head).ty_args.pop().unwrap();
        if args.len() != 1 {
            return Err(());
        }
        let arg = args.pop().unwrap();
        let Term::Abs(abs) = arg else {
            return Err(());
        };
        let TermAbs {
            binder_type,
            binder_name,
            body,
        } = Arc::unwrap_or_clone(abs);
        if binder_type != domain_ty {
            return Err(());
        }
        Ok(Forall {
            name: binder_name,
            ty: binder_type,
            body,
        })
    }
}

impl From<Forall> for Term {
    fn from(value: Forall) -> Self {
        let Forall { name, ty, body } = value;
        let abs = mk_abs(name, ty.clone(), body);
        let mut m = mk_const(*FORALL, vec![ty]);
        m.apply([abs]);
        m
    }
}

#[derive(Debug, Clone, Default)]
pub struct Env {
    pub tt_env: tt::Env,
    // Proved or postulated facts
    pub axioms: HashMap<Name, (Vec<Name>, Term)>,
}

#[derive(Debug, Clone, Default)]
pub struct Context {
    pub props: Vec<Term>,
}

impl Env {
    /// prop must be certified.
    pub fn check_prop(
        &self,
        local_env: &mut LocalEnv,
        context: &mut Context,
        h: &mut Proof,
        prop: &Term,
    ) -> anyhow::Result<()> {
        let p = self.infer_prop(local_env, context, h)?;
        if &p != prop {
            bail!("propositions mismatch: {p} is not equal to {prop}");
        };
        Ok(())
    }

    pub fn infer_prop(
        &self,
        local_env: &mut LocalEnv,
        context: &mut Context,
        h: &mut Proof,
    ) -> anyhow::Result<Term> {
        match h {
            Proof::Assump(p) => {
                self.tt_env.check_type(local_env, p, &mut mk_type_prop())?;
                for c in &context.props {
                    if p == c {
                        return Ok(p.clone());
                    }
                }
                bail!("assumption not found");
            }
            Proof::ImpIntro(inner) => {
                let (p, h) = Arc::make_mut(inner);
                self.tt_env.check_type(local_env, p, &mut mk_type_prop())?;
                context.props.push(p.clone());
                let h = self.infer_prop(local_env, context, h)?;
                let p = context.props.pop().unwrap();
                Ok(Imp { lhs: p, rhs: h }.into())
            }
            Proof::ImpElim(inner) => {
                let (h1, h2) = Arc::make_mut(inner);
                let h1 = self.infer_prop(local_env, context, h1)?;
                let Ok(Imp { lhs, rhs }) = h1.clone().try_into() else {
                    bail!("not an implication: {}", h1);
                };
                self.check_prop(local_env, context, h2, &lhs)?;
                Ok(rhs)
            }
            Proof::ForallIntro(inner) => {
                let (x, t, h) = Arc::make_mut(inner);
                self.tt_env.check_kind(local_env, t, &Kind::base())?;
                for c in &context.props {
                    if !c.is_fresh(&[*x]) {
                        bail!("eigenvariable condition fails");
                    }
                }
                local_env.locals.push((*x, t.clone()));
                let h = self.infer_prop(local_env, context, h)?;
                let (x, t) = local_env.locals.pop().unwrap();
                let mut body = h;
                body.close(x);
                Ok(Forall {
                    name: x,
                    ty: t,
                    body,
                }
                .into())
            }
            Proof::ForallElim(inner) => {
                let (m, h) = Arc::make_mut(inner);
                let h = self.infer_prop(local_env, context, h)?;
                let Ok(Forall {
                    name: _,
                    mut ty,
                    body,
                }) = h.clone().try_into()
                else {
                    bail!("not a forall: {}", h);
                };
                self.tt_env.check_type(local_env, m, &mut ty)?;
                let mut target = body;
                target.open(m);
                Ok(target)
            }
            Proof::Conv(inner) => {
                let (h1, h2) = Arc::make_mut(inner);
                let h1 = self.tt_env.infer_conv(local_env, h1)?;
                self.check_prop(local_env, context, h2, &h1.left)?;
                Ok(h1.right)
            }
            Proof::Ref(inner) => {
                let (name, ty_args) = Arc::make_mut(inner);
                let Some((tv, mut target)) = self.axioms.get(name).cloned() else {
                    bail!("proposition not found");
                };
                if ty_args.len() != tv.len() {
                    bail!("wrong number of type arguments supplied");
                }
                for ty_arg in &mut *ty_args {
                    self.tt_env.check_kind(local_env, ty_arg, &Kind::base())?;
                }
                let subst: Vec<_> = std::iter::zip(tv, ty_args.iter()).collect();
                target.subst_type(&subst);
                Ok(target)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::tt::{mk_abs, mk_app, mk_fresh_type_hole, mk_local, mk_var};
    use super::*;

    static P: LazyLock<Name> = LazyLock::new(|| Name::intern("p").unwrap());
    static Q: LazyLock<Name> = LazyLock::new(|| Name::intern("q").unwrap());
    static ALPHA: LazyLock<Name> = LazyLock::new(|| Name::intern("α").unwrap());
    static X: LazyLock<Name> = LazyLock::new(|| Name::intern("x").unwrap());
    static Y: LazyLock<Name> = LazyLock::new(|| Name::intern("y").unwrap());

    fn new_kernel() -> Env {
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
            axioms: Default::default(),
        }
    }

    fn infer(m: &mut Term) {
        let env = new_kernel();
        let mut local_env = LocalEnv::default();
        env.tt_env.infer_type(&mut local_env, m).unwrap();
    }

    // Check if (p : Prop) | hs ⊢ h : ?
    fn check(hs: impl IntoIterator<Item = Term>, mut h: Proof) -> Term {
        let env = new_kernel();
        let mut local_env = LocalEnv::default();
        local_env
            .locals
            .push(("p".try_into().unwrap(), mk_type_prop()));
        let mut cx = Context::default();
        for h in hs {
            cx.props.push(h);
        }
        env.infer_prop(&mut local_env, &mut cx, &mut h).unwrap()
    }

    #[test]
    fn test_assume_ok() {
        // terms may contain local variables
        let p = mk_local(*P);
        insta::assert_snapshot!(check([p.clone()], mk_proof_assump(p)), @"(local p)");

        // terms may contain type variables
        // ∀ x, x ⇒ x
        let p = mk_app(
            mk_const(*FORALL, vec![mk_fresh_type_hole()]),
            mk_abs(
                *X,
                mk_fresh_type_hole(),
                mk_app(mk_app(mk_const(*IMP, vec![]), mk_var(0)), mk_var(0)),
            ),
        );
        let mut q = p.clone();
        infer(&mut q);
        insta::assert_snapshot!(check([q], mk_proof_assump(p)), @"(forall.{Prop} (lam Prop ((imp (var 0)) (var 0))))");
    }

    // #[test]
    // fn test_assume_err() {
    //     // not a proposition
    //     let p = mk_local(*P, mk_type_arrow(mk_type_prop(), mk_type_prop()));
    //     insta::assert_snapshot!(assume(p).unwrap_err(), @"type mismatch");

    //     // ill-typed
    //     // (λ (x : Prop), x) (λ y, y)
    //     let p = mk_app(
    //         mk_abs(*X, mk_type_prop(), mk_var(0)),
    //         mk_abs(*Y, mk_fresh_type_mvar(), mk_var(0)),
    //     );
    //     insta::assert_snapshot!(assume(p).unwrap_err(), @"type mismatch");

    //     // not fully instantiated
    //     // (λ x, x) = (λ x, x)
    //     let p = mk_app(
    //         mk_app(
    //             mk_const(*EQ, vec![mk_fresh_type_mvar()]),
    //             mk_abs(*X, mk_fresh_type_mvar(), mk_var(0)),
    //         ),
    //         mk_abs(*X, mk_fresh_type_mvar(), mk_var(0)),
    //     );
    //     insta::assert_snapshot!(assume(p).unwrap_err(), @"uninstantiated meta type variable");
    // }
    // #[test]
    // fn test_imp_ok() {
    //     let p = mk_local(*P, mk_fresh_type_mvar());
    //     let h = assume(p.clone()).unwrap();
    //     insta::assert_snapshot!(imp_intro(p, h).unwrap(), @"⊢ ((imp (local p Prop)) (local p Prop))");

    //     // weakening
    //     let p = mk_local(*P, mk_fresh_type_mvar());
    //     insta::assert_snapshot!(imp_intro(p, eq_intro(mk_const(*IMP, vec![])).unwrap()).unwrap(), @"⊢ ((imp (local p Prop)) ((eq.{(Prop → (Prop → Prop))} imp) imp))");

    //     // p → q
    //     let p1 = mk_app(
    //         mk_app(mk_const(*IMP, vec![]), mk_local(*P, mk_fresh_type_mvar())),
    //         mk_local(*Q, mk_fresh_type_mvar()),
    //     );
    //     // p
    //     let p2 = mk_local(*P, mk_fresh_type_mvar());
    //     let h1 = assume(p1).unwrap();
    //     let h2 = assume(p2).unwrap();
    //     insta::assert_snapshot!(imp_elim(h1, h2).unwrap(), @"((imp (local p Prop)) (local q Prop)) (local p Prop) ⊢ (local q Prop)");
    // }

    // #[test]
    // fn test_imp_err() {
    //     // (λ (x : Prop), x) (λ (x : Prop), x)
    //     let p1 = mk_app(
    //         mk_abs(*X, mk_type_prop(), mk_var(0)),
    //         mk_abs(*X, mk_type_prop(), mk_var(0)),
    //     );
    //     // p
    //     let p2 = mk_local(*P, mk_fresh_type_mvar());
    //     // p q
    //     let p3 = mk_app(
    //         mk_local(*P, mk_fresh_type_mvar()),
    //         mk_local(*Q, mk_fresh_type_mvar()),
    //     );
    //     // q
    //     let p4 = mk_local(*Q, mk_fresh_type_mvar());

    //     insta::assert_snapshot!(imp_intro(p1, assume(p2.clone()).unwrap()).unwrap_err(), @"type mismatch");
    //     insta::assert_snapshot!(imp_intro(p3, assume(p2.clone()).unwrap()).unwrap_err(), @"uninstantiated meta type variable");

    //     let h1 = assume(p2).unwrap();
    //     let h2 = assume(p4).unwrap();
    //     insta::assert_snapshot!(imp_elim(h1, h2).unwrap_err(), @"not an implication");
    // }

    // #[test]
    // fn test_forall() {
    //     // err
    //     let p: Term = mk_local(*P, mk_fresh_type_mvar());
    //     let h = assume(p.clone()).unwrap();
    //     insta::assert_snapshot!(forall_intro(*P, mk_type_prop(), h).unwrap_err(), @"eigenvariable condition fails");

    //     let p: Term = mk_local(*P, mk_fresh_type_mvar());
    //     let h = assume(p.clone()).unwrap();
    //     let h = imp_intro(p, h).unwrap();
    //     insta::assert_snapshot!(forall_intro(*P, mk_type_prop(), h).unwrap(), @"⊢ (forall.{Prop} (lam Prop ((imp (var 0)) (var 0))))");

    //     // weakening
    //     let h = eq_intro(mk_const(*IMP, vec![])).unwrap();
    //     insta::assert_snapshot!(forall_intro(*P, mk_type_prop(), h).unwrap(), @"⊢ (forall.{Prop} (lam Prop ((eq.{(Prop → (Prop → Prop))} imp) imp)))");

    //     let p: Term = mk_local(*P, mk_fresh_type_mvar());
    //     let h = assume(p.clone()).unwrap();
    //     let h = imp_intro(p, h).unwrap();
    //     let h = forall_intro(*P, mk_type_prop(), h).unwrap();
    //     insta::assert_snapshot!(forall_elim(mk_local(*Q, mk_fresh_type_mvar()), h).unwrap(), @"⊢ ((imp (local q Prop)) (local q Prop))");
    // }

    #[test]
    fn test_infer_prop() {
        let proof_env = new_kernel();
        let p = mk_local(Name::intern("p").unwrap());

        /*
         * take p, assume p, already p
         * apply p q
         * instantiate p m
         */

        let mut h = mk_proof_forall_intro(
            Name::intern("p").unwrap(),
            mk_type_prop(),
            mk_proof_imp_intro(p.clone(), mk_proof_assump(p)),
        );
        proof_env
            .infer_prop(&mut LocalEnv::default(), &mut Context::default(), &mut h)
            .unwrap();
    }
}
