//! Prove by type synthesis.

use std::{collections::HashMap, iter::zip, sync::Arc, vec};

use std::sync::LazyLock;

use crate::tt::{self, Name, Parameter, Path, Term, Type};

#[derive(Debug, Clone)]
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
    /// Γ | Φ ⊢ h : ∀ φ
    /// ------------------------------
    /// Γ | Φ ⊢ forall_elim m, h : φ m
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

static IMP: LazyLock<Name> = LazyLock::new(|| Name::intern("imp").unwrap());
static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall").unwrap());

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

#[derive(Debug, Clone)]
pub struct Forall {
    pub domain: Type,
    pub pred: Term,
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
        let domain = Arc::make_mut(&mut head).ty_args.pop().unwrap();
        if args.len() != 1 {
            return Err(());
        }
        let pred = args.pop().unwrap();
        Ok(Forall { domain, pred })
    }
}

#[derive(Debug, Clone, Default)]
pub struct Env {
    pub tt_env: tt::Env,
    // Proved or postulated facts
    pub axioms: HashMap<Name, (Vec<Name>, Term)>,
}

#[derive(Debug, Clone, Default)]
pub struct LocalEnv {
    pub local_axioms: Vec<Term>,
}

impl Env {
    // prop is trusted
    pub fn check_prop(
        &self,
        tt_local_env: &mut tt::LocalEnv,
        local_env: &mut LocalEnv,
        h: &Proof,
        prop: &Term,
    ) -> bool {
        let Some(p) = self.infer_prop(tt_local_env, local_env, h) else {
            return false;
        };
        p.typed_eq(prop)
    }

    pub fn infer_prop(
        &self,
        tt_local_env: &mut tt::LocalEnv,
        local_env: &mut LocalEnv,
        h: &Proof,
    ) -> Option<Term> {
        match h {
            Proof::Assump(p) => {
                for local_axiom in &local_env.local_axioms {
                    if p.typed_eq(local_axiom) {
                        return Some(p.clone());
                    }
                }
                None
            }
            Proof::ImpIntro(h) => {
                let (p, h) = &**h;
                if !self.tt_env.is_wff(tt_local_env, p) {
                    return None;
                }
                local_env.local_axioms.push(p.clone());
                let mut target = self.infer_prop(tt_local_env, local_env, h)?;
                let p = local_env.local_axioms.pop().unwrap();
                target.guard([p]);
                Some(target)
            }
            Proof::ImpElim(h) => {
                let (h1, h2) = &**h;
                let h1 = self.infer_prop(tt_local_env, local_env, h1)?;
                let Ok(Imp { lhs, rhs }) = h1.clone().try_into() else {
                    return None;
                };
                if !self.check_prop(tt_local_env, local_env, h2, &lhs) {
                    return None;
                }
                Some(rhs)
            }
            Proof::ForallIntro(h) => {
                let &(name, ref ty, ref h) = &**h;
                if !self.tt_env.is_wft(tt_local_env, ty) {
                    return None;
                }
                for c in &local_env.local_axioms {
                    if !c.is_fresh(&[name]) {
                        // eigenvariable condition fails
                        return None;
                    }
                }
                let x = Parameter {
                    name,
                    ty: ty.clone(),
                };
                tt_local_env.locals.push(x);
                let mut target = self.infer_prop(tt_local_env, local_env, h)?;
                let x = tt_local_env.locals.pop().unwrap();
                target.generalize(&[x]);
                Some(target)
            }
            Proof::ForallElim(h) => {
                let (m, h) = &**h;
                let h = self.infer_prop(tt_local_env, local_env, h)?;
                let Ok(Forall { domain, pred }) = h.clone().try_into() else {
                    return None;
                };
                if !self.tt_env.check_type(tt_local_env, m, &domain) {
                    return None;
                }
                let mut target = pred;
                target.apply([m.clone()]);
                Some(target)
            }
            Proof::Conv(h) => {
                let (h1, h2) = &**h;
                let h1 = self.tt_env.infer_conv(tt_local_env, h1)?;
                if !self.check_prop(tt_local_env, local_env, h2, &h1.left) {
                    return None;
                }
                Some(h1.right)
            }
            Proof::Ref(h) => {
                let (name, ty_args) = &**h;
                let (tv, target) = self.axioms.get(name)?;
                if ty_args.len() != tv.len() {
                    return None;
                }
                for ty_arg in ty_args {
                    if !self.tt_env.is_wft(tt_local_env, ty_arg) {
                        return None;
                    }
                }
                let mut subst = vec![];
                for (&x, t) in zip(tv, ty_args) {
                    subst.push((x, t.clone()))
                }
                let mut target = target.clone();
                target.subst_type(&subst);
                Some(target)
            }
        }
    }
}
