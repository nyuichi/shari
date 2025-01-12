//! Prove by type synthesis.

use std::{collections::HashMap, iter::zip, sync::Arc, vec};

use anyhow::bail;
use std::sync::LazyLock;

use crate::tt::{self, mk_abs, mk_const, mk_type_const, LocalEnv, Name, Path, Term, TermAbs, Type};

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
        if !p.typed_eq(prop) {
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
                    if p.typed_eq(c) {
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
                self.tt_env.ensure_wft(local_env, t)?;
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
                    self.tt_env.ensure_wft(local_env, ty_arg)?;
                }
                let mut subst = vec![];
                for (&x, t) in zip(&tv, &*ty_args) {
                    subst.push((x, t.clone()))
                }
                target.subst_type(&subst);
                Ok(target)
            }
        }
    }
}
