//! Prove by type synthesis.

use std::{collections::HashMap, iter::zip, sync::Arc, vec};

use std::sync::LazyLock;

use crate::tt::{self, Class, Instance, Name, Parameter, Term, Type};

// TODO: Proof tree object は処理系が遅くなる原因なのでやめたい。
// elabの中でexprをガチャガチャしないといけないのでexprは用意して、exprをrunするときに proof.rs で用意された証明規則に対応する関数を呼び出してその関数実行が通ればOKにしたい。
// 同様の理由で Path も捨てたい。
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
    /// Γ ⊢ φ ≡ ψ    Γ | Φ ⊢ h : φ
    /// ---------------------------
    /// Γ | Φ ⊢ conv ψ, h : ψ
    /// ```
    Conv(Arc<(Term, Proof)>),
    /// ```text
    ///
    /// -------------------------- (c.{uᵢ} :⇔ φ)
    /// Γ | Φ ⊢ c.{tᵢ} : [τᵢ/uᵢ]φ
    /// ```
    Ref(Arc<(Name, Vec<Type>, Vec<Instance>)>),
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

pub fn mk_proof_conv(target: Term, h: Proof) -> Proof {
    Proof::Conv(Arc::new((target, h)))
}

pub fn mk_proof_ref(name: Name, ty_args: Vec<Type>, instances: Vec<Instance>) -> Proof {
    Proof::Ref(Arc::new((name, ty_args, instances)))
}

static IMP: LazyLock<Name> = LazyLock::new(|| Name::intern("imp").unwrap());
static FORALL: LazyLock<Name> = LazyLock::new(|| Name::intern("forall").unwrap());

// TODO: これ(とForall)イケてないからやめたい。struct Formula { inner: Term }を用意して、Formulaにgeneralizeとかguardとかを実装したい。
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

#[derive(Debug, Clone)]
pub struct Axiom {
    pub local_types: Vec<Name>,
    pub local_classes: Vec<Class>,
    pub target: Term,
}

#[derive(Debug, Clone)]
pub struct Env<'a> {
    pub tt_env: tt::Env<'a>,
    // Proved or postulated facts
    pub axiom_table: &'a HashMap<Name, Axiom>,
}

#[derive(Debug, Clone, Default)]
pub struct LocalEnv {
    pub local_axioms: Vec<Term>,
}

impl Env<'_> {
    // prop is trusted
    pub fn check_prop(
        &self,
        tt_local_env: &mut tt::LocalEnv,
        local_env: &mut LocalEnv,
        h: &Proof,
        prop: &Term,
    ) {
        let inferred = self.infer_prop(tt_local_env, local_env, h);
        if !inferred.alpha_eq(prop) {
            panic!("proposition mismatch: expected {}, got {}", prop, inferred);
        }
    }

    pub fn infer_prop(
        &self,
        tt_local_env: &mut tt::LocalEnv,
        local_env: &mut LocalEnv,
        h: &Proof,
    ) -> Term {
        match h {
            Proof::Assump(p) => {
                for local_axiom in &local_env.local_axioms {
                    if p.alpha_eq(local_axiom) {
                        return p.clone();
                    }
                }
                panic!("unknown assumption: {}", p);
            }
            Proof::ImpIntro(h) => {
                let (p, h) = &**h;
                self.tt_env.check_wff(tt_local_env, p);
                local_env.local_axioms.push(p.clone());
                let mut target = self.infer_prop(tt_local_env, local_env, h);
                let p = local_env.local_axioms.pop().unwrap();
                target.guard([p]);
                target
            }
            Proof::ImpElim(h) => {
                let (h1, h2) = &**h;
                let h1 = self.infer_prop(tt_local_env, local_env, h1);
                let Imp { lhs, rhs } = h1
                    .clone()
                    .try_into()
                    .unwrap_or_else(|_| panic!("implication expected, got {}", h1));
                self.check_prop(tt_local_env, local_env, h2, &lhs);
                rhs
            }
            Proof::ForallIntro(h) => {
                let &(name, ref ty, ref h) = &**h;
                self.tt_env.check_wft(tt_local_env, ty);
                for c in &local_env.local_axioms {
                    if !c.is_fresh(&[name]) {
                        // eigenvariable condition fails
                        panic!("eigenvariable condition violated by {}", c);
                    }
                }
                let x = Parameter {
                    name,
                    ty: ty.clone(),
                };
                tt_local_env.locals.push(x);
                let mut target = self.infer_prop(tt_local_env, local_env, h);
                let x = tt_local_env.locals.pop().unwrap();
                target.generalize(&[x]);
                target
            }
            Proof::ForallElim(h) => {
                let (m, h) = &**h;
                let h = self.infer_prop(tt_local_env, local_env, h);
                let Forall { domain, pred } = h
                    .clone()
                    .try_into()
                    .unwrap_or_else(|_| panic!("∀ expected, got {}", h));
                self.tt_env.check_type(tt_local_env, m, &domain);
                let mut target = pred;
                target.apply([m.clone()]);
                target
            }
            Proof::Conv(h) => {
                let (target, proof) = &**h;
                self.tt_env.check_wff(tt_local_env, target);
                let source = self.infer_prop(tt_local_env, local_env, proof);
                if !self.tt_env.equiv(&source, target) {
                    panic!(
                        "conversion failed: expected {} but proof showed {}",
                        target, source
                    );
                }
                target.clone()
            }
            Proof::Ref(h) => {
                let (name, ty_args, instances) = &**h;
                let Axiom {
                    local_types,
                    local_classes,
                    target,
                } = self
                    .axiom_table
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown axiom: {:?}", name));
                if ty_args.len() != local_types.len() {
                    panic!(
                        "axiom {:?} expects {} type arguments but got {}",
                        name,
                        local_types.len(),
                        ty_args.len()
                    );
                }
                for ty_arg in ty_args {
                    self.tt_env.check_wft(tt_local_env, ty_arg);
                }
                let mut type_subst = vec![];
                for (&x, t) in zip(local_types, ty_args) {
                    type_subst.push((x, t.clone()))
                }
                if local_classes.len() != instances.len() {
                    panic!(
                        "axiom {:?} expects {} class arguments but got {}",
                        name,
                        local_classes.len(),
                        instances.len()
                    );
                }
                for (local_class, instance) in zip(local_classes, instances) {
                    let mut local_class = local_class.clone();
                    local_class.subst(&type_subst);
                    self.tt_env
                        .check_class(tt_local_env, instance, &local_class);
                }
                let mut target = target.clone();
                target.subst_type(&type_subst);
                target
            }
        }
    }
}
