use crate::kernel::{
    proof::{Proof, Prop},
    tt::{Name, Term, Type},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Fixity {
    Infix,
    Infixl,
    Infixr,
    Nofix,
    Prefix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operator {
    pub symbol: String,
    pub fixity: Fixity,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cmd {
    Infix(CmdInfix),
    Infixr(CmdInfixr),
    Infixl(CmdInfixl),
    Prefix(CmdPrefix),
    Nofix(CmdNofix),
    Def(CmdDef),
    Axiom(CmdAxiom),
    MetaDef(CmdMetaDef),
    // Lemma(CmdLemma),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdInfix {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdInfixr {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdInfixl {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdPrefix {
    pub op: String,
    pub prec: usize,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdNofix {
    pub op: String,
    pub entity: Name,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdDef {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub ty: Type,
    pub target: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdAxiom {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub target: Prop,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdMetaDef {
    pub name: Name,
    pub meta_expr: MetaExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetaValue {
    Proof(Box<Proof>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(Name),
    App(Box<ExprApp>),
    Fun(Box<ExprFun>),
    Unq(Box<MetaExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprApp {
    fun: MetaExpr,
    arg: MetaExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExprFun {
    name: Name,
    ty: Option<Type>,
    body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetaExpr {
    Var(Name),
    App(Box<MetaExprApp>),
    Fun(Box<MetaExprFun>),
    Let(Box<MetaExprLet>),
    Quote(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaExprApp {
    fun: MetaExpr,
    arg: MetaExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaExprFun {
    var: Name,
    body: MetaExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MetaExprLet {
    name: Name,
    val: MetaExpr,
    body: MetaExpr,
}

pub fn mk_expr_fun(name: Name, ty: Option<Type>, body: Expr) -> Expr {
    Expr::Fun(Box::new(ExprFun { name, ty, body }))
}

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub struct CmdLemma {
//     pub name: Name,
//     pub local_types: Vec<Name>,
//     pub target: Prop,
//     pub expr: Expr,
// }

// already : Term → Proof
// assume : Term → Proof → Proof
// take : Var → Term → Proof → Proof
// suffices : [Term →] Proof → Proof → Proof
// use : [Term →] Term → Proof
// show : Term → Proof

// already : (φ : Term Prop) → Proof φ
// assume : (φ : Term Prop) → Proof ψ → Proof (φ → ψ)
// take : ((x : Var u) → Proof (φ x)) → Proof (∀ x, φ x)

// p ::= already φ                -- assump
//     | assume φ, p                   -- imp_intro
//     | take (x : τ), p             -- forall_intro
//     | suffices φ, p, p                      -- imp_elim
//     | use φ, m, p                      -- forall_elim
//     | show φ, p
//     | c.{u₁, ⋯, uₙ}

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum Expr {
//     Already(ExprAlready),
//     Assume(Box<ExprAssume>),
//     Take(Box<ExprTake>),
//     Suffices(Box<ExprSuffices>),
//     Use(Box<ExprUse>),
//     Show(Box<ExprShow>),
//     Const(Box<ExprConst>),
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct ExprAlready {
//     target: Prop,
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct ExprAssume {
//     target: Prop,
//     expr: Expr,
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct ExprTake {
//     name: Name,
//     ty: Type,
//     expr: Expr,
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct ExprSuffices {
//     name: Name,
//     ty: Type,
//     expr: Expr,
// }
