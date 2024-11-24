use anyhow::bail;

use crate::{
    expr::{self, mk_expr_app, mk_expr_assume, mk_expr_assump, Expr},
    kernel::{
        proof::{self, mk_type_prop},
        tt::{Def, Kind, LocalEnv, Name, Term, Type},
    },
    parse::{Nasmespace, TokenTable},
    print::OpTable,
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
    Lemma(CmdLemma),
    Const(CmdConst),
    TypeConst(CmdTypeConst),
    // MetaDef(CmdMetaDef),
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
    pub target: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdLemma {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub target: Term,
    pub holes: Vec<(Name, Type)>,
    pub expr: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdConst {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdTypeConst {
    pub name: Name,
    pub kind: Kind,
}

#[derive(Debug, Clone)]
pub struct Eval {
    pub proof_env: proof::Env,
    pub tt: TokenTable,
    pub ns: Nasmespace,
    pub pp: OpTable,
}

impl Eval {
    pub fn new() -> Eval {
        let proof_env = proof::Env::new_kernel();

        let mut ns = Nasmespace::default();
        for &x in proof_env.tt_env.type_consts.keys() {
            ns.type_consts.insert(x);
        }
        for (&x, (local_types, _)) in &proof_env.tt_env.consts {
            ns.consts.insert(x, local_types.len());
        }

        Eval {
            proof_env,
            ns,
            tt: Default::default(),
            pp: Default::default(),
        }
    }

    pub fn run_cmd(&mut self, cmd: Cmd) -> anyhow::Result<()> {
        match cmd {
            Cmd::Infix(inner) => {
                let CmdInfix { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infix,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Infixr(inner) => {
                let CmdInfixr { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infixr,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;

                Ok(())
            }
            Cmd::Infixl(inner) => {
                let CmdInfixl { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Infixl,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;

                Ok(())
            }
            Cmd::Prefix(inner) => {
                let CmdPrefix { op, prec, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Prefix,
                    prec,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Nofix(inner) => {
                let CmdNofix { op, entity } = inner;
                let op = Operator {
                    symbol: op,
                    fixity: Fixity::Nofix,
                    prec: usize::MAX,
                    entity,
                };
                self.tt.add(op.clone())?;
                self.pp.add(op)?;
                Ok(())
            }
            Cmd::Def(inner) => {
                let CmdDef {
                    name,
                    local_types,
                    mut ty,
                    mut target,
                } = inner;
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env
                    .tt_env
                    .check_type(&mut local_env, &mut target, &mut ty)?;
                if self.proof_env.tt_env.consts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.consts.insert(name, local_env.local_types.len());
                self.proof_env
                    .tt_env
                    .consts
                    .insert(name, (local_env.local_types.clone(), ty.clone()));
                self.proof_env.tt_env.defs.insert(
                    name,
                    Def {
                        local_types: local_env.local_types,
                        ty,
                        target,
                        hint: self.proof_env.tt_env.defs.len(),
                    },
                );
                Ok(())
            }
            Cmd::Axiom(inner) => {
                let CmdAxiom {
                    name,
                    local_types,
                    mut target,
                } = inner;
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target,
                    &mut mk_type_prop(),
                )?;
                if self.proof_env.facts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.facts.insert(name, local_env.local_types.len());
                self.proof_env
                    .facts
                    .insert(name, (local_env.local_types, target));
                Ok(())
            }
            Cmd::Lemma(inner) => {
                let CmdLemma {
                    name,
                    local_types,
                    mut target,
                    holes,
                    expr,
                } = inner;
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                let mut local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes,
                };
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target,
                    &mut mk_type_prop(),
                )?;
                // auto insert 'change'
                let mut expr = mk_expr_app(
                    mk_expr_assume(target.clone(), mk_expr_assump(target.clone())),
                    expr,
                    target.clone(),
                );
                let mut h = expr::Env::new(
                    &self.proof_env.tt_env,
                    &mut local_env,
                    &self.proof_env.facts,
                )
                .elaborate(&mut expr)?;
                self.proof_env.check_prop(
                    &mut local_env,
                    &mut proof::Context::default(),
                    &mut h,
                    &target,
                )?;
                if self.proof_env.facts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.facts.insert(name, local_env.local_types.len());
                self.proof_env
                    .facts
                    .insert(name, (local_env.local_types, target));
                Ok(())
            }
            Cmd::Const(inner) => {
                let CmdConst {
                    name,
                    local_types,
                    ty,
                } = inner;
                for i in 0..local_types.len() {
                    for j in i + 1..local_types.len() {
                        if local_types[i] == local_types[j] {
                            bail!("duplicate type variables");
                        }
                    }
                }
                let local_env = LocalEnv {
                    local_types,
                    locals: vec![],
                    holes: vec![],
                };
                self.proof_env
                    .tt_env
                    .check_kind(&local_env, &ty, &Kind::base())?;
                if self.proof_env.tt_env.consts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.consts.insert(name, local_env.local_types.len());
                self.proof_env
                    .tt_env
                    .consts
                    .insert(name, (local_env.local_types.clone(), ty.clone()));
                Ok(())
            }
            Cmd::TypeConst(inner) => {
                let CmdTypeConst { name, kind } = inner;
                if self.proof_env.tt_env.type_consts.contains_key(&name) {
                    bail!("already defined");
                }
                self.ns.type_consts.insert(name);
                self.proof_env.tt_env.type_consts.insert(name, kind);
                Ok(())
            }
        }
    }
}
