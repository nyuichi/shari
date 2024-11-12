use anyhow::bail;

use crate::{
    expr::{self, mk_expr_change, Expr},
    kernel::{
        proof::{self, mk_type_prop, Prop},
        tt::{Def, LocalEnv, Name, Term, Type},
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
    pub target: Prop,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CmdLemma {
    pub name: Name,
    pub local_types: Vec<Name>,
    pub target: Prop,
    pub expr: Expr,
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
                };
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target.target,
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
                };
                self.proof_env.tt_env.check_type(
                    &mut local_env,
                    &mut target.target,
                    &mut mk_type_prop(),
                )?;
                let expr = mk_expr_change(target.target.clone(), expr);
                let (mut h, _target) =
                    expr::Eval::new(&self.proof_env, &mut local_env).run_expr(&expr)?;
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
        }
    }
}
