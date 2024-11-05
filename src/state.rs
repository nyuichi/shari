use anyhow::bail;

use crate::{
    cmd::{
        Cmd, CmdAxiom, CmdDef, CmdInfix, CmdInfixl, CmdInfixr, CmdLemma, CmdNofix, CmdPrefix,
        Fixity, Operator,
    },
    kernel::{
        proof::{self, mk_type_prop},
        tt::{Def, LocalEnv},
    },
    lex::Lex,
    parse::{Nasmespace, Parser, TokenTable},
    print::OpTable,
};

#[derive(Debug, Clone)]
pub struct State {
    proof_env: proof::Env,
    tt: TokenTable,
    ns: Nasmespace,
    pp: OpTable,
}

impl State {
    pub fn new() -> State {
        let proof_env = proof::Env::new_kernel();

        let mut ns = Nasmespace::default();
        for &x in proof_env.tt_env.type_consts.keys() {
            ns.type_consts.insert(x);
        }
        for (&x, (local_types, _)) in &proof_env.tt_env.consts {
            ns.consts.insert(x, local_types.len());
        }

        State {
            proof_env,
            ns,
            tt: Default::default(),
            pp: Default::default(),
        }
    }

    fn parse_cmd(&self, input: &str) -> anyhow::Result<Cmd> {
        let mut lex = Lex::new(input);
        let mut parser = Parser::new(&mut lex, &self.tt, &self.ns);
        let cmd = parser.cmd()?;
        parser.eof()?;
        Ok(cmd)
    }

    fn run_cmd(&mut self, cmd: Cmd) -> anyhow::Result<()> {
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
                    mut proof,
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
                if self.proof_env.infer_prop(
                    &mut local_env,
                    &mut proof::Context::default(),
                    &mut proof,
                )? != target
                {
                    bail!("propositions mismatch");
                };
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

    pub fn run(&mut self, input: &str) -> anyhow::Result<()> {
        let cmd = self.parse_cmd(input)?;
        self.run_cmd(cmd)?;
        Ok(())
    }
}
