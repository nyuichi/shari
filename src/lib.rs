use anyhow::Context;
use lex::Lex;
use parse::{ParseError, Parser};

mod cmd;
mod elab;
mod expr;
mod lex;
mod parse;
mod print;
mod proof;
mod tt;

pub fn process(input: &str) -> anyhow::Result<()> {
    let mut eval = cmd::Eval::default();

    let mut lex = Lex::new(input);

    loop {
        let cmd =
            match Parser::new(&mut lex, &eval.tt, &eval.ns, eval.local_type_consts.clone()).cmd() {
                Ok(cmd) => cmd,
                Err(ParseError::Eof { .. }) => {
                    break;
                }
                Err(e) => {
                    return Err(e).context("parse error");
                }
            };
        eval.run_cmd(cmd.clone()).context("command error")?;
    }

    Ok(())
}
