use anyhow::Context;
use lex::Lex;
use parse::Parser;

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

    while !lex.is_eof() {
        let cmd =
            match Parser::new(&mut lex, &eval.tt, &eval.ns, eval.local_type_consts.clone()).cmd() {
                Ok(cmd) => cmd,
                Err(e) => {
                    return Err(e).context("parse error");
                }
            };
        eval.run_cmd(cmd.clone()).context("command error")?;
    }

    Ok(())
}
