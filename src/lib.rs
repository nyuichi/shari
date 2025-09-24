use std::sync::Arc;

use anyhow::Context;
use lex::Lex;
use parse::Parser;

mod cmd;
mod elab;
mod lex;
mod parse;
mod print;
mod proof;
mod tt;

pub fn process(input: &str) -> anyhow::Result<()> {
    let mut eval = cmd::Eval::default();

    let mut lex = Lex::new(Arc::new(input.to_owned()));

    while !lex.is_eof() {
        let cmd = match Parser::new(
            &mut lex,
            &eval.tt,
            &eval.type_const_table,
            &eval.const_table,
            &eval.axiom_table,
            &eval.class_predicate_table,
            eval.local_type_consts.clone(),
        )
        .cmd()
        {
            Ok(cmd) => cmd,
            Err(e) => {
                return Err(e).context("parse error");
            }
        };
        eval.run_cmd(cmd.clone()).context("command error")?;
    }

    Ok(())
}
