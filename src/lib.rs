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

pub use lex::File;

pub fn process(file: Arc<File>) -> anyhow::Result<()> {
    let mut eval = cmd::Eval::default();

    let mut lex = Lex::new(file);

    while !lex.is_eof() {
        let cmd = match Parser::new(
            &mut lex,
            &eval.tt,
            &eval.namespace_table,
            &eval.current_namespace,
            &eval.type_const_table,
            &eval.const_table,
            &eval.axiom_table,
            &eval.class_predicate_table,
        )
        .cmd()
        {
            Ok(cmd) => {
                log::trace!("parsed command:\n{cmd}");
                cmd
            }
            Err(e) => {
                return Err(e).context("parse error");
            }
        };
        eval.run_cmd(cmd.clone()).context("command error")?;
    }

    if !eval.namespace_stack.is_empty() {
        return Err(anyhow::anyhow!("unclosed namespace block")).context("command error");
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn error_chain(err: &anyhow::Error) -> Vec<String> {
        err.chain().map(ToString::to_string).collect()
    }

    #[test]
    fn root_closing_brace_is_command_error() {
        let file = Arc::new(File::new("<test>", "}"));
        let err = process(file).expect_err("top-level block end should fail");
        let chain = error_chain(&err);
        assert!(
            chain.iter().any(|msg| msg == "command error"),
            "expected command error in chain: {chain:?}"
        );
    }

    #[test]
    fn unclosed_namespace_is_command_error() {
        let file = Arc::new(File::new("<test>", "namespace foo {"));
        let err = process(file).expect_err("unclosed namespace should fail");
        let chain = error_chain(&err);
        assert!(
            chain.iter().any(|msg| msg == "command error"),
            "expected command error in chain: {chain:?}"
        );
    }

    #[test]
    fn namespace_allows_referencing_prior_declaration() {
        let file = Arc::new(File::new(
            "<test>",
            "namespace foo {
                 type const U : Type
                 const c : U
                 def d : U := c
             }",
        ));
        process(file).expect("namespace declarations should be resolved incrementally");
    }
}
