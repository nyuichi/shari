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

    fn minimal_logic_prelude() -> &'static str {
        "type const Prop : Type
         const imp : Prop → Prop → Prop
         const forall.{u} : (u → Prop) → Prop
         const uexists.{u} : (u → Prop) → Prop
         const eq.{u} : u → u → Prop
         const and : Prop → Prop → Prop
         const true : Prop
         axiom eq.refl.{u} (x : u) : eq x x
         infixr → : 25 := imp
         infix = : 50 := eq
         const top : Prop"
    }

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

    #[test]
    fn class_instance_allows_referencing_prior_definition() {
        let file = Arc::new(File::new(
            "<test>",
            "type const Prop : Type
             const p : Prop
             class structure C := {
                 const a : Prop
                 const b : Prop
             }
             class instance c_inst : C := {
                 def a : Prop := p
                 def b : Prop := a
             }",
        ));
        process(file).expect("class instance definitions should resolve prior fields");
    }

    #[test]
    fn instance_preceding_definition_is_definitionally_equal() {
        let script = format!(
            "{}
             structure foo := {{
                 const a : Prop
                 const b : Prop
             }}
             instance bar : foo := {{
                 def a : Prop := top
                 def b : Prop := a
             }}
             lemma instance_defeq : bar.b = bar.a := eq.refl",
            minimal_logic_prelude()
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("bar.b and bar.a should be definitionally equal");
    }

    #[test]
    fn class_instance_preceding_definition_is_definitionally_equal() {
        let script = format!(
            "{}
             class structure foo_class := {{
                 const a : Prop
                 const b : Prop
             }}
             class instance bar_class : foo_class := {{
                 def a : Prop := top
                 def b : Prop := a
             }}
             lemma class_instance_defeq : foo_class.b = foo_class.a := eq.refl",
            minimal_logic_prelude()
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("foo_class.b and foo_class.a should be definitionally equal");
    }
}
