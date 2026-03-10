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
            &eval.type_def_table,
            &eval.const_table,
            &eval.axiom_table,
            &eval.class_predicate_table,
            &eval.structure_table,
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
         const exists.{u} : (u → Prop) → Prop
         const uexists.{u} : (u → Prop) → Prop
         const eq.{u} : u → u → Prop
         const and : Prop → Prop → Prop
         const true : Prop
         infixr → : 25 := imp
         infix = : 50 := eq
         axiom eq.refl.{u} (x : u) : eq x x
         axiom exists.ind.{u} (P : u → Prop) (Q : Prop) : exists P → forall (λ (x : u), P x → Q) → Q
         axiom uexists.exists.{u} (P : u → Prop) : uexists P → exists P
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

    #[test]
    fn instance_lemma_can_reference_preceding_lemma() {
        let script = format!(
            "{}
             const p : Prop
             axiom hp : p
             structure foo := {{
                 axiom h1 : p
                 axiom h2 : p
             }}
             instance bar : foo := {{
                 lemma h1 : p := hp
                 lemma h2 : p := h1
             }}",
            minimal_logic_prelude()
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("instance lemma should resolve preceding lemma alias");
    }

    #[test]
    fn class_instance_lemma_can_reference_preceding_lemma() {
        let script = format!(
            "{}
             const p : Prop
             axiom hp : p
             class structure foo_class := {{
                 axiom h1 : p
                 axiom h2 : p
             }}
             class instance bar_class : foo_class := {{
                 lemma h1 : p := hp
                 lemma h2 : p := h1
             }}",
            minimal_logic_prelude()
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("class instance lemma should resolve preceding lemma alias");
    }

    #[test]
    fn obtain_instance_expression_processes() {
        let script = format!(
            "{}
             const p : Prop
             axiom hp : p
             structure foo := {{
                 const rep : Prop
                 axiom ok : rep
             }}
             lemma obtain_instance_expr : p :=
               obtain instance c : foo := {{
                   def rep : Prop := p
                   lemma ok : rep := hp
               }},
               c.ok",
            minimal_logic_prelude()
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("obtain instance expression should elaborate");
    }

    #[test]
    fn obtain_instance_expression_supports_multiple_const_fields() {
        let script = format!(
            "{}
             const p : Prop
             const q : Prop
             axiom hp : p
             axiom hq : q
             structure pairish := {{
                 const left : Prop
                 const right : Prop
                 axiom left_ok : left
                 axiom right_ok : right
             }}
             lemma obtain_instance_pairish : p :=
               obtain instance c : pairish := {{
                   def left : Prop := p
                   def right : Prop := q
                   lemma left_ok : left := hp
                   lemma right_ok : right := hq
               }},
               c.left_ok",
            minimal_logic_prelude()
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("obtain instance should support multi-field characteristics");
    }

    #[test]
    fn process_allows_type_definitions() {
        let script = format!(
            "{}
             type const U : Type
             type def sub u := u → Prop
             const s : sub U",
            minimal_logic_prelude()
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("type def should be available in later declarations");
    }

    #[test]
    fn process_accepts_nat_alias_defined_via_type_def() {
        let script = format!(
            "{}
             type const nat : Type
             type def ℕ := nat
             const zero : nat
             const one : ℕ",
            minimal_logic_prelude()
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("ℕ alias should be provided by type def");
    }

    #[test]
    fn main_prelude_supports_proposition_truncation_helpers() {
        let script = format!(
            "{}
             type const test_A : Type
             type const test_B : Type
             const test_a : test_A
             const test_b : test_B
             const test_f : test_B → test_A
             const test_hp : is_proposition test_A

             def test_fun_prop : is_proposition (test_B → test_A) := fun.is_proposition test_hp
             def test_a_inhabited : is_inhabited test_A := is_inhabited.mk test_a
             def test_a_contractible : is_contractible test_A := is_proposition.is_contractible test_hp test_a_inhabited
             def test_chosen_a : test_A := is_proposition.indefinite_description test_hp test_a_inhabited
             def test_rec_a : test_A := is_inhabited.rec test_hp test_f (is_inhabited.mk test_b)",
            include_str!("main.shari")
        );
        let file = Arc::new(File::new("<test>", script));
        process(file).expect("main prelude should provide proposition truncation helpers");
    }
}
