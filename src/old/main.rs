use shari::parser;
use shari::term;

fn main() {
    let mut sign = term::Sign::default();
    sign.add_type(term::Name::Str("Prop".to_owned()));

    let mut token_table = parser::TokenTable::default();
    let filename = "example/basic.neta";
    let input = std::fs::read_to_string(filename).unwrap();
    let mut lex = parser::Lex::new(&input, filename);
    loop {
        let mut parser = parser::Parser::new(&mut lex, &token_table);
        if parser.eof_opt() {
            break;
        }
        let cmd = parser
            .command()
            .map_err(|e| {
                println!("{}", e);
                e
            })
            .unwrap();
        println!("{}", cmd);
        match cmd {
            parser::Command::DefCmd(parser::DefCommand {
                name,
                r#type,
                term: _term,
            }) => {
                //TODO: check integrity of r#type and type of term
                sign.add_const(name, r#type.elaborate(&sign));
            }
            parser::Command::ConstCmd(parser::ConstCommand { name, r#type }) => {
                sign.add_const(name, r#type.elaborate(&sign))
            }
            parser::Command::PropCmd(parser::PropCommand {
                name: _name,
                prop: _prop,
                proof: _proof,
            }) => {
                // TODO
            }
            parser::Command::AxiomCmd(parser::AxiomCommand {
                name: _name,
                prop: _prop,
            }) => {
                // TODO
                // spec.add_axiom(name, prop.elaborate(&sign))
            }
            parser::Command::CheckCmd(_) => todo!(),
            parser::Command::InfixrCmd(parser::InfixrCommand { op, prec, entity }) => {
                token_table.add(&op, parser::Fixity::Infixr, prec, entity);
            }
            parser::Command::InfixlCmd(parser::InfixlCommand { op, prec, entity }) => {
                token_table.add(&op, parser::Fixity::Infixl, prec, entity);
            }
            parser::Command::InfixCmd(parser::InfixCommand { op, prec, entity }) => {
                // alias to infixl
                token_table.add(&op, parser::Fixity::Infixl, prec, entity);
            }
            parser::Command::NofixCmd(parser::NofixCommand { op, entity }) => {
                token_table.add(&op, parser::Fixity::Nofix, 12345678, entity);
            }
            parser::Command::PrefixCmd(parser::PrefixCommand { op, prec, entity }) => {
                token_table.add(&op, parser::Fixity::Prefix, prec, entity);
            }
        }
    }
    /*
    let mut p = Prover::default();
    // TODO: env.add_type(p.name("Prop"));
    p.new_const("eq", &["α"], "α → α → Prop");
    p.new_infix("=", 50, "eq");
    p.new_const("top", &[], "Prop");
    p.new_nofix("⊤", "top");
    p.new_const("imp", &[], "Prop → Prop → Prop");
    p.new_infixr("→", 25, "imp");
    p.new_const("forall", &["α"], "(α → Prop) → Prop");
    p.new_def(
        "and",
        &[],
        "Prop → Prop → Prop",
        "λ p q, ∀ r, (p → q → r) → r",
    );
    p.new_infixr("∧", 35, "and");
    p.new_def("iff", &[], "Prop → Prop → Prop", "λ p q, (p → q) ∧ (q → p)");
    p.new_infix("↔", 20, "iff");
    p.new_def("bot", &[], "Prop", "∀ r, r");
    p.new_nofix("⊥", "bot");
    p.new_def("not", &[], "Prop → Prop", "λ p, ∀ r, p → r");
    p.new_prefix("¬", 40, "not");
    p.new_def(
        "or",
        &[],
        "Prop → Prop → Prop",
        "λ p q, ∀ r, (p → r) ∧ (q → r) → r",
    );
    p.new_infixr("∨", 30, "or");
    p.new_def(
        "exists",
        &["α"],
        "(α → Prop) → Prop",
        "λ P, ∀ r, (∀ (x : α), P x → r) → r",
    );
    p.new_axiom(
        "fun_ext",
        &["α", "β"],
        "∀ (f₁ f₂ : α → β), (f₁ = f₂) ↔ (∀ x, f₁ x = f₂ x)",
    );
    p.new_axiom("prop_ext", &[], "∀ p q, (p = q) ↔ (p ↔ q)");

    p.new_theorem("mp", &[], {
        let locals = [("p", "Prop"), ("q", "Prop")];
        let mut h = p.assume(&locals, "p → q");
        h.imp_elim(p.assume(&locals, "p"));
        h.imp_intro(&p.term(&locals, "p → q"));
        h.imp_intro(&p.term(&locals, "p"));
        h.forall_intro(&p.name("q"));
        h.forall_intro(&p.name("p"));
        println!("{}", h);
        h
    });

    p.new_theorem("mp_by_tactic", &[], {
        let mut t = tactic::TacticState::new(p.spec.clone(), p.term(&[], "∀ p q, p → (p → q) → q"));
        t.forall_intro(p.name("p"));
        t.forall_intro(p.name("q"));
        t.imp_intro();
        t.imp_intro();
        t.imp_elim(p.term(&[("p", "Prop")], "p"));
        t.assume();
        t.assume();
        let h = t.qed();
        println!("{}", h);
        h
    });
    */
}
