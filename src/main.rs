use shari::elaborator;
use shari::logic;
use shari::parser;
use shari::tactic;
use shari::term;

#[derive(Default)]
struct Prover {
    spec: logic::Spec,
    token_table: parser::TokenTable,
}

impl Prover {
    fn new_const(&mut self, name: &str, type_vars: &[&str], t: &str) {
        self.spec.sign.add_const(
            self.name(name),
            term::Scheme::<term::Type> {
                type_vars: self.type_vars(type_vars),
                main: self.r#type(t),
            },
        )
    }

    fn new_infixr(&mut self, name: &str, prec: usize, entity: &str) {
        self.token_table
            .add(name, parser::Fixity::Infixr, prec, entity);
    }

    fn new_infixl(&mut self, name: &str, prec: usize, entity: &str) {
        self.token_table
            .add(name, parser::Fixity::Infixl, prec, entity);
    }

    /// alias to infixl
    fn new_infix(&mut self, name: &str, prec: usize, entity: &str) {
        self.new_infixl(name, prec, entity);
    }

    fn new_prefix(&mut self, name: &str, prec: usize, entity: &str) {
        self.token_table
            .add(name, parser::Fixity::Prefix, prec, entity);
    }

    fn new_nofix(&mut self, name: &str, entity: &str) {
        self.token_table
            .add(name, parser::Fixity::Nofix, 12345678, entity);
    }

    fn new_def(&mut self, name: &str, type_vars: &[&str], t: &str, m: &str) {
        self.new_const(name, type_vars, t);
        let m = self.term(&[], m);
        assert_eq!(*m.r#type(), self.r#type(t));
        self.spec.defs.insert(
            self.name(name),
            term::Scheme {
                type_vars: self.type_vars(type_vars),
                main: m,
            },
        );
    }

    fn new_axiom(&mut self, name: &str, type_vars: &[&str], m: &str) {
        let m = self.term(&[], m);
        assert_eq!(*m.r#type(), term::Type::Fvar(self.name("Prop")));
        self.spec.axioms.insert(
            self.name(name),
            term::Scheme {
                type_vars: self.type_vars(type_vars),
                main: m,
            },
        );
    }

    fn new_theorem(&mut self, name: &str, type_vars: &[&str], h: logic::Theorem) {
        self.spec.theorems.insert(
            self.name(name),
            term::Scheme {
                type_vars: self.type_vars(type_vars),
                main: h,
            },
        );
    }

    fn name(&self, input: &str) -> term::Name {
        let mut parser = parser::Parser::new(input, "", &self.token_table);
        let x = parser.name().unwrap_or_else(|_| todo!());
        parser.eof().unwrap_or_else(|_| todo!());
        term::Name::from(x)
    }

    fn r#type(&self, input: &str) -> term::Type {
        let mut parser = parser::Parser::new(input, "", &self.token_table);
        let t = parser.r#type().unwrap_or_else(|_| todo!());
        parser.eof().unwrap_or_else(|_| todo!());
        let t = elaborator::Type::from(t);
        t.elaborate(&self.spec.sign)
    }

    fn type_vars(&self, input: &[&str]) -> Vec<term::Name> {
        input.into_iter().map(|x| self.name(*x)).collect()
    }

    fn term(&self, locals: &[(&str, &str)], input: &str) -> term::Term {
        let mut parser = parser::Parser::new(input, "", &self.token_table);
        let m = parser.term().unwrap_or_else(|_| todo!());
        parser.eof().unwrap_or_else(|_| todo!());
        let m = elaborator::Term::from(m);
        let local_consts = locals
            .iter()
            .map(|(x, t)| (self.name(x), self.r#type(t)))
            .collect();
        m.elaborate(&self.spec.sign, &local_consts)
    }

    fn assume(&self, locals: &[(&str, &str)], input: &str) -> logic::Theorem {
        let local_consts = locals
            .iter()
            .map(|(x, t)| (self.name(x), self.r#type(t)))
            .collect();
        let m = self.term(locals, input);
        logic::Theorem::assume(self.spec.clone(), local_consts, m)
    }
}

fn main() {
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
}
