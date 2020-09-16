use shari::elaborator;
use shari::env;
use shari::logic;
use shari::parser;
use shari::term;
use std::collections::HashMap;

#[derive(Default)]
struct Prover {
    env: env::Env,
    token_table: parser::TokenTable,
    defs: HashMap<term::Name, (Vec<term::Name>, term::Term)>,
    axioms: HashMap<term::Name, (Vec<term::Name>, term::Term)>,
    theorems: HashMap<term::Name, (Vec<term::Name>, term::Term)>,
}

impl Prover {
    fn new_const(&mut self, name: &str, type_vars: &[&str], t: &str) {
        self.env.add_const(
            self.name(name),
            env::TypeScheme {
                vars: self.type_vars(type_vars),
                scheme: self.r#type(t),
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
        let m = self.term(m);
        assert_eq!(*m.r#type(), self.r#type(t));
        self.defs
            .insert(self.name(name), (self.type_vars(type_vars), m));
    }

    fn new_axiom(&mut self, name: &str, type_vars: &[&str], m: &str) {
        let m = self.term(m);
        assert_eq!(*m.r#type(), term::Type::Fvar(self.name("Prop")));
        self.axioms
            .insert(self.name(name), (self.type_vars(type_vars), m));
    }

    fn new_theorem(&mut self, name: &str, type_vars: &[&str], h: logic::Theorem) {
        self.theorems
            .insert(self.name(name), (self.type_vars(type_vars), h.certify()));
    }

    fn name(&self, input: &str) -> term::Name {
        term::Name::Named(input.to_owned())
    }

    fn r#type(&self, input: &str) -> term::Type {
        let t = parser::Parser::new(input, "", &self.token_table)
            .r#type()
            .unwrap_or_else(|_| todo!());
        let t = elaborator::Type::from(t);
        t.elaborate(&self.env)
    }

    fn type_vars(&self, input: &[&str]) -> Vec<term::Name> {
        input.into_iter().map(|x| self.name(*x)).collect()
    }

    fn term(&self, input: &str) -> term::Term {
        self.local_term(input, Default::default())
    }

    fn local_term(&self, input: &str, locals: HashMap<term::Name, term::Type>) -> term::Term {
        let m = parser::Parser::new(input, "", &self.token_table)
            .term()
            .unwrap_or_else(|_| todo!());
        let m = elaborator::Term::from(m);
        m.elaborate(&self.env, locals)
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
    p.new_def(
        "iff",
        &[],
        "Prop → Prop → Prop",
        "λ (p q : Prop), (p → q) ∧ (q → p)",
    );
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
        "∀ (m₁ m₂ : α → β), (m₁ = m₂) ↔ (∀ x, m₁ x = m₂ x)",
    );
    p.new_axiom("prop_ext", &[], "∀ p q, (p = q) ↔ (p ↔ q)");

    p.new_theorem("mp", &[], {
        use logic::Theorem as T;

        let locals: HashMap<_, _> = vec![
            (term::Name::Named("p".to_owned()), p.r#type("Prop")),
            (term::Name::Named("q".to_owned()), p.r#type("Prop")),
        ]
        .into_iter()
        .collect();
        let mut h = T::assume(locals.clone(), p.local_term("p → q", locals.clone()));
        h.imp_elim(T::assume(locals.clone(), p.local_term("p", locals.clone())));
        h.imp_intro(&p.local_term("p → q", locals.clone()));
        h.imp_intro(&p.local_term("p", locals.clone()));
        h.forall_intro(&p.name("q"));
        h.forall_intro(&p.name("p"));
        println!("proved: {}.", h.clone().certify());
        h
    });
}
