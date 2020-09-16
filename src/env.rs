use crate::term;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub vars: Vec<term::Name>,
    pub scheme: term::Type,
}

#[derive(Debug, Default)]
pub struct Env {
    consts: HashMap<term::Name, TypeScheme>,
    types: HashSet<term::Name>,
}

impl Env {
    pub fn add_const(&mut self, name: term::Name, t: TypeScheme) {
        self.consts.insert(name, t).map(|_| todo!());
    }

    pub fn get_const(&self, name: &term::Name) -> Option<&TypeScheme> {
        self.consts.get(name)
    }

    pub fn has_type(&self, name: &term::Name) -> bool {
        self.types.get(name).is_some()
    }
}
