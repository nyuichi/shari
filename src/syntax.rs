use crate::term;
use once_cell::sync::Lazy;
use std::collections::{HashMap, HashSet, VecDeque};
use std::mem;

/// surface language

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Name {
    Named(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Var(Name),
    Arrow(Box<Type>, Box<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(Name),
    Abs(Name, Option<Type>, Box<Term>),
    App(Box<Term>, Box<Term>),
}
