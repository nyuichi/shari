use crate::{
    cmd::{Fixity, Operator},
    proof::Axiom,
    tt::{Class, ClassType, Const, Ctor, Kind, Name, Term, Type},
};

use anyhow::bail;
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Default, Clone)]
pub struct OpTable {
    op_table: HashMap<Name, Operator>,
}

impl OpTable {
    pub fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        let entity = op.entity;
        if self.op_table.insert(entity, op).is_some() {
            bail!("notation already defined");
        }
        Ok(())
    }

    fn get(&self, name: Name) -> Option<&Operator> {
        self.op_table.get(&name)
    }
}

struct Printer<'a> {
    op_table: &'a OpTable,
    print_type_args: bool,
    print_binder_types: bool,
}

impl<'a> Printer<'a> {
    fn new(op_table: &'a OpTable) -> Self {
        Printer {
            op_table,
            print_type_args: false,
            print_binder_types: false,
        }
    }

    fn fmt_term(&self, m: &Term, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut local_names = vec![];
        let res = self.fmt_term_help(m, 0, true, &mut local_names, f);
        assert!(local_names.is_empty());
        res
    }

    fn fmt_term_help(
        &self,
        m: &Term,
        prec: usize,
        mut allow_lambda: bool,
        local_names: &mut Vec<Name>,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        if let Ok(Ctor { head, mut args }) = m.clone().try_into() {
            let name = head.name;
            if let Some(op) = self.op_table.get(name) {
                match op.fixity {
                    Fixity::Infix | Fixity::Infixl => {
                        if args.len() == 2 {
                            if prec >= op.prec {
                                write!(f, "(")?;
                                allow_lambda = true;
                            }
                            let m2 = args.pop().unwrap();
                            let m1 = args.pop().unwrap();
                            self.fmt_term_help(&m1, op.prec - 1, false, local_names, f)?;
                            write!(f, " {} ", op.symbol)?;
                            self.fmt_term_help(&m2, op.prec, allow_lambda, local_names, f)?;
                            if prec >= op.prec {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                    Fixity::Infixr => {
                        if args.len() == 2 {
                            if prec >= op.prec {
                                write!(f, "(")?;
                                allow_lambda = true;
                            }
                            let m2 = args.pop().unwrap();
                            let m1 = args.pop().unwrap();
                            self.fmt_term_help(&m1, op.prec, false, local_names, f)?;
                            write!(f, " {} ", op.symbol)?;
                            self.fmt_term_help(&m2, op.prec - 1, allow_lambda, local_names, f)?;
                            if prec >= op.prec {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                    Fixity::Nofix => {
                        if args.is_empty() {
                            write!(f, "{}", op.symbol)?;
                            return Ok(());
                        }
                    }
                    Fixity::Prefix => {
                        if args.len() == 1 {
                            if prec > op.prec {
                                write!(f, "(")?;
                                allow_lambda = true;
                            }
                            write!(f, "{}", op.symbol)?;
                            let m = args.pop().unwrap();
                            self.fmt_term_help(&m, op.prec, allow_lambda, local_names, f)?;
                            if prec > op.prec {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                }
            }
            match name.to_string().as_str() {
                "forall" => {
                    if args.len() == 1 {
                        let mut arg = args.pop().unwrap();
                        if let Term::Abs(inner) = &mut arg {
                            if !allow_lambda {
                                write!(f, "(")?;
                            }
                            let mut x = inner.binder_name;
                            'refresh: for refresh_index in 0.. {
                                if refresh_index > 0 {
                                    x = Name::try_from(
                                        format!("{}{refresh_index}", inner.binder_name).as_str(),
                                    )
                                    .unwrap();
                                }
                                for (i, local_name) in local_names.iter().rev().enumerate() {
                                    if local_name == &x && inner.body.contains_var(i + 1) {
                                        continue 'refresh;
                                    }
                                }
                                break;
                            }
                            if self.print_binder_types {
                                write!(f, "∀ ({} : ", x)?;
                                self.fmt_type(f, &inner.binder_type)?;
                                write!(f, "), ")?;
                            } else {
                                write!(f, "∀ {}, ", x)?;
                            }
                            local_names.push(x);
                            self.fmt_term_help(&inner.body, 0, true, local_names, f)?;
                            local_names.pop();
                            if !allow_lambda {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                        args.push(arg);
                    }
                }
                "exists" => {
                    if args.len() == 1 {
                        let mut arg = args.pop().unwrap();
                        if let Term::Abs(inner) = &mut arg {
                            if !allow_lambda {
                                write!(f, "(")?;
                            }
                            let mut x = inner.binder_name;
                            'refresh: for refresh_index in 0.. {
                                if refresh_index > 0 {
                                    x = Name::try_from(
                                        format!("{}{refresh_index}", inner.binder_name).as_str(),
                                    )
                                    .unwrap();
                                }
                                for (i, local_name) in local_names.iter().rev().enumerate() {
                                    if local_name == &x && inner.body.contains_var(i + 1) {
                                        continue 'refresh;
                                    }
                                }
                                break;
                            }
                            if self.print_binder_types {
                                write!(f, "∃ ({} : ", x)?;
                                self.fmt_type(f, &inner.binder_type)?;
                                write!(f, "), ")?;
                            } else {
                                write!(f, "∃ {}, ", x)?;
                            }
                            local_names.push(x);
                            self.fmt_term_help(&inner.body, 0, true, local_names, f)?;
                            local_names.pop();
                            if !allow_lambda {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                        args.push(arg);
                    }
                }
                "uexists" => {
                    if args.len() == 1 {
                        let mut arg = args.pop().unwrap();
                        if let Term::Abs(inner) = &mut arg {
                            if !allow_lambda {
                                write!(f, "(")?;
                            }
                            let mut x = inner.binder_name;
                            'refresh: for refresh_index in 0.. {
                                if refresh_index > 0 {
                                    x = Name::try_from(
                                        format!("{}{refresh_index}", inner.binder_name).as_str(),
                                    )
                                    .unwrap();
                                }
                                for (i, local_name) in local_names.iter().rev().enumerate() {
                                    if local_name == &x && inner.body.contains_var(i + 1) {
                                        continue 'refresh;
                                    }
                                }
                                break;
                            }
                            if self.print_binder_types {
                                write!(f, "∃! ({} : ", x)?;
                                self.fmt_type(f, &inner.binder_type)?;
                                write!(f, "), ")?;
                            } else {
                                write!(f, "∃! {}, ", x)?;
                            }

                            local_names.push(x);
                            self.fmt_term_help(&inner.body, 0, true, local_names, f)?;
                            local_names.pop();
                            if !allow_lambda {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                        args.push(arg);
                    }
                }
                _ => {}
            }
        };

        match m {
            &Term::Var(i) => {
                if i >= local_names.len() {
                    write!(f, "#Var({i})")
                } else {
                    match local_names.get(local_names.len() - i - 1) {
                        Some(name) => write!(f, "{name}"),
                        None => write!(f, "{i}"),
                    }
                }
            }
            Term::Local(name) => {
                write!(f, "{name}")
            }
            Term::Hole(name) => {
                write!(f, "?{name}")
            }
            Term::Const(inner) => {
                write!(f, "{}", inner.name)?;
                if self.print_type_args && !inner.ty_args.is_empty() {
                    write!(f, ".{{",)?;
                    let mut first = true;
                    for ty_arg in &inner.ty_args {
                        if !first {
                            write!(f, ", ")?;
                        }
                        first = false;
                        self.fmt_type(f, ty_arg)?;
                    }
                    write!(f, "}}",)?;
                }
                Ok(())
            }
            Term::Abs(inner) => {
                if !allow_lambda {
                    write!(f, "(")?;
                }
                let mut x = inner.binder_name;
                'refresh: for refresh_index in 0.. {
                    if refresh_index > 0 {
                        x = Name::try_from(
                            format!("{}{refresh_index}", inner.binder_name).as_str(),
                        )
                        .unwrap();
                    }
                    for (i, local_name) in local_names.iter().rev().enumerate() {
                        if local_name == &x && inner.body.contains_var(i + 1) {
                            continue 'refresh;
                        }
                    }
                    break;
                }
                if self.print_binder_types {
                    write!(f, "λ ({} : ", x)?;
                    self.fmt_type(f, &inner.binder_type)?;
                    write!(f, "), ")?;
                } else {
                    write!(f, "λ {}, ", x)?;
                }
                local_names.push(x);
                self.fmt_term_help(&inner.body, 0, true, local_names, f)?;
                local_names.pop();
                if !allow_lambda {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Term::App(inner) => {
                if prec >= 1024 {
                    write!(f, "(")?;
                    allow_lambda = true;
                }
                self.fmt_term_help(&inner.fun, 1023, false, local_names, f)?;
                write!(f, " ")?;
                self.fmt_term_help(&inner.arg, 1024, allow_lambda, local_names, f)?;
                if prec >= 1024 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }

    fn fmt_type(&self, f: &mut std::fmt::Formatter, t: &Type) -> std::fmt::Result {
        self.fmt_type_help(f, t, 0)
    }

    #[allow(clippy::only_used_in_recursion)]
    fn fmt_type_help(
        &self,
        f: &mut std::fmt::Formatter,
        t: &Type,
        prec: usize,
    ) -> std::fmt::Result {
        match t {
            Type::Const(name) => write!(f, "{name}"),
            Type::Arrow(inner) => {
                if prec >= 25 {
                    write!(f, "(")?;
                }
                self.fmt_type_help(f, &inner.dom, 25)?;
                write!(f, " → ")?;
                self.fmt_type_help(f, &inner.cod, 24)?;
                if prec >= 25 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::App(inner) => {
                if prec >= 1024 {
                    write!(f, "(")?;
                }
                self.fmt_type_help(f, &inner.fun, 1023)?;
                write!(f, " ")?;
                self.fmt_type_help(f, &inner.arg, 1024)?;
                if prec >= 1024 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::Hole(name) => write!(f, "{name}"),
            Type::Local(name) => write!(f, "{name}"),
        }
    }

    fn fmt_class(&self, f: &mut std::fmt::Formatter, c: &Class) -> std::fmt::Result {
        write!(f, "{}", c.name)?;
        if !c.args.is_empty() {
            for arg in &c.args {
                write!(f, " ")?;
                self.fmt_type_help(f, arg, 1023)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Pretty<'a, T> {
    op_table: &'a OpTable,
    data: T,
}

impl<'a, T> Pretty<'a, T> {
    pub fn new(op_table: &'a OpTable, data: T) -> Self {
        Pretty { op_table, data }
    }
}

impl Display for Pretty<'_, &Type> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table).fmt_type(f, self.data)
    }
}

impl Display for Pretty<'_, Type> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table).fmt_type(f, &self.data)
    }
}

impl Display for Pretty<'_, &Term> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table).fmt_term(self.data, f)
    }
}

impl Display for Pretty<'_, Term> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table).fmt_term(&self.data, f)
    }
}

impl Display for Pretty<'_, &Class> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table).fmt_class(f, self.data)
    }
}

impl Display for Pretty<'_, Class> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table).fmt_class(f, &self.data)
    }
}

impl Display for Pretty<'_, (&Name, &Const)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (
            name,
            Const {
                local_types,
                local_classes,
                ty,
            },
        ) = self.data;
        write!(f, "const {}", name)?;
        if !local_types.is_empty() {
            write!(f, ".{{")?;
            let mut first = true;
            for local_type in local_types {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", local_type)?;
                first = false;
            }
            write!(f, "}}")?;
        }
        for local_class in local_classes {
            write!(f, " [{}]", Pretty::new(self.op_table, local_class))?;
        }
        write!(f, " : {}", Pretty::new(self.op_table, ty))?;
        Ok(())
    }
}

impl Display for Pretty<'_, (&Name, &Axiom)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (
            name,
            Axiom {
                local_types,
                local_classes,
                target,
            },
        ) = self.data;
        write!(f, "axiom {}", name)?;
        if !local_types.is_empty() {
            write!(f, ".{{")?;
            let mut first = true;
            for local_type in local_types {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", local_type)?;
                first = false;
            }
            write!(f, "}}")?;
        }
        for local_class in local_classes {
            write!(f, " [{}]", Pretty::new(self.op_table, local_class))?;
        }
        write!(f, " : {}", Pretty::new(self.op_table, target))?;
        Ok(())
    }
}

impl Display for Pretty<'_, (&Name, &Kind)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (name, kind) = self.data;
        write!(f, "type const {} : {}", name, kind)
    }
}

impl Display for Pretty<'_, (&Name, &ClassType)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (name, &ClassType { arity }) = self.data;
        write!(f, "class {}", name)?;
        for _ in 0..arity {
            write!(f, " _")?;
        }
        Ok(())
    }
}
