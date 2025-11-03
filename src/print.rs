use crate::{
    cmd::{Fixity, Operator},
    proof::Axiom,
    tt::{Class, ClassType, Const, Ctor, Id, Kind, QualifiedName, Term, Type},
};

use anyhow::bail;
use std::{collections::HashMap, fmt::Display};

#[derive(Debug, Default, Clone)]
pub struct OpTable {
    op_table: HashMap<QualifiedName, Operator>,
}

impl OpTable {
    pub fn add(&mut self, op: Operator) -> anyhow::Result<()> {
        let entity = op.entity.clone();
        if self.op_table.insert(entity, op).is_some() {
            bail!("notation already defined");
        }
        Ok(())
    }

    fn get(&self, name: &QualifiedName) -> Option<&Operator> {
        self.op_table.get(name)
    }
}

fn uniquify_binder_name(binder_id: Id, body: &Term, local_names: &[String]) -> String {
    const DEFAULT_NAME: &str = "x";
    const SUBSCRIPT_DIGITS: [char; 10] = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'];

    // avoid empty names, default to "x". this choice is arbitrary.
    let name = binder_id
        .name()
        .map(|name| name.as_str().to_owned())
        .unwrap_or_else(|| DEFAULT_NAME.to_string());
    let mut x = name.clone();
    'refresh: for refresh_index in 0.. {
        if refresh_index > 0 {
            let mut n = refresh_index;
            let mut chars = Vec::new();
            while n > 0 {
                let d = (n % 10) as usize;
                chars.push(SUBSCRIPT_DIGITS[d]);
                n /= 10;
            }
            x = format!("{}{}", name, chars.iter().rev().collect::<String>());
        }
        // TODO: ensure also that x is not used as a global name
        for (i, local_name) in local_names.iter().rev().enumerate() {
            if local_name == &x && body.contains_var(i + 1) {
                continue 'refresh;
            }
        }
        break;
    }
    x
}

struct Printer<'a> {
    op_table: &'a OpTable,
    print_type_args: bool,
    print_binder_types: bool,
    local_type_names: &'a HashMap<Id, String>,
}

impl<'a> Printer<'a> {
    fn new(op_table: &'a OpTable, local_type_names: &'a HashMap<Id, String>) -> Self {
        Printer {
            op_table,
            print_type_args: false,
            print_binder_types: false,
            local_type_names,
        }
    }

    fn collect_lambda_binders(
        &self,
        mut term: Term,
        local_names: &mut Vec<String>,
    ) -> (Vec<(String, Type)>, Term) {
        let mut binders = Vec::new();
        while let Term::Abs(inner) = &term {
            let binder = uniquify_binder_name(inner.binder_id, &inner.body, local_names);
            binders.push((binder.clone(), inner.binder_type.clone()));
            local_names.push(binder);
            term = inner.body.clone();
        }
        (binders, term)
    }

    fn collect_ctor_binders(
        &self,
        mut term: Term,
        ctor_name: QualifiedName,
        local_names: &mut Vec<String>,
    ) -> (Vec<(String, Type)>, Term) {
        let mut binders = Vec::new();
        loop {
            while let Term::Abs(inner) = &term {
                let binder = uniquify_binder_name(inner.binder_id, &inner.body, local_names);
                binders.push((binder.clone(), inner.binder_type.clone()));
                local_names.push(binder);
                term = inner.body.clone();
            }
            if let Ok(mut ctor) = Ctor::try_from(term.clone())
                && ctor.head.name == ctor_name
                && ctor.args.len() == 1
            {
                term = ctor.args.pop().unwrap();
                continue;
            }
            break;
        }
        (binders, term)
    }

    fn fmt_binder_prefix(
        &self,
        f: &mut std::fmt::Formatter,
        symbol: &str,
        binders: &[(String, Type)],
    ) -> std::fmt::Result {
        debug_assert!(!binders.is_empty());
        if self.print_binder_types {
            write!(f, "{} ", symbol)?;
            for (idx, (name, ty)) in binders.iter().enumerate() {
                if idx > 0 {
                    write!(f, " ")?;
                }
                write!(f, "({} : ", name)?;
                self.fmt_type(f, ty)?;
                write!(f, ")")?;
            }
        } else {
            write!(f, "{}", symbol)?;
            for (name, _) in binders {
                write!(f, " {}", name)?;
            }
        }
        write!(f, ", ")
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
        local_names: &mut Vec<String>,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        if let Ok(Ctor { head, mut args }) = m.clone().try_into() {
            if let Some(op) = self.op_table.get(&head.name) {
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
            let name = head.name.clone();
            // TODO: don't use to_string. this is inefficient. Use LazyLock to cache QualifiedName instances of "forall", "exists", "uexists".
            match name.to_string().as_str() {
                "forall" => {
                    if args.len() == 1 {
                        let arg = args.pop().unwrap();
                        let arg_copy = arg.clone();
                        let snapshot = local_names.len();
                        let (binders, body) =
                            self.collect_ctor_binders(arg, name.clone(), local_names);
                        if binders.is_empty() {
                            local_names.truncate(snapshot);
                            args.push(arg_copy);
                        } else {
                            if !allow_lambda {
                                write!(f, "(")?;
                            }
                            self.fmt_binder_prefix(f, "∀", &binders)?;
                            let res = self.fmt_term_help(&body, 0, true, local_names, f);
                            local_names.truncate(snapshot);
                            res?;
                            if !allow_lambda {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                }
                "exists" => {
                    if args.len() == 1 {
                        let arg = args.pop().unwrap();
                        let arg_copy = arg.clone();
                        let snapshot = local_names.len();
                        let (binders, body) =
                            self.collect_ctor_binders(arg, name.clone(), local_names);
                        if binders.is_empty() {
                            local_names.truncate(snapshot);
                            args.push(arg_copy);
                        } else {
                            if !allow_lambda {
                                write!(f, "(")?;
                            }
                            self.fmt_binder_prefix(f, "∃", &binders)?;
                            let res = self.fmt_term_help(&body, 0, true, local_names, f);
                            local_names.truncate(snapshot);
                            res?;
                            if !allow_lambda {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                }
                "uexists" => {
                    if args.len() == 1 {
                        let arg = args.pop().unwrap();
                        let arg_copy = arg.clone();
                        let snapshot = local_names.len();
                        let (binders, body) =
                            self.collect_ctor_binders(arg, name.clone(), local_names);
                        if binders.is_empty() {
                            local_names.truncate(snapshot);
                            args.push(arg_copy);
                        } else {
                            if !allow_lambda {
                                write!(f, "(")?;
                            }
                            self.fmt_binder_prefix(f, "∃!", &binders)?;
                            let res = self.fmt_term_help(&body, 0, true, local_names, f);
                            local_names.truncate(snapshot);
                            res?;
                            if !allow_lambda {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                }
                _ => {}
            }
        };

        match m {
            Term::Var(inner) => {
                let i = inner.index;
                if i >= local_names.len() {
                    write!(f, "#Var({i})")
                } else {
                    match local_names.get(local_names.len() - i - 1) {
                        Some(name) => write!(f, "{name}"),
                        None => write!(f, "{i}"),
                    }
                }
            }
            Term::Local(inner) => {
                write!(f, "{}", inner.id)
            }
            Term::Hole(inner) => {
                write!(f, "?{}", inner.id)
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
            Term::Abs(_) => {
                let snapshot = local_names.len();
                let (binders, body) = self.collect_lambda_binders(m.clone(), local_names);
                debug_assert!(!binders.is_empty());
                if !allow_lambda {
                    write!(f, "(")?;
                }
                self.fmt_binder_prefix(f, "λ", &binders)?;
                let res = self.fmt_term_help(&body, 0, true, local_names, f);
                local_names.truncate(snapshot);
                res?;
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
            Type::Const(inner) => write!(f, "{}", inner.name),
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
            Type::Hole(inner) => write!(f, "{}", inner.id),
            Type::Local(inner) => {
                if let Some(name) = self.local_type_names.get(&inner.id) {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}", inner.id)
                }
            }
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
pub struct PrettyInner<'a, T> {
    op_table: &'a OpTable,
    local_type_names: &'a HashMap<Id, String>,
    data: T,
}

impl<'a, T> PrettyInner<'a, T> {
    pub fn new(op_table: &'a OpTable, local_type_names: &'a HashMap<Id, String>, data: T) -> Self {
        PrettyInner {
            op_table,
            local_type_names,
            data,
        }
    }
}

impl Display for PrettyInner<'_, &Type> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table, self.local_type_names).fmt_type(f, self.data)
    }
}

impl Display for PrettyInner<'_, Type> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table, self.local_type_names).fmt_type(f, &self.data)
    }
}

impl Display for PrettyInner<'_, &Term> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table, self.local_type_names).fmt_term(self.data, f)
    }
}

impl Display for PrettyInner<'_, Term> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table, self.local_type_names).fmt_term(&self.data, f)
    }
}

impl Display for PrettyInner<'_, &Class> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table, self.local_type_names).fmt_class(f, self.data)
    }
}

impl Display for PrettyInner<'_, Class> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Printer::new(self.op_table, self.local_type_names).fmt_class(f, &self.data)
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

fn generate_fresh_local_type(local_types: &Vec<String>) -> String {
    const DEFAULT_NAME: &str = "u";
    const SUBSCRIPT_DIGITS: [char; 10] = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'];

    let mut x = DEFAULT_NAME.to_string();
    'refresh: for refresh_index in 0.. {
        if refresh_index > 0 {
            let mut n = refresh_index;
            let mut chars = Vec::new();
            while n > 0 {
                let d = (n % 10) as usize;
                chars.push(SUBSCRIPT_DIGITS[d]);
                n /= 10;
            }
            x = format!("{DEFAULT_NAME}{}", chars.iter().rev().collect::<String>());
        }
        for local_type in local_types {
            if local_type.as_str() == x {
                continue 'refresh;
            }
        }
        break;
    }
    x
}

fn create_local_type_name(local_types: &Vec<Id>) -> HashMap<Id, String> {
    let mut local_type_names = HashMap::new();
    let mut local_type_list = Vec::new();
    for local_type in local_types {
        if local_type.is_generated() {
            let name = generate_fresh_local_type(&local_type_list);
            local_type_list.push(name.clone());
            local_type_names.insert(*local_type, name);
        } else {
            let name = local_type.name().unwrap().to_string();
            local_type_list.push(name.clone());
            local_type_names.insert(*local_type, name);
        }
    }
    local_type_names
}

impl Display for Pretty<'_, (&QualifiedName, &Const)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (
            name,
            Const {
                local_types,
                local_classes,
                ty,
            },
        ) = self.data;
        let local_type_names = create_local_type_name(local_types);
        write!(f, "const {}", name)?;
        if !local_types.is_empty() {
            write!(f, ".{{")?;
            let mut first = true;
            for local_type in local_types {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", local_type_names.get(&local_type).unwrap())?;
                first = false;
            }
            write!(f, "}}")?;
        }
        for local_class in local_classes {
            write!(
                f,
                " [{}]",
                PrettyInner::new(self.op_table, &local_type_names, local_class)
            )?;
        }
        write!(
            f,
            " : {}",
            PrettyInner::new(self.op_table, &local_type_names, ty)
        )?;
        Ok(())
    }
}

impl Display for Pretty<'_, (&QualifiedName, &Axiom)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (
            name,
            Axiom {
                local_types,
                local_classes,
                target,
            },
        ) = self.data;
        let local_type_names = create_local_type_name(local_types);
        write!(f, "axiom {}", name)?;
        if !local_types.is_empty() {
            write!(f, ".{{")?;
            let mut first = true;
            for local_type in local_types {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{}", local_type_names.get(&local_type).unwrap())?;
                first = false;
            }
            write!(f, "}}")?;
        }
        for local_class in local_classes {
            write!(
                f,
                " [{}]",
                PrettyInner::new(self.op_table, &local_type_names, local_class)
            )?;
        }
        write!(
            f,
            " : {}",
            PrettyInner::new(self.op_table, &local_type_names, target)
        )?;
        Ok(())
    }
}

impl Display for Pretty<'_, (&QualifiedName, &Kind)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (name, kind) = self.data;
        write!(f, "type const {} : {}", name, kind)
    }
}

impl Display for Pretty<'_, (&QualifiedName, &ClassType)> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (name, &ClassType { arity }) = self.data;
        write!(f, "class {}", name)?;
        for _ in 0..arity {
            write!(f, " _")?;
        }
        Ok(())
    }
}
