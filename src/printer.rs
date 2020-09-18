use crate::parser;
use crate::term;

impl std::fmt::Display for term::Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            term::Name::Named(name) => write!(f, "{}", name),
            term::Name::Anon(k) => write!(f, "#{}", k),
        }
    }
}

impl std::fmt::Display for term::MvarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id())
    }
}

impl std::fmt::Display for term::Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        fn go(t: &term::Type, prec: usize, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match t {
                term::Type::Fvar(name) => write!(f, "{}", name),
                term::Type::Arrow(p) => {
                    let (t1, t2) = &**p;
                    if prec > 0 {
                        write!(f, "(")?;
                    }
                    go(t1, 1, f)?;
                    write!(f, " → ")?;
                    go(t2, 0, f)?;
                    if prec > 0 {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
            }
        }
        go(self, 0, f)
    }
}

struct Operator {
    fixity: parser::Fixity,
    prec: usize,
    symbol: &'static str,
}

fn find_user_notation(name: &term::Name) -> Option<Operator> {
    match name {
        term::Name::Named(name) => match name.as_str() {
            "imp" => Some(Operator {
                fixity: parser::Fixity::Infixr,
                prec: 50,
                symbol: "→",
            }),
            _ => None,
        },
        term::Name::Anon(_) => None,
    }
}

impl term::Term {
    fn fmt_help(
        &mut self,
        prec: usize,
        mut allow_lambda: bool,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        let mut args = self.uncurry();
        if let term::Term::Const(_, p) = self {
            let (name, _) = &mut **p;
            if let Some(op) = find_user_notation(name) {
                match op.fixity {
                    parser::Fixity::Infixl => {
                        if args.len() == 2 {
                            if prec >= op.prec {
                                write!(f, "(")?;
                                allow_lambda = true;
                            }
                            let mut m2 = args.pop().unwrap();
                            let mut m1 = args.pop().unwrap();
                            m1.fmt_help(op.prec - 1, false, f)?;
                            write!(f, " {} ", op.symbol)?;
                            m2.fmt_help(op.prec, allow_lambda, f)?;
                            if prec >= op.prec {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                    parser::Fixity::Infixr => {
                        if args.len() == 2 {
                            if prec >= op.prec {
                                write!(f, "(")?;
                                allow_lambda = true;
                            }
                            let mut m2 = args.pop().unwrap();
                            let mut m1 = args.pop().unwrap();
                            m1.fmt_help(op.prec, false, f)?;
                            write!(f, " {} ", op.symbol)?;
                            m2.fmt_help(op.prec - 1, allow_lambda, f)?;
                            if prec >= op.prec {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                    parser::Fixity::Nofix => {
                        if args.len() == 0 {
                            write!(f, "{}", op.symbol)?;
                            return Ok(());
                        }
                    }
                    parser::Fixity::Prefix => {
                        if args.len() == 1 {
                            if prec > op.prec {
                                write!(f, "(")?;
                                allow_lambda = true;
                            }
                            write!(f, "{}", op.symbol)?;
                            let mut m = args.pop().unwrap();
                            m.fmt_help(op.prec, allow_lambda, f)?;
                            if prec > op.prec {
                                write!(f, ")")?;
                            }
                            return Ok(());
                        }
                    }
                }
            }
            if let term::Name::Named(name) = name {
                match name.as_str() {
                    "forall" => {
                        if args.len() == 1 {
                            let mut arg = args.pop().unwrap();
                            if let term::Term::Abs(_, p) = &mut arg {
                                let term::Context(t, m) = &mut **p;
                                if !allow_lambda {
                                    write!(f, "(")?;
                                }
                                let x = term::Name::fresh();
                                write!(f, "∀ ({} : {}), ", x, t)?;
                                m.open(&x);
                                m.fmt_help(0, true, f)?;
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
            }
        }
        self.curry(args);
        match self {
            term::Term::Bvar(_, i) => write!(f, "{}", i),
            term::Term::Fvar(_, name) => write!(f, "{}", name),
            term::Term::Const(_, p) => {
                let (name, _) = &mut **p;
                write!(f, "{}", name)
            }
            term::Term::Mvar(_, name) => write!(f, "?{}", name),
            term::Term::Abs(_, p) => {
                let term::Context(t, m) = &mut **p;
                if !allow_lambda {
                    write!(f, "(")?;
                }
                let x = term::Name::fresh();
                write!(f, "λ ({} : {}), ", x, t)?;
                m.open(&x);
                m.fmt_help(0, true, f)?;
                if !allow_lambda {
                    write!(f, ")")?;
                }
                Ok(())
            }
            term::Term::App(_, p) => {
                let (m1, m2) = &mut **p;
                if prec >= 1024 {
                    write!(f, "(")?;
                    allow_lambda = true;
                }
                m1.fmt_help(1023, false, f)?;
                write!(f, " ")?;
                m2.fmt_help(1024, allow_lambda, f)?;
                if prec >= 1024 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for term::Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.clone().fmt_help(0, true, f)
    }
}
