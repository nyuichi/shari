use std::sync::Arc;

use anyhow::bail;

use crate::kernel::tt::{Name, Term, TermConst, TermLocal, Type};
use crate::parse::{Lex, Parser};

#[doc(hidden)]
pub trait Arg<T> {
    fn as_arg(&self) -> &T;
}

impl Arg<Term> for &Term {
    fn as_arg(&self) -> &Term {
        self
    }
}

impl Arg<Term> for Term {
    fn as_arg(&self) -> &Term {
        self
    }
}

impl Arg<Type> for &Type {
    fn as_arg(&self) -> &Type {
        self
    }
}

impl Arg<Type> for Type {
    fn as_arg(&self) -> &Type {
        self
    }
}

#[doc(hidden)]
pub trait ToArg<T> {
    type ToArg<'a>: Arg<T>
    where
        Self: 'a;
    fn to_arg(&self) -> Self::ToArg<'_>;
}

impl ToArg<Term> for Term {
    type ToArg<'a> = &'a Term;
    fn to_arg(&self) -> Self::ToArg<'_> {
        self
    }
}

impl ToArg<Term> for TermLocal {
    type ToArg<'a> = Term;
    fn to_arg(&self) -> Self::ToArg<'_> {
        Term::Local(Arc::new(self.clone()))
    }
}

impl ToArg<Term> for TermConst {
    type ToArg<'a> = Term;
    fn to_arg(&self) -> Self::ToArg<'_> {
        Term::Const(Arc::new(self.clone()))
    }
}

impl ToArg<Type> for Type {
    type ToArg<'a> = &'a Type;
    fn to_arg(&self) -> Self::ToArg<'_> {
        self
    }
}

#[doc(hidden)]
pub trait Quote: Sized + 'static {
    type Arg;
    fn quote<'a>(
        template: &str,
        args: impl IntoIterator<Item = &'a dyn Arg<Self::Arg>>,
    ) -> anyhow::Result<Self>;
}

impl Quote for Term {
    type Arg = Term;
    fn quote<'a>(
        template: &str,
        args: impl IntoIterator<Item = &'a dyn Arg<Term>>,
    ) -> anyhow::Result<Term> {
        let mut lex = Lex::new(template);
        let env = Env::get();
        let mut parser = Parser::new(&mut lex, &env, true);
        let mut m = parser.term()?;
        parser.eof()?;
        let args: Vec<_> = args.into_iter().collect();
        if args.len() != parser.holes.len() {
            bail!("number of holes mismatch");
        }
        for ((name, ty), arg) in std::iter::zip(parser.holes, args) {
            m.close(name, &ty);
            m.open(arg.as_arg());
        }
        Ok(m)
    }
}

impl Quote for Type {
    type Arg = Type;
    fn quote<'a>(
        template: &str,
        args: impl IntoIterator<Item = &'a dyn Arg<Type>>,
    ) -> anyhow::Result<Type> {
        let mut lex = Lex::new(template);
        let env = Env::get();
        let mut parser = Parser::new(&mut lex, &env, true);
        let mut t = parser.ty()?;
        parser.eof()?;
        let args: Vec<_> = args.into_iter().map(|arg| arg.as_arg()).collect();
        if args.len() != parser.type_holes.len() {
            bail!(
                "number of holes mismatch: {} arguments for {} holes",
                args.len(),
                parser.type_holes.len()
            );
        }
        t.subst(&std::iter::zip(parser.type_holes, args).collect::<Vec<_>>());
        Ok(t)
    }
}

impl Quote for Name {
    type Arg = ();
    fn quote<'a>(
        template: &str,
        args: impl IntoIterator<Item = &'a dyn Arg<()>>,
    ) -> anyhow::Result<Name> {
        let args: Vec<_> = args.into_iter().collect();
        if !args.is_empty() {
            unimplemented!();
        }
        Ok(template.try_into()?)
    }
}

impl Quote for Fact {
    type Arg = Type;
    fn quote<'a>(
        template: &str,
        args: impl IntoIterator<Item = &'a dyn Arg<Type>>,
    ) -> anyhow::Result<Fact> {
        let (local_types, fact) =
            get_prop(Name::try_from(template)?).ok_or_else(|| anyhow::anyhow!("fact not found"))?;
        let args: Vec<_> = args.into_iter().map(|arg| arg.as_arg()).collect();
        instantiate(&std::iter::zip(local_types, args).collect::<Vec<_>>(), fact)
    }
}

#[doc(hidden)]
pub fn quote<'a, T: Quote>(
    template: &str,
    args: impl IntoIterator<Item = &'a dyn Arg<<T as Quote>::Arg>>,
) -> anyhow::Result<T> {
    Quote::quote(template, args)
}

#[macro_export]
macro_rules! q {
    (Fact $template:expr) => {
        $crate::quote::quote::<$crate::kernel::proof::Fact>($template, []).unwrap()
    };
    (Fact $template:expr, $($arg:expr),*) => {
        {
            use $crate::quote::ToArg;
            use $crate::quote::Arg;
            $crate::quote::quote::<$crate::kernel::proof::Fact>($template, [$(&$arg.to_arg() as &dyn Arg<_>),*]).unwrap()
        }
    };
    ($template:expr) => {
        $crate::quote::quote($template, []).unwrap()
    };
    ($template:expr, $($arg:expr),*) => {
        {
            use $crate::quote::ToArg;
            use $crate::quote::Arg;
            $crate::quote::quote($template, [$(&$arg.to_arg() as &dyn Arg<_>),*]).unwrap()
        }
    };
}
