use std::{ops::Deref, rc::Rc};

use eyre::{eyre, Result};
use ocaml_interop::{OCaml, OCamlRuntime, ToOCaml};
use tuples::TupleCollect;

use crate::{
    store::{Session, Token},
    DynFunction,
};

/// Dynamic call argument type.
pub enum Val<'a> {
    /// A token to a value stored in the global store.
    Token(&'a Token),
    /// A string.
    Str(&'a str),
}

impl<'a> From<&'a str> for Val<'a> {
    fn from(s: &'a str) -> Self {
        Val::Str(s)
    }
}

impl<'a> From<&'a String> for Val<'a> {
    fn from(s: &'a String) -> Self {
        Val::Str(s)
    }
}

impl<'a> From<&'a Token> for Val<'a> {
    fn from(key: &'a Token) -> Self {
        Val::Token(key)
    }
}

impl Session {
    /// Dynamic call function.
    pub(crate) unsafe fn caml_dyn_call(
        &self,
        cr: &mut OCamlRuntime,
        func: &DynFunction,
        args: &[Val],
    ) -> Result<Token> {
        let args = args
            .iter()
            .map(|arg| match arg {
                Val::Token(key) => self.get(key).ok_or_else(|| eyre!("Invalid key {}", key)),
                Val::Str(s) => Ok(Rc::new(s.to_boxroot(cr))),
            })
            .collect::<Result<Vec<_>>>()?;

        let result = if args.is_empty() {
            func.call(cr, OCaml::unit().as_ref())
        } else if args.len() == 1 {
            func.call(cr, &args[0])
        } else if args.len() == 2 {
            func.call2(cr, &args[0], &args[1])
        } else if args.len() == 3 {
            func.call3(cr, &args[0], &args[1], &args[2])
        } else {
            func.call_n(cr, args.iter().map(|arg| arg.as_ref().deref()))
        }?;
        let result = result.root();

        Ok(self.store(Rc::new(result)))
    }

    pub(crate) unsafe fn caml_destruct<const N: usize, T>(&self, value: OCaml<String>) -> T
    where
        T: tuples::TupleSame<Token> + tuples::TupleFromIter<Token>,
    {
        (0..N)
            .map(|i| {
                let value = unsafe { value.field(i) }.root();
                self.store(Rc::new(value))
            })
            .collect_tuple::<T>()
    }
}
