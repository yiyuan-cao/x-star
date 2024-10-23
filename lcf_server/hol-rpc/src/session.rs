use std::{
    cell::{Ref, RefCell, RefMut},
    rc::Rc,
};

use crate::caml_dyn_call::Token;
use hol_rpc::{TermKey, TheoremKey, TypeKey};

#[derive(Clone, Default)]
pub struct Session(Rc<SessionInner>);

#[derive(Default)]
struct SessionInner {
    session: crate::caml_dyn_call::Session,
    terms: RefCell<slotmap::SlotMap<TermKey, Token>>,
    theorems: RefCell<slotmap::SlotMap<TheoremKey, Token>>,
    types: RefCell<slotmap::SlotMap<TypeKey, Token>>,
}

impl Session {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) unsafe fn dyn_call<'a>(
        &self,
        func: &crate::caml_dyn_call::DynFunction,
        args: impl AsRef<[crate::caml_dyn_call::Val<'a>]>,
    ) -> eyre::Result<Token> {
        self.0.session.dyn_call(func, args)
    }

    pub(crate) unsafe fn destruct<const N: usize, T>(&self, token: &Token) -> eyre::Result<T>
    where
        T: tuples::TupleSame<Token> + tuples::TupleFromIter<Token>,
    {
        self.0.session.destruct::<N, T>(token)
    }

    pub(crate) fn terms(&self) -> Ref<slotmap::SlotMap<TermKey, Token>> {
        self.0.terms.borrow()
    }

    pub(crate) fn terms_mut(&mut self) -> RefMut<slotmap::SlotMap<TermKey, Token>> {
        self.0.terms.borrow_mut()
    }

    pub(crate) fn theorems(&self) -> Ref<slotmap::SlotMap<TheoremKey, Token>> {
        self.0.theorems.borrow()
    }

    pub(crate) fn theorems_mut(&mut self) -> RefMut<slotmap::SlotMap<TheoremKey, Token>> {
        self.0.theorems.borrow_mut()
    }

    pub(crate) fn types(&self) -> Ref<slotmap::SlotMap<TypeKey, Token>> {
        self.0.types.borrow()
    }

    pub(crate) fn types_mut(&mut self) -> RefMut<slotmap::SlotMap<TypeKey, Token>> {
        self.0.types.borrow_mut()
    }
}

/// Dynamically load a function from the toplevel by name.
///
/// # Example
///
/// ```rust,no_run
/// // Load the `ASSUME` function from the toplevel,
/// // and bind it to the `assume` variable.
/// load_dyn_function!(ASSUME as assume);
///
/// // shorthand when the name and alias are the same
/// load_dyn_function!(string_of_thm);
/// ```
macro_rules! load_dyn_function {
    ($name: ident) => {
        load_dyn_function!($name as $name);
    };
    ($name: ident as $alias: ident) => {
        ::stack_tokens::stack_token!(local);
        let $alias = {
            use $crate::caml_dyn_call::DynFunction;
            use ::stack_tokens::LocalKeyExt;
            use ::std::cell::OnceCell;
            thread_local! {
                static FUNCTION: OnceCell<DynFunction> = const { OnceCell::new() };
            }
            FUNCTION.borrow(local).get_or_init(|| {
                DynFunction::from_toplevel(stringify!($name))
                    .map_err(|e| {
                        eprintln!("error loading function {}: {}", stringify!($name), e);
                        ::std::process::exit(1);
                    })
                    .unwrap()
            })
        };
    };
}
