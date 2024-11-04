//! Dynamically call OCaml functions by name.
//!
//! # Overview
//!
//! The `Callback.register` feature in OCaml enables the registration of OCaml
//! functions to be discovered by name in native code. This crate offers a
//! mechanism to invoke these functions by name from Rust. To manage arbitrary
//! OCaml values, the crate treats all OCaml values as opaque, with the
//! exception of strings. It is recommended to create a lightweight wrapper
//! around the OCaml functions you intend to call, ensuring that data
//! transferred between Rust and OCaml can be represented in string format.
//!
//! This crate is specifically designed to function with the OCaml toplevel.
//! Consequently, the function registration should be executed in an OCaml
//! toplevel script (which is notably marked by the `;;` delimiter), rather than
//! a compiled OCaml library. This script is stored in a file and supplied to
//! the [`init`] function.
//!
//! Note that nearly all functions in this crate are signatured as `unsafe`
//! due to the inability to guarantee type safety when dynamically calling OCaml
//! functions. However, this doesn't imply that you are responsible for manual
//! memory management. The crate automatically handles memory management.
//!
//! # Example
//!
//! simple.ml:
//!
//! ```ocaml
//! let add (x: int) (y: int) = x + y in
//! Callback.register "add" add;;
//!
//! let sub (x: int) (y: int) = x - y in
//! Callback.register "sub" sub;;
//!
//! let parse_int (s: string) = int_of_string s in
//! Callback.register "parse_int" parse_int;;
//!
//! let print_int (i: int) = string_of_int i in
//! Callback.register "print_int" print_int;;
//! ```
//!
//! main.rs:
//!
//! ```rust,no_run
//! use std::path::Path;
//! use crate::caml_dyn_call::*;
//! use eyre::Result;
//!
//! fn main() -> Result<()> {
//!     init(Some(&Path::new(file!()).with_file_name("simple.ml")))?;
//!     
//!     let s = Session::new();
//!     
//!     let add = DynFunction::lookup("add")?;
//!     let parse_int = DynFunction::from_toplevel("parse_int")?;
//!     let print_int = DynFunction::from_toplevel("print_int")?;
//!     
//!     let (a, b, c, d) = unsafe {
//!         let a = s.dyn_call(&parse_int, args!("123"))?;
//!         let b = s.dyn_call(&parse_int, args!("456"))?;
//!         let c = s.dyn_call(&add, args!(&a, &b))?;
//!         let d = s.dyn_call(&print_int, args!(&c))?.get_str()?;
//!         (a, b, c, d)
//!     };
//!     
//!     println!("a: {}", a);
//!     println!("b: {}", b);
//!     println!("c: {}", c);
//!     println!("d: {}", d);
//!     
//!     Ok(())
//! }
//! ```
use std::{cell::RefCell, rc::Rc};

use eyre::{eyre, Result};
use ocaml_interop::{ocaml, BoxRoot, OCamlRuntime, ToOCaml};

mod call;
mod function;
mod store;

pub use call::Val;
pub use function::DynFunction;
pub use store::{Session, Token};

thread_local! {
    static OCAML_RUNTIME: RefCell<OCamlRuntime> = RefCell::new(OCamlRuntime::init());
}

impl Session {
    /// Call an OCaml function by name.
    ///
    /// # Safety
    /// All arguments must be of the correct type for the OCaml function.
    pub unsafe fn dyn_call<'a>(
        &self,
        func: &DynFunction,
        args: impl AsRef<[Val<'a>]>,
    ) -> Result<Token> {
        OCAML_RUNTIME.with_borrow_mut(|cr| {
            let key = self.caml_dyn_call(cr, func, args.as_ref())?;
            Ok(key)
        })
    }

    /// Get the value of the token as a string.
    ///
    /// # Safety
    /// The value behind the token must be an OCaml string.
    pub unsafe fn get_str(&self, token: &Token) -> Result<String> {
        OCAML_RUNTIME.with_borrow_mut(|cr| {
            let value = self
                .get(token)
                .ok_or_else(|| eyre!("Invalid token {}", token))?;
            Ok(value.to_rust(cr))
        })
    }

    /// Destruct a tuple into its components.
    ///
    /// # Safety
    /// The value behind the token must be an OCaml tuple with no less than `N` components.
    pub unsafe fn destruct<const N: usize, T>(&self, token: &Token) -> Result<T>
    where
        T: tuples::TupleSame<Token> + tuples::TupleFromIter<Token>,
    {
        OCAML_RUNTIME.with_borrow_mut(|cr| {
            let value = self
                .get(token)
                .ok_or_else(|| eyre!("Invalid token {}", token))?;
            let value = value.to_ocaml(cr);
            Ok(self.caml_destruct::<N, T>(value))
        })
    }
}

impl DynFunction {
    /// Fetch a function from the OCaml toplevel by name.
    pub fn from_toplevel(name: &str) -> Result<Self> {
        OCAML_RUNTIME.with_borrow_mut(|cr| Self::caml_from_toplevel(cr, name))
    }
}

impl Token {
    /// Get the value of the token as a string.
    ///
    /// # Safety
    /// The value behind the token must be an OCaml string.
    pub unsafe fn get_str(&self) -> Result<String> {
        OCAML_RUNTIME.with_borrow_mut(|cr| {
            let value = self.get().ok_or_else(|| eyre!("Invalid token {}", self))?;
            Ok(value.to_rust(cr))
        })
    }

    /// Get the value of the token as a boolean.
    ///
    /// # Safety
    /// The value behind the token must be an OCaml boolean.
    pub unsafe fn get_bool(&self) -> Result<bool> {
        OCAML_RUNTIME.with_borrow_mut(|cr| {
            let value = self.get().ok_or_else(|| eyre!("Invalid token {}", self))?;
            let value =
                unsafe { std::mem::transmute::<Rc<BoxRoot<String>>, Rc<BoxRoot<bool>>>(value) };
            Ok(value.to_rust(cr))
        })
    }
}

/// Initialize the OCaml runtime and run an initialization script.
pub fn init(preludes: &[String]) -> Result<()> {
    OCAML_RUNTIME.with_borrow_mut(|cr| {
        for prelude in preludes {
            let command = prelude.to_boxroot(cr);
            eval(cr, &command);
        }
        Ok(())
    })
}

ocaml! {
    fn eval(command: String);
}

/// Helper macro to create a list of `Val` arguments.
///
/// # Example
///
/// ```
/// let s = Session::new();
/// let c = s.dyn_call("add", args!(&a, &b))?;
/// ```
#[macro_export]
macro_rules! args {
    ($($x:expr),*) => {
        [$($x.into()),*]
    };
}
