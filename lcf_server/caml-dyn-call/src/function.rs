//! Dynamic function, from `ocaml_interop::internal::OCamlClosure`.

use eyre::{eyre, Result};
use ocaml_interop::{internal::tag, ocaml, OCaml, OCamlRef, OCamlRuntime, RawOCaml, ToOCaml};
use ocaml_sys::{
    caml_callback2_exn, caml_callback3_exn, caml_callbackN_exn, caml_callback_exn,
    caml_named_value, tag_val,
};

type OCamlResult<'a, T> = Result<OCaml<'a, T>>;

ocaml! {
    fn expose_toplevel(name: String);
}

/// Dynamic call function.
#[derive(Copy, Clone)]
pub struct DynFunction(*const RawOCaml);

unsafe impl Sync for DynFunction {}

impl DynFunction {
    fn named(name: &str) -> Option<Self> {
        let named = unsafe {
            let s = match std::ffi::CString::new(name) {
                Ok(s) => s,
                Err(_) => return None,
            };
            caml_named_value(s.as_ptr())
        };
        if named.is_null() || unsafe { tag_val(*named) } != tag::CLOSURE {
            None
        } else {
            Some(Self(named))
        }
    }

    /// Lookup a function by name.
    pub fn lookup(name: &str) -> Result<Self> {
        Self::named(name).ok_or_else(|| eyre!("Function {} not found", name))
    }

    pub(crate) fn caml_from_toplevel(cr: &mut OCamlRuntime, name: &str) -> Result<Self> {
        match Self::named(name) {
            Some(func) => Ok(func),
            None => {
                let name_ocaml = name.to_boxroot(cr);
                expose_toplevel(cr, &name_ocaml);
                Self::lookup(name)
            }
        }
    }

    pub(crate) fn call<'a, T, R>(
        &self,
        cr: &'a mut OCamlRuntime,
        arg: OCamlRef<T>,
    ) -> OCamlResult<'a, R> {
        let result = unsafe { caml_callback_exn(*self.0, arg.get_raw()) };
        self.handle_call_result(cr, result)
    }

    pub(crate) fn call2<'a, T, U, R>(
        &self,
        cr: &'a mut OCamlRuntime,
        arg1: OCamlRef<T>,
        arg2: OCamlRef<U>,
    ) -> OCamlResult<'a, R> {
        let result = unsafe { caml_callback2_exn(*self.0, arg1.get_raw(), arg2.get_raw()) };
        self.handle_call_result(cr, result)
    }

    pub(crate) fn call3<'a, T, U, V, R>(
        &self,
        cr: &'a mut OCamlRuntime,
        arg1: OCamlRef<T>,
        arg2: OCamlRef<U>,
        arg3: OCamlRef<V>,
    ) -> OCamlResult<'a, R> {
        let result =
            unsafe { caml_callback3_exn(*self.0, arg1.get_raw(), arg2.get_raw(), arg3.get_raw()) };
        self.handle_call_result(cr, result)
    }

    pub(crate) fn call_n<'a, 'b, T: 'b, R>(
        &self,
        cr: &'a mut OCamlRuntime,
        args: impl IntoIterator<Item = OCamlRef<'b, T>>,
    ) -> OCamlResult<'a, R> {
        let mut args = args
            .into_iter()
            .map(|arg| unsafe { arg.get_raw() })
            .collect::<Vec<_>>();
        let len = args.len();
        let result = unsafe { caml_callbackN_exn(*self.0, len, args.as_mut_ptr()) };
        self.handle_call_result(cr, result)
    }

    #[inline]
    fn handle_call_result<'a, R>(
        &self,
        cr: &'a mut OCamlRuntime,
        result: RawOCaml,
    ) -> OCamlResult<'a, R> {
        match unsafe { OCaml::of_exception_result(cr, result) } {
            Some(ex) => match ex.message() {
                Some(message) => Err(eyre!("OCaml exception: {}", message)),
                None => Err(eyre!("OCaml exception")),
            },
            None => unsafe { Ok(OCaml::new(cr, result)) },
        }
    }
}
