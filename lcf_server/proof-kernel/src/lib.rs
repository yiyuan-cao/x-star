//! The proof kernel library.
#![deny(missing_docs)]
#![allow(clippy::missing_safety_doc)]

use std::{
    ffi::{c_char, c_int, CStr, CString},
    sync::OnceLock,
};

use envconfig::Envconfig;
use hol_rpc::client::{Client, Term, Theorem, Type};

use crate::{
    error::clear_last_error,
    gc::{Gc, IntoGc, ToGc},
};

#[macro_use]
pub mod error;
mod gc;
mod types;

pub use types::{IndDef, IndType};

#[inline]
fn client() -> &'static OnceLock<Client> {
    static CLIENT: OnceLock<Client> = OnceLock::new();
    &CLIENT
}

#[inline]
fn get_client() -> Result<&'static Client, &'static str> {
    client()
        .get()
        .ok_or("proof kernel not initialized; call `cst_init` first")
}

/// Configuration.
#[derive(Envconfig)]
pub struct Config {
    /// The address of the HOL-RPC server.
    #[envconfig(from = "LCF_SERVER_ADDRESS", default = "127.0.0.1")]
    pub addr: String,

    /// The port of the HOL-RPC server.
    #[envconfig(from = "LCF_SERVER_PORT", default = "5000")]
    pub port: u16,
}

/// Initialize the proof kernel.
///
/// # Returns
/// `0` on success, `-1` on failure.
#[no_mangle]
pub unsafe extern "C" fn cst_init() -> c_int {
    clear_last_error();
    let config = Config::init_from_env().expect("Failed to load configuration");
    let addr = format!("{}:{}", config.addr, config.port);

    if client().get().is_none() {
        let init = ensures_ok!(Client::new(addr), -1);
        client().set(init).unwrap();
    }
    0
}

/// Parse a term from a string.
///
/// # Parameters
/// - `s`: The string to parse.
///
/// # Returns
/// A pointer to the parsed term on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn parse_term(s: *const c_char) -> *const Gc<Term> {
    clear_last_error();
    ensures!(!s.is_null(), "`s` is null", std::ptr::null());

    let string = unsafe { CStr::from_ptr(s) }.to_str();
    let string = ensures_ok!(string, std::ptr::null()).to_string();

    let client = ensures_ok!(get_client(), std::ptr::null());
    let term = ensures_ok!(client.parse_term_from_string(string), std::ptr::null());
    term.into_gc()
}

/// Parse a type from a string.
///
/// # Parameters
/// - `s`: The string to parse.
///
/// # Returns
/// A pointer to the parsed type on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn parse_type(s: *const c_char) -> *const Gc<Type> {
    clear_last_error();
    ensures!(!s.is_null(), "`s` is null", std::ptr::null());

    let string = unsafe { CStr::from_ptr(s) }.to_str();
    let string = ensures_ok!(string, std::ptr::null()).to_string();

    let client = ensures_ok!(get_client(), std::ptr::null());
    let term = ensures_ok!(client.parse_type_from_string(string), std::ptr::null());
    term.into_gc()
}

/// Convert a term to a string.
///
/// # Parameters
/// - `term`: The term to convert.
///
/// # Returns
/// A pointer to the string on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn string_of_term(term: *const Gc<Term>) -> *const c_char {
    clear_last_error();
    ensures!(!term.is_null(), "`term` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let term = unsafe { &*term }.as_ref();
    let string = ensures_ok!(client.string_of_term(term), std::ptr::null());
    let string = CString::new(string).unwrap();
    string.to_gc()
}

/// Convert a theorem to a string.
///
/// # Parameters
/// - `thm`: The theorem to convert.
///
/// # Returns
/// A pointer to the string on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn string_of_thm(thm: *const Gc<Theorem>) -> *const c_char {
    clear_last_error();
    ensures!(!thm.is_null(), "`thm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let thm = unsafe { &*thm }.as_ref();
    let string = ensures_ok!(client.string_of_thm(thm), std::ptr::null());
    let string = CString::new(string).unwrap();
    string.to_gc()
}

/// Dump a Coq axiom.
///
/// # Parameters
/// - `name`: The name of the axiom.
/// - `th`: The theorem to dump.
///
/// # Returns
/// A pointer to the string on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn dump_coq_axiom(
    name: *const c_char,
    th: *const Gc<Theorem>,
) -> *const c_char {
    clear_last_error();
    ensures!(!name.is_null(), "`name` is null", std::ptr::null());
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let name = unsafe { CStr::from_ptr(name) }.to_str();
    let name = ensures_ok!(name, std::ptr::null()).to_string();

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let string = ensures_ok!(client.dump_coq_axiom(name, th), std::ptr::null());
    let string = CString::new(string).unwrap();
    string.to_gc()
}

/// Theorem: A |- A
///
/// # Parameters
/// - `term`: The term to assume.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn assume(term: *const Gc<Term>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!term.is_null(), "`term` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let term = unsafe { &*term }.as_ref();
    let thm = ensures_ok!(client.assume(term), std::ptr::null());
    thm.into_gc()
}

/// Transitivity of the theorem.
///
/// ```text
/// A1 |- a = b  A2 |- b = c
/// -------------------------
/// A1, A2 |- a = c
/// ```
///
/// # Parameters
/// - `th1`: The first theorem.
/// - `th2`: The second theorem.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn trans(
    th1: *const Gc<Theorem>,
    th2: *const Gc<Theorem>,
) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th1.is_null(), "`th1` is null", std::ptr::null());
    ensures!(!th2.is_null(), "`th2` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th1 = unsafe { &*th1 }.as_ref();
    let th2 = unsafe { &*th2 }.as_ref();
    let thm = ensures_ok!(client.trans(th1, th2), std::ptr::null());
    thm.into_gc()
}

/// Reflexivity.
///
/// ```text
/// ----------
/// A |- a = a
/// ```
///
/// # Parameters
/// - `tm`: The term.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn refl(tm: *const Gc<Term>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let thm = ensures_ok!(client.refl(tm), std::ptr::null());
    thm.into_gc()
}

/// Discharge an assumption.
///
/// ```text
/// A, u |- t
/// ---------
/// A |- u ==> t
/// ```
///
/// # Parameters
/// - `th`: The theorem to discharge.
/// - `tm`: The term to discharge.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn disch(th: *const Gc<Theorem>, tm: *const Gc<Term>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let tm = unsafe { &*tm }.as_ref();
    let thm = ensures_ok!(client.disch(th, tm), std::ptr::null());
    thm.into_gc()
}

/// Generalize a free term in a theorem.
///
/// ```text
/// A |- t
/// -------     (x not free in A)
/// A |- !x. t
/// ```
///
/// # Parameters
/// - `tm`: The term to generalize.
/// - `th`: The theorem to generalize.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn gen(tm: *const Gc<Term>, th: *const Gc<Theorem>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let th = unsafe { &*th }.as_ref();
    let thm = ensures_ok!(client.gen(tm, th), std::ptr::null());
    thm.into_gc()
}

/// Specializes the conclusion of a theorem with its own quantified variables.
///
/// ```text
/// A |- !x1...xn. t
/// -------------------------
/// A |- t[x1'/x1]...[xn'/xn]
/// ```
///
/// # Parameters
/// - `th`: The theorem to specialize.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn spec_all(th: *const Gc<Theorem>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let thm = ensures_ok!(client.spec_all(th), std::ptr::null());
    thm.into_gc()
}

/// Specializes the conclusion of a theorem.
///
/// ```text
/// A |- !x. t
/// ----------- SPEC `u`
/// A |- t[u/x]
/// ```
///
/// # Parameters
/// - `tm`: The variable to be specialized.
/// - `th`: The theorem to specialize.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn spec(tm: *const Gc<Term>, th: *const Gc<Theorem>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let th = unsafe { &*th }.as_ref();
    let thm = ensures_ok!(client.spec(tm, th), std::ptr::null());
    thm.into_gc()
}

/// Modus ponens.
///
/// ```text
/// A1 |- t1 ==> t2   A2 |- t1
/// --------------------------
/// A1, A2 |- t2
/// ```
///
/// # Parameters
/// - `th1`: The first theorem.
/// - `th2`: The second theorem.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn mp(
    th1: *const Gc<Theorem>,
    th2: *const Gc<Theorem>,
) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th1.is_null(), "`th1` is null", std::ptr::null());
    ensures!(!th2.is_null(), "`th2` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th1 = unsafe { &*th1 }.as_ref();
    let th2 = unsafe { &*th2 }.as_ref();
    let thm = ensures_ok!(client.mp(th1, th2), std::ptr::null());
    thm.into_gc()
}

/// Equality version of the Modus Ponens rule.
///
/// ```text
/// A1 |- t1 <=> t2   A2 |- t1'
/// ---------------------------
///       A1 u A2 |- t2
/// ```
///
/// # Parameters
/// - `th1`: The first theorem.
/// - `th2`: The second theorem.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn eq_mp(
    th1: *const Gc<Theorem>,
    th2: *const Gc<Theorem>,
) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th1.is_null(), "`th1` is null", std::ptr::null());
    ensures!(!th2.is_null(), "`th2` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th1 = unsafe { &*th1 }.as_ref();
    let th2 = unsafe { &*th2 }.as_ref();
    let thm = ensures_ok!(client.eq_mp(th1, th2), std::ptr::null());
    thm.into_gc()
}

/// Conjunction.
///
/// ```text
/// A1 |- t1  A2 |- t2
/// ------------------
/// A1, A2 |- t1 /\ t2
/// ```
///
/// # Parameters
/// - `th1`: The first theorem.
/// - `th2`: The second theorem.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn conjunct(
    th1: *const Gc<Theorem>,
    th2: *const Gc<Theorem>,
) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th1.is_null(), "`th1` is null", std::ptr::null());
    ensures!(!th2.is_null(), "`th2` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th1 = unsafe { &*th1 }.as_ref();
    let th2 = unsafe { &*th2 }.as_ref();
    let thm = ensures_ok!(client.conjunct(th1, th2), std::ptr::null());
    thm.into_gc()
}

/// Extracts left conjunct of theorem.
///
/// ```text
/// A |- t1 /\ t2
/// -------------
///    A |- t1
/// ```
///
/// # Parameters
/// - `th`: The theorem.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn conjunct1(th: *const Gc<Theorem>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let thm = ensures_ok!(client.conjunct1(th), std::ptr::null());
    thm.into_gc()
}

/// Extracts right conjunct of theorem.
///
/// ```text
/// A |- t1 /\ t2
/// -------------
///    A |- t2
/// ```
///
/// # Parameters
/// - `th`: The theorem.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn conjunct2(th: *const Gc<Theorem>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let thm = ensures_ok!(client.conjunct2(th), std::ptr::null());
    thm.into_gc()
}

/// Symmetry.
///
/// ```text
/// A |- t1 = t2
/// ------------
/// A |- t2 = t1
/// ```
///
/// # Parameters
/// - `th`: The equation theorem.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn symm(th: *const Gc<Theorem>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let thm = ensures_ok!(client.symm(th), std::ptr::null());
    thm.into_gc()
}

/// Eliminates disjunction by cases.
///
/// ```text
/// A |- t1 \/ t2   A1 |- t   A2 |- t
/// ----------------------------------
/// A u (A1 - {t1}) u (A2 - {t2}) |- t
/// ```
///
/// # Parameters
/// - `th1`: The first theorem.
/// - `th2`: The second theorem.
/// - `th3`: The third theorem.
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn disj_cases(
    th1: *const Gc<Theorem>,
    th2: *const Gc<Theorem>,
    th3: *const Gc<Theorem>,
) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th1.is_null(), "`th1` is null", std::ptr::null());
    ensures!(!th2.is_null(), "`th2` is null", std::ptr::null());
    ensures!(!th3.is_null(), "`th3` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th1 = unsafe { &*th1 }.as_ref();
    let th2 = unsafe { &*th2 }.as_ref();
    let th3 = unsafe { &*th3 }.as_ref();
    let thm = ensures_ok!(client.disj_cases(th1, th2, th3), std::ptr::null());
    thm.into_gc()
}

/// Deduces logical equivalence from deduction in both directions.
///
/// ```text
///      A |- p        B |- q
/// --------------------------------
/// (A - {q}) u (B - {p}) |- p <=> q
/// ```
///
/// # Parameters
/// - `th1`: The first theorem
/// - `th2`: The second theorem
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn deduct_antisym(
    th1: *const Gc<Theorem>,
    th2: *const Gc<Theorem>,
) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th1.is_null(), "`th1` is null", std::ptr::null());
    ensures!(!th2.is_null(), "`th2` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th1 = unsafe { &*th1 }.as_ref();
    let th2 = unsafe { &*th2 }.as_ref();
    let thm = ensures_ok!(client.deduct_antisym(th1, th2), std::ptr::null());
    thm.into_gc()
}

/// Existentially quantifies a hypothesis of a theorem.
///
/// ```text
/// A |- t   `x` is not free in `A |- t`
/// ------------------------------------ CHOOSE `x` th
///            A |- ?x. t
/// ```
/// # Parameters
/// - `tm`: The term
/// - `th`: The theorem
///
/// # Returns
/// A pointer to the theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn choose(tm: *const Gc<Term>, th: *const Gc<Theorem>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let th = unsafe { &*th }.as_ref();
    let thm = ensures_ok!(client.choose(tm, th), std::ptr::null());
    thm.into_gc()
}

/// Define an inductive type.
///
/// # Parameters
/// - `name`: The name of the inductive type.
/// - `variants`: The variants of the inductive type.
///
/// # Returns
/// Two theorems on success, `NULL` on failure.
///
/// cbindgen:ptrs-as-arrays=[[variants;]]
#[no_mangle]
pub unsafe extern "C" fn define_type(
    name: *const c_char,
    variants: *const *const c_char,
) -> *const IndType {
    clear_last_error();
    ensures!(!name.is_null(), "`name` is null", std::ptr::null());
    ensures!(!variants.is_null(), "`variants` is null", std::ptr::null());

    let name = unsafe { CStr::from_ptr(name) }.to_str();
    let name = ensures_ok!(name, std::ptr::null()).to_string();

    let variants = {
        let mut ptr = variants;
        let mut variants = Vec::new();
        while !(*ptr).is_null() {
            let variant = unsafe { CStr::from_ptr(*ptr) }.to_str();
            let variant = ensures_ok!(variant, std::ptr::null()).to_string();
            variants.push(variant);
            ptr = ptr.add(1);
        }
        variants
    };

    let client = ensures_ok!(get_client(), std::ptr::null());
    let ind_type = ensures_ok!(client.define_type(name, variants), std::ptr::null());
    let ind = ind_type.ind.into_gc();
    let rec = ind_type.rec.into_gc();
    let distinct = ind_type.distinct.into_gc();
    let cases = ind_type.cases.into_gc();
    let inject = ind_type.inject.into_gc();
    let ind_type = IndType {
        ind,
        rec,
        distinct,
        cases,
        inject,
    };
    ind_type.into_gc()
}

/// Define a new constant or function.
///
/// # Parameters
/// - `tm`: The term to define.
///
/// # Returns
/// A theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn define(tm: *const Gc<Term>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let thm = ensures_ok!(client.define(tm), std::ptr::null());
    thm.into_gc()
}

/// Uses an instance of a given equation to rewrite a term.
///
/// # Parameters
/// - `th`: The theorem to use for rewriting.
/// - `tm`: The term to rewrite.
///
/// # Returns
/// A theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn rewrite(
    th: *const Gc<Theorem>,
    tm: *const Gc<Term>,
) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let tm = unsafe { &*tm }.as_ref();
    let thm = ensures_ok!(client.rewrite(th, tm), std::ptr::null());
    thm.into_gc()
}

/// Instantiation of induction principle.
///
/// # Parameters
/// - `th`: The induction principle theorem.
/// - `tm1`: The first term.
/// - `tm2`: The second term.
///
/// # Returns
/// A theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn induction_aux(
    th: *const Gc<Theorem>,
    tm1: *const Gc<Term>,
    tm2: *const Gc<Term>,
) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());
    ensures!(!tm1.is_null(), "`tm1` is null", std::ptr::null());
    ensures!(!tm2.is_null(), "`tm2` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let tm1 = unsafe { &*tm1 }.as_ref();
    let tm2 = unsafe { &*tm2 }.as_ref();
    let thm = ensures_ok!(client.induction_aux(th, tm1, tm2), std::ptr::null());
    thm.into_gc()
}

/// Substitute terms for other terms inside a term.
///
/// # Parameters
/// - `tm1`: first term
/// - `tm2`: second term
/// - `tm`: term to be substituted
///
/// # Returns
///   a term `tm[tm1/tm2]`.
#[no_mangle]
pub unsafe extern "C" fn subst(
    tm1: *const Gc<Term>,
    tm2: *const Gc<Term>,
    tm: *const Gc<Term>,
) -> *const Gc<Term> {
    clear_last_error();
    ensures!(!tm1.is_null(), "`tm1` is null", std::ptr::null());
    ensures!(!tm2.is_null(), "`tm2` is null", std::ptr::null());
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm1 = unsafe { &*tm1 }.as_ref();
    let tm2 = unsafe { &*tm2 }.as_ref();
    let tm = unsafe { &*tm }.as_ref();
    let tm = ensures_ok!(client.subst(tm1, tm2, tm), std::ptr::null());
    tm.into_gc()
}

/// Check if a term is an application.
///
/// # Parameters
/// - `tm`: The term to check.
///
/// # Returns
/// `true` on it is an application, `false` on it is not (or failure).
#[no_mangle]
pub unsafe extern "C" fn is_comb(tm: *const Gc<Term>) -> bool {
    clear_last_error();
    ensures!(!tm.is_null(), "`term` is null", false);

    let client = ensures_ok!(get_client(), false);
    let tm = unsafe { &*tm }.as_ref();
    ensures_ok!(client.is_comb(tm), false)
}

/// First element of the destruct of an application.
///
/// # Parameters
/// - `tm`: The term to destruct
///
/// # Returns
/// A term on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn fst_comb(tm: *const Gc<Term>) -> *const Gc<Term> {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let term = ensures_ok!(client.dest_comb(tm), std::ptr::null()).0;
    term.into_gc()
}

/// Second element of the destruct of an application.
///
/// # Parameters
/// - `tm`: The term to destruct
///
/// # Returns
/// A term on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn snd_comb(tm: *const Gc<Term>) -> *const Gc<Term> {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let term = ensures_ok!(client.dest_comb(tm), std::ptr::null()).1;
    term.into_gc()
}

/// Construct a abstraction.
///
/// # Parametes
/// - `tm1`: The first term
/// - `tm2`: The second term
///
/// # Returns
/// A term on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn mk_abs(tm1: *const Gc<Term>, tm2: *const Gc<Term>) -> *const Gc<Term> {
    clear_last_error();
    ensures!(!tm1.is_null(), "`tm1` is null", std::ptr::null());
    ensures!(!tm2.is_null(), "`tm2` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm1 = unsafe { &*tm1 }.as_ref();
    let tm2 = unsafe { &*tm2 }.as_ref();
    let term = ensures_ok!(client.mk_abs(tm1, tm2), std::ptr::null());
    term.into_gc()
}

/// Construct a combination.
///
/// # Parametes
/// - `tm1`: The first term
/// - `tm2`: The second term
///
/// # Returns
/// A term on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn mk_comb(tm1: *const Gc<Term>, tm2: *const Gc<Term>) -> *const Gc<Term> {
    clear_last_error();
    ensures!(!tm1.is_null(), "`tm1` is null", std::ptr::null());
    ensures!(!tm2.is_null(), "`tm2` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm1 = unsafe { &*tm1 }.as_ref();
    let tm2 = unsafe { &*tm2 }.as_ref();
    let term = ensures_ok!(client.mk_comb(tm1, tm2), std::ptr::null());
    term.into_gc()
}

/// Conclusion of a theorem.
///
/// # Parameters
/// - `th`: The theorem
///
/// # Returns
/// A term on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn concl(th: *const Gc<Theorem>) -> *const Gc<Term> {
    clear_last_error();
    ensures!(!th.is_null(), "`th` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let th = unsafe { &*th }.as_ref();
    let tm = ensures_ok!(client.concl(th), std::ptr::null());
    tm.into_gc()
}

/// Create a new type.
///
/// # Parameters
/// - `name`: The name of the type.
///
/// # Returns
/// `0` on success, `-1` on failure.
#[no_mangle]
pub unsafe extern "C" fn new_type(name: *const c_char, arity: u32) -> c_int {
    clear_last_error();
    ensures!(!name.is_null(), "`name` is null", -1);

    let name = unsafe { CStr::from_ptr(name) }.to_str();
    let name = ensures_ok!(name, -1).to_string();

    let client = ensures_ok!(get_client(), -1);
    ensures_ok!(client.new_type(name, arity), -1);
    0
}

/// Declare a new constant.
///
/// # Parameters
/// - `name`: The name of the constant.
/// - `ty`: The type of the constant.
///
/// # Returns
/// `0` on success, `-1` on failure.
#[no_mangle]
pub unsafe extern "C" fn new_constant(name: *const c_char, ty: *const Gc<Type>) -> c_int {
    clear_last_error();
    ensures!(!name.is_null(), "`name` is null", -1);
    ensures!(!ty.is_null(), "`ty` is null", -1);

    let name = unsafe { CStr::from_ptr(name) }.to_str();
    let name = ensures_ok!(name, -1).to_string();

    let client = ensures_ok!(get_client(), -1);
    let ty = unsafe { &*ty }.as_ref();
    ensures_ok!(client.new_constant(name, ty), -1);
    0
}

/// Set up a new axiom.
///
/// # Parameters
/// - `tm`: The term of the axiom.
///
/// # Returns
/// A theorem on success, `NULL` on failure.
#[no_mangle]
pub unsafe extern "C" fn new_axiom(tm: *const Gc<Term>) -> *const Gc<Theorem> {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let thm = ensures_ok!(client.new_axiom(tm), std::ptr::null());
    thm.into_gc()
}

/// Define a relation or family of relations inductively.
#[no_mangle]
pub unsafe extern "C" fn new_inductive_definition(tm: *const Gc<Term>) -> *const IndDef {
    clear_last_error();
    ensures!(!tm.is_null(), "`tm` is null", std::ptr::null());

    let client = ensures_ok!(get_client(), std::ptr::null());
    let tm = unsafe { &*tm }.as_ref();
    let ind_def = ensures_ok!(client.new_inductive_definition(tm), std::ptr::null());
    let def = ind_def.def.into_gc();
    let ind = ind_def.ind.into_gc();
    let cases = ind_def.cases.into_gc();
    let ind_def = IndDef { def, ind, cases };
    ind_def.into_gc()
}
