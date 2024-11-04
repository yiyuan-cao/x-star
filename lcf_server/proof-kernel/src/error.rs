//! Error handling utilities.

use parking_lot::{Mutex, MutexGuard};
use std::{
    ffi::{c_char, CString},
    fmt::Display,
    sync::OnceLock,
};

use crate::gc::ToGc;

/// cbindgen:ignore
static LAST_ERROR_MSG: OnceLock<Mutex<Option<CString>>> = OnceLock::new();

#[inline]
fn last_error_msg() -> MutexGuard<'static, Option<CString>> {
    LAST_ERROR_MSG.get_or_init(|| Mutex::new(None)).lock()
}

#[inline]
pub(crate) fn clear_last_error() {
    last_error_msg().take();
}

#[inline]
pub(crate) fn set_last_error<T: Display>(msg: T) {
    let msg = msg.to_string();
    eprintln!("error: {}", msg);
    last_error_msg().replace(CString::new(msg).unwrap());
}

/// Get the last error message.
///
/// If no error has been set, this function returns `NULL`.
///
/// The returned string is GC-managed and should not be freed.
#[no_mangle]
pub extern "C" fn cst_last_error() -> *const c_char {
    let msg = last_error_msg();
    match msg.as_ref() {
        Some(msg) => msg.to_gc(),
        None => std::ptr::null(),
    }
}

macro_rules! ensures {
    ($cond:expr, $err:expr) => {
        if !($cond) {
            $crate::error::set_last_error($err);
            return;
        }
    };
    ($cond:expr, $err:expr, $ret:expr) => {
        if !($cond) {
            $crate::error::set_last_error($err);
            return $ret;
        }
    };
}

macro_rules! ensures_ok {
    ($expr:expr) => {
        match $expr {
            Ok(val) => val,
            Err(e) => {
                $crate::error::set_last_error(e);
                return;
            }
        }
    };
    ($expr:expr, $ret:expr) => {
        match $expr {
            Ok(val) => val,
            Err(e) => {
                $crate::error::set_last_error(e);
                return $ret;
            }
        }
    };
}
