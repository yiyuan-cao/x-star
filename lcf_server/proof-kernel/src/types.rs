use std::mem::size_of;

use hol_rpc::client::{Term, Theorem, Type, Conversion};

use crate::gc::{gc_sys, AutoIntoGc, Gc, IntoGc};

impl AutoIntoGc for Term {}
impl AutoIntoGc for Type {}
impl AutoIntoGc for Theorem {}
impl AutoIntoGc for Conversion {}

/// Inductive type.
#[repr(C)]
pub struct IndType {
    /// The inductive theorem.
    pub ind: *const Gc<Theorem>,
    /// The recursion theorem.
    pub rec: *const Gc<Theorem>,
}

unsafe impl IntoGc for IndType {
    type GcPtr = *const IndType;

    fn into_gc(self) -> Self::GcPtr {
        let indtyp = unsafe { gc_sys::GC_malloc(size_of::<IndType>()) as *mut IndType };
        unsafe { std::ptr::write(indtyp, self) };
        indtyp as *const IndType
    }
}

/// Inductive relation.
#[repr(C)]
pub struct IndDef {
  /// definition.
  pub def: *const Gc<Theorem>, 
  /// inductive rule.
  pub ind: *const Gc<Theorem>, 
  /// cases rule.
  pub cases: *const Gc<Theorem>, 
}

unsafe impl IntoGc for IndDef {
  type GcPtr = *const IndDef;

  fn into_gc(self) -> Self::GcPtr {
      let inddef = unsafe { gc_sys::GC_malloc(size_of::<IndDef>()) as *mut IndDef };
      unsafe { std::ptr::write(inddef, self) };
      inddef as *const IndDef
  }
}