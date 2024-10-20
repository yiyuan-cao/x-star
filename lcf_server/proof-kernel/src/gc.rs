use std::ffi::{c_char, c_void, CString};

#[allow(
    dead_code,
    non_snake_case,
    non_camel_case_types,
    non_upper_case_globals
)]
pub(crate) mod gc_sys {
    include!(concat!(env!("OUT_DIR"), "/gc_bindings.rs"));
}

/// Types that can clone themselves into the garbage collector.
pub trait ToGc {
    type GcPtr;
    fn to_gc(&self) -> Self::GcPtr;
}

impl ToGc for CString {
    type GcPtr = *const c_char;
    fn to_gc(&self) -> Self::GcPtr {
        let len = self.as_bytes_with_nul().len();
        // SAFETY: `CString` is guaranteed to be nul-terminated.
        let s = unsafe { gc_sys::GC_malloc_atomic(len) as *mut c_char };
        unsafe { std::ptr::copy_nonoverlapping(self.as_ptr(), s, len) };
        s as *const c_char
    }
}

/// Types that can move themselves into the garbage collector.
///
/// # Safety
/// The `into_gc` method must currectly set up the finalizer for the object to free its memory.
pub unsafe trait IntoGc {
    type GcPtr;
    fn into_gc(self) -> Self::GcPtr;
}

#[derive(Clone, Copy)]
pub struct Gc<T: Sized>(*const T);

pub trait AutoIntoGc: Sized {}

unsafe impl<T: AutoIntoGc> IntoGc for T {
    type GcPtr = *const Gc<T>;

    fn into_gc(self) -> Self::GcPtr {
        let ptr =
            unsafe { gc_sys::GC_malloc_atomic(std::mem::size_of::<*const T>()) as *mut *const T };
        unsafe { std::ptr::write(ptr, Box::into_raw(Box::new(self))) };
        unsafe {
            extern "C" fn drop_box<T>(ptr: *mut c_void, _: *mut c_void) {
                let ptr = unsafe { std::ptr::read(ptr as *mut *const T) };
                let _ = unsafe { Box::from_raw(ptr as *mut T) };
            }

            gc_sys::GC_register_finalizer(
                ptr as *mut c_void,
                Some(drop_box::<T>),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            );
        }
        ptr as *const Gc<T>
    }
}

impl<T: Sized> Gc<T> {
    pub fn as_ref(&self) -> &T {
        // SAFETY: `Gc` is constructed from a valid pointer.
        unsafe { &*self.0 }
    }
}
