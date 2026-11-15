// Ruling OD-216, residual 2: the crate's own `memcpy` (it copies nothing) in
// one module, a copy in another. `ptr::copy_nonoverlapping` lowers to an LIR
// `Memcpy`, the selector's `call memcpy`, which binds to the object's own
// definition ahead of the C library's.
#![no_std]

pub mod routine {
    use core::ffi::c_void;

    /// The crate's own `memcpy`: it copies nothing.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn memcpy(dest: *mut c_void, _src: *const c_void, _n: usize) -> *mut c_void {
        dest
    }
}

pub mod user {
    /// `n` bytes from `src` to `dst`.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn copy_bytes(dst: *mut u8, src: *const u8, n: usize) {
        unsafe { core::ptr::copy_nonoverlapping(src, dst, n) }
    }
}
