// Ruling OD-216, control of `copy_split.rs`: the crate defines no `memcpy`,
// so the copy binds to the C library's, which slice 13 trusts.
#![no_std]

pub mod user {
    /// `n` bytes from `src` to `dst`.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn copy_bytes(dst: *mut u8, src: *const u8, n: usize) {
        unsafe { core::ptr::copy_nonoverlapping(src, dst, n) }
    }
}
