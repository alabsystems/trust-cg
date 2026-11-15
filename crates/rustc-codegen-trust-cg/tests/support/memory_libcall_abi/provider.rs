#![no_std]

#[inline(never)]
#[no_mangle]
pub extern "C" fn opaque_libcall_count(n: usize) -> usize {
    core::hint::black_box(n)
}
