#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]
use core::ffi::{c_int, c_void};

// The exact public C prototypes match the pinned SDK core/src/ffi/mod.rs
// lines97/100/103: return pointer, unsigned size_t and 32-bit C int.
#[link(name = "c")]
extern "C" {
    #[link_name = "memcpy"]
    fn real_memcpy(dst: *mut c_void, src: *const c_void, n: usize) -> *mut c_void;
    #[link_name = "memmove"]
    fn real_memmove(dst: *mut c_void, src: *const c_void, n: usize) -> *mut c_void;
    #[link_name = "memset"]
    fn real_memset(dst: *mut c_void, value: c_int, n: usize) -> *mut c_void;
    fn opaque_libcall_count(n: usize) -> usize;
}

#[inline(never)]
pub unsafe fn memcpy_intrinsic_first(dst_a: *mut u8, dst_b: *mut u8, src: *const u8, n: usize) -> *mut c_void {
    let n = opaque_libcall_count(n);
    core::intrinsics::copy_nonoverlapping(src, dst_a, n);
    real_memcpy(dst_b.cast(), src.cast(), n)
}

#[inline(never)]
pub unsafe fn memcpy_extern_first(dst_a: *mut u8, dst_b: *mut u8, src: *const u8, n: usize) -> *mut c_void {
    let n = opaque_libcall_count(n);
    let result = real_memcpy(dst_b.cast(), src.cast(), n);
    core::intrinsics::copy_nonoverlapping(src, dst_a, n);
    result
}

#[inline(never)]
pub unsafe fn memmove_intrinsic_first(dst_a: *mut u8, src_a: *const u8, dst_b: *mut u8, src_b: *const u8, n: usize) -> *mut c_void {
    let n = opaque_libcall_count(n);
    core::intrinsics::copy(src_a, dst_a, n);
    real_memmove(dst_b.cast(), src_b.cast(), n)
}

#[inline(never)]
pub unsafe fn memmove_extern_first(dst_a: *mut u8, src_a: *const u8, dst_b: *mut u8, src_b: *const u8, n: usize) -> *mut c_void {
    let n = opaque_libcall_count(n);
    let result = real_memmove(dst_b.cast(), src_b.cast(), n);
    core::intrinsics::copy(src_a, dst_a, n);
    result
}

#[inline(never)]
pub unsafe fn memset_intrinsic_first(dst_a: *mut u8, dst_b: *mut u8, value: c_int, n: usize) -> *mut c_void {
    let n = opaque_libcall_count(n);
    core::intrinsics::write_bytes(dst_a, value as u8, n);
    real_memset(dst_b.cast(), value, n)
}

#[inline(never)]
pub unsafe fn memset_extern_first(dst_a: *mut u8, dst_b: *mut u8, value: c_int, n: usize) -> *mut c_void {
    let n = opaque_libcall_count(n);
    let result = real_memset(dst_b.cast(), value, n);
    core::intrinsics::write_bytes(dst_a, value as u8, n);
    result
}
