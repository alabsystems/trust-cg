// A C-variadic definition whose FIXED arguments hold an over-aligned padded
// newtype: rustc's Linux C FnAbi passes `Oa16U64` as `[2 x i64]` (x1:x2 after
// one integer), so `p2` arrives in x3. Built by LLVM only: trust-cg refuses
// variadic definitions ([TCG-VARIADIC-DEFINITION]). It reads no anonymous
// argument; its caller passes none.
#![crate_name = "xoavariadic"]
#![feature(c_variadic)]
#![allow(improper_ctypes_definitions)]

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U64 {
    pub a: u64,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn xoa_va_none(p0: u64, a: Oa16U64, p2: u64, mut _ap: ...) -> u64 {
    p0.wrapping_mul(31).wrapping_add(a.a).wrapping_mul(31).wrapping_add(p2)
}
