#![crate_type = "rlib"]
#![crate_name = "vapad"]
#![feature(c_variadic)]

// 16 bytes, repr(align(16)) over one u64: rustc's Linux C FnAbi casts it to
// [2 x i64] (x1:x2 after one integer), also as a FIXED argument of a
// C-variadic function.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U64 {
    pub a: u64,
}

// LLVM-built only (trust-cg refuses variadic definitions). Reads no anonymous
// argument: the call below passes none.
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn va_pad_u64(p0: u64, a: Oa16U64, p2: u64, mut _ap: ...) -> u64 {
    p0 * 10_000 + a.a * 100 + p2
}

// The same function reached through a C-variadic `fn` pointer.
#[inline(never)]
pub fn va_pad_u64_ptr() -> unsafe extern "C" fn(u64, Oa16U64, u64, ...) -> u64 {
    va_pad_u64
}
