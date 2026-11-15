#![crate_type = "rlib"]
#![crate_name = "vapad"]
#![feature(c_variadic)]

// 16 bytes, repr(align(16)) over one u64: rustc's Linux C FnAbi casts it to
// [2 x i64] (x1:x2 after one integer).
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U64 {
    pub a: u64,
}

// A repr(C) struct around a 16-aligned member: rustc casts it to i128 (an
// even register pair, x2:x3 after one integer).
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U8 {
    pub a: u8,
}
#[repr(C)]
#[derive(Clone, Copy)]
pub struct OaWrap16 {
    pub a: Oa16U8,
}

// The padded f64 newtype: [2 x i64] in GPRs, not d-registers.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Of64 {
    pub a: f64,
}

// Variadic callees (trust-cg refuses variadic definitions, so these are only
// ever LLVM-built). Each reads exactly one anonymous u64.
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn va_pad_u64(p0: u64, a: Oa16U64, p2: u64, mut ap: ...) -> u64 {
    let v: u64 = ap.next_arg::<u64>();
    p0 * 1_000_000 + a.a * 10_000 + p2 * 100 + v
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn va_wrap16(p0: u64, a: OaWrap16, p2: u64, mut ap: ...) -> u64 {
    let v: u64 = ap.next_arg::<u64>();
    p0 * 1_000_000 + (a.a.a as u64) * 10_000 + p2 * 100 + v
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn va_pad_f64(p0: u64, a: Of64, p2: u64, mut ap: ...) -> u64 {
    let v: u64 = ap.next_arg::<u64>();
    p0 * 1_000_000 + (a.a as u64) * 10_000 + p2 * 100 + v
}
