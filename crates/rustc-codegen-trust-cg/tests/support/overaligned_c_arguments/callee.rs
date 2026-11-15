// Over-aligned C composites at the AAPCS64 placements their NATURAL
// alignment decides (the `repr(align)` attribute does not count): built as an
// rlib by LLVM and by the bridge, and called from a binary built by each.
#![crate_name = "xoa"]
#![allow(improper_ctypes_definitions)]

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16 {
    pub a: u64,
    pub b: u64,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U32 {
    pub a: u32,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U64 {
    pub a: u64,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U8 {
    pub a: u8,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U32x3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}

#[repr(C, align(4))]
#[derive(Clone, Copy)]
pub struct Oa4 {
    pub a: u8,
    pub b: u8,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct OaIn16 {
    pub a: u32,
    pub b: Oa4,
}

// The fold every function returns: each word in order into a 64-bit
// accumulator.
macro_rules! fold {
    ($seed:expr; $($word:expr),*) => {{
        let mut acc: u64 = $seed;
        $(acc = acc.wrapping_mul(31).wrapping_add($word);)*
        acc
    }};
}

// x1:x2, then x3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_x1(p0: u64, a: Oa16, p2: u64) -> u64 {
    fold!(1; p0, a.a, a.b, p2)
}

// x3:x4, then x5.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_x3(p0: u64, p1: u64, p2: u64, a: Oa16, p4: u64) -> u64 {
    fold!(3; p0, p1, p2, a.a, a.b, p4)
}

// x5:x6, then x7.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_x5(p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, a: Oa16, p6: u64) -> u64 {
    fold!(5; p0, p1, p2, p3, p4, a.a, a.b, p6)
}

// One register left: the whole composite goes to the stack (sp+0), NGRN
// becomes 8 and the next u64 follows it on the stack (sp+16).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_x7(
    p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, a: Oa16, p8: u64,
) -> u64 {
    fold!(7; p0, p1, p2, p3, p4, p5, p6, a.a, a.b, p8)
}

// On the stack after one 8-byte slot: sp+8 (an 8-aligned slot), then sp+24.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_s8(
    p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64, q: u8, a: Oa16, p10: u64,
) -> u64 {
    fold!(8; p0, p1, p2, p3, p4, p5, p6, p7, q as u64, a.a, a.b, p10)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_u32_x1(p0: u64, a: Oa16U32, p2: u32) -> u64 {
    fold!(11; p0, a.a as u64, p2 as u64)
}

// Over-aligned single-scalar newtypes: the bridge keeps the scalar, rustc
// passes the 16 padded bytes as `[2 x i64]`.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_u8_x5(p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, a: Oa16U8, p6: u8) -> u64 {
    fold!(37; p0, p1, p2, p3, p4, a.a as u64, p6 as u64)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_u64_s8(
    p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64, q: u8, a: Oa16U64, p10: u64,
) -> u64 {
    fold!(41; p0, p1, p2, p3, p4, p5, p6, p7, q as u64, a.a, p10)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_u32x3_x1(p0: u64, a: Oa16U32x3, p2: u64) -> u64 {
    fold!(13; p0, a.a as u64, a.b as u64, a.c as u64, p2)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_u32x3_s8(
    p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64, q: u8, a: Oa16U32x3, p10: u16,
) -> u64 {
    fold!(17; p0, p1, p2, p3, p4, p5, p6, p7, q as u64, a.a as u64, a.b as u64, a.c as u64, p10 as u64)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_in16_x1(p0: u64, a: OaIn16, p2: u8) -> u64 {
    fold!(19; p0, a.a as u64, a.b.a as u64, a.b.b as u64, p2 as u64)
}

// Returned in x0:x1.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_give(p0: u64, a: Oa16) -> Oa16 {
    Oa16 { a: p0.wrapping_add(a.b), b: a.a.wrapping_mul(2) }
}

// The callee calls back into the binary's crate through a C fn pointer,
// passing a composite at x1 that it built itself.
#[inline(never)]
pub extern "C" fn oa_callback(cb: extern "C" fn(u64, Oa16, u64) -> u64, seed: u64) -> u64 {
    let r = cb(seed, Oa16 { a: seed.wrapping_mul(3), b: seed ^ 0x55 }, seed.wrapping_add(9));
    fold!(29; r)
}

// The binary calls `oa_x1` through a C fn pointer.
#[inline(never)]
pub fn oa_pointer() -> extern "C" fn(u64, Oa16, u64) -> u64 {
    oa_x1
}
