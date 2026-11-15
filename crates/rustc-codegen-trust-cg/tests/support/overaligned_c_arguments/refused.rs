// Over-aligned C shapes the bridge still declares as their one scalar while
// rustc's Linux FnAbi casts them to an integer of their padded size: each must
// be refused by name ([TCG-ARG-ABI], the whole-signature placement check),
// never passed in the scalar's register.
#![crate_name = "xoarefused"]
#![allow(improper_ctypes_definitions)]

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U8 {
    pub a: u8,
}

// The member is 16-aligned, so the composite's natural alignment is 16 and
// rustc casts it to `i128`, from an even register (x2:x3 here).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct OaWrap16 {
    pub a: Oa16U8,
}

// Two padded bytes: rustc casts them to `i16`.
#[repr(C, align(2))]
#[derive(Clone, Copy)]
pub struct Oa2 {
    pub a: u8,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_wrap16_x1(p0: u64, a: OaWrap16, p2: u64) -> u64 {
    p0.wrapping_mul(31).wrapping_add(a.a.a as u64).wrapping_mul(31).wrapping_add(p2)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa2_x1(p0: u64, a: Oa2, p2: u64) -> u64 {
    p0.wrapping_mul(31).wrapping_add(a.a as u64).wrapping_mul(31).wrapping_add(p2)
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Oa16U64 {
    pub a: u64,
}

// A FIXED argument of a C-variadic function is placed as for any C function:
// rustc passes this padded newtype as `[2 x i64]` (x1:x2 here). On this route
// the bridge declares it as its one scalar (the variadic aggregate scope admits
// no two-unit carrier), so the whole-call check of the direct variadic call
// refuses the CALLER.
unsafe extern "C" {
    fn xoa_va_pad_u64(p0: u64, a: Oa16U64, p2: u64, ...) -> u64;
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_va_fixed_x1(p0: u64, a: u64, p2: u64, v: u64) -> u64 {
    unsafe { xoa_va_pad_u64(p0, Oa16U64 { a }, p2, v) }
}

// The same fixed arguments through a C-variadic `fn` pointer, with NO anonymous
// argument: the argument count equals the pointer's input count, so the
// ordinary `fn`-pointer call route takes the call, and the whole-signature
// check of the pointer's signature refuses it (on 395954590's backend this was
// a silent wrong value).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_va_pointer_x1(
    f: unsafe extern "C" fn(u64, Oa16U64, u64, ...) -> u64,
    p0: u64,
    a: u64,
    p2: u64,
) -> u64 {
    unsafe { f(p0, Oa16U64 { a }, p2) }
}
