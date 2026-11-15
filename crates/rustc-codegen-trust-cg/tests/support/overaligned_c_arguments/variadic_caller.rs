// A DIRECT call of a C-variadic function that passes NO anonymous argument,
// with an over-aligned FIXED argument (LD-29's residual). The call goes through
// the bridge's direct variadic call lane, whose whole-call placement check is
// the only judgment of its fixed half; with no anonymous argument nothing else
// looks at the call. The bridge declares `Oa16U64` as its one `u64` there (the
// variadic aggregate scope admits no two-unit carrier), so the call must be
// refused by name; passed in the scalar's register it puts `p2` in x2, where
// the callee reads x3 (a silent wrong value at 395954590).
#![crate_name = "xoavariadiccaller"]

extern crate xoavariadic;

use std::hint::black_box as bb;
use xoavariadic::Oa16U64;

unsafe extern "C" {
    fn xoa_va_none(p0: u64, a: Oa16U64, p2: u64, ...) -> u64;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn oa_va_none_x1(p0: u64, a: u64, p2: u64) -> u64 {
    unsafe { xoa_va_none(p0, Oa16U64 { a }, p2) }
}

// `oa_va_none_x1=<16 hex digits>` through write(2), as `caller.rs` prints: no
// `core::fmt`, so a bridge build that admits the call also runs.
fn main() {
    let value = oa_va_none_x1(bb(0x1111), bb(0x2222), bb(0x3333));
    let mut out = *b"oa_va_none_x1=0000000000000000\n";
    let mut k = 0;
    while k < 16 {
        let digit = ((value >> (60 - 4 * k)) & 0xf) as u8;
        out[14 + k] = if digit < 10 { b'0' + digit } else { b'a' + digit - 10 };
        k += 1;
    }
    unsafe {
        write(1, out.as_ptr(), out.len());
    }
}
