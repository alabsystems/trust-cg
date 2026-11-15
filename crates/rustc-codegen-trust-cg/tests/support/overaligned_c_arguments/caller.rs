// The binary half of `overaligned_c_arguments`: calls every callee function
// through the C declarations below (the FFI shape), through a C fn pointer,
// and hands the callee a callback; prints one line per call.
extern crate xoa;
use std::hint::black_box as bb;
use xoa::{Oa4, Oa16, Oa16U8, Oa16U32, Oa16U32x3, Oa16U64, OaIn16};

#[allow(improper_ctypes)]
unsafe extern "C" {
    fn oa_x1(p0: u64, a: Oa16, p2: u64) -> u64;
    fn oa_x3(p0: u64, p1: u64, p2: u64, a: Oa16, p4: u64) -> u64;
    fn oa_x5(p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, a: Oa16, p6: u64) -> u64;
    fn oa_x7(p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, a: Oa16, p8: u64) -> u64;
    fn oa_s8(
        p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64, q: u8, a: Oa16, p10: u64,
    ) -> u64;
    fn oa_u32_x1(p0: u64, a: Oa16U32, p2: u32) -> u64;
    fn oa_u8_x5(p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, a: Oa16U8, p6: u8) -> u64;
    fn oa_u64_s8(
        p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64, q: u8, a: Oa16U64, p10: u64,
    ) -> u64;
    fn oa_u32x3_x1(p0: u64, a: Oa16U32x3, p2: u64) -> u64;
    fn oa_u32x3_s8(
        p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u64, q: u8, a: Oa16U32x3, p10: u16,
    ) -> u64;
    fn oa_in16_x1(p0: u64, a: OaIn16, p2: u8) -> u64;
    fn oa_give(p0: u64, a: Oa16) -> Oa16;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

// One `name=<16 hex digits>` line per call through write(2): no `core::fmt`,
// so the printing path is the same small code under either backend.
#[inline(never)]
fn line(name: &[u8], value: u64) {
    let mut out = [0u8; 64];
    let mut n = 0;
    while n < name.len() {
        out[n] = name[n];
        n += 1;
    }
    out[n] = b'=';
    n += 1;
    let mut k = 0;
    while k < 16 {
        let digit = ((value >> (60 - 4 * k)) & 0xf) as u8;
        out[n] = if digit < 10 { b'0' + digit } else { b'a' + digit - 10 };
        n += 1;
        k += 1;
    }
    out[n] = b'\n';
    unsafe {
        write(1, out.as_ptr(), n + 1);
    }
}

#[inline(never)]
extern "C" fn cbimpl(p0: u64, a: Oa16, p2: u64) -> u64 {
    let mut acc: u64 = 31;
    acc = acc.wrapping_mul(31).wrapping_add(p0);
    acc = acc.wrapping_mul(31).wrapping_add(a.a);
    acc = acc.wrapping_mul(31).wrapping_add(a.b);
    acc.wrapping_mul(31).wrapping_add(p2)
}

// Scalar leaves only go through `black_box`: a black-boxed composite would be
// a second, Rust-ABI call in front of the C call under test.
macro_rules! oa16 {
    ($a:expr, $b:expr) => {
        Oa16 { a: bb($a), b: bb($b) }
    };
}

fn main() {
    let x3 = Oa16U32x3 { a: bb(0x3101), b: bb(0x3202), c: bb(0x3303) };
    unsafe {
        line(b"oa_x1", oa_x1(bb(1), oa16!(2, 3), bb(4)));
        line(b"oa_x3", oa_x3(bb(1), bb(2), bb(3), oa16!(4, 5), bb(6)));
        line(b"oa_x5", oa_x5(bb(1), bb(2), bb(3), bb(4), bb(5), oa16!(6, 7), bb(8)));
        line(b"oa_x7", oa_x7(bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(7), oa16!(8, 9), bb(10)));
        line(b"oa_s8", oa_s8(bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(7), bb(8), bb(9), oa16!(10, 11), bb(12)));
        line(b"oa_u32_x1", oa_u32_x1(bb(1), Oa16U32 { a: bb(0x2222) }, bb(3)));
        line(b"oa_u8_x5", oa_u8_x5(bb(1), bb(2), bb(3), bb(4), bb(5), Oa16U8 { a: bb(0x66) }, bb(7)));
        line(
            b"oa_u64_s8",
            oa_u64_s8(bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(7), bb(8), bb(9), Oa16U64 { a: bb(0x1010) }, bb(11)),
        );
        line(b"oa_u32x3_x1", oa_u32x3_x1(bb(1), x3, bb(5)));
        line(b"oa_u32x3_s8", oa_u32x3_s8(bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(7), bb(8), bb(9), x3, bb(13)));
        line(b"oa_in16_x1", oa_in16_x1(bb(1), OaIn16 { a: bb(0x4444), b: Oa4 { a: bb(5), b: bb(6) } }, bb(7)));
        let r = oa_give(bb(5), oa16!(6, 7));
        line(b"oa_give", r.a.wrapping_mul(1_000_003).wrapping_add(r.b));
    }
    let pointer = xoa::oa_pointer();
    line(b"oa_pointer", pointer(bb(21), oa16!(22, 23), bb(24)));
    line(b"oa_callback", xoa::oa_callback(cbimpl, bb(41)));
}
