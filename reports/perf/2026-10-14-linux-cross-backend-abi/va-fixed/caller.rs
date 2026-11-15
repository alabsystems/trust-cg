extern crate vapad;
use std::hint::black_box as bb;
use vapad::{Oa16U64, Oa16U8, OaWrap16};

extern "C" {
    fn va_pad_u64(p0: u64, a: Oa16U64, p2: u64, ...) -> u64;
    fn va_wrap16(p0: u64, a: OaWrap16, p2: u64, ...) -> u64;
}

fn main() {
    let r1 = unsafe { va_pad_u64(bb(1), Oa16U64 { a: bb(2) }, bb(3), bb(4u64)) };
    let r2 = unsafe { va_wrap16(bb(1), OaWrap16 { a: Oa16U8 { a: bb(2) } }, bb(3), bb(4u64)) };
    println!("{} {}", r1, r2);
    std::process::exit(if r1 == 1_020_304 && r2 == 1_020_304 { 42 } else { 1 });
}
