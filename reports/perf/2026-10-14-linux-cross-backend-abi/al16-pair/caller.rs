extern crate al16bcallee;
use al16bcallee::Al16;
use std::hint::black_box as bb;

extern "C" {
    fn take_al16(p0: u64, p1: Al16, p2: u64) -> u64;
    fn give_al16(p0: u64, p1: Al16) -> Al16;
}

fn main() {
    let r1 = unsafe { take_al16(bb(1), Al16 { a: bb(2), b: bb(3) }, bb(4)) };
    let r2 = unsafe { give_al16(bb(5), Al16 { a: bb(6), b: bb(7) }) };
    let a = r2.a;
    let b = r2.b;
    println!("{} {} {}", r1, a, b);
    std::process::exit(if r1 == 1_020_304 && a == 12 && b == 12 { 42 } else { 1 });
}
