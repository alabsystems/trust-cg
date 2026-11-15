extern crate al16callee;
use al16callee::Al16s;
use std::hint::black_box as bb;

extern "C" {
    fn take_al16s(p0: u64, p1: Al16s, p2: u32) -> u64;
    fn take_al16s_stack(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64, a7: u64,
                        p0: u8, p1: Al16s, p2: u32) -> u64;
}

fn main() {
    let r1 = unsafe { take_al16s(bb(1), Al16s { a: bb(2) }, bb(3)) };
    let r2 = unsafe { take_al16s_stack(bb(1), bb(1), bb(1), bb(1), bb(1), bb(1), bb(1), bb(1), bb(4), Al16s { a: bb(5) }, bb(6)) };
    println!("{} {}", r1, r2);
    std::process::exit(if r1 == 1_002_003 && r2 == 8_004_005_006 { 42 } else { 1 });
}
