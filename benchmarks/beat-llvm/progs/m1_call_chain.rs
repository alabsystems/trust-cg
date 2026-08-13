// multifn: inlining-shaped small-callee chain (f1->f2->f3->f4, no inline attrs).
// LLVM inlines the whole chain into a tight loop; a backend without inlining pays
// 4 calls per iteration — this row measures the inlining gap directly (OPT-4).
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn f4(x: u64) -> u64 {
    x ^ (x << 9)
}
fn f3(x: u64, k: u64) -> u64 {
    f4(x.wrapping_add(k)).rotate_left(5)
}
fn f2(x: u64, k: u64) -> u64 {
    f3(x ^ (x >> 7), k).wrapping_mul(3)
}
fn f1(x: u64, k: u64) -> u64 {
    f2(x.wrapping_mul(k | 1), k).wrapping_add(1)
}
fn main() {
    let k = bb(0x2545F4914F6CDD1Du64);
    let n = bb(30_000_000u64);
    let mut acc: u64 = bb(1u64);
    let mut i = 0u64;
    while i < n {
        acc = f1(acc ^ i, k);
        i += 1;
    }
    done(acc);
}
