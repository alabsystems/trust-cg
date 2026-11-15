// CORPUS FIXTURE — `Vec<Vec<i64>>::swap_remove` is the receiver's own method,
// never an intercepted `Vec<i64>` one.
//
// WHAT IT PINS. The `swap_remove` twin of `fix_vec_receiver_remove`: keyed off
// its `Vec<i64>` DESTINATION, `g.swap_remove(0)` was lowered as
// `Vec<i64>::swap_remove` over 24-byte header images: SIGSEGV at -O0..-O3 (LLVM
// exits 12).
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM. With
// the fix, std's real `Vec::<Vec<i64>>::swap_remove` body is the function the
// bridge refuses (its `ptr::read` of a header), or it matches.

use std::hint::black_box as bb;

fn main() {
    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut a = Vec::new();
    a.push(bb(10i64));
    let mut b = Vec::new();
    b.push(bb(20i64));
    b.push(bb(21i64));
    g.push(a);
    g.push(b);
    let r = g.swap_remove(bb(0));
    std::process::exit((r.len() * 10 + g[0].len()) as i32);
}
