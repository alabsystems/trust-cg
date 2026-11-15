// CORPUS FIXTURE — the `collect::<Vec<T>>()` header-identity rows the bridge
// compiles at -O0 only (companion of `fix_vec_collect_header_identity`).
//
// WHAT IT PINS. The same defect as the companion fixture: the collect loop
// pushed into a scratch header the destination had already been copied out of,
// so the destination read len 0. Measured on aarch64 with origin/main
// 7b2412bc8 at -O0, both rows printed 0 where LLVM prints the trailing values.
// At -O1..-O3 the bridge refuses these shapes by name (the `StepBy` lane past
// -O0, the owning `vec::IntoIter` source at -O2/-O3); the differential admits
// such a refusal there, and requires a match wherever it compiles.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES at -O0 and DIVERGES.

use std::hint::black_box as bb;

#[inline(never)]
fn ck(v: &[u64]) -> u64 {
    let mut s = 0u64;
    let mut i = 0;
    while i < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[i]);
        i += 1;
    }
    s
}
#[inline(never)]
fn step_by(n: u64) -> u64 {
    let v: Vec<u64> = (0..n).step_by(3).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn into_iter_map(n: u64) -> u64 {
    let v: Vec<u64> = vec![1, 2, 3, n];
    let w: Vec<u64> = v.into_iter().map(|x| x * 2).collect();
    w.len() as u64 * 1000 + ck(&w)
}

fn main() {
    let r = step_by(bb(10)); //       7078
    println!("{r}");
    let r = into_iter_map(bb(4)); //  67620
    println!("{r}");
}
