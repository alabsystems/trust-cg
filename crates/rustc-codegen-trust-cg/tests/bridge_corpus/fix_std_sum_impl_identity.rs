// CORPUS FIXTURE — `.sum()` / `.product()` arithmetic decided by the SELECTED IMPL.
//
// WHAT IT PINS. The bridge replaces a `.sum()` over a chain it models with its own
// loop. Until 2026-09-27 that loop's operator was chosen from the accumulator's
// trust-ir scalar type, which collapses `Saturating<u64>` to `u64`, so every
// `Saturating` sum was computed with a WRAPPING add. Measured on the unpatched
// base: this file printed `8 6` / `4 3` / `7 13` where LLVM prints
// `18446744073709551615 6` / `255 3` / `4294967295 13` — a silent miscompile. The
// arithmetic is now `std_sum_product_arith`'s: `saturating_add` / `saturating_mul`
// for `Saturating`, `wrapping_add` / `wrapping_mul` for `Wrapping`, the checked op
// for a primitive. (The `Saturating` PRODUCT rows live in
// `fix_saturating_product_std_impl`, a no-proof-certs pin: its overflow check emits
// `AArch64::CSet`, which this host's opcode-proof inventory cannot map.)
//
// HOW IT FAILS IF THE CHANGE IS REVERTED. It COMPILES and DIVERGES from LLVM on the
// first three lines — a hard failure of `sum_product_reduction_differential`.

use std::num::{Saturating, Wrapping};

#[inline(never)]
fn sat_u64(v: &[u64]) -> u64 {
    let s: Saturating<u64> = v.iter().map(|&x| Saturating(x)).sum();
    s.0
}
#[inline(never)]
fn sat_u8(v: &[u8]) -> u8 {
    let s: Saturating<u8> = v.iter().map(|&x| Saturating(x)).sum();
    s.0
}
// `impl Sum<&Saturating<u32>> for Saturating<u32>` (a reference item).
#[inline(never)]
fn sat_ref_u32(v: &[Saturating<u32>]) -> u32 {
    let s: Saturating<u32> = v.iter().sum();
    s.0
}
#[inline(never)]
fn wrap_sum(v: &[u64]) -> u64 {
    let s: Wrapping<u64> = v.iter().map(|&x| Wrapping(x)).sum();
    s.0
}
#[inline(never)]
fn wrap_product(v: &[u64]) -> u64 {
    let s: Wrapping<u64> = v.iter().map(|&x| Wrapping(x)).product();
    s.0
}

fn main() {
    println!("{} {}", sat_u64(&[u64::MAX - 3, 5, 7]), sat_u64(&[1, 2, 3]));
    println!("{} {}", sat_u8(&[200, 50, 10]), sat_u8(&[1, 2]));
    println!(
        "{} {}",
        sat_ref_u32(&[Saturating(u32::MAX - 1), Saturating(9)]),
        sat_ref_u32(&[Saturating(4), Saturating(9)])
    );
    println!(
        "{} {}",
        wrap_sum(&[u64::MAX - 1, 5]),
        wrap_product(&[1u64 << 40, 1u64 << 40, 3])
    );
}
