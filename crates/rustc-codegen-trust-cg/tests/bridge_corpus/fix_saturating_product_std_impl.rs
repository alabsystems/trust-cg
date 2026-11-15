// CORPUS FIXTURE — MISCOMPILE PIN: a `Saturating<u64>` product must SATURATE.
//
// `impl Product for Saturating<u64>` is `saturating_mul`. The bridge's modeled
// `product` loop used a WRAPPING `Mul`: measured on the unpatched base, `p(&[1 << 40,
// 1 << 40])` printed `0` where LLVM prints `18446744073709551615`. The loop now
// takes its arithmetic from `std_sum_product_arith` (unsigned `saturating_mul` =
// clamp to MAX on overflow). Run WITHOUT proof certificates: the multiply-overflow
// check emits `AArch64::CSet`, which this host's opcode-proof inventory cannot map
// (`[TCG-PROOF-465]`, pre-existing and not this lane's). If a later change refuses
// it, that is fail-closed; if it compiles, it must match LLVM.
use std::num::Saturating;
#[inline(never)]
fn p(v: &[u64]) -> u64 {
    let s: Saturating<u64> = v.iter().map(|&x| Saturating(x)).product();
    s.0
}
#[inline(never)]
fn p8(v: &[u8]) -> u8 {
    let s: Saturating<u8> = v.iter().map(|&x| Saturating(x)).product();
    s.0
}
fn main() {
    println!("{} {}", p(&[1u64 << 40, 1u64 << 40]), p(&[3, 5, 7]));
    println!("{} {}", p8(&[16, 16, 2]), p8(&[3, 5]));
}
