// CORPUS FIXTURE — a `Saturating<u128>` sum is NOT computed by the bridge's loop.
//
// `emit_std_reduction_step` models saturating arithmetic of at most 64 bits
// (`std_reduction_modeled`: the >64-bit clamp constants are not wired), so a
// direct `.sum()` into `Saturating<u128>` steps aside to the real
// `Iterator::sum`, which runs core's `Saturating::add` — refused today by name
// further down, a correct fail-closed outcome. Measured on the unpatched bridge
// (origin/main 5828b4ce6, `no-proof-certs`, O0): the modeled loop's WRAPPING add
// printed `1 9` where LLVM prints `340282366920938463463374607431768211455 9`.
// The r20 refuter's mutant with only the `width > 64` guard removed printed
// `0 9` (the >64-bit clamp constants are not wired).
//
// HOW IT FAILS IF THE WIDTH GUARD IS REMOVED: it COMPILES and DIVERGES from LLVM —
// a hard failure. A refusal is accepted; a compile must match.
use std::hint::black_box;
use std::num::Saturating;

#[inline(never)]
fn sat_u128(v: &[u128]) -> u128 {
    let s: Saturating<u128> = v.iter().map(|&x| Saturating(x)).sum();
    s.0
}

fn main() {
    println!(
        "{} {}",
        sat_u128(black_box(&[u128::MAX - 3, 5])),
        sat_u128(black_box(&[4, 5]))
    );
}
