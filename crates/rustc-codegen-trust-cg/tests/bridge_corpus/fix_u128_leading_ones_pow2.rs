// The three `u128` bit-manipulation ops that had NO two-limb decomposition:
// `leading_ones`, `trailing_ones`, `is_power_of_two`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// They are why `core::num::<impl u128>::checked_pow` and `overflowing_pow` were
// `library/core` census roots ("bitmanip op with width > 64 unsupported"):
// `checked_pow`'s change-of-base fast path opens with `base.is_power_of_two()`.
// The other eight ops were already decomposed across `lo = trunc(v)` /
// `hi = trunc(v >> 64)`; these three are the same limb arithmetic
// (`leading_ones(v) == leading_zeros(!v)`, `is_power_of_two(v) == count_ones(v) == 1`).
//
// A wrong limb identity is SILENT — it returns a plausible small integer — so
// every value is folded into one printed checksum over ten seeds, including the
// limb boundary (2^64 - 1, 2^64), the top bit, all-ones and zero.
#[inline(never)]
fn probe(seed: u128) -> u128 {
    let a = seed.leading_ones() as u128;
    let b = seed.trailing_ones() as u128;
    let c = seed.is_power_of_two() as u128;
    let d = (!seed).leading_ones() as u128;
    let e = (!seed).trailing_ones() as u128;
    a ^ (b << 8) ^ (c << 16) ^ (d << 24) ^ (e << 32)
}

fn main() {
    let k: u128 = std::hint::black_box(0);
    let mut acc = 0u128;
    acc ^= probe(k);
    acc ^= probe(k.wrapping_add(1));
    acc ^= probe(k.wrapping_add(2));
    acc ^= probe(k.wrapping_add(3));
    acc ^= probe(u128::MAX.wrapping_sub(k));
    acc ^= probe((u128::MAX >> 1).wrapping_add(k));
    acc ^= probe((1u128 << 127).wrapping_add(k));
    acc ^= probe((1u128 << 64).wrapping_sub(1).wrapping_add(k));
    acc ^= probe((1u128 << 64).wrapping_add(k));
    acc ^= probe(0xFFFF_FFFF_FFFF_FFFFu128.wrapping_mul(3).wrapping_add(k));
    // Printed as a small integer: a `u128` Display goes through a `core::fmt`
    // path blocked by the unrelated [TCG-REGALLOC-063] lane, which would mask
    // this row.
    println!("{}", (acc % 1_000_003) as u32);
}
