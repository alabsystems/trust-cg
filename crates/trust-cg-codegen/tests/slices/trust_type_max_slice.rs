// Trust-toolchain slice — the production trust-ir `type_max`
// (trust-ir/crates/trust-ir/src/alloc_bound.rs:306) lowered VERBATIM.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (2nd batch, fn #1).
//
// `type_max(bits)` is the "largest unsigned value representable in `bits` bits"
// helper that the trust-ir ALLOCATION-BOUNDS analyzer (`check_allocation_bounds`,
// alloc_bound.rs:108) uses to convert a narrow type's bit-width into the maximal
// element count it can hold (see `local_count_bound`, alloc_bound.rs:317, which
// does `src_ty.bit_width_with(pointer_bits).map(type_max)`). It is a genuine
// SOUNDNESS-adjacent computation: an over-large `type_max` would let an
// out-of-bounds allocation count slip past the bounds checker.
//
// It is PURE, deterministic, closure-free, self-contained:
//   * a single branch (`bits >= 128`) guarding the all-ones saturation case,
//   * real u128 SHIFT + SUBTRACT arithmetic (`(1u128 << bits) - 1`) on the
//     other path — and crucially the `bits >= 128` guard is what AVOIDS the
//     `1u128 << 128` shift-overflow UB, so the branch carries real meaning.
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM (alloc_bound.rs:305-312), byte-for-byte. No types needed
// (operates purely on u32 -> u128).

#![allow(dead_code)]

/// Largest unsigned value representable in `bits` bits.
fn type_max(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

// ── C-ABI entrypoint. The verified body is `type_max`; this wrapper only splits
//    the u128 result into two u64 halves (hi, lo) to avoid any u128 C-ABI
//    ambiguity across native/JIT — the split is OUTSIDE the verified body. The
//    result is written through an out-pointer (two u64 slots). ──
#[no_mangle]
pub extern "C" fn type_max_entry(bits: u32) -> u64 {
    // Return the LOW 64 bits directly; a separate entry returns the high half.
    type_max(bits) as u64
}

#[no_mangle]
pub extern "C" fn type_max_hi_entry(bits: u32) -> u64 {
    (type_max(bits) >> 64) as u64
}

fn main() {
    // Smoke: observable from a native bin.
    println!("{}", type_max_entry(0)); // (1<<0)-1 = 0
    println!("{}", type_max_entry(8)); // 255
    println!("{}", type_max_entry(64)); // u64::MAX
    println!("{}", type_max_hi_entry(128)); // u128::MAX hi = u64::MAX
}
