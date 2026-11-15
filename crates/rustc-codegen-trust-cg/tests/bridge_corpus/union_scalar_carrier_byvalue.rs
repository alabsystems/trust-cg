// Corpus: the WHOLE-VALUE read of a SCALAR-ABI union — `MaybeUninit<u32>` passed
// and returned BY VALUE, and read whole after a union FIELD WRITE.
//
// A scalarized union is modeled as ONE `abi_ty` carrier with each field a
// reinterpret-cast of it. `lower_union_adt_aggregate` (the CONSTRUCTED union)
// bound BOTH the carrier and the per-field projections; the entry-arg seeding
// bound only the projections. A union PARAMETER therefore reached
// `resolve_place_kernel` with `has_proj_any && !scalar_value`, which for an
// `Empty` projection is the "whole scalarized aggregate used as a single scalar
// value" refusal. Measured on a `library/core` census at `-Copt-level=0`: 5 failed
// roots — `MaybeUninit::<u8>::assume_init`, `MaybeUninit::<usize>::assume_init`,
// `transmute_neo::<MaybeUninit<u8>, u8>`, `transmute_neo::<MaybeUninit<usize>,
// usize>`, `select_unpredictable::<MaybeUninit<usize>>`.
//
// WHY THE CARRIER AND THE PROJECTIONS MUST MOVE TOGETHER. Binding the carrier
// alone would be a SILENT WRONG READ, not a widening: `rebind_union_sibling_-`
// `projections` re-derives every FIELD after `u.f = x` but used to leave the
// carrier at its construction value, so the whole-value read would observe the
// PRE-WRITE union. That case is section (3) below and is the reason the two
// bindings are now one decision.
//
// WHAT A WRONG LOWERING LOOKS LIKE:
//   * the parameter's value dropped (the callee reads the default / zero) —
//     every value is distinctive and printed;
//   * the carrier stale behind a field write — section (3) writes through one
//     field and reads the union WHOLE afterwards;
//   * a cast in the wrong direction on a narrow field — a `u8` union is passed
//     and returned by value with a high-bit-set value.
#![allow(dead_code)]

use std::mem::MaybeUninit;

#[inline(never)]
fn mk32(v: u32) -> MaybeUninit<u32> {
    MaybeUninit::new(v)
}

#[inline(never)]
fn thru32(m: MaybeUninit<u32>) -> u32 {
    unsafe { m.assume_init() }
}

#[inline(never)]
fn mk8(v: u8) -> MaybeUninit<u8> {
    MaybeUninit::new(v)
}

#[inline(never)]
fn thru8(m: MaybeUninit<u8>) -> u8 {
    unsafe { m.assume_init() }
}

/// A union parameter passed STRAIGHT THROUGH another by-value boundary before
/// being read: the carrier must survive two hops.
#[inline(never)]
fn relay32(m: MaybeUninit<u32>) -> u32 {
    thru32(m)
}

/// `MaybeUninit::uninit()` + a write through the raw pointer + `assume_init` —
/// the shape where the union's storage is written OUTSIDE the construct.
#[inline(never)]
fn write_then_read(v: u32) -> u32 {
    let mut m = MaybeUninit::<u32>::uninit();
    unsafe {
        m.as_mut_ptr().write(v.wrapping_mul(2654435761));
    }
    unsafe { m.assume_init() }
}

/// (3) THE CARRIER-STALENESS CASE. `MaybeUninit`'s own field is private, so the
/// same single-non-ZST-field shape is spelled here: the union is CONSTRUCTED with
/// one value, then written through its FIELD, then read WHOLE (passed by value to
/// an `#[inline(never)]` callee, and read back through the field). A carrier left
/// at its construction value prints the PRE-WRITE number for `w`.
#[derive(Clone, Copy)]
union Carrier {
    v: u32,
}

#[inline(never)]
fn take_carrier(c: Carrier) -> u32 {
    unsafe { c.v }
}

#[inline(never)]
fn field_write_then_whole_read(initial: u32, written: u32) -> (u32, u32) {
    let mut c = Carrier { v: initial };
    c.v = written;
    // whole-value read (by-value call) and field read, in that order
    (take_carrier(c), unsafe { c.v })
}

fn main() {
    println!("a {}", thru32(mk32(0xABCD1234)));
    println!("b {}", relay32(mk32(0x0F0F_F0F0)));
    println!("c {}", write_then_read(7));
    println!("d {}", write_then_read(0xFFFF_FFFF));
    println!("e {}", thru8(mk8(0xFE)));
    println!("f {}", thru8(mk8(0)));
    let (gw, gf) = field_write_then_whole_read(0xAABB_CC00, 0x0000_0042);
    println!("g {} {}", gw, gf);
    let (g2w, g2f) = field_write_then_whole_read(1, 0xDEAD_BEEF);
    println!("g2 {} {}", g2w, g2f);
    let m = mk32(99);
    println!("h {}", thru32(m));
    let n = mk8(200);
    println!("i {}", thru8(n));
}
