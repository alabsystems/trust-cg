// Corpus: an AGGREGATE ELEMENT STORE into a `&mut [T]` slice — `parts[i] =
// MaybeUninit::new(Part::…)`, the exact shape `core::num::imp::flt2dec` builds
// every float's formatted output in.
//
// `lower_memory_slice_element_store` asked `rust_ty_to_trust_ir_ty` for the
// element's single trust-ir SCALAR and propagated its error. For a 24-byte
// `MaybeUninit<Part<'_>>` that error was not about the store at all — it was the
// union's own "no scalar ABI carrier", raised three frames down in
// `scalar_union_abi_layout` and naming the union's FIELD type. Measured on a
// `library/core` census at `-Copt-level=0`: 10 failed roots, all of
// `to_shortest_str` / `to_shortest_exp_str` / `to_exact_exp_str` /
// `to_exact_fixed_str` (f32 and f64) / `digits_to_dec_str` / `digits_to_exp_str`.
//
// WHAT A WRONG LOWERING LOOKS LIKE, and what pins it here:
//   * a wrong element STRIDE (the register width, or `size_of` of the union's
//     first field, instead of 24) puts part `i` on top of part `i-1` — every
//     part is read back and printed, in order, at three different indices;
//   * a one-lane store of the `Copy(&[u8])` payload writes `data` and leaves
//     `len` stale, so the read-back slice has the WRONG LENGTH — every `Copy`
//     part prints its length AND folds its bytes;
//   * a tag written at the wrong offset reads back as the WRONG VARIANT — the
//     three variants are interleaved so a shifted tag shows as a variant swap;
//   * a from-END index (`parts[len-1]`) resolved against the PATTERN's minimum
//     length instead of the runtime one writes the FRONT — the last slot is
//     written through a `[.., last]` binding and read back separately.
#![allow(dead_code)]

use std::mem::MaybeUninit;

// The exact shape of `core::num::imp::fmt::Part<'_>`.
enum Part<'a> {
    Zero(usize),
    Num(u16),
    Copy(&'a [u8]),
}

fn part_val(p: &Part<'_>) -> i64 {
    match p {
        Part::Zero(n) => 1_000_000 + *n as i64,
        Part::Num(n) => 2_000_000 + *n as i64,
        Part::Copy(s) => {
            // LENGTH is folded in FIRST and separately: a dropped metadata lane
            // changes this number even when every byte read happens to agree.
            let mut acc = 3_000_000 + s.len() as i64 * 1000;
            for b in *s {
                acc = acc.wrapping_mul(31).wrapping_add(*b as i64);
            }
            acc
        }
    }
}

/// The `digits_to_dec_str` shape: write N parts by index into a caller-owned
/// `&mut [MaybeUninit<Part>]` and hand back the initialized prefix — the exact
/// signature `core::num::imp::flt2dec` uses.
#[inline(never)]
fn fill<'a>(out: &'a mut [MaybeUninit<Part<'a>>], buf: &'a [u8], nzeroes: usize) -> &'a [Part<'a>] {
    out[0] = MaybeUninit::new(Part::Copy(b"0."));
    out[1] = MaybeUninit::new(Part::Zero(nzeroes));
    out[2] = MaybeUninit::new(Part::Copy(buf));
    out[3] = MaybeUninit::new(Part::Num(1234));
    out[4] = MaybeUninit::new(Part::Copy(&buf[..1]));
    // SAFETY: elements `..5` were just initialized.
    unsafe { out[..5].assume_init_ref() }
}

/// Three different `Copy` LENGTHS through the same slot indices, so a stale
/// length lane cannot survive by coincidence.
#[inline(never)]
fn fill_lengths<'a>(out: &'a mut [MaybeUninit<Part<'a>>], buf: &'a [u8]) -> &'a [Part<'a>] {
    out[0] = MaybeUninit::new(Part::Copy(buf));
    out[1] = MaybeUninit::new(Part::Copy(&buf[..2]));
    out[2] = MaybeUninit::new(Part::Copy(&buf[..0]));
    // SAFETY: elements `..3` were just initialized.
    unsafe { out[..3].assume_init_ref() }
}

/// A FROM-END element store (`[.., last]`): the index must come from the
/// RUNTIME length, not from the pattern's minimum length. A wrong resolution
/// writes the FRONT slot, which shows up as `p0` and `p3` swapping payloads.
#[inline(never)]
fn fill_last<'a>(out: &'a mut [MaybeUninit<Part<'a>>], buf: &'a [u8]) -> &'a [Part<'a>] {
    out[0] = MaybeUninit::new(Part::Zero(1));
    out[1] = MaybeUninit::new(Part::Zero(2));
    out[2] = MaybeUninit::new(Part::Zero(3));
    if let [.., last] = &mut out[..4] {
        *last = MaybeUninit::new(Part::Copy(buf));
    }
    // SAFETY: elements `..4` were just initialized.
    unsafe { out[..4].assume_init_ref() }
}

#[inline(never)]
fn read_all(tag: u32, parts: &[Part<'_>]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0usize;
    while i < parts.len() {
        let v = part_val(&parts[i]);
        println!("g{} p{} {}", tag, i, v);
        acc = acc.wrapping_mul(7).wrapping_add(v);
        i += 1;
    }
    acc
}

fn main() {
    let digits = [b'1', b'2', b'3', b'4'];

    let mut b1: [MaybeUninit<Part<'_>>; 6] = [const { MaybeUninit::uninit() }; 6];
    println!("acc1 {}", read_all(1, fill(&mut b1, &digits, 7)));

    let mut b2: [MaybeUninit<Part<'_>>; 3] = [const { MaybeUninit::uninit() }; 3];
    println!("acc2 {}", read_all(2, fill_lengths(&mut b2, &digits)));

    let mut b3: [MaybeUninit<Part<'_>>; 4] = [const { MaybeUninit::uninit() }; 4];
    println!("acc3 {}", read_all(3, fill_last(&mut b3, &digits[..3])));
}
