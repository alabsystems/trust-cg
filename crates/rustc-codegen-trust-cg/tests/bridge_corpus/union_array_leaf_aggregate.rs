// Corpus: a UNION whose field is itself NON-SCALAR (an ARRAY) — the
// `core::escape::MaybeEscapedCharacter<N> = union { escape_seq: [ascii::Char; N],
// literal: char }` shape, carried through a struct, a newtype and a TUPLE.
//
// The scalarized-aggregate flattening (`scalar_field_aggregate_trust_ir_fields`)
// has no spelling for such a union: it asks `rust_ty_to_trust_ir_ty` for the
// union's single scalar carrier, `scalar_union_abi_layout` asks the same of the
// union's ARRAY field, and that error — about the ARRAY, three frames down —
// became the whole aggregate's refusal. Measured on a `library/core` census at
// `-Copt-level=0`: 4 failed roots, all in the `char::escape_debug` /
// `escape_default` / `escape_unicode` Display + iterator chain, each carrying the
// text `Ty::[ascii::ascii_char::AsciiChar; 10_usize]`.
//
// The memory path CAN place this shape — every leaf is a scalar at a rustc-layout
// byte offset — so the fix is to let `memory_aggregate_layout` admit a TUPLE the
// scalarized path cannot spell, which is the identical predicate
// `compute_memory_backed_locals` rule (0e) already applies to named aggregates.
//
// WHAT A WRONG LOWERING LOOKS LIKE, and what pins it here:
//   * a wrong ARRAY STRIDE inside the union reads the wrong byte — EVERY buffer
//     position is printed, not a fold;
//   * the union read through the WRONG FIELD (the `char` variant where the
//     `[u8; N]` one was written, or vice versa) — both variants are exercised
//     through the same slot and the discriminating value is printed;
//   * a TUPLE whose rustc layout REORDERED its fields — the tuple's second
//     element is a scalar whose value is printed after the buffer;
//   * a FIELD SHIFT past the union — `alive: Range<u8>` sits AFTER the union in
//     the struct and drives the iteration bounds, so a shifted `alive` changes
//     how many elements come out.
#![allow(dead_code)]

use std::ops::Range;

#[derive(Clone, Copy)]
union MaybeEsc {
    escape_seq: [u8; 10],
    literal: char,
}

/// The `EscapeIterInner<N, ESCAPING>` shape: the union, then the live range.
struct Inner {
    data: MaybeEsc,
    alive: Range<u8>,
}

/// The `char::EscapeDebug` newtype over it.
struct EscDbg(Inner);

#[inline(never)]
fn mk_seq(k: u8) -> EscDbg {
    let mut b = [0u8; 10];
    let mut i = 0usize;
    while i < 10 {
        b[i] = k.wrapping_add(i as u8).wrapping_mul(3);
        i += 1;
    }
    EscDbg(Inner { data: MaybeEsc { escape_seq: b }, alive: 1..9 })
}

#[inline(never)]
fn mk_lit(c: char) -> EscDbg {
    // The `LITERAL_ESCAPE_START` convention: `alive.start >= 128` selects the
    // `literal` variant of the union.
    EscDbg(Inner { data: MaybeEsc { literal: c }, alive: 128..129 })
}

#[inline(never)]
fn step(e: &mut EscDbg) -> Option<u32> {
    if e.0.alive.start >= e.0.alive.end {
        return None;
    }
    let i = e.0.alive.start;
    e.0.alive.start += 1;
    if i >= 128 {
        Some(unsafe { e.0.data.literal } as u32)
    } else {
        Some(unsafe { e.0.data.escape_seq[usize::from(i)] } as u32)
    }
}

/// THE TUPLE: the aggregate whose scalarized flattening has no spelling. The
/// second element is an ordinary scalar, so a reordered / shifted tuple layout
/// shows up in its printed value.
#[inline(never)]
fn pair(e: EscDbg, tag: i64) -> (EscDbg, i64) {
    (e, tag)
}

fn main() {
    let (mut e, t) = pair(mk_seq(5), -77);
    while let Some(v) = step(&mut e) {
        println!("s {}", v);
    }
    println!("t {}", t);

    let (mut l, t2) = pair(mk_lit('Z'), 42);
    while let Some(v) = step(&mut l) {
        println!("c {}", v);
    }
    println!("t {}", t2);

    // A SECOND buffer, different seed and a different live range, so a single
    // hard-coded stride or a cached offset cannot pass both.
    let (mut e2, t3) = pair(mk_seq(200), i64::MIN + 1);
    while let Some(v) = step(&mut e2) {
        println!("s2 {}", v);
    }
    println!("t {}", t3);

    let (mut l2, t4) = pair(mk_lit('\u{1F600}'), 0);
    while let Some(v) = step(&mut l2) {
        println!("c2 {}", v);
    }
    println!("t {}", t4);
}
