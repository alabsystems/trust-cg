// Corpus: a NICHE-ENCODED multi-variant enum written as a WHOLE VALUE through a
// `&mut` field projection — `(*r).field = move _src`.
//
// `char` has invalid bit patterns, so `Option<(u64, char)>` stores its
// discriminant INSIDE the payload's spare patterns: there is NO separate tag
// byte. The fixed-offset field-map store path must decline such a destination,
// because reconstructing the value field-by-field requires knowing which variant
// is live. The fix is a whole-value BYTE COPY, which carries payload bytes and
// niche bytes together and never decides a variant at all.
//
// WHY THE TEMPTING FIX IS A FALSE PROVE. The apparent move is to relax
// `require_tagless_single_variant_aggregate` to admit "any enum rustc lays out
// compactly". `Result<(), fmt::Error>` and `Option<NonZeroU8>` have an IDENTICAL
// repr signature and OPPOSITE semantics — under `TagEncoding::Niche` the scalar
// IS the payload, not a tag — so that widening silently miscompiles every
// `Some(x)` while the census scores it as progress.
//
// WHAT EACH ROW CATCHES:
//   * `z` / `n`  — a `None` written through the projection reads back as `None`.
//   * `s`        — a `Some` payload survives the copy intact (`777`, `'Q'`=81).
//   * `e`        — THE NICHE ROW: `Some((0, '\u{0}'))` is an ALL-ZERO payload that
//                  must still read as `Some`. A model that reconstructs the
//                  discriminant from payload bytes, or that zeroes the niche,
//                  reports `None` here and prints `0 0 0` instead of `1 0 0`.
//   * `before` / `after` flank the enum field in the struct, so a wrong
//     destination offset shows up as a shifted neighbour rather than silently.
#![allow(dead_code)]

struct Holder {
    before: i64,
    slot: Option<(u64, char)>,
    after: i64,
}

#[inline(never)]
fn set(h: &mut Holder, v: Option<(u64, char)>) {
    h.slot = v;
}

#[inline(never)]
fn read(h: &Holder) -> (i64, u64, u32, i64, i64) {
    match h.slot {
        Some((n, c)) => (1, n, c as u32, h.before, h.after),
        None => (0, 0, 0, h.before, h.after),
    }
}

fn main() {
    let mut h = Holder {
        before: 3,
        slot: None,
        after: 4,
    };

    let (t0, n0, c0, b0, a0) = read(&h);
    println!("z {} {} {} {} {}", t0, n0, c0, b0, a0); // 0 0 0 3 4

    set(&mut h, Some((777, 'Q')));
    let (t1, n1, c1, b1, a1) = read(&h);
    println!("s {} {} {} {} {}", t1, n1, c1, b1, a1); // 1 777 81 3 4

    set(&mut h, None);
    let (t2, n2, c2, b2, a2) = read(&h);
    println!("n {} {} {} {} {}", t2, n2, c2, b2, a2); // 0 0 0 3 4

    set(&mut h, Some((0, '\u{0}')));
    let (t3, n3, c3, b3, a3) = read(&h);
    println!("e {} {} {} {} {}", t3, n3, c3, b3, a3); // 1 0 0 3 4
}
