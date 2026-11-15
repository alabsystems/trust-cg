// Corpus: a whole-aggregate copy of a NESTED scalar-leaf aggregate from a
// scalarized temp into a memory-backed (loop-carried) local.
//
// `flat_scalar_aggregate_copy_plan` handled only FLAT aggregates — leaf count ==
// sized layout field count — because the flat plan names each leaf by its MIR
// FIELD INDEX. `Outer` here has ONE layout field whose own type has TWO scalar
// leaves, which is the `str::iter::Chars` shape (one field, an inner
// `slice::Iter<u8>`, two leaves), and it declined. The consumer then failed with
// "ADT Use source field 0 before aggregate binding" — a message that reads like a
// lowering-ORDER problem and is not one.
//
// The nested plan enumerates leaves in the SAME declaration-order DFS the
// scalarized source's `projected_values` were bound in and uses the flat DFS
// position as the binding index — the identical scheme the nested field-OPERAND
// path already uses, so the two agree by construction.
//
// THE PLAN IS STILL FORMALLY CHECKED, by a DIFFERENT property. A nested plan has
// more leaf spans than layout fields, which the 1:1 `verify_field_copy_tiling`
// cannot express; `verify_nested_field_copy_tiling` states the generalization —
// the leaves TILE the fields: pairwise disjoint, each inside one field, each
// field covered exactly, no gap and no straddle — against the same INDEPENDENT
// rustc layout rather than against the leaf recursion itself.
//
// BOUNDARY, deliberately not exercised here because it must keep FAILING CLOSED:
// a nested field with INTERNAL PADDING (`Inner { a: i64, b: i32 }` — 16 bytes,
// leaves covering only 12) is REFUSED by that verifier with "layout field 0 is
// covered only to byte 12 but extends to 16". That is the check working: the
// emitter would leave 4 bytes of the destination unwritten. Measured.
//
// `n 106 11` — four iterations, each building a scalarized temp and writing it
// back whole; `a` accumulates 0+1+2+3 onto 100 and `b` increments per iteration.
// A wrong leaf offset swaps the two fields and prints `11 106`; a dropped leaf
// leaves one at its initial value.
#![allow(dead_code)]

#[derive(Clone, Copy)]
struct Inner {
    a: i64,
    b: i64,
}

#[derive(Clone, Copy)]
struct Outer {
    inner: Inner,
}

#[inline(never)]
fn step(o: Outer, k: i64) -> Outer {
    Outer {
        inner: Inner {
            a: o.inner.a + k,
            b: o.inner.b + 1,
        },
    }
}

fn main() {
    let mut acc = Outer {
        inner: Inner { a: 100, b: 7 },
    };
    let mut i = 0i64;
    while i < 4 {
        let t = step(acc, i);
        acc = t;
        i += 1;
    }
    let a = acc.inner.a;
    let b = acc.inner.b;
    println!("n {} {}", a, b); // 106 11
}
