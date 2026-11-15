// Corpus: a reference to a DST whose unsized TAIL is `dyn Trait`.
//
// `core::error::Request<'a>(Tagged<dyn Erased<'a>>)`, where
// `Tagged<E: ?Sized> { tag_id: TypeId, value: E }` — a sized prefix and a `dyn`
// tail. `&Request` is therefore a `{ data, VTABLE }` fat pointer, exactly like
// `&dyn Trait`, and rustc passes it as TWO pointer-width lanes.
//
// The bridge used to see only the KIND-based `is_trait_object_reference_ty`
// (pointee must be `ty::Dynamic`), so `&Tagged<dyn Er>` missed the two-lane
// branch and fell into the by-value AGGREGATE branch, which tried to flatten an
// UNSIZED pointee into scalar leaves. That walk died on `Tagged`'s `TypeId`
// field — `[*const (); 16 / size_of::<*const ()>()]`, an array whose length is
// an unevaluated anon const — and the refusal therefore NAMED AN ARRAY, which is
// nowhere near the actual problem. Found by arming the type-lowering trace and
// reading the captured backtrace:
//
//     classify_func_ty -> memory_aggregate_layout
//       -> scalar_field_aggregate_trust_ir_fields
//       -> scalar_leaf_trust_ir_fields_inner -> rust_ty_to_trust_ir_ty
//
// WHY THIS IS NOT A WIDENING OF THE TRAIT-OBJECT PREDICATE: that predicate has
// 37 call sites and they MIX representation with vtable DISPATCH. A
// `&Tagged<dyn Er>` is a `{data, vtable}` PAIR, but it is NOT a dispatchable
// trait-object receiver — its vtable belongs to the TAIL, and the struct around
// the tail has no trait of its own. So `is_dyn_tail_fat_ref_ty` is deliberately
// DISJOINT (a bare `&dyn` returns false from it) and the two are combined only
// by `is_vtable_pair_abi_ref_ty`, used at exactly the four REPRESENTATION sites:
// the aggregate-lane decline, the declaration, the entry-block params, and the
// call-argument expansion. Every dispatch site keeps the strict predicate.
//
// SCOPE, and it is the honest boundary of this lane: the reference can be
// CONSTRUCTED, PASSED and FORWARDED, but not READ THROUGH. Reading even a SIZED
// PREFIX field (`t.tag`) still fails closed — the byte-offset memory model has
// no fixed size for the pointee. `<Request as Debug>::fmt` never reads through
// its `&self` either (`f.debug_struct("Request").finish_non_exhaustive()`),
// which is exactly why it is the root this closes.
//
// WHY EVERY ROW IS A WRONG NUMBER, NOT A CRASH, IF THE LANE COUNT IS WRONG: the
// fat reference is followed by ORDINARY arguments. If it occupied ONE lane
// instead of two, every later argument would be read from the wrong register —
// a wrong number, silently.
//   * `one 304 506` — two different concrete tails (`i64`, `u8`) erased to the
//     same `dyn Er`, each called with distinct trailing args. Two tails means a
//     lowering that reused one vtable is caught.
//   * `relay 406 608` — the fat reference FORWARDED across a second ABI
//     boundary, so the two lanes must survive as a pair, and the trailing args
//     are perturbed (+1/+2) so a stale-register read shows up as the old value.
#![allow(dead_code)]

trait Er {
    fn v(&self) -> i64;
}
impl Er for i64 {
    fn v(&self) -> i64 {
        *self
    }
}
impl Er for u8 {
    fn v(&self) -> i64 {
        *self as i64
    }
}

struct Tagged<E: ?Sized> {
    tag: i64,
    value: E,
}

#[inline(never)]
fn ignores(_t: &Tagged<dyn Er>, a: i64, b: i64) -> i64 {
    a * 100 + b
}

#[inline(never)]
fn relay(t: &Tagged<dyn Er>, a: i64, b: i64) -> i64 {
    ignores(t, a + 1, b + 2)
}

fn main() {
    let x: Tagged<i64> = Tagged { tag: 7, value: 100 };
    let y: Tagged<u8> = Tagged { tag: 9, value: 5 };
    let rx: &Tagged<dyn Er> = &x;
    let ry: &Tagged<dyn Er> = &y;
    println!("one {} {}", ignores(rx, 3, 4), ignores(ry, 5, 6)); // 304 506
    println!("relay {} {}", relay(rx, 3, 4), relay(ry, 5, 6)); // 406 608
}
