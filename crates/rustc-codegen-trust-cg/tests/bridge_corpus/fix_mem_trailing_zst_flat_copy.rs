// Corpus: a flat scalar-leaf aggregate with a TRAILING ZERO-SIZED field
// (`PhantomData`) — `slice::Iter<'a, T>`'s exact shape — moved whole across the
// scalarized <-> memory boundary.
//
// `flat_scalar_aggregate_copy_plan` compared the SCALARIZED leaf count (which
// drops ZSTs — a ZST carries no lane) against `layout.fields.count()` (which does
// not), so every aggregate with a `PhantomData` declined the plan. The
// memory->scalarized whole read then never ran, and the shape fell through to
// `lower_scalarized_aggregate_use`, which reported "ADT Use source field 0 before
// aggregate binding" — a message that reads like a lowering ORDER problem and is
// not one: measured 2026-09-14, the source was a whole MEMORY-BACKED
// `slice::Iter<T>` entry arg with `fields_bound=[]` and `any_proj=false`, i.e. no
// scalarized binding at all, ever. Three `library/core` roots
// (`<Zip<IterMut<u8>, Iter<u8>>>::new` and its `u32` / `&str`+`&dyn` siblings).
//
// The count is now taken over the SIZED layout fields on both sides, and
// `verify_aggregate_field_copy_plan` likewise skips zero-size layout spans (a
// zero-byte span is vacuously covered and nothing about it can be copied wrong).
//
// SOUNDNESS BOUNDARY, unchanged: only a TRAILING ZST is admitted. A ZST that
// PRECEDES a sized field shifts the MIR-field-index-to-lane mapping every consumer
// of these projected values assumes, which is a measured divergence class; it
// still declines through `zero_sized_field_precedes_sized_field`, and
// `fix_e_zst_first_field_by_ref` / `fix_e_zst_tuple_by_ref` /
// `fix_k_zst_newtype_first_field` are its rows.
//
// NOTE ON WHAT THIS ROW PROVES. It MATCHES on both the pre- and post-fix backend:
// in a user crate this shape already lowered, and the three roots it is derived
// from are only reachable when `core` is compiled AS A LIBRARY (in user code the
// `zip()` interception takes over before `Zip::new` is a required root). It is a
// REGRESSION pin for the trailing-ZST plan, not a watched-failing row; the
// evidence for the fix is the census delta (-3 roots, 0 new failures).
#![allow(dead_code)]
use core::marker::PhantomData;

// `slice::Iter<'a, T>`'s exact shape: two scalar fields then a TRAILING ZST.
struct Cur<'a> {
    p: *const u8,
    n: i64,
    tag: i64,
    _m: PhantomData<&'a u8>,
}

#[inline(never)]
fn make<'a>(s: &'a [u8]) -> Cur<'a> {
    Cur {
        p: s.as_ptr(),
        n: s.len() as i64,
        tag: 7,
        _m: PhantomData,
    }
}

// The `Zip::new(a, b)` shape: whole-aggregate moves of by-value params into a
// constructed aggregate.
struct Pair<'a> {
    a: Cur<'a>,
    b: Cur<'a>,
    n: i64,
}

#[inline(never)]
fn zip<'a>(a: Cur<'a>, b: Cur<'a>, n: i64) -> Pair<'a> {
    Pair { a, b, n }
}

#[inline(never)]
fn drain(c: &Cur<'_>) -> i64 {
    let mut acc = 0i64;
    let mut i = 0i64;
    while i < c.n {
        acc = acc * 10 + unsafe { *c.p.offset(i as isize) } as i64;
        i += 1;
    }
    acc
}

#[inline(never)]
fn seed() -> u8 { 3 }

#[inline(never)]
fn run(a: &[u8], b: &[u8], n: i64) -> i64 {
    let z = zip(make(a), make(b), n);
    drain(&z.a) * 1_000_000 + drain(&z.b) * 1000 + z.n + z.a.tag * 10 + z.b.tag
}

fn main() {
    let a = [seed(), 5, 7];
    let b = [seed() + 1, 2];
    println!("a {}", run(&a, &b, 99));
    let e: [u8; 0] = [];
    println!("b {}", run(&e, &a[1..], -7));
    println!("c {}", run(&a[2..], &e, 1));
}
