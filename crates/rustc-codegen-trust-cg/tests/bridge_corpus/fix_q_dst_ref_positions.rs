// Corpus: a `&DST` fat reference in every POSITION a two-lane leaf can occupy.
//
// The companion to `fix_q_dst_slice_tail_ref.rs`, which covers the ACCESSES.
// This one covers the REPRESENTATION: every row puts a `&Bytes` (a reference to
// a `[u8]`-tailed DST, so a `{ data, len }` `ScalarPair`) next to ordinary
// scalars and reads the scalars BACK. If the reference is ever bound into ONE
// lane, the length is dropped and every field after it sits 8 bytes off — so the
// NEIGHBOUR prints wrong, which is a wrong number rather than a refusal.
//
// Each row also reads the reference's own METADATA (`count()`), so a model that
// keeps the data half but loses the length prints a wrong length too.
//
// Rows, and the one-lane symptom each would show:
//   e1 by-value STRUCT field between two `i64`s      -> `9` becomes `5`
//   e2 by-value TUPLE, same shape                    -> `9` becomes `5`
//   e3 ENUM PAYLOAD beside an `i64`                  -> `9` becomes `5`
//   e4 CLOSURE UPVAR beside an `i64`                 -> `9` becomes `5`
//   e6 `Option<&Bytes>` NICHE payload beside an `i64`-> `9` becomes `5`
//
// Every one of these REFUSED on the pre-lane backend (measured), so a wrong
// value here is a regression of this lane's own model, never of an older one.
#![allow(dead_code)]

#[repr(transparent)]
struct Bytes([u8]);

impl Bytes {
    #[inline(never)]
    fn new(b: &[u8]) -> &Bytes {
        unsafe { &*(b as *const [u8] as *const Bytes) }
    }
    #[inline(never)]
    fn count(&self) -> usize {
        self.0.len()
    }
}

struct S3<'a> {
    a: i64,
    r: &'a Bytes,
    b: i64,
}

#[inline(never)]
fn by_value(s: S3<'_>) -> (i64, usize, i64) {
    (s.a, s.r.count(), s.b)
}

#[inline(never)]
fn in_tuple(t: (i64, &Bytes, i64)) -> (i64, usize, i64) {
    (t.0, t.1.count(), t.2)
}

enum E<'a> {
    N(i64),
    B(&'a Bytes, i64),
}

#[inline(never)]
fn in_enum(e: &E<'_>) -> (i64, usize, i64) {
    match e {
        E::N(n) => (*n, 0, -1),
        E::B(r, k) => (0, r.count(), *k),
    }
}

#[inline(never)]
fn in_closure(r: &Bytes, k: i64) -> (usize, i64) {
    let f = move || (r.count(), k);
    f()
}

#[inline(never)]
fn in_option(o: Option<&Bytes>, k: i64) -> (usize, i64) {
    match o {
        Some(r) => (r.count(), k),
        None => (999, k),
    }
}

fn main() {
    let a: [u8; 5] = [11, 22, 33, 44, 55];
    let b = Bytes::new(&a);

    let (x1, y1, z1) = by_value(S3 { a: 7, r: b, b: 9 });
    println!("e1 {} {} {}", x1, y1, z1);

    let (x2, y2, z2) = in_tuple((7, b, 9));
    println!("e2 {} {} {}", x2, y2, z2);

    let (x3, y3, z3) = in_enum(&E::B(b, 9));
    println!("e3 {} {} {}", x3, y3, z3);

    let (x4, y4) = in_closure(b, 9);
    println!("e4 {} {}", x4, y4);

    let (x6, y6) = in_option(Some(b), 9);
    println!("e6 {} {}", x6, y6);
}
