// A by-value AGGREGATE read straight out of `&self` — `_0 = copy ((*_1).0)`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// UNPATCHED every accessor below fails closed with "nested aggregate field
// operand uses a projection". On `library/core` this is exactly three roots —
// `Ipv4Addr::octets`, `Ipv6Addr::octets`, `Ipv6Addr::segments` — i.e. the
// `fn f(&self) -> [T; N] { self.field }` accessor, which is one of the most
// ordinary shapes a Rust struct has.
//
// The destination is a memory-backed slot; the SOURCE is a projection whose base
// is a thin reference rather than a memory-backed local, and only the latter base
// was admitted. The address arithmetic is identical (`base + field_offset`), so
// the fix is which bases are resolved, not how the bytes move.
//
// A wrong answer is SILENT here: reading from the wrong offset, or through the
// wrong base, yields a well-typed array of the wrong bytes. Every row therefore
// prints RUNTIME VALUES, element by element, and the fields are given distinct
// values and a NON-ZERO offset so an off-by-one-field or offset-0 bug shows up.

#[derive(Clone, Copy)]
struct Inner {
    a: u16,
    b: u16,
}

struct V4 {
    lead: u32,
    octets: [u8; 4],
}

struct Holder {
    tag: u64,
    inner: Inner,
}

impl V4 {
    // The `Ipv4Addr::octets` shape exactly: a by-value array returned out of a
    // shared reference, from a NON-ZERO field offset.
    #[inline(never)]
    fn octets(&self) -> [u8; 4] {
        self.octets
    }
}

impl Holder {
    // The same shape with a nested STRUCT (not an array) leaf.
    #[inline(never)]
    fn inner(&self) -> Inner {
        self.inner
    }

    // The same read as an aggregate FIELD operand rather than a whole return:
    // `Wrap { inner: (*self).inner, n }` builds a second aggregate whose field
    // operand is the deref projection.
    #[inline(never)]
    fn wrapped(&self, n: u64) -> Wrap {
        Wrap { inner: self.inner, n }
    }
}

struct Wrap {
    inner: Inner,
    n: u64,
}

// The RAW-POINTER base, which resolves through the same arm.
#[inline(never)]
unsafe fn octets_raw(p: *const V4) -> [u8; 4] {
    (*p).octets
}

// Every printed value is produced by its OWN `#[inline(never)]` scalar-returning
// helper: a `println!` whose argument is an element of a memory-backed array is a
// separate (unrelated) bridge gate, and a fixture must fail for its OWN reason.
#[inline(never)]
fn octet(v: &V4, i: usize) -> u32 {
    v.octets()[i] as u32
}

#[inline(never)]
fn octet_raw(v: &V4, i: usize) -> u32 {
    unsafe { octets_raw(v as *const V4)[i] as u32 }
}

#[inline(never)]
fn inner_a(h: &Holder) -> u32 {
    h.inner().a as u32
}

#[inline(never)]
fn inner_b(h: &Holder) -> u32 {
    h.inner().b as u32
}

#[inline(never)]
fn wrap_a(h: &Holder, n: u64) -> u32 {
    h.wrapped(n).inner.a as u32
}

#[inline(never)]
fn wrap_b(h: &Holder, n: u64) -> u32 {
    h.wrapped(n).inner.b as u32
}

#[inline(never)]
fn wrap_n(h: &Holder, n: u64) -> u64 {
    h.wrapped(n).n
}

fn main() {
    let v = V4 { lead: 0xDEAD_BEEF, octets: [11, 22, 33, 44] };
    println!("{}", octet(&v, std::hint::black_box(0)));
    println!("{}", octet(&v, std::hint::black_box(1)));
    println!("{}", octet(&v, std::hint::black_box(2)));
    println!("{}", octet(&v, std::hint::black_box(3)));
    // The LEADING field must be untouched by the read — a base resolved at
    // offset 0 instead of the field offset would print these bytes instead.
    let lead = v.lead;
    println!("{}", lead);
    println!("{}", octet_raw(&v, std::hint::black_box(0)));
    println!("{}", octet_raw(&v, std::hint::black_box(3)));

    let h = Holder { tag: 0x0102_0304_0506_0708, inner: Inner { a: 4097, b: 8193 } };
    println!("{}", inner_a(&h));
    println!("{}", inner_b(&h));
    let tag = h.tag;
    println!("{}", tag);
    println!("{}", wrap_a(&h, std::hint::black_box(77)));
    println!("{}", wrap_b(&h, std::hint::black_box(77)));
    println!("{}", wrap_n(&h, std::hint::black_box(77)));
}
