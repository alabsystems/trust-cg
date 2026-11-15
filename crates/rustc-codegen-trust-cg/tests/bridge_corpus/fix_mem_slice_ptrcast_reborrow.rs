// Corpus: a fat -> fat `PtrToPtr` CAST feeding a REBORROW — `&*(s as *const [U])`.
//
// `lower_memory_slice_assign` has had the fat->fat `PtrToPtr` lowering arm (a
// verbatim `{data, len}` lane copy) since the cast-const lane. But that arm only
// runs for a destination the memory-backing pass CLASSIFIED as a runtime slice,
// and the classifier's cast list (`compute_memory_backed_locals` rule 3b) named
// `Unsize` and `Transmute` and NOT `PtrToPtr`. So the destination of such a cast
// got no slot, the cast bound it as a single SCALAR — the data half alone, the
// LENGTH silently dropped — and the following reborrow failed closed on it
// ("memory-backed slice reborrow source is neither a memory-backed slice nor a
// const-slice binding").
//
// Measured 2026-09-14 on a `library/core` census, that was 6 failed roots:
// `<[MaybeUninit<T>]>::assume_init_ref` / `assume_init_mut`,
// `<[AsciiChar]>::as_str` and `str::from_utf8_unchecked_mut` — every one of them
// the same `&*(self as *const [T])` transmute-by-cast idiom.
//
// A fat->fat pointer cast is defined as a BITWISE copy of `{data, metadata}`
// (the element count is never rescaled — that would be `from_raw_parts`, an
// `AggregateKind::RawPtr`), so the destination is exactly as much a runtime
// slice as the source, and the lowering arm that was already there is the right
// one.
//
// WHAT A WRONG LOWERING LOOKS LIKE, AND WHAT PINS IT: every case prints a value
// built from the LENGTH (`len * 1_000_000`) as well as the elements, at three
// different lengths including ZERO, so a dropped, stale or rescaled metadata
// lane changes stdout rather than merely refusing. `seed()` is `#[inline(never)]`
// so the inputs are not const-folded away at `-O2` (a const-folded row would
// exercise the const-slice binding, which is a different path).
#![allow(dead_code)]
use core::mem::MaybeUninit;

#[inline(never)]
fn sum_with_len(s: &[u8]) -> i64 {
    let mut acc = s.len() as i64 * 1_000_000;
    for b in s { acc += *b as i64; }
    acc
}

#[inline(never)]
fn init_ref(buf: &[MaybeUninit<u8>]) -> i64 { sum_with_len(unsafe { buf.assume_init_ref() }) }

#[inline(never)]
fn cast_reborrow(s: &[i8]) -> i64 {
    let p = s as *const [i8] as *const [u8];
    sum_with_len(unsafe { &*p })
}

#[inline(never)]
fn as_str_len(v: &[u8]) -> i64 {
    let s: &str = unsafe { core::str::from_utf8_unchecked(v) };
    let mut acc = s.len() as i64 * 1_000_000;
    for b in s.as_bytes() { acc += *b as i64; }
    acc
}

#[inline(never)]
fn seed() -> u8 { 4 }

fn main() {
    let x: u8 = seed();
    let buf: [MaybeUninit<u8>; 3] =
        [MaybeUninit::new(x), MaybeUninit::new(x + 2), MaybeUninit::new(x + 4)];
    println!("a {}", init_ref(&buf));
    println!("b {}", init_ref(&buf[1..]));
    println!("c {}", init_ref(&buf[..0]));
    let arr = [seed() as i8 - 3, 2, 3, 4];
    println!("d {}", cast_reborrow(&arr));
    println!("e {}", cast_reborrow(&[]));
    let hb = [seed() + 100, b'e', b'l', b'l', b'o'];
    println!("f {}", as_str_len(&hb));
    println!("g {}", as_str_len(b""));
}
