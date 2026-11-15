// Corpus: the FAT -> THIN pointer cast seam, and the `repr(transparent)` fat
// pointer CARRIER (`NonNull<[T]>` / `NonNull<str>`) that reaches it.
//
// A fat pointer is `{data, metadata}`; narrowing it to a thin pointer keeps the
// data half and discards the metadata. That is what `*const [T] as *const T`,
// `*mut str as *mut u8` and `NonNull::<[T]>::cast::<T>()` all are, and it is
// lossless in this direction. Before the seam the narrowing had no arm: it
// worked only by accident, because `rust_ty_to_trust_ir_ty` mapped the CARRIER
// to a single thin `Ptr` — i.e. by never having modeled the metadata at all.
// That is the silent-truncation channel (miscompile class `3b9b89a8`) reached
// through the non-null niche, measured at 2,965 leaf-walk visits on one
// `library/core` compile.
//
// WHAT EACH ROW WOULD CATCH.
//  * `nn_cast` / `raw_cast_const` / `raw_cast_str`: the pure narrowing. Every
//    printed value is an ELEMENT read through the thin pointer, and `.add(k)`
//    reaches a LATER element — so a data half taken from the wrong lane, or a
//    wrong stride, changes stdout rather than merely refusing.
//  * `cast_and_len`: the same carrier's METADATA half, read beside the cast.
//    A carrier modeled as one thin `Ptr` cannot answer this at all (measured:
//    "slice pointer metadata before known array length"), so a wrong length is
//    a visible number, not a refusal.
//  * `str_carrier_as_ref`: the carrier reached through a THIN REFERENCE
//    (`&NonNull<str>`), the `NonNull::<str>::as_ref` shape — both lanes are
//    loaded from the pointee's bytes rather than from a slot.
#![allow(dead_code)]

use std::ptr::NonNull;

#[inline(never)]
fn nn_cast(s: &[u8]) -> (u8, u8) {
    let nn: NonNull<[u8]> = NonNull::from(s);
    let thin: NonNull<u8> = nn.cast::<u8>();
    unsafe { (*thin.as_ptr(), *thin.as_ptr().add(1)) }
}

#[inline(never)]
fn raw_cast_const(s: &[u8]) -> (u8, u8) {
    let p: *const [u8] = s as *const [u8];
    let t: *const u8 = p as *const u8;
    unsafe { (*t, *t.add(2)) }
}

#[inline(never)]
fn raw_cast_str(s: &str) -> (u8, u8) {
    let p: *const str = s as *const str;
    let t: *const u8 = p as *const u8;
    unsafe { (*t, *t.add(1)) }
}

#[inline(never)]
fn cast_and_len(s: &[u8]) -> (u8, u8, usize) {
    let nn: NonNull<[u8]> = NonNull::from(s);
    let len = nn.len();
    let thin: NonNull<u8> = nn.cast::<u8>();
    unsafe { (*thin.as_ptr(), *thin.as_ptr().add(1), len) }
}

#[inline(never)]
fn str_carrier_as_ref(s: &str) -> (usize, u8) {
    let nn: NonNull<str> = NonNull::from(s);
    let back: &str = unsafe { nn.as_ref() };
    (back.len(), back.as_bytes()[1])
}

fn main() {
    let a: [u8; 5] = [11, 22, 33, 44, 55];

    let (x, y) = nn_cast(&a);
    println!("c1 {} {}", x, y);
    let (p, q) = raw_cast_const(&a[1..]);
    println!("c2 {} {}", p, q);
    let (m, n) = nn_cast(&a[3..]);
    println!("c3 {} {}", m, n);
    let (u, v) = raw_cast_str("hello");
    println!("c4 {} {}", u, v);

    let (bx, by, bl) = cast_and_len(&a);
    println!("c5 {} {} {}", bx, by, bl);
    let (cx, cy, cl) = cast_and_len(&a[2..]);
    println!("c6 {} {} {}", cx, cy, cl);

    let (sl, sb) = str_carrier_as_ref("worlds");
    println!("c7 {} {}", sl, sb);
}
