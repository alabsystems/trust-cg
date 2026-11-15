// CORPUS FIXTURE — `size_of_val` / `align_of_val` reached through a GENERIC body.
//
// WHY THIS SHAPE. rustc's `LowerIntrinsics` MIR pass const-folds both intrinsics
// wherever `T` is CONCRETE at the call site, so a direct `size_of_val(&x)` never
// reaches a backend at all. What reaches one is the call inside a body that is
// generic over `T: ?Sized` (`core::alloc::Layout::for_value{,_raw}`,
// `core::ptr::Alignment::of_val_raw`, and the two `#[inline(never)]` helpers
// here) monomorphized at a concrete `T`. That is exactly the five
// `library/alloc` census roots this lane covers: `for_value_raw::<io::Custom>`
// (SIZED), `for_value_raw::<[u8]>`, `for_value::<[u8]>`, `for_value::<CStr>`
// and `Alignment::of_val_raw::<Wtf8>` (a `repr(transparent)` wrapper of `[u8]`).
//
// The rows are chosen to separate the two modeled arms and their edge cases:
// a SIZED type with a non-1 alignment and trailing padding; a `[u8]` (stride 1,
// so `len * stride` is the length verbatim); a `[u32]` (stride 4, where a
// missing multiply prints 3 instead of 12); a `str` with multi-byte code points
// (so a char count cannot be mistaken for a byte count); and a `CStr`, a
// non-generic `#[repr(transparent)]` unsized wrapper whose metadata INCLUDES
// the nul terminator.
//
// Edition 2015 (the harness passes no `--edition`): no `c"..."` literals, no
// inline format captures.
#![allow(dead_code)]

use std::ffi::CStr;

#[inline(never)]
fn sz<T: ?Sized>(r: &T) -> usize {
    std::mem::size_of_val(r)
}

#[inline(never)]
fn al<T: ?Sized>(r: &T) -> usize {
    std::mem::align_of_val(r)
}

#[repr(align(4))]
struct Aligned4 {
    a: u8,
    b: u32,
}

// SLICE-TAILED DSTs with a SIZED PREFIX — `alloc::rc::RcInner<[u8]>` and
// `alloc::sync::ArcInner<[u8]>` in miniature. `Layout::for_value_raw::<RcInner<[u8]>>`
// is the `library/alloc` root that needs them, and its answer decides the size
// `Rc::allocate_for_slice` re-checks against what it just allocated: a size that is
// short by the round-up, or that forgets the prefix, is a heap-corruption bug rather
// than a wrong printed number.
//
// The rows separate every term of rustc's formula
// (`(fields.offset(last) + len * unit_size + full_align - 1) & -full_align`):
//   * `Tail<[u8]>`   — prefix align 8 dominates the unit align 1, so the round-up is
//                      what makes the answer right (16, not 11 + 5 = 16 by luck: see
//                      `tail_empty`, where the unrounded value would be 11);
//   * `Tail<[u32]>`  — stride 4, so a missing multiply prints 3 elements' worth;
//   * `WTail<[u32]>` — the TAIL's alignment (4) EXCEEDS the sized prefix's own (1),
//                      which is the case `layout.size` would get wrong and
//                      `fields.offset(last)` gets right;
//   * `CTail<[u64]>` — `repr(C)`, so the prefix padding is explicit;
//   * `Tail<[u8; 0]>`— an EMPTY tail, where the size is the ROUNDED prefix and
//                      nothing else;
//   * `WTail<[u8]>`  — `full_align == 1`, the one case where no round-up is emitted.
struct Tail<T: ?Sized> {
    a: u8,
    b: u64,
    c: u16,
    tail: T,
}

struct WTail<T: ?Sized> {
    n: u8,
    tail: T,
}

#[repr(C)]
struct CTail<T: ?Sized> {
    n: u32,
    tail: T,
}

fn main() {
    let bytes: [u8; 5] = [1, 2, 3, 4, 5];
    let b: &[u8] = &bytes;
    let words: [u32; 3] = [7, 8, 9];
    let w: &[u32] = &words;
    let s: &str = "aXYZb";
    let m: &str = "a\u{e9}\u{4e2d}b";
    let c: &CStr = unsafe { CStr::from_bytes_with_nul_unchecked(b"abc\0") };
    let a4 = Aligned4 { a: 1, b: 2 };
    let n: u64 = 7;
    let u: () = ();

    println!("u8slice {} {}", sz(b), al(b));
    println!("u32slice {} {}", sz(w), al(w));
    println!("asciistr {} {}", sz(s), al(s));
    println!("utf8str {} {}", sz(m), al(m));
    println!("cstr {} {}", sz(c), al(c));
    println!("sizedadt {} {}", sz(&a4), al(&a4));
    println!("u64 {} {}", sz(&n), al(&n));
    println!("unit {} {}", sz(&u), al(&u));
    // An EMPTY slice / str: `len * stride` must be 0, and the alignment must
    // still be the element's (4), not the size.
    let e: &[u32] = &words[0..0];
    let es: &str = &s[0..0];
    println!("emptyu32 {} {}", sz(e), al(e));
    println!("emptystr {} {}", sz(es), al(es));

    // Slice-tailed DSTs, reached by the `&S<[T; N]> -> &S<[T]>` unsize coercion.
    let t1: Tail<[u8; 5]> = Tail { a: 1, b: 2, c: 3, tail: [4, 5, 6, 7, 8] };
    let r1: &Tail<[u8]> = &t1;
    println!("tail_u8 {} {}", sz(r1), al(r1));

    let t2: Tail<[u32; 3]> = Tail { a: 1, b: 2, c: 3, tail: [4, 5, 6] };
    let r2: &Tail<[u32]> = &t2;
    println!("tail_u32 {} {}", sz(r2), al(r2));

    let t3: WTail<[u32; 3]> = WTail { n: 9, tail: [1, 2, 3] };
    let r3: &WTail<[u32]> = &t3;
    println!("wtail_u32 {} {}", sz(r3), al(r3));

    let t4: CTail<[u64; 2]> = CTail { n: 4, tail: [1, 2] };
    let r4: &CTail<[u64]> = &t4;
    println!("ctail_u64 {} {}", sz(r4), al(r4));

    let t5: Tail<[u8; 0]> = Tail { a: 1, b: 2, c: 3, tail: [] };
    let r5: &Tail<[u8]> = &t5;
    println!("tail_empty {} {}", sz(r5), al(r5));

    let t6: WTail<[u8; 3]> = WTail { n: 9, tail: [1, 2, 3] };
    let r6: &WTail<[u8]> = &t6;
    println!("wtail_u8 {} {}", sz(r6), al(r6));
}
