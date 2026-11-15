// CORPUS FIXTURE — the `repr(transparent)` WIDE-POINTER CARRIER build.
//
// WHAT IT PINS. `lower_memory_slice_assign`'s `Rvalue::Aggregate(Adt(..))` arm:
// the construction of a `repr(transparent)` carrier of a `{ data, len }` wide
// pointer out of the pointer it wraps. `core::ptr::Unique::<T>::new_unchecked`
// is this one statement —
//
//     _0 = Unique::<T> { pointer: move _2, _marker: const PhantomData }
//
// — and it is the last step of every `Box<DST>` construction, so it was measured
// (2026-09-26, `-Copt-level=0`) as 4 of `library/alloc`'s 37 failed roots:
// `Unique::<[u8]>::new_unchecked`, `Unique::<str>`, `Unique::<CStr>` and
// `Unique::<[MaybeUninit<u8>]>`. `Owned<T>` below is that shape with a local
// name, and its `new` reproduces the refusal verbatim on the unpatched tree
// (`memory-backed slice assignment Rvalue::Aggregate`, one root per `T`).
//
// WHY EVERY PRINTED VALUE IS A LENGTH. The whole content of the lowering is that
// BOTH lanes move: a data-only store compiles fine and prints a length of 0.
// Mutation-measured: forcing the metadata lane to a constant in the new arm makes
// this fixture print `u8 0 10 50` against LLVM's `u8 5 10 50`. So the `len` column
// — not merely "did it compile" — is what this row gates.
//
// THE THREE `T`s separate the failure modes a single one would hide: `[u8]`
// (stride 1, where a byte count and an element count coincide), `[u32]` (stride
// 4, where a rescaled count prints 12 instead of 3), and `str` (a multi-byte
// UTF-8 literal, where a char count prints 4 instead of 7).
//
// The length and the elements are read behind `#[inline(never)]` accessors and
// bound to plain locals before `println!`: the format interception refused a
// placeholder whose value is a slice `.len()` (`[TCG-FMT-LEN]`, removed
// 2026-10-03) and refuses a projected borrow (`[TCG-FMT-ARGPLACE]`), neither of
// which is this lane.
#![allow(dead_code)]

use std::marker::PhantomData;
use std::ptr::NonNull;

#[repr(transparent)]
struct Owned<T: ?Sized> {
    p: NonNull<T>,
    _m: PhantomData<T>,
}

impl<T: ?Sized> Owned<T> {
    #[inline(never)]
    unsafe fn new(p: *mut T) -> Owned<T> {
        Owned {
            p: NonNull::new_unchecked(p),
            _m: PhantomData,
        }
    }
    #[inline(never)]
    fn raw(&self) -> *mut T {
        self.p.as_ptr()
    }
}

#[inline(never)]
fn len_u8(s: &[u8]) -> usize {
    s.len()
}
#[inline(never)]
fn nth_u8(s: &[u8], i: usize) -> u8 {
    unsafe { *s.as_ptr().add(i) }
}
#[inline(never)]
fn len_u32(s: &[u32]) -> usize {
    s.len()
}
#[inline(never)]
fn nth_u32(s: &[u32], i: usize) -> u32 {
    unsafe { *s.as_ptr().add(i) }
}
#[inline(never)]
fn len_str(s: &str) -> usize {
    s.len()
}
#[inline(never)]
fn nth_str(s: &str, i: usize) -> u8 {
    unsafe { *s.as_ptr().add(i) }
}

fn main() {
    let mut bytes: [u8; 5] = [10, 20, 30, 40, 50];
    let bs: *mut [u8] = &mut bytes[..] as *mut [u8];
    let ob: Owned<[u8]> = unsafe { Owned::new(bs) };
    let br: *mut [u8] = ob.raw();
    let bv: &[u8] = unsafe { &*br };
    let bl = len_u8(bv);
    let b0 = nth_u8(bv, 0);
    let b4 = nth_u8(bv, 4);
    println!("u8 {} {} {}", bl, b0, b4);

    let mut words: [u32; 3] = [7, 8, 9];
    let ws: *mut [u32] = &mut words[..] as *mut [u32];
    let ow: Owned<[u32]> = unsafe { Owned::new(ws) };
    let wr: *mut [u32] = ow.raw();
    let wv: &[u32] = unsafe { &*wr };
    let wl = len_u32(wv);
    let w0 = nth_u32(wv, 0);
    let w2 = nth_u32(wv, 2);
    println!("u32 {} {} {}", wl, w0, w2);

    let s: &str = "a\u{e9}\u{4e2d}b";
    let sp: *mut str = s as *const str as *mut str;
    let os: Owned<str> = unsafe { Owned::new(sp) };
    let sr: *mut str = os.raw();
    let sv: &str = unsafe { &*sr };
    let sl = len_str(sv);
    let s0 = nth_str(sv, 0);
    let s6 = nth_str(sv, 6);
    println!("str {} {} {}", sl, s0, s6);
}
