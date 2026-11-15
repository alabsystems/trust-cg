// Corpus: `<[T; N]>::map` and `core::array::from_fn` whose RESULT element is a
// length-metadata WIDE pointer (`&[u8]`, `&str`), and `map` over the
// `repr(transparent)` carrier `NonNull<[u8]>`. The other wide SOURCE elements
// are `fix_array_map_wide_element.rs`.
//
// The bridge intercepts both calls and builds the element loop itself. The
// closure body returns a wide value as rustc's two-value `PassMode::Pair`, and
// both lanes must land in the destination element at their rustc offsets. A
// carrier source is the same `{ data, len }` image as the pointer it wraps and
// crosses the call the same way.
//
// WHAT EACH ROW WOULD CATCH. Each summary prints a result's length and a byte
// read through its data lane, so a dropped or misplaced lane changes a number:
//  * `to_subslices`: `[usize; N] -> [&[u8]; N]`;
//  * `str_tails`: `[&str; N] -> [&str; N]` (wide on both sides);
//  * `from_fn_strs`: `array::from_fn` producing `[&str; N]`;
//  * `nonnull_lens`: a `NonNull<[u8]>` source element; a dropped length lane
//    prints a garbage length.
#![allow(dead_code)]

use std::hint::black_box as bb;
use std::ptr::NonNull;

static T: [u8; 5] = [1, 2, 3, 4, 5];

#[inline(never)]
fn to_subslices(a: [usize; 2]) -> [&'static [u8]; 2] {
    a.map(|i| &T[..i])
}

#[inline(never)]
fn str_tails(a: [&str; 2]) -> [&str; 2] {
    a.map(|s| &s[1..])
}

#[inline(never)]
fn from_fn_strs(k: usize) -> [&'static str; 3] {
    std::array::from_fn(|i| &"abcdef"[i + k..])
}

#[inline(never)]
fn nonnull_lens(a: [NonNull<[u8]>; 2]) -> [usize; 2] {
    a.map(|p| p.len())
}

/// Lengths and one byte of each wide result, computed out of line so the
/// printed values are plain integers.
#[inline(never)]
fn slice_summary(a: [&[u8]; 2]) -> [usize; 4] {
    let [x, y] = a;
    [x.len(), x[1] as usize, y.len(), y[3] as usize]
}

#[inline(never)]
fn str_summary2(a: [&str; 2]) -> [usize; 4] {
    let [x, y] = a;
    [
        x.len(),
        x.as_bytes()[0] as usize,
        y.len(),
        y.as_bytes()[0] as usize,
    ]
}

#[inline(never)]
fn str_summary3(a: [&str; 3]) -> [usize; 4] {
    let [x, _, z] = a;
    [
        x.len(),
        x.as_bytes()[0] as usize,
        z.len(),
        z.as_bytes()[0] as usize,
    ]
}

fn main() {
    // Every printed value is bound to a local first: the whole-program bridge
    // formats only call-stable places.
    let [u0, u1, u2, u3] = slice_summary(to_subslices(bb([2, 4])));
    println!("to_subslices {} {} {} {}", u0, u1, u2, u3);
    let [e0, e1, e2, e3] = str_summary2(str_tails(bb(["hello", "wor"])));
    println!("str_tails {} {} {} {}", e0, e1, e2, e3);
    let [f0, f1, f2, f3] = str_summary3(from_fn_strs(bb(1)));
    println!("from_fn_strs {} {} {} {}", f0, f1, f2, f3);
    let mut w = bb([4u8, 5, 6]);
    let (w0, w1) = w.split_at_mut(1);
    let [n0, n1] = nonnull_lens(bb([NonNull::from(w0), NonNull::from(w1)]));
    println!("nonnull_lens {} {}", n0, n1);
}
