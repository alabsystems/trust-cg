// CORPUS FIXTURE — a THIN raw pointer whose POINTEE is a `&dyn Trait` fat
// pointer: `*const &dyn Shape` / `*mut &dyn Shape` / `NonNull<&dyn Shape>`, the
// machinery of `slice::Iter<'_, &dyn Trait>` (`new`, `next`, `size_hint`,
// `as_ref`, `add`, `offset_from_unsigned`, `NonNull::eq`) that
// `Formatter::debug_tuple_fields_finish` walks over `&[&dyn Debug]` — 16
// `library/core` roots. The type mapper had no arm for a `&dyn` pointee behind a
// raw pointer; it now types the pointee as the two-lane `{data, vtable}` image
// (the same answer `&&dyn` gets), and every access takes its numbers from
// rustc: a 16-byte stride, a two-lane `*q` load, `ptr == end` on the thin
// pointer. A dropped vtable lane changes which `val()` runs; a wrong stride
// changes the element count and the `/ 16` term; a wrong `ptr == end` loops
// forever or stops early.
trait Shape {
    fn val(&self) -> i64;
}
struct Sq(i64);
struct Ci(i64);
struct Tri(i64);
impl Shape for Sq {
    fn val(&self) -> i64 {
        self.0 * self.0
    }
}
impl Shape for Ci {
    fn val(&self) -> i64 {
        self.0 * 3
    }
}
impl Shape for Tri {
    fn val(&self) -> i64 {
        self.0 + 100
    }
}

/// `slice::Iter<&dyn Shape>::{new, next, size_hint}` through `xs.iter()`.
#[inline(never)]
fn walk(xs: &[&dyn Shape]) -> i64 {
    let mut acc = 0;
    let mut n = 0;
    for s in xs.iter() {
        acc = acc * 7 + s.val();
        n += 1;
    }
    acc + n * 1_000_000 + (xs.iter().len() as i64) * 10_000_000
}

/// Explicit `*const &dyn Shape` arithmetic: `add`, `==`, the two-lane `*q`
/// load, `offset_from_unsigned`, and `NonNull<&dyn>::{from_ref, as_ref, as_ptr,
/// cast_const}`.
#[inline(never)]
fn raw(xs: &[&dyn Shape]) -> i64 {
    let p: *const &dyn Shape = xs.as_ptr();
    let end = unsafe { p.add(xs.len()) };
    let mut acc = 0;
    for i in 0..xs.len() {
        let q = unsafe { p.add(i) };
        if q == end {
            acc += 1_000_000_000;
        }
        let s: &dyn Shape = unsafe { *q };
        acc += s.val();
    }
    let nn = core::ptr::NonNull::from_ref(&xs[1]);
    acc + unsafe { nn.as_ref().val() }
        + unsafe { end.offset_from_unsigned(p) as i64 } * 1000
        + ((nn.as_ptr().cast_const() as usize - p as usize) / 16) as i64 * 100
}

/// The store twin: `*p = v` with `p: *mut &dyn Shape` (an `IterMut<&dyn>`-style
/// swap through the raw pointer), then the swapped slice is walked again.
#[inline(never)]
fn swap_first_last(xs: &mut [&dyn Shape]) -> i64 {
    let p: *mut &dyn Shape = xs.as_mut_ptr();
    let n = xs.len();
    unsafe {
        let first: &dyn Shape = *p;
        let last: &dyn Shape = *p.add(n - 1);
        *p = last;
        *p.add(n - 1) = first;
    }
    walk(xs)
}

fn main() {
    let (a, b, c) = (Sq(7), Ci(5), Tri(9));
    let mut v: [&dyn Shape; 3] = [&a, &b, &c];
    println!("{} {} {}", walk(&v), raw(&v), walk(&v[1..]));
    println!("{}", swap_first_last(&mut v));
    let e: [&dyn Shape; 0] = [];
    println!("{}", walk(&e));
}
