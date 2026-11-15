// CORPUS FIXTURE — `v.extend([&a, &b])` appends `a` and `b`, not their
// addresses.
//
// WHAT IT PINS. alloc's `impl Extend<&'a T> for Vec<T>` takes a by-value
// `[&T; N]`. The by-value array source of `lower_vec_extend` discarded the
// array's element type and copied `N` elements of `size_of::<T>()` bytes typed
// as `T` out of an array of pointers: the Vec received the low bits of stack
// addresses. Measured on 6b108b81d at -O0/-O1: both `[&T; N]` sums below
// differ from LLVM's (exit 6); the by-value `[u16; 2]` control matches. The
// array's element must now be `T` (copied) or `&T` (read through each
// pointer); anything else is refused by name (`[TCG-VEC-EXTEND-SOURCE]`).
//
// HOW IT FAILS IF THE FIX IS REVERTED. It compiles and DIVERGES from LLVM: the
// exit code carries one bit per wrong answer.

use std::hint::black_box as bb;

#[inline(never)]
fn extend_refs(a: &u32, b: &u32) -> Vec<u32> {
    let mut v = Vec::new();
    v.push(1u32);
    v.extend([a, b]);
    v
}

#[inline(never)]
fn extend_into(v: &mut Vec<u64>, a: &u64, b: &u64) {
    v.extend([a, b, a]);
}

#[inline(never)]
fn extend_values(a: u16, b: u16) -> Vec<u16> {
    let mut v = Vec::new();
    v.extend([a, b]);
    v
}

fn main() {
    let (x, y) = (bb(100u32), bb(200u32));
    let r = extend_refs(&x, &y);
    let mut w: Vec<u64> = Vec::new();
    w.push(bb(7));
    let (p, q) = (bb(11u64), bb(12u64));
    extend_into(&mut w, &p, &q);
    let s = extend_values(bb(3), bb(4));
    let mut code = 0;
    if r.len() != 3 || r[0] + r[1] + r[2] != 301 {
        code |= 1;
    }
    if w.len() != 4 || w[1] + w[2] + w[3] != 34 {
        code |= 2;
    }
    if s.len() != 2 || s[0] + s[1] != 7 {
        code |= 4;
    }
    std::process::exit(code + 3);
}
