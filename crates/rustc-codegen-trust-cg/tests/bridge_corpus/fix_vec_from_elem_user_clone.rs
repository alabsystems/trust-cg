// CORPUS FIXTURE — `vec![x; n]` of a class-2 struct runs the element's `Clone`.
//
// WHAT IT PINS. std's `extend_with` clones `x` into the first `n - 1` slots and
// moves it into the last. The class-2 `from_elem` lowering broadcast the bytes
// of `x` instead, so a hand-written `clone` never ran: the elements' `a` fields
// read `1 1 1` where std's read `2 2 1` (digest 114198 for 130070), at -O0..-O3.
// The bridge must run the clone or refuse by name (`[TCG-FROM-ELEM-CLONE]`).
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM.

use std::hint::black_box as bb;

struct E {
    a: u8,
    b: u8,
}

impl Clone for E {
    fn clone(&self) -> E {
        E {
            a: self.a.wrapping_add(1),
            b: self.b,
        }
    }
}

#[inline(never)]
fn from_elem(a: u8, n: usize) -> Vec<E> {
    vec![E { a, b: 9 }; n]
}

#[inline(never)]
fn digest(v: &Vec<E>) -> u32 {
    let mut s = v.len() as u32;
    let mut i = 0;
    while i < v.len() {
        s = s
            .wrapping_mul(31)
            .wrapping_add(u32::from(v[i].a) * 16 + u32::from(v[i].b));
        i += 1;
    }
    s
}

fn main() {
    let v = from_elem(bb(1), bb(3));
    println!("{}", digest(&v));
}
