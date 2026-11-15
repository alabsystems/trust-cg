// CORPUS FIXTURE — `Vec<u32> == Vec<W>` runs the user's `u32: PartialEq<W>`.
//
// WHAT IT PINS. alloc's `impl PartialEq<Vec<U>> for Vec<T> where T:
// PartialEq<U>` compares element by element through `T::eq`. The `eq`/`ne` arm
// of `lower_vec_call` took the element type from the self alone and scanned
// both buffers as raw `u32` lanes: the user's `eq` (here "equal to half") was
// never called, and a narrower or zero-sized right element was read out of
// bounds. Measured on 6b108b81d: `half` answered `false` and `bitwise` `true`
// (LLVM: `true`, `false`) through the non-inlined generic at -O0..-O3, and so
// did the direct `*v == *w` / `*v != *w` at -O0/-O1 (exit 18 at -O0/-O1, 6 at
// -O2/-O3). The intercepted comparison now requires the right operand to be a
// `Vec` of the self's own element type.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It compiles and DIVERGES from LLVM: the
// exit code carries one bit per wrong answer.

use std::hint::black_box as bb;

pub struct W(pub u32);

impl PartialEq<W> for u32 {
    fn eq(&self, o: &W) -> bool {
        *self == o.0 / 2
    }
}

#[inline(never)]
fn generic_eq<A: PartialEq<B>, B>(a: &A, b: &B) -> bool {
    a == b
}

#[inline(never)]
fn direct_eq(v: &Vec<u32>, w: &Vec<W>) -> bool {
    *v == *w
}

#[inline(never)]
fn direct_ne(v: &Vec<u32>, w: &Vec<W>) -> bool {
    *v != *w
}

fn main() {
    let mut v: Vec<u32> = Vec::new();
    v.push(bb(1));
    v.push(bb(2));
    v.push(bb(3));
    let mut half: Vec<W> = Vec::new();
    half.push(W(bb(2)));
    half.push(W(bb(4)));
    half.push(W(bb(6)));
    let mut bitwise: Vec<W> = Vec::new();
    bitwise.push(W(bb(1)));
    bitwise.push(W(bb(2)));
    bitwise.push(W(bb(3)));
    let mut code = 0;
    if !generic_eq(&v, &half) {
        code |= 1;
    }
    if generic_eq(&v, &bitwise) {
        code |= 2;
    }
    if !direct_eq(&v, &half) {
        code |= 4;
    }
    if !direct_ne(&v, &bitwise) {
        code |= 8;
    }
    std::process::exit(code + 3);
}
