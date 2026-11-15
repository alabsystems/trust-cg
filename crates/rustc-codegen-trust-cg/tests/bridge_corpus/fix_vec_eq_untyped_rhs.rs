// CORPUS FIXTURE — `Vec<T> == [T; N]` / `== [T]` / `== &[T; N]` compares
// through std's own impl, never as two `Vec` headers.
//
// WHAT IT PINS. alloc's `PartialEq` impls for `Vec<T>` are generic over the
// right operand (`[U; N]`, `[U]`, `&[U]`, `&[U; N]`, `Vec<U>`). The `eq`/`ne`
// arm of `lower_vec_call` read ANY right operand as a `{cap, ptr, len}` Vec
// header: an array's own elements became the data pointer and length of a
// `__trustcg_slice_eq_*` scan. Measured on 6b108b81d: every comparison below
// answered the opposite of LLVM at -O0/-O1 (exit 18), and the two through the
// non-inlined generics at -O2/-O3 too (exit 9). Only `Vec<T> op Vec<T>` with
// the self's own element type is the intercepted comparison now; every other
// right operand runs the real impl body.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It compiles and DIVERGES from LLVM: the
// exit code carries one bit per wrong answer.

use std::hint::black_box as bb;

#[inline(never)]
fn generic_eq<A: PartialEq<B>, B>(a: &A, b: &B) -> bool {
    a == b
}

#[inline(never)]
fn generic_ne<A: PartialEq<B>, B>(a: &A, b: &B) -> bool {
    a != b
}

#[inline(never)]
fn direct_eq(a: u32) -> bool {
    let mut v: Vec<u32> = Vec::new();
    v.push(a);
    v.push(a + 1);
    v == [a, a + 1]
}

#[inline(never)]
fn array_rhs(a: i64) -> bool {
    let mut v: Vec<i64> = Vec::new();
    v.push(a);
    v.push(a * 3);
    generic_eq(&v, &[a, a * 3])
}

#[inline(never)]
fn array_rhs_ne(a: u8) -> bool {
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(a + 1);
    generic_ne(&v, &[a, a + 1])
}

#[inline(never)]
fn slice_rhs(a: u16, s: &[u16]) -> bool {
    let mut v: Vec<u16> = Vec::new();
    v.push(a);
    v.push(a + 7);
    v == *s
}

fn main() {
    let mut code = 0;
    if !direct_eq(bb(5)) {
        code |= 1;
    }
    if !array_rhs(bb(-4)) {
        code |= 2;
    }
    if array_rhs_ne(bb(9)) {
        code |= 4;
    }
    let s = [bb(300u16), 307];
    if !slice_rhs(bb(300), &s) {
        code |= 8;
    }
    std::process::exit(code + 3);
}
