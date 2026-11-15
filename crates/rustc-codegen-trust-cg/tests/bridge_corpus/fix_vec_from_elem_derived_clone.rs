// CORPUS FIXTURE — `vec![x; n]` of a class-2 struct with a DERIVED `Clone`
// keeps compiling: its clone is a bitwise copy (`clone_is_bitwise_copy`), so the
// byte broadcast is std's result. The control for
// `fix_vec_from_elem_user_clone`.

use std::hint::black_box as bb;

#[derive(Clone)]
struct E {
    a: u8,
    b: u8,
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
