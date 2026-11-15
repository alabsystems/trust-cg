// CORPUS FIXTURE — `core::ptr::eq::<Vec<u32>>` compares addresses.
//
// WHAT IT PINS. `ptr::eq` is a free function named `eq` whose arguments are
// `*const Vec<u32>`. `lower_vec_call` recognized a Vec method by a crate test,
// the first argument's type with one reference OR raw pointer peeled, and the
// item name, so it lowered `ptr::eq(a, b)` as `Vec::eq`: content equality, and
// a load through a null pointer. Measured on 6b108b81d at -O0/-O1: the
// program died of SIGSEGV on the null right operand (and two distinct Vecs
// with equal contents compare `true` there, LLVM `false`). A Vec method is now
// the standard library's own code for a `Vec` receiver; a free function runs
// its real body.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It compiles and DIVERGES from LLVM (a
// wrong exit code, or a SIGSEGV on the null case).

use std::hint::black_box as bb;

#[inline(never)]
fn same(a: *const Vec<u32>, b: *const Vec<u32>) -> bool {
    std::ptr::eq(a, b)
}

#[inline(never)]
fn null() -> *const Vec<u32> {
    std::ptr::null()
}

fn main() {
    let mut x: Vec<u32> = Vec::new();
    x.push(bb(1));
    let mut y: Vec<u32> = Vec::new();
    y.push(bb(1));
    let mut code = 0;
    if same(&x, &y) {
        code |= 1;
    }
    if !same(&x, &x) {
        code |= 2;
    }
    if same(&x, null()) {
        code |= 4;
    }
    std::process::exit(code + 3);
}
