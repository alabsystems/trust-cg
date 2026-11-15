// CORPUS FIXTURE — `[const { Vec::new() }; N]` writes N whole 24-byte
// `{cap, ptr, len}` header images.
//
// WHAT IT PINS. The array-of-header lowering
// (`lower_memory_collection_header_array_assign`) also owns `Rvalue::Repeat` of a
// constant header: each element is the constant's in-memory image. Before it,
// the repeat reached the scalar-element arms with the header's one-word `Ptr`
// carrier and refused (`ConstValue::Indirect`), at -O0..-O3.
//
// HOW IT FAILS IF THE FIX IS REVERTED. The bridge refuses a row that must
// compile -- a hard failure of `collection_header_element_image_differential`.

use std::hint::black_box as bb;

#[inline(never)]
fn digest_v(v: &Vec<i64>) -> u64 {
    let mut s = v.len() as u64 * 1000 + v.capacity().min(999) as u64;
    let mut j = 0;
    while j < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[j] as u64);
        j += 1;
    }
    s
}

// `[const { Vec::new() }; 4]`, then pushes through `a[i]`. LLVM: 21279791.
#[inline(never)]
fn const_repeat_vec_array() -> u64 {
    let mut a: [Vec<i64>; 4] = [const { Vec::new() }; 4];
    a[1].push(bb(4));
    a[3].push(bb(6));
    a[3].push(bb(7));
    digest_v(&a[0]) + digest_v(&a[1]) * 3 + digest_v(&a[3]) * 11
}

fn main() {
    println!("{}", const_repeat_vec_array());
}
