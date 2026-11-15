// CORPUS FIXTURE — `ptr::copy_nonoverlapping(src, dst, 1)` of a `String` /
// `Vec<T>` element moves all 24 bytes of its header.
//
// WHAT IT PINS. `lower_copy_nonoverlapping` unrolls a small constant count of a
// "scalar-leaf" element into one typed load/store per element. For a header,
// `memory_scalar_leaf_ty` answers the one-word `Ptr` carrier, so the unroll moved
// 8 of the element's 24 bytes. `Vec<String>::retain` compacts every kept element
// with exactly that copy: the kept strings became `{cap, <stale ptr>, <stale
// len>}` -- a wrong digest (71845 for 179076) and then a trap freeing a stale
// pointer, at -O0..-O3 (also on the v52 base, where the digest was 143145755).
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM -- a
// hard failure of `collection_header_element_image_differential`.

use std::hint::black_box as bb;

#[inline(never)]
fn digest_s(v: &String) -> u64 {
    let b = v.as_bytes();
    let mut s = b.len() as u64;
    let mut j = 0;
    while j < b.len() {
        s = s.wrapping_mul(31).wrapping_add(b[j] as u64);
        j += 1;
    }
    s
}

#[inline(never)]
fn digest_all(v: &Vec<String>) -> u64 {
    let mut s = v.len() as u64;
    let mut j = 0;
    while j < v.len() {
        s = s.wrapping_mul(31).wrapping_add(digest_s(&v[j]));
        j += 1;
    }
    s
}

#[inline(never)]
fn out(x: u64) {
    println!("{x}");
}

// Keep the strings whose digest is even. LLVM: 179076.
#[inline(never)]
fn retain_even() -> u64 {
    let mut v: Vec<String> = Vec::new();
    let mut i = 0u64;
    while i < bb(5u64) {
        v.push(format!("s{}", i));
        i += 1;
    }
    v.retain(|x| digest_s(x) % 2 == 0);
    digest_all(&v)
}

// Drop the first two and keep the tail, so every kept element moves. LLVM:
// 7752950428065.
#[inline(never)]
fn retain_tail() -> u64 {
    let mut v: Vec<String> = Vec::new();
    let mut i = 0u64;
    while i < bb(6u64) {
        v.push(format!("row{}", i * 7));
        i += 1;
    }
    let mut k = 0;
    v.retain(|_| {
        k += 1;
        k > 2
    });
    digest_all(&v) + v[0].len() as u64
}

fn main() {
    out(retain_even());
    out(retain_tail());
}
