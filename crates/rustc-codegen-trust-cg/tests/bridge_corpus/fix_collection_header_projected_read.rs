// CORPUS FIXTURE — a header read out of a PROJECTION is the projected image's
// address, never its first word.
//
// WHAT IT PINS. At -O2/-O3 `format!(..).into_bytes()` inlines to
// `_61 = move (_6.0: Vec<u8>)`: the `vec` field of a `String` header local. The
// bridge's value of a header place is the ADDRESS of its 24-byte image (an
// unprojected header local reads as its slot). The projected read instead went
// down the generic memory-leaf path, which types a header as a one-word `Ptr`
// leaf, and LOADED the image's first word -- the capacity -- as the image
// address; the following 24-byte copy dereferenced it: SIGSEGV. The same path
// served `ptr::write(&mut a[1], w)` into a `[Vec<i64>; 3]` element (a whole
// header written through a pointer into an array image).
//
// HOW IT FAILS IF THE FIX IS REVERTED. At -O2/-O3 it COMPILES and DIVERGES from
// LLVM (a signal) -- a hard failure of
// `collection_header_element_image_differential`. At -O0/-O1 the un-inlined
// `String::into_bytes` / `ptr::write` calls are refused by name (rows that may
// refuse, but never diverge).

use std::hint::black_box as bb;

#[inline(never)]
fn digest_bytes(b: &[u8]) -> u64 {
    let mut s = b.len() as u64;
    let mut i = 0;
    while i < b.len() {
        s = s.wrapping_mul(31).wrapping_add(b[i] as u64);
        i += 1;
    }
    s
}

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

#[inline(never)]
fn out(x: u64) {
    println!("{x}");
}

// `Vec<Vec<u8>>` of `format!(..).into_bytes()` rows. LLVM: 5387380.
#[inline(never)]
fn rows_of_string_bytes() -> u64 {
    let mut g: Vec<Vec<u8>> = Vec::new();
    for i in 0..bb(3usize) {
        g.push(format!("n{}", i).into_bytes());
    }
    digest_bytes(&g[2]) * 1000 + digest_bytes(&g[0])
}

// `ptr::write` of a pushed `Vec<i64>` into element 1 of a `[Vec<i64>; 3]`, then
// a push through the element. LLVM: 89499148.
#[inline(never)]
fn ptr_write_array_element() -> u64 {
    let mut a: [Vec<i64>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    let mut w = Vec::new();
    w.push(bb(7));
    w.push(bb(8));
    unsafe {
        std::ptr::write(&mut a[1], w);
    }
    a[1].push(9);
    digest_v(&a[0]) * 100000 + digest_v(&a[1])
}

fn main() {
    out(rows_of_string_bytes());
    out(ptr_write_array_element());
}
