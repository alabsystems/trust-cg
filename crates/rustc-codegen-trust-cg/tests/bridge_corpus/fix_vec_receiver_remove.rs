// CORPUS FIXTURE — `Vec<Vec<i64>>::remove` is the receiver's own method, never
// an intercepted `Vec<i64>` one.
//
// WHAT IT PINS. `lower_vec_call` identified a Vec method by its DESTINATION
// before its self: `g.remove(1)` RETURNS a `Vec<i64>`, so it was lowered as
// `Vec<i64>::remove` -- 8-byte element stride, `__trustcg_vec_remove_shift_i64`,
// an `i64` loaded as the returned header -- over a buffer of 24-byte images. A
// SILENT wrong exit status at -O0..-O3 (the bridge exited 1, LLVM 21). The self
// `Vec<Vec<i64>>` is not a modeled Vec, so the call must reach std's real
// `remove` (which the bridge compiles or refuses by name).
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM --
// a hard failure of `collection_header_element_image_differential`. With the
// fix, std's `Vec::<Vec<i64>>::remove` body is the function the bridge refuses
// (`[TCG-COLLECTION-IMAGE]`: its `Option<Vec<i64>>`), or it matches.

use std::hint::black_box as bb;

fn main() {
    let mut g: Vec<Vec<i64>> = Vec::new();
    let mut a = Vec::new();
    a.push(bb(10i64));
    let mut b = Vec::new();
    b.push(bb(20i64));
    b.push(bb(21i64));
    g.push(a);
    g.push(b);
    let r = g.remove(bb(1));
    std::process::exit((r.len() * 10 + g.len()) as i32);
}
