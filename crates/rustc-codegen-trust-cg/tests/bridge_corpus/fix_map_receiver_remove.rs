// CORPUS FIXTURE — `Vec<BTreeMap<i64, i64>>::remove` is never routed to the
// BTreeMap intercept.
//
// WHAT IT PINS. `lower_btreemap_call` identified a map method by its
// DESTINATION before its self, exactly as `lower_vec_call` did: `v.remove(i)`
// RETURNS a `BTreeMap<i64, i64>`, so it would be lowered as
// `BTreeMap::remove(&mut map, &key)` with the `Vec` as the map slot. Today no
// program can populate a `Vec<BTreeMap<_, _>>` (every element store of the
// synthetic map carrier refuses), so the misroute is latent; the guard refuses
// it by name, `[TCG-MAP-RECEIVER]`.
//
// HOW IT FAILS IF THE FIX IS REVERTED. The bridge still refuses the program
// (the `Vec<BTreeMap>` drop glue), but no longer names `[TCG-MAP-RECEIVER]` --
// the row's required refusal reason.

use std::collections::BTreeMap;
use std::hint::black_box as bb;

#[inline(never)]
fn take(v: &mut Vec<BTreeMap<i64, i64>>, i: usize) -> usize {
    if i < v.len() {
        let m = v.remove(i);
        m.len()
    } else {
        7
    }
}

fn main() {
    let mut v: Vec<BTreeMap<i64, i64>> = Vec::new();
    println!("{}", take(&mut v, bb(0)));
}
