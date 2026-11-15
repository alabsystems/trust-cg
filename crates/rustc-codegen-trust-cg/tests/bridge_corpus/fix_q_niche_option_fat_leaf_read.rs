// Corpus: reading a FAT-POINTER payload out of a NICHE-ENCODED enum —
// `<Option<&[u8]> as Try>::branch` and its `&mut` twin, i.e. `let s = o?;`.
//
// `Option<&[u8]>` has no tag byte: `None` is the NULL DATA POINTER of the
// payload's `{data, len}` pair, so the niche lives in lane 0 of a `ScalarPair`.
// Two things had to be true for this to lower, and each guards a different way
// of silently losing information:
//
//  1. The enum must get a memory layout at all. The niche arm required the niche
//     FIELD to be a single `Scalar`; a pair qualifies only when rustc's own tag
//     scalar IS the pair's FIRST lane. That equality is the proof the niche is
//     lane 0 and not lane 1 — reading lane 1 would decode the slice's LENGTH as
//     a discriminant.
//  2. The DESTINATION must own a real `{data, len}` slot. `lower_memory_fat_leaf_use`
//     loads both lanes, and if there were nowhere to put the pair it would have to
//     bind the data half alone and DROP THE LENGTH. It deliberately refuses
//     instead; rule (0g) gives the destination a slot.
//
// WHAT EACH ROW CATCHES, and why a wrong model is a wrong NUMBER:
//   * `3` / `4` are `s.len()` — the METADATA lane. A dropped or wrong length
//     prints something else entirely; reading lane 1 as the niche would have made
//     `Some` undecodable in the first place.
//   * `99` is the `None` arm — the NICHE discriminant decoded from lane 0.
//   * the mutation through `&mut [u8]`, read back by the caller from its OWN
//     array, checks the DATA lane really points at the caller's buffer.
//   * the element reads check data+offset addressing, not just the pointer.
#![allow(dead_code)]

#[inline(never)]
fn first_len(o: Option<&[u8]>) -> Option<usize> {
    let s = o?;
    Some(s.len())
}

#[inline(never)]
fn elem_at(o: Option<&[u8]>, i: usize) -> Option<u8> {
    let s = o?;
    Some(s[i])
}

#[inline(never)]
fn write_back(o: Option<&mut [u8]>) -> Option<usize> {
    let s = o?;
    s[0] = 9;
    Some(s.len())
}

fn main() {
    let a: [u8; 3] = [11, 22, 33];
    let mut b: [u8; 4] = [5, 6, 7, 8];

    let r1 = first_len(Some(&a)).unwrap_or(99);
    let r2 = first_len(None).unwrap_or(99);
    println!("l {} {}", r1, r2); // 3 99

    let e0 = elem_at(Some(&a), 0).unwrap_or(99);
    let e2 = elem_at(Some(&a), 2).unwrap_or(99);
    let en = elem_at(None, 0).unwrap_or(99);
    println!("e {} {} {}", e0, e2, en); // 11 33 99

    let w = write_back(Some(&mut b)).unwrap_or(99);
    let w0 = b[0];
    let w3 = b[3];
    println!("w {} {} {}", w, w0, w3); // 4 9 8
}
