// CORPUS FIXTURE — under `panic=unwind`, `Vec::dedup` of an element with a
// hand-written `PartialEq` that panics leaves the Vec as std's unwind guard
// does.
//
// WHAT IT PINS. std's `dedup` is `dedup_by(|a, b| a == b)`, and std's
// `dedup_by` closes the gap it is compacting (`FillGapOnDrop`) when `eq`
// panics. The bridge runs std's `dedup` body for a hand-written `eq`, and the
// intercepted `dedup_by` it calls closes the gap in its model's landing pad
// (`emit_vec_compaction_guard_pad`). Here `eq` panics on the last element; the
// guard reads the Vec while the panic unwinds, where std leaves `[3, 4, 5, 9]`
// (`4 3787465`), at -O0..-O3 (at -O2/-O3 rustc inlines `dedup` into
// `dedup_by`).
//
// HOW IT FAILS IF THE FIX IS REVERTED. Without the guard's gap closing it
// COMPILES and DIVERGES from LLVM (`6 1119789290`: the compacted prefix plus the
// stale tail).

use std::hint::black_box as bb;

#[derive(Clone, Copy)]
struct W(u32);

impl PartialEq for W {
    fn eq(&self, other: &W) -> bool {
        if self.0 == 9 {
            panic!("eq");
        }
        self.0 == other.0
    }
}

struct Guard(*mut Vec<W>);

impl Drop for Guard {
    fn drop(&mut self) {
        let v = unsafe { &*self.0 };
        let mut s = v.len() as u32;
        let mut i = 0;
        while i < v.len() {
            s = s.wrapping_mul(31).wrapping_add(v[i].0);
            i += 1;
        }
        line(v.len() as u32, s);
        std::process::exit(0);
    }
}

#[inline(never)]
fn line(len: u32, digest: u32) {
    println!("{len} {digest}");
}

#[inline(never)]
fn dedup(v: &mut Vec<W>) {
    v.dedup();
}

fn main() {
    let mut v = Vec::new();
    for x in [3u32, 3, 4, 4, 5, 9] {
        v.push(W(bb(x)));
    }
    let p: *mut Vec<W> = &mut v;
    let g = Guard(p);
    dedup(unsafe { &mut *p });
    std::mem::forget(g);
    println!("no panic");
}
