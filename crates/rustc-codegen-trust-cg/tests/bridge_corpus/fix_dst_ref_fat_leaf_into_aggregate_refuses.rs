// [TCG-DEREF-BASE-ADDR] REGRESSION PIN — a WIDE (`&[u8]`) prefix field READ
// through a slice-tail DST reference into a temp that flows BY VALUE into an
// aggregate (`W { k: 9, s: h.i.s }`), so the temp is SCALARIZED rather than
// slot-backed and the read reaches `lower_memory_fat_leaf_use`'s deref-base
// branch.
//
// # What this fixture is for
//
// That branch took `h`'s ONE bound value as the pointee's address whenever the
// old thin/fat ENUMERATION called `h` thin — and it calls `&H<'_, [u32]>` thin.
// Measured at the unpatched lane tip, BOTH opt levels, a silent wrong answer
// with a wrong LENGTH: the bridge printed `wrap 9 2 346` (O0) / `wrap 9 2 191`
// (O2) where LLVM prints `wrap 9 6 21`. A wrong length read out of a fat pointer
// is one step from an out-of-bounds read.
//
// This row is expected to be an INCOMPLETE: the base-address predicate refuses
// the slice-tail DST base here (no data-lane path is modelled for a scalarized
// wide destination), and the refusal is the correct outcome.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// Give `lower_memory_fat_leaf_use` the enumeration back and the bridge compiles
// this and prints a wrong length and sum; the harness's
// `assert_eq!(bridge.stdout, oracle.stdout)` fails with "STDOUT differs from
// LLVM", at both opt levels. Do NOT make this row compile unless the read
// addresses the DATA lane.
#![allow(dead_code)]

struct In<'a> {
    s: &'a [u8],
    n: u64,
}
struct H<'a, T: ?Sized> {
    i: In<'a>,
    tail: T,
}
struct W<'a> {
    k: u8,
    s: &'a [u8],
}

static BIG: [u8; 6] = [1, 2, 3, 4, 5, 6];

#[inline(never)]
fn wrap_s<'a>(h: &H<'a, [u32]>) -> W<'a> {
    W { k: 9, s: h.i.s }
}
#[inline(never)]
fn sum(s: &[u8]) -> (usize, u64) {
    let l = s.len();
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < l {
        acc = acc + unsafe { *s.as_ptr().add(i) } as u64;
        i = i + 1;
    }
    (l, acc)
}

fn main() {
    let o: H<[u32; 2]> = H {
        i: In { s: &BIG, n: 3 },
        tail: [9, 9],
    };
    let w = wrap_s(&o);
    let k = w.k;
    let (l, a) = sum(w.s);
    println!("wrap {} {} {}", k, l, a);
}
