// [TCG-DEREF-BASE-ADDR] REGRESSION PIN — the RAW-POINTER spelling: a scalar
// prefix store, a whole-prefix read and a discriminant read, all through
// `*const` / `*mut H<[u32]>` (a slice-tail DST behind a raw pointer).
//
// # What this fixture is for
//
// `*mut H<[u32]>` is exactly as wide as `&mut H<[u32]>` — `{ data, len }` — and
// is admitted by every predicate that admits the reference. This program was
// REFUSED at the unpatched lane tip; slice-assign v2 made its `set_b` store
// compile, and the two READS then took the pointer's one bound value (its lane
// tuple) as the pointee's address. Measured on v2: `raw 6121613408 2 1826646112
// 0` at `-Copt-level=0` and `raw 0 6132459600 0 0` at `-Copt-level=2`, where LLVM
// prints `raw 1 77 3 42` at both — the `-O2` row is why this fixture exists
// alongside the reference-spelled ones, whose `-O2` rows refuse on the
// host-wide `[TCG-PROOF-465]` gap.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// Revert the whole-aggregate deref-read arm or the projected discriminant to
// their pre-fix bases and the bridge compiles this and prints garbage; the
// harness's `assert_eq!(bridge.stdout, oracle.stdout)` fails with "STDOUT
// differs from LLVM", at BOTH opt levels.
#![allow(dead_code)]

#[derive(Clone, Copy)]
struct Inner {
    a: u64,
    b: u64,
    c: u32,
}
#[derive(Clone, Copy)]
enum E {
    A(u64),
    B,
}
struct H<T: ?Sized> {
    i: Inner,
    e: E,
    tail: T,
}

#[inline(never)]
unsafe fn get_i(h: *const H<[u32]>) -> Inner {
    unsafe { (*h).i }
}
#[inline(never)]
unsafe fn disc(h: *const H<[u32]>) -> u64 {
    unsafe {
        match (*h).e {
            E::A(x) => x,
            E::B => 7,
        }
    }
}
#[inline(never)]
unsafe fn set_b(h: *mut H<[u32]>, v: u64) {
    unsafe {
        (*h).i.b = v;
    }
}

fn main() {
    let mut o: H<[u32; 2]> = H {
        i: Inner { a: 1, b: 2, c: 3 },
        e: E::A(42),
        tail: [5, 6],
    };
    let p: *mut H<[u32]> = &mut o;
    unsafe {
        set_b(p, 77);
    }
    let g = unsafe { get_i(p) };
    let d = unsafe { disc(p) };
    let (a, b, c) = (g.a, g.b, g.c);
    println!("raw {} {} {} {}", a, b, c, d);
}
