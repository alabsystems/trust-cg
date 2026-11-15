// (p) L3 ([TCG-REGALLOC-063]) — the exact-width aggregate RETURN lanes refused
// every width outside {1,2,4,8}, so a 3/5/6/7-byte `#[repr(C)]` aggregate
// returned BY VALUE failed the compile closed. They are now COMPOSED from
// exact-width loads (3 = 2+1, 5 = 4+1, 6 = 4+2, 7 = 4+2+1) — never widened to
// one 8-byte load, which would be the (o) over-read on the return side.
//
// The caller checks EVERY byte of each returned aggregate.
// Must print the four little-endian byte-folds (197121 / 21542142465 /
// 6618611909121 / 1976943448883713) and exit 0 under both backends at -O0
// and -O2.
#[repr(C)]
#[derive(Clone, Copy)]
struct A3 {
    a: u8,
    b: u8,
    c: u8,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct A5 {
    a: u8,
    b: u8,
    c: u8,
    d: u8,
    e: u8,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct A6 {
    a: u8,
    b: u8,
    c: u8,
    d: u8,
    e: u8,
    f: u8,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct A7 {
    a: u8,
    b: u8,
    c: u8,
    d: u8,
    e: u8,
    f: u8,
    g: u8,
}

#[inline(never)]
fn mk3(seed: u8) -> A3 {
    A3 {
        a: seed,
        b: seed + 1,
        c: seed + 2,
    }
}
#[inline(never)]
fn mk5(seed: u8) -> A5 {
    A5 {
        a: seed,
        b: seed + 1,
        c: seed + 2,
        d: seed + 3,
        e: seed + 4,
    }
}
#[inline(never)]
fn mk6(seed: u8) -> A6 {
    A6 {
        a: seed,
        b: seed + 1,
        c: seed + 2,
        d: seed + 3,
        e: seed + 4,
        f: seed + 5,
    }
}
#[inline(never)]
fn mk7(seed: u8) -> A7 {
    A7 {
        a: seed,
        b: seed + 1,
        c: seed + 2,
        d: seed + 3,
        e: seed + 4,
        f: seed + 5,
        g: seed + 6,
    }
}

fn main() {
    let v3 = mk3(1);
    let v5 = mk5(1);
    let v6 = mk6(1);
    let v7 = mk7(1);
    // Every byte of every returned aggregate is folded in at its own weight,
    // so a wrong or missing lane changes the printed number.
    let c3: u64 = v3.a as u64 | (v3.b as u64) << 8 | (v3.c as u64) << 16;
    let c5: u64 = v5.a as u64
        | (v5.b as u64) << 8
        | (v5.c as u64) << 16
        | (v5.d as u64) << 24
        | (v5.e as u64) << 32;
    let c6: u64 = v6.a as u64
        | (v6.b as u64) << 8
        | (v6.c as u64) << 16
        | (v6.d as u64) << 24
        | (v6.e as u64) << 32
        | (v6.f as u64) << 40;
    let c7: u64 = v7.a as u64
        | (v7.b as u64) << 8
        | (v7.c as u64) << 16
        | (v7.d as u64) << 24
        | (v7.e as u64) << 32
        | (v7.f as u64) << 40
        | (v7.g as u64) << 48;
    println!("{}", c3);
    println!("{}", c5);
    println!("{}", c6);
    println!("{}", c7);
}
