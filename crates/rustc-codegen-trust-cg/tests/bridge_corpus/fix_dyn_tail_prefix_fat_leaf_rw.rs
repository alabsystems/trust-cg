// [TCG-DEREF-BASE-ADDR] CAPABILITY PIN — prefix reads and a WIDE prefix store
// through a VTABLE-tailed struct reference (`t: &T<dyn Er>`), the class whose ONE
// bound value IS the pointee's address.
//
// # What this fixture is for
//
// The fix for the slice-tail DST class could be written two ways, and one of
// them is wrong in the other direction. Answering "may a field offset be folded
// onto this base's one value?" with SIZEDNESS refuses `&T<dyn Er>` too — but the
// entry-arg loop declares a vtable-pair reference as two `Ptr` params with the
// DATA lane first, so its value IS the data address, and every function
// below COMPILED AND MATCHED LLVM on the unpatched lane tip at both opt levels.
// slice-assign v2 asked sizedness at `lower_memory_fat_leaf_store` and
// `lower_memory_fat_leaf_use` and withdrew `set_s` and `wrap_s`
// (`[TCG-MIR-UNSUPPORTED]`), capability losses with no soundness gain.
// `deref_base_scalar_is_pointee_addr` excludes the slice-tail class and keeps
// this one.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// Make any of the three base-address sites (`lower_memory_aggregate_use`'s deref
// read, `lower_memory_fat_leaf_use` — reached by `wrap_s` — or
// `lower_memory_fat_leaf_store`) ask sizedness and this row becomes an
// INCOMPLETE at `-Copt-level=0` (each of the three measured separately,
// 2026-09-27). `COMPILED_FLOOR` counts that `-O0` row, so the floor assertion
// fails by name. (The `-O2` row is already an INCOMPLETE for a reason that is
// not this lane's: exactly one function, `main`, refuses on the host-wide
// `[TCG-PROOF-465]` opcode-proof gap.) Make them ask the old enumeration and
// nothing here changes — that direction is pinned by the slice-tail fixtures.
#![allow(dead_code)]

trait Er {
    fn k(&self) -> u64;
}
impl Er for u32 {
    fn k(&self) -> u64 {
        *self as u64
    }
}

#[derive(Clone, Copy)]
struct Inner {
    a: u64,
    b: u64,
    c: u32,
}
struct T<'a, E: ?Sized> {
    i: Inner,
    s: &'a [u8],
    v: E,
}

static BIG: [u8; 6] = [1, 2, 3, 4, 5, 6];
static SMALL: [u8; 2] = [1, 2];

#[inline(never)]
fn get_i(t: &T<'_, dyn Er>) -> Inner {
    t.i
}
#[inline(never)]
fn get_s<'a>(t: &T<'a, dyn Er>) -> &'a [u8] {
    t.s
}
#[inline(never)]
fn set_s<'a>(t: &mut T<'a, dyn Er>, v: &'a [u8]) {
    t.s = v;
}
struct W<'a> {
    k: u8,
    s: &'a [u8],
}
// The wide read into a SCALARIZED temp (it flows by value into `W`), which is the
// shape that reaches `lower_memory_fat_leaf_use`'s deref-base branch itself.
#[inline(never)]
fn wrap_s<'a>(t: &T<'a, dyn Er>) -> W<'a> {
    W { k: 9, s: t.s }
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
    let mut o: T<u32> = T {
        i: Inner {
            a: 11,
            b: 22,
            c: 33,
        },
        s: &BIG,
        v: 9,
    };
    let g = get_i(&o);
    let (a, b, c) = (g.a, g.b, g.c);
    println!("get_i {} {} {}", a, b, c);
    let (l0, s0) = sum(get_s(&o));
    let w = wrap_s(&o);
    let wk = w.k;
    let (wl, ws) = sum(w.s);
    println!("wrap {} {} {}", wk, wl, ws);
    {
        let r: &mut T<dyn Er> = &mut o;
        set_s(r, &SMALL);
    }
    let (l1, s1) = sum(o.s);
    println!("s {} {} {} {}", l0, s0, l1, s1);
}
