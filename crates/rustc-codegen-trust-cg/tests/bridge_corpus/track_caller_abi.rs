// Corpus: `#[track_caller]` functions, whose ABI (rustc's `FnAbi`) ends with
// a hidden `&'static Location` parameter. The program records the address
// `Location::caller()` returns in each position below and prints, for every
// pair of positions, whether the two addresses are equal; it never prints an
// address. rustc's semantics fix that equality pattern: one call site yields
// the same `Location` on every execution, two call sites yield different
// ones, a `#[track_caller]` fn called from another one sees its caller's
// caller location, and calls through a `fn` pointer or a vtable see the
// location their shim passes. A definition that did not take the parameter,
// or a call that did not pass it, reads some other register or stack word and
// breaks the pattern. The positions cover direct calls, forwarding, a `fn`
// pointer, a user `Index` impl (`Index::index` is `#[track_caller]`), a
// trait method declared `#[track_caller]` called through a vtable, a
// `#[track_caller]` fn item behind `dyn Fn` (its `FnPtrShim` passes the
// location of `Fn::call`, not the fn pointer's) and one passed to `fold`
// (called through `FnMut::call_mut`); `Into::into` and `Option::unwrap` (also
// `#[track_caller]`) are called for their values. Arrays are read through
// patterns and iterators, never a bounds-checked index: a native
// `panic=abort` canonical bounds check is refused (`[TCG-ASSERT-PANIC]`).
#![allow(dead_code)]

use std::cell::Cell;
use std::panic::Location;

type Loc = *const Location<'static>;

const POSITIONS: usize = 16;

#[track_caller]
#[inline(never)]
fn site() -> Loc {
    Location::caller()
}

// `site()` inside a `#[track_caller]` fn reports this fn's caller.
#[track_caller]
#[inline(never)]
fn site_pair() -> (Loc, Loc) {
    (site(), Location::caller())
}

#[track_caller]
#[inline(never)]
fn add_one(x: u32) -> u32 {
    x.wrapping_add(1)
}

struct Tbl {
    v: [u32; 4],
    last: Cell<Loc>,
}

impl std::ops::Index<u32> for Tbl {
    type Output = u32;
    #[inline(never)]
    fn index(&self, i: u32) -> &u32 {
        self.last.set(Location::caller());
        let [a, b, c, d] = &self.v;
        match i & 3 {
            0 => a,
            1 => b,
            2 => c,
            _ => d,
        }
    }
}

trait Tc {
    #[track_caller]
    fn tc(&self, x: u32) -> (u32, Loc);
}

struct K(u32);

impl Tc for K {
    #[inline(never)]
    fn tc(&self, x: u32) -> (u32, Loc) {
        (self.0 ^ add_one(x), Location::caller())
    }
}

/// Bit `j` set when positions `i` and `j` hold the same address.
#[inline(never)]
fn same_as(locs: &[Loc; POSITIONS], i: usize) -> u32 {
    let Some(&at) = locs.get(i) else {
        return 0;
    };
    let mut row = 0u32;
    for (j, &other) in locs.iter().enumerate() {
        if std::ptr::eq(at, other) {
            row |= 1 << j;
        }
    }
    row
}

#[track_caller]
#[inline(never)]
fn fold_site(_: usize, _: u32) -> usize {
    let at: Loc = Location::caller();
    at as usize
}

#[inline(never)]
fn call_dyn_fn(f: &dyn Fn() -> Loc) -> Loc {
    f()
}

#[inline(never)]
fn call_dyn_fn_again(f: &dyn Fn() -> Loc) -> Loc {
    f()
}

#[inline(never)]
fn call_dyn(t: &dyn Tc, x: u32) -> (u32, Loc) {
    t.tc(x)
}

#[inline(never)]
fn call_dyn_again(t: &dyn Tc, x: u32) -> (u32, Loc) {
    t.tc(x)
}

fn main() {
    let fp: fn() -> Loc = site;
    let mut first: Loc = std::ptr::null();
    let mut acc = 0u64;
    for x in [0u32, 1, 2, 3, 250, 65_535, u32::MAX] {
        let t = Tbl {
            v: [10, 20, 30, x],
            last: Cell::new(std::ptr::null()),
        };
        let a = site();
        let b = site();
        let (pf, pc) = site_pair();
        let (qf, qc) = site_pair();
        let f1 = fp();
        let f2 = fp();
        let d = t[x];
        let i1 = t.last.get();
        let _ = t[x ^ 1];
        let i2 = t.last.get();
        let (e1, v1) = call_dyn(&K(x ^ 9), x);
        let (e2, v2) = call_dyn_again(&K(x), x);
        let s1 = call_dyn_fn(&site);
        let s2 = call_dyn_fn_again(&site);
        let fo = [x, x ^ 1].iter().copied().fold(0, fold_site) as Loc;
        if first.is_null() {
            first = a;
        }
        let locs: [Loc; POSITIONS] = [
            first, a, b, pf, pc, qf, qc, f1, f2, i1, i2, v1, v2, s1, s2, fo,
        ];
        let mut nulls = 0u32;
        for (i, loc) in locs.iter().enumerate() {
            println!("{x} eq {i}: {}", same_as(&locs, i));
            nulls += u32::from(loc.is_null());
        }
        let wide: u64 = (x as u16).into();
        let g = Some(x ^ 5).unwrap();
        let n = add_one(x);
        println!("{x}: {nulls} {d} {e1} {e2} {g} {n} {wide}");
        let sum = u64::from(d) + u64::from(e1) + u64::from(e2) + u64::from(g) + u64::from(n);
        acc = acc.wrapping_mul(31).wrapping_add(sum ^ wide);
    }
    println!("acc {acc}");
}
