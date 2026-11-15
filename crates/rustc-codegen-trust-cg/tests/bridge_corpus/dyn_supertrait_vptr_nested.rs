// Corpus: the SUPERTRAIT VPTR lane at its widest — TWO vptr slots in one vtable,
// a NESTED vptr table (a supertrait that itself needs one), a CHAINED upcast
// through both, and an upcast whose source is an ADDRESS-TAKEN `&dyn` (so the
// halves come out of a memory slot rather than out of projected SSA bindings).
//
// `Top: Mid + A3` and `Mid: A1 + A2`, so rustc's `<Q as Top>` vtable carries the
// `Mid` chain inline, a `TraitVPtr` for `A3`, and — inside the `<Q as Mid>` table
// that the `Mid` chain resolves to — a second `TraitVPtr` for `A2`. Emission is
// therefore RECURSIVE here, and the depth cap
// (`MAX_SUPERTRAIT_VPTR_DEPTH`) has to be above 1 for the program to compile at
// all.
//
// WHY THIS EXISTS BESIDE `dyn_supertrait_vptr_upcast.rs`. That file is the
// MINIMAL shape (one vptr slot, one level) and mirrors the `library/alloc` root
// this lane cleared (`core::error::Error: Debug + Display`). This one is the
// GENERALIZATION the one-slot case cannot see: with a single slot, almost any
// index arithmetic happens to land on it, and with a single level the recursion
// is never taken. Every method returns a DISTINCT constant so a slot read at the
// wrong index, a nested table that was never emitted, or a vptr load applied to a
// PREFIX upcast prints a different number rather than crashing.
//
// Expected, in order: `77` (`Top::t`, the field), `44` (`Mid::m` after the
// PREFIX upcast `Top -> Mid`), `11` (`A1::a1`, also a prefix), `22` (`A2::a2` —
// reached from `Top` through the NESTED slot), `33` (`A3::a3` — the first-level
// slot), `22` again (the CHAINED `Top -> Mid -> A2`, which must agree with the
// direct route), and `33` from a `&&dyn Top` whose inner reference is
// address-taken.
//
// Arithmetic-free on purpose: a multiply or comparison lowers to `AArch64::CSet`,
// which this host's opcode-proof inventory does not map, and the resulting
// `[TCG-PROOF-465]` refusal would hide this row's real verdict.
#![allow(dead_code)]

trait A1 {
    fn a1(&self) -> i64;
}
trait A2 {
    fn a2(&self) -> i64;
}
trait A3 {
    fn a3(&self) -> i64;
}
trait Mid: A1 + A2 {
    fn m(&self) -> i64;
}
trait Top: Mid + A3 {
    fn t(&self) -> i64;
}

struct Q(i64);

impl A1 for Q {
    fn a1(&self) -> i64 {
        11
    }
}
impl A2 for Q {
    fn a2(&self) -> i64 {
        22
    }
}
impl A3 for Q {
    fn a3(&self) -> i64 {
        33
    }
}
impl Mid for Q {
    fn m(&self) -> i64 {
        44
    }
}
impl Top for Q {
    fn t(&self) -> i64 {
        self.0
    }
}

#[inline(never)]
fn u_mid<'a>(d: &'a dyn Top) -> &'a dyn Mid {
    d
}
#[inline(never)]
fn u_a1<'a>(d: &'a dyn Top) -> &'a dyn A1 {
    d
}
#[inline(never)]
fn u_a2<'a>(d: &'a dyn Top) -> &'a dyn A2 {
    d
}
#[inline(never)]
fn u_a3<'a>(d: &'a dyn Top) -> &'a dyn A3 {
    d
}
#[inline(never)]
fn u_a2_from_mid<'a>(d: &'a dyn Mid) -> &'a dyn A2 {
    d
}
#[inline(never)]
fn c_mid(d: &dyn Mid) -> i64 {
    d.m()
}
#[inline(never)]
fn c_a1(d: &dyn A1) -> i64 {
    d.a1()
}
#[inline(never)]
fn c_a2(d: &dyn A2) -> i64 {
    d.a2()
}
#[inline(never)]
fn c_a3(d: &dyn A3) -> i64 {
    d.a3()
}
#[inline(never)]
fn c_top(d: &dyn Top) -> i64 {
    d.t()
}
#[inline(never)]
fn emit(x: i64) {
    println!("{}", x);
}

fn main() {
    let q = Q(77);
    let d: &dyn Top = &q;
    emit(c_top(d));
    emit(c_mid(u_mid(d)));
    emit(c_a1(u_a1(d)));
    emit(c_a2(u_a2(d)));
    emit(c_a3(u_a3(d)));
    emit(c_a2(u_a2_from_mid(u_mid(d))));
    // An ADDRESS-TAKEN `&dyn Top`: the upcast source's two lanes come out of a
    // memory slot, not out of projected SSA halves.
    let r: &dyn Top = &q;
    let rr: &&dyn Top = &r;
    emit(c_a3(u_a3(*rr)));
}
