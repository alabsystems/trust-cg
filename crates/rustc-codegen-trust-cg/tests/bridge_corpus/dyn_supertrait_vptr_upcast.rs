// Corpus: a vtable that carries a SUPERTRAIT VPTR slot (`VtblEntry::TraitVPtr`),
// and the NON-PREFIX trait upcast that loads out of it.
//
// `trait Sub: Alpha + Beta` has TWO supertraits, so rustc embeds one of them in
// the `<P as Sub>` vtable's single-inheritance prefix and gives the OTHER a
// `TraitVPtr` slot holding a pointer to the separate `<P as Super>` table. The
// emitter used to refuse that entry outright ("vtable for `_` has a supertrait
// vptr entry, which this backend cannot yet emit"), which cost `library/alloc` a
// root (`<alloc::ffi::c_str::IntoStringError as core::error::Error>::source`,
// whose `<core::str::Utf8Error as Error>` vtable has one because
// `Error: Debug + Display`). It now emits the nested table as its own read-only
// global and relocates the slot to it, and the upcast LOADS the new vtable from
// that slot — rustc's `supertrait_vtable_slot` decides WHICH slot, scaled by
// `pointer_size`, exactly as `rustc_codegen_ssa` does.
//
// WHY EVERY ROW IS A WRONG NUMBER, NOT A CRASH, IF A SLOT IS WRONG. Each impl
// returns a DISTINCT constant, so the value printed names the function that was
// actually called:
//   * `3` / `7` / `200` — `Sub::s`, `Alpha::a`, `Beta::b` dispatched through the
//     `&dyn Sub` pointer. These need the vtable to be EMITTABLE at all (before
//     this lane the whole program refused), and they pin that adding a vptr slot
//     did not shift the METHOD slots around it: a one-slot shift would call a
//     neighbour and print another constant, or jump through the size/align word.
//   * `200` via `up_beta` — the NON-PREFIX upcast `&dyn Sub -> &dyn Beta`, i.e.
//     the `Some(slot)` branch. If the load reads the WRONG slot it dispatches
//     through a method address, a size word (2 or 3 here) or a null drop word;
//     if the load is skipped and the source vtable is copied through, `Beta::b`
//     is called at `Sub`'s own layout and prints `3` or `7`.
//   * `7` via `up_alpha` — the PREFIX upcast, rustc's `None` answer, which must
//     keep taking the identity copy. This row is the control that the vptr load
//     was not wired onto every upcast.
//
// DELIBERATELY ARITHMETIC-FREE: every method returns a constant or a plain field
// read. An `i64` multiply / comparison lowers to `AArch64::CSet`/`Csel`, which
// this host's opcode-proof inventory does not map, and the resulting
// `[TCG-PROOF-465]` refusal would hide this row's real verdict at `-O2`.
#![allow(dead_code)]

trait Alpha {
    fn a(&self) -> i64;
}
trait Beta {
    fn b(&self) -> i64;
}
trait Sub: Alpha + Beta {
    fn s(&self) -> i64;
}

struct P(i64);

impl Alpha for P {
    fn a(&self) -> i64 {
        self.0
    }
}
impl Beta for P {
    fn b(&self) -> i64 {
        200
    }
}
impl Sub for P {
    fn s(&self) -> i64 {
        3
    }
}

#[inline(never)]
fn call_sub(d: &dyn Sub) -> i64 {
    d.s()
}
#[inline(never)]
fn call_alpha_via_sub(d: &dyn Sub) -> i64 {
    d.a()
}
#[inline(never)]
fn call_beta_via_sub(d: &dyn Sub) -> i64 {
    d.b()
}
/// The NON-PREFIX upcast: `supertrait_vtable_slot` answers `Some(slot)`.
#[inline(never)]
fn up_beta<'a>(d: &'a dyn Sub) -> &'a dyn Beta {
    d
}
/// The PREFIX upcast: `supertrait_vtable_slot` answers `None` (identity copy).
#[inline(never)]
fn up_alpha<'a>(d: &'a dyn Sub) -> &'a dyn Alpha {
    d
}
#[inline(never)]
fn call_beta(d: &dyn Beta) -> i64 {
    d.b()
}
#[inline(never)]
fn call_alpha(d: &dyn Alpha) -> i64 {
    d.a()
}
#[inline(never)]
fn emit(x: i64) {
    println!("{}", x);
}

fn main() {
    let p = P(7);
    let d: &dyn Sub = &p;
    emit(call_sub(d));
    emit(call_alpha_via_sub(d));
    emit(call_beta_via_sub(d));
    emit(call_beta(up_beta(d)));
    emit(call_alpha(up_alpha(d)));
}
