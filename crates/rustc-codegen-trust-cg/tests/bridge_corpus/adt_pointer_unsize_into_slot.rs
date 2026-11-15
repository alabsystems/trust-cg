// Corpus: an `Unsize` coercion between two instances of ONE pointer-wrapping ADT
// whose destination owns a whole memory slot — `MyBox<T> -> MyBox<dyn Trait>`,
// `MyBox<[u8; 3]> -> MyBox<[u8]>`, `MyBox<dyn A + Send + Sync> -> MyBox<dyn A>`,
// and both trait-UPCAST directions.
//
// `MyBox` is `Box`'s exact shape — one `NonNull<T>` field beside a 1-ZST, NOT
// `repr(transparent)`, with a `CoerceUnsized` impl — so it is a plain ADT the
// bridge's `Box` model never intercepts. That is precisely what `alloc::boxed::Box`
// is INSIDE `library/alloc` (a crate-LOCAL ADT, `std_def_is_interceptable` is
// false), where `<Box<dyn Error + Send + Sync> as From<String>>::from` (`_0 = move
// _2 as Box<dyn Error + Send + Sync> (PointerCoercion(Unsize, Implicit))`) and
// `<Box<dyn Error> as From<String>>::from` (the auto-trait-dropping `dyn -> dyn`
// form) refused with `memory-backed aggregate assignment Rvalue::Cast [cast
// PointerCoercion(Unsize, Implicit) ...]`: no arm of `lower_memory_aggregate_assign`
// handled an `Unsize` cast at all. The lowering is rustc's `unsize_ptr` +
// `unsized_info`, transcribed in `adt_pointer_unsize_plan`.
//
// Each coercion sits alone in an `#[inline(never)]` function returning the
// 16-byte ADT BY VALUE (so `_0` is slot-backed at both opt levels), and every
// result is read back through the field + `NonNull::as_ref` + a virtual call, or
// the slice's length and first byte.
//
// WHY EVERY ROW IS A WRONG NUMBER, NOT A CRASH, IF A LANE IS WRONG. Each impl
// returns a DISTINCT constant:
//   * `3` / `7` / `200` — `Sub::s`, `Alpha::a`, `Beta::b` through the NEW vtable
//     `T -> dyn Sub` must install. A vtable written at the wrong offset, or the
//     data pointer written into the metadata lane, dispatches through garbage.
//   * `3` via `drop_auto` — `dyn Sub + Send + Sync -> dyn Sub`: rustc KEEPS the
//     old vtable (same principal). Reading the old vtable from the wrong source
//     offset calls through the data pointer.
//   * `200` via `up_beta` — the NON-PREFIX upcast: the new vtable is LOADED from
//     the old one's supertrait vptr slot (`supertrait_vtable_slot == Some(_)`). If
//     the old vtable were kept instead, `Beta::b` is called at `Sub`'s layout and
//     prints `3` or `7`.
//   * `7` via `up_alpha` — the PREFIX upcast (`None`): must KEEP the old vtable.
//     The control that the vptr load was not applied to every upcast.
//   * `3` / `41` — `[u8; 3] -> [u8]`: the length must be the SOURCE array's `N`
//     and the data lane the array's address (first byte `41`).
//
// ARITHMETIC-FREE on purpose: a multiply or a materialized comparison lowers to
// `AArch64::CSet`, which this host's opcode-proof inventory does not map, and the
// `[TCG-PROOF-465]` refusal would hide this case's real verdict.
#![feature(coerce_unsized, unsize)]
#![allow(dead_code)]

use core::marker::Unsize;
use core::ops::CoerceUnsized;
use core::ptr::NonNull;

struct Zst;
struct MyBox<T: ?Sized>(NonNull<T>, Zst);
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyBox<U>> for MyBox<T> {}

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

static G: P = P(7);
static ARR: [u8; 3] = [41, 42, 43];

#[inline(never)]
fn mk() -> MyBox<P> {
    MyBox(NonNull::from(&G), Zst)
}
#[inline(never)]
fn mk_arr() -> MyBox<[u8; 3]> {
    MyBox(NonNull::from(&ARR), Zst)
}
/// Sized `P -> dyn Sub`: a NEW vtable.
#[inline(never)]
fn to_sub(b: MyBox<P>) -> MyBox<dyn Sub> {
    b
}
#[inline(never)]
fn to_sub_ss(b: MyBox<P>) -> MyBox<dyn Sub + Send + Sync> {
    b
}
/// `dyn Sub + Send + Sync -> dyn Sub`: same principal, the OLD vtable is kept.
#[inline(never)]
fn drop_auto(b: MyBox<dyn Sub + Send + Sync>) -> MyBox<dyn Sub> {
    b
}
/// NON-PREFIX upcast: the new vtable is loaded out of the old one.
#[inline(never)]
fn up_beta(b: MyBox<dyn Sub>) -> MyBox<dyn Beta> {
    b
}
/// PREFIX upcast: the old vtable is kept.
#[inline(never)]
fn up_alpha(b: MyBox<dyn Sub>) -> MyBox<dyn Alpha> {
    b
}
/// `[u8; 3] -> [u8]`: the length is the source array's `N`.
#[inline(never)]
fn to_slice(b: MyBox<[u8; 3]>) -> MyBox<[u8]> {
    b
}
#[inline(never)]
fn nn_sub(b: MyBox<dyn Sub>) -> NonNull<dyn Sub> {
    b.0
}
#[inline(never)]
fn nn_beta(b: MyBox<dyn Beta>) -> NonNull<dyn Beta> {
    b.0
}
#[inline(never)]
fn nn_alpha(b: MyBox<dyn Alpha>) -> NonNull<dyn Alpha> {
    b.0
}
#[inline(never)]
fn nn_slice(b: MyBox<[u8]>) -> NonNull<[u8]> {
    b.0
}
#[inline(never)]
fn emit(x: i64) {
    println!("{}", x);
}
#[inline(never)]
fn emit_u(x: usize) {
    println!("{}", x);
}

fn main() {
    let s = to_sub(mk());
    let n = nn_sub(s);
    emit(unsafe { n.as_ref() }.s());
    emit(unsafe { n.as_ref() }.a());
    emit(unsafe { n.as_ref() }.b());
    let s2 = drop_auto(to_sub_ss(mk()));
    emit(unsafe { nn_sub(s2).as_ref() }.s());
    emit(unsafe { nn_beta(up_beta(to_sub(mk()))).as_ref() }.b());
    emit(unsafe { nn_alpha(up_alpha(to_sub(mk()))).as_ref() }.a());
    let sl = nn_slice(to_slice(mk_arr()));
    emit_u(sl.len());
    emit_u(unsafe { *(sl.as_ptr() as *const u8) } as usize);
}
