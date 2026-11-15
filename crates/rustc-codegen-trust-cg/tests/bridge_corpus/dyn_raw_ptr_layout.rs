// Corpus: the `*mut dyn Trait` statements `<Box<dyn Trait> as Drop>::drop` makes
// at `-O0` — outside `library/alloc`, where `Box` is intercepted and its `drop` is
// inlined — and `size_of_val` / `align_of_val` of a bare `dyn Trait`.
//
// Inside `library/alloc` (where `Box` is a plain LOCAL ADT and nothing inlines
// at `-O0`) `Box::drop` opens with
//
//     _2 = copy ((*_1).0: Unique<dyn T>);
//     _5 = Unique::<dyn T>::as_ptr(copy _2);
//     _4 = move _5 as *const dyn T (PtrToPtr);          // fat -> FAT
//     _3 = Layout::for_value_raw::<dyn T>(move _4);    // size_of_val / align_of_val
//
// and refused at the `PtrToPtr` with `[TCG-POINTEE-DYN-VALUE]`, then (had it got
// past) in `for_value_raw` with `[TCG-SIZE-OF-VAL-UNSIZED]`. `size_of_boxed` /
// `align_of_boxed` below are that opening verbatim in shape over a `Unique<dyn
// Tr>`-carrying `UBox` — their MIR carries the same `_4 = move _5 as *const dyn
// Tr (PtrToPtr)` — and `size_raw` / `align_raw` are the intrinsics on a `*const
// dyn` param.
//
// `call_const` / `call_const_of_call` are CONTROLS, not `PtrToPtr` rows: in
// NON-generic source rustc spells `p as *const dyn Tr` as an identity
// `PointerCoercion(Unsize, AsCast)` (a `PtrToPtr` only appears where the pointee
// is a type PARAMETER, as in `Box::drop`), which the pre-existing identity-unsize
// path lowers. They pin that the two spellings of one cast agree.
//
// WHY EVERY ROW IS A WRONG NUMBER IF A LANE OR A SLOT IS WRONG:
//   * `42` / `9` / `42` — `Tr::v` dispatched through the cast pointer: a dropped
//     or swapped vtable lane calls through garbage.
//   * `24` / `8` and `16` / `16`, twice — `S` (three `i64`) and `T16`
//     (`repr(align(16))`) answered from the VTABLE's size word (slot 1) and align
//     word (slot 2), through the `PtrToPtr` result and directly. Slot 0 is the
//     `drop_in_place` pointer, so an off-by-one slot prints an address or `0`;
//     the two types differ in both answers, so a size/align swap shows on `S`
//     (24 vs 8) and a constant answer shows on the pair. A `PtrToPtr` that tore
//     the pair reads a vtable word out of the data (`S`'s own fields).
//
// ARITHMETIC-FREE on purpose (see the harness header on `AArch64::CSet`).
#![feature(ptr_internals, layout_for_ptr)]
#![allow(dead_code)]

use core::ptr::Unique;
use std::alloc::Layout;

trait Tr {
    fn v(&self) -> i64;
}
struct S {
    a: i64,
    b: i64,
    c: i64,
}
impl Tr for S {
    fn v(&self) -> i64 {
        self.a
    }
}
#[repr(align(16))]
struct T16 {
    a: i64,
}
impl Tr for T16 {
    fn v(&self) -> i64 {
        9
    }
}
static mut G: S = S { a: 42, b: 1, c: 2 };

struct Zst;
/// `Box`'s field shape inside `alloc`: a `Unique<T>` beside a 1-ZST.
struct UBox<T: ?Sized>(Unique<T>, Zst);

#[inline(never)]
fn ptr_s() -> *mut dyn Tr {
    let q: *mut S = core::hint::black_box(&raw mut G);
    q
}
#[inline(never)]
fn ptr_t(r: &mut T16) -> *mut dyn Tr {
    let q: *mut T16 = core::hint::black_box(r as *mut T16);
    q
}
#[inline(never)]
fn ubox(p: *mut dyn Tr) -> UBox<dyn Tr> {
    UBox(unsafe { Unique::new_unchecked(p) }, Zst)
}
/// CONTROL: `p as *const dyn Tr` of a PARAMETER — an identity `Unsize(AsCast)`
/// in this non-generic body, not a `PtrToPtr` — then a dispatch.
#[inline(never)]
fn call_const(p: *mut dyn Tr) -> i64 {
    let q = p as *const dyn Tr;
    unsafe { (*q).v() }
}
/// CONTROL: the same cast of a CALL RESULT.
#[inline(never)]
fn call_const_of_call() -> i64 {
    let p = ptr_s();
    let q = p as *const dyn Tr;
    unsafe { (*q).v() }
}
/// `Box::drop`'s opening: `Unique::as_ptr`, the fat -> fat `PtrToPtr`, and
/// `Layout::for_value_raw` (the vtable's size word).
#[inline(never)]
fn size_of_boxed(b: &mut UBox<dyn Tr>) -> usize {
    let ptr = b.0;
    let layout = unsafe { Layout::for_value_raw(ptr.as_ptr()) };
    layout.size()
}
/// The same, reading the vtable's align word.
#[inline(never)]
fn align_of_boxed(b: &mut UBox<dyn Tr>) -> usize {
    let ptr = b.0;
    let layout = unsafe { Layout::for_value_raw(ptr.as_ptr()) };
    layout.align()
}
#[inline(never)]
fn size_raw(p: *const dyn Tr) -> usize {
    unsafe { std::mem::size_of_val_raw(p) }
}
#[inline(never)]
fn align_raw(p: *const dyn Tr) -> usize {
    unsafe { std::mem::align_of_val_raw(p) }
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
    let p = ptr_s();
    let mut h = T16 { a: 5 };
    let t = ptr_t(&mut h);
    emit(call_const(p));
    emit(call_const(t));
    emit(call_const_of_call());
    let mut bs = ubox(p);
    let mut bt = ubox(t);
    emit_u(size_of_boxed(&mut bs));
    emit_u(align_of_boxed(&mut bs));
    emit_u(size_of_boxed(&mut bt));
    emit_u(align_of_boxed(&mut bt));
    emit_u(size_raw(p));
    emit_u(align_raw(p));
    emit_u(size_raw(t));
    emit_u(align_raw(t));
}
