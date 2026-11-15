// Corpus: a TRAIT UPCAST — `&dyn Ext` -> `&dyn Base` where `Ext: Base`.
//
// The bridge refused EVERY principal-trait mismatch, on the argument that "the
// destination's (super)trait vtable is NOT in general the source vtable — copying
// it would dispatch through the wrong vtable". That argument is right in general
// and wrong for this case, and the difference is not ours to decide:
// `tcx.supertrait_vtable_slot((src_pointee, dst_pointee))` is rustc's OWN answer —
// `None` when the target's vtable is a PREFIX of the source's (the single-
// inheritance chain, which is this shape) and `Some(idx)` when a supertrait vptr
// must be LOADED from that slot. rustc's codegen branches on exactly this value.
//
// Taking rustc's answer instead of deriving the layout is the whole point: a
// hand-rolled "supertrait vtables are prefixes" rule dispatches through the wrong
// vtable when it is wrong, and NOTHING DOWNSTREAM WOULD CATCH IT — the call would
// simply land on another function.
//
// UPDATED 2026-09-26: the `Some(idx)` half no longer fails closed. The emitter
// builds the nested `VtblEntry::TraitVPtr` table as its own read-only global and
// the upcast LOADS the destination vtable out of slot `idx` (scaled by
// `pointer_size`, as `rustc_codegen_ssa` does). This file still covers only the
// `None` / PREFIX half — `Ext: Base` is single inheritance, so there is no vptr
// slot to load — and the `Some(idx)` half is covered by
// `dyn_supertrait_vptr_upcast.rs`, which is wired into
// `tests/dyn_fat_leaf_differential.rs`. NOTE: no test target includes THIS file;
// it has been orphaned since it was written, so nothing runs it.
//
// WHY EVERY ROW IS A WRONG NUMBER, NOT A CRASH, IF THE VTABLE IS WRONG: two impls
// whose methods return DIFFERENT values, dispatched through the UPCAST pointer.
//   * `u 107 209` — upcast, then call the BASE method. A vtable that still
//     dispatches as `Ext` would call `e()` and print `1007 2009`; one that picked
//     the wrong object prints the other impl's value.
//   * `v 107 209` — the upcast result passed ACROSS a second ABI boundary into a
//     `&dyn Base` parameter, so the pair must survive as a pair.
//   * `e 1007 2009` — the EXT method through the original pointer still works;
//     this pins that the upcast did not disturb the source.
#![allow(dead_code)]

trait Base {
    fn b(&self) -> i64;
}

trait Ext: Base {
    fn e(&self) -> i64;
}

struct A(i64);
struct B(i64);

impl Base for A {
    fn b(&self) -> i64 {
        self.0 + 100
    }
}
impl Ext for A {
    fn e(&self) -> i64 {
        self.0 + 1000
    }
}
impl Base for B {
    fn b(&self) -> i64 {
        self.0 + 200
    }
}
impl Ext for B {
    fn e(&self) -> i64 {
        self.0 + 2000
    }
}

#[inline(never)]
fn upcast<'a>(x: &'a dyn Ext) -> &'a dyn Base {
    x
}

#[inline(never)]
fn via_base(x: &dyn Base) -> i64 {
    x.b()
}

fn main() {
    let a = A(7);
    let b = B(9);
    let ea: &dyn Ext = &a;
    let eb: &dyn Ext = &b;

    let u1 = upcast(ea).b();
    let u2 = upcast(eb).b();
    println!("u {} {}", u1, u2); // 107 209

    let v1 = via_base(upcast(ea));
    let v2 = via_base(upcast(eb));
    println!("v {} {}", v1, v2); // 107 209

    let e1 = ea.e();
    let e2 = eb.e();
    println!("e {} {}", e1, e2); // 1007 2009
}
