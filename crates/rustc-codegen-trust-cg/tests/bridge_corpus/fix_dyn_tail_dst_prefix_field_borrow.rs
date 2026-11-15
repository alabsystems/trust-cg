// FIXTURE: a borrow of a SIZED PREFIX FIELD of a DST whose TAIL is `dyn Trait`,
// reached through the DST's own `{ data, vtable }` WIDE pointer — in BOTH
// spellings rustc emits (`&mut (*p).f` / `&raw mut (*p).f`), at three distinct
// offsets, through an ENTRY-ARG base and through a `&mut *p` LOCAL REBORROW.
//
// This is `core::error::Request` — `struct Tagged<E: ?Sized> { tag_id: TypeId,
// value: E }` with `E = dyn Erased` — and it is the VTABLE-metadata twin of
// `fix_dst_prefix_field_borrow.rs`'s LENGTH-metadata rows.
//
// WHY IT IS A SEPARATE FIXTURE, AND WHAT IT PINS. The wide-deref-base refusal
// that makes the slice-tail rows sound was first written keyed on EVERY wide
// pointer (`is_wide_pointer_memory_leaf_ty`). That is one direction of a two-way
// distinction, and the other direction was already WORKING: for a VTABLE-metadata
// base the local's single scalar value IS the pointee's address, because the
// entry-arg loop declares exactly this class (`is_vtable_pair_abi_ref_ty`) as two
// `Ptr` block params with `ValueId(arg.index())` pushed FIRST as the DATA lane.
// The over-broad refusal withdrew four measured, LLVM-exact capabilities and
// bought ZERO census roots, while printing — of this very type — "its single
// scalar value is not the pointee's address".
//
// MEASURED (`-Copt-level=0`, 2026-09-27), all four rows below:
//   * pre-refusal tree      : COMPILED, LLVM-exact.
//   * over-broad refusal    : REFUSED, `[TCG-WIDEPTR-DEREF-BASE]` (the `&`/`&mut`
//                             rows) and the untagged `Rvalue::RawPtr (unsupported
//                             &raw shape …)` fall-through (the `&raw` rows).
//   * narrowed refusal      : COMPILED, LLVM-exact again.
//
// HOW IT FAILS IF THE NARROWING IS REVERTED. Both of this fixture's rows stop
// compiling, `compiled` falls by 2, and the `COMPILED_FLOOR` assertion in
// `unsized_value_measurement_differential.rs` fails by name. Reverting only the
// `&`/`&mut` half or only the `&raw` half is equally fatal: `fill_ref` and
// `fill_raw` are in the SAME binary, so either reversion refuses the crate.
//
// WHY THE FIELD WIDTHS ARE UNEQUAL, and why `value` is READ BACK. `a: u8, b: u64,
// c: u16` under `repr(Rust)` gives rustc's layout no reason to match declaration
// order, so an addressing model that folds offsets in DECLARATION order disagrees
// at every field. `value` is printed after every write and DISPATCHED through the
// trait: a prefix store that overran into the tail, or a base taken from a 16-byte
// `{ data, vtable }` slot's own address instead of its data lane, shows up as a
// wrong payload, a wrong dispatch result, or a trap.
//
// No `{:?}`, no projected argument places in the printed expressions, and every
// value is bound to a bare local before formatting: the bridge's `core::fmt`
// interception declines Debug placeholders and projected operands, and those
// refusals are not what this fixture is about.

trait Erased {
    fn id(&self) -> u64;
}

struct Leaf {
    v: u64,
}

impl Erased for Leaf {
    fn id(&self) -> u64 {
        self.v
    }
}

struct Tagged<E: ?Sized> {
    a: u8,
    b: u64,
    c: u16,
    value: E,
}

/// The `Rvalue::Ref` spelling, three prefix offsets, base is an ENTRY ARG.
#[inline(never)]
fn fill_ref(p: &mut Tagged<dyn Erased>) {
    let pa: &mut u8 = &mut (*p).a;
    *pa = 0x5A;
    let pb: &mut u64 = &mut (*p).b;
    *pb = 0x0102_0304_0506_0708;
    let pc: &mut u16 = &mut (*p).c;
    *pc = 0xFEED;
}

/// The `Rvalue::RawPtr` spelling of the SAME three fields. Must produce the
/// identical addresses as `fill_ref`.
#[inline(never)]
fn fill_raw(p: &mut Tagged<dyn Erased>) {
    unsafe {
        let pa: *mut u8 = &raw mut (*p).a;
        let pb: *mut u64 = &raw mut (*p).b;
        let pc: *mut u16 = &raw mut (*p).c;
        pa.write(0xA5);
        pb.write(0x1122_3344_5566_7788);
        pc.write(0xBEEF);
    }
}

/// SHARED prefix borrows read back, both spellings.
#[inline(never)]
fn read_ref(p: &Tagged<dyn Erased>) -> u64 {
    let rb: &u64 = &(*p).b;
    *rb
}

#[inline(never)]
fn read_raw(p: &Tagged<dyn Erased>) -> u64 {
    unsafe {
        let rb: *const u64 = &raw const (*p).b;
        rb.read()
    }
}

/// The base is a LOCAL REBORROW (`&mut *p`), not an entry arg — so the base local
/// is resolved from `ctx.scalar_values` rather than from the entry-arg fallback.
/// Both resolutions must yield the data lane; this row is the one that says so.
#[inline(never)]
fn fill_via_local_reborrow(p: &mut Tagged<dyn Erased>) {
    let r2: &mut Tagged<dyn Erased> = &mut *p;
    let pb: &mut u64 = &mut (*r2).b;
    *pb = 0x00DE_CAF0_0BAD_F00D;
    let pa: &mut u8 = &mut (*r2).a;
    *pa = 0x77;
}

fn main() {
    let mut h: Tagged<Leaf> = Tagged {
        a: 0,
        b: 0,
        c: 0,
        value: Leaf { v: 777 },
    };

    {
        let r: &mut Tagged<dyn Erased> = &mut h;
        fill_ref(r);
    }
    let a1 = h.a as u64;
    let b1 = h.b;
    let c1 = h.c as u64;
    let v1 = h.value.v;
    let d1 = h.value.id();
    println!("ref a={} b={} c={}", a1, b1, c1);
    println!("ref value={} dispatch={}", v1, d1);

    {
        let r: &mut Tagged<dyn Erased> = &mut h;
        fill_raw(r);
    }
    let a2 = h.a as u64;
    let b2 = h.b;
    let c2 = h.c as u64;
    let v2 = h.value.v;
    let d2 = h.value.id();
    println!("raw a={} b={} c={}", a2, b2, c2);
    println!("raw value={} dispatch={}", v2, d2);

    {
        let r: &mut Tagged<dyn Erased> = &mut h;
        fill_via_local_reborrow(r);
    }
    let a3 = h.a as u64;
    let b3 = h.b;
    let c3 = h.c as u64;
    let v3 = h.value.v;
    println!("lrb a={} b={} c={}", a3, b3, c3);
    println!("lrb value={}", v3);

    let rr;
    let rw;
    {
        let r: &Tagged<dyn Erased> = &h;
        rr = read_ref(r);
        rw = read_raw(r);
    }
    println!("read ref={} raw={}", rr, rw);
}
