// Corpus: a TRAIT-OBJECT fat pointer NARROWING to a thin one —
// `*mut dyn Trait as *mut ()` — and the `NonNull::<dyn Trait>::new_unchecked`
// that contains one.
//
// `lower_wide_to_thin_ptr_cast` handles this for the LENGTH metadata kind
// (`*const [T] as *const T`) and deliberately excludes `dyn`; the vtable kind had
// no arm at all, so `rust_ty_to_trust_ir_ty(*mut dyn Trait)` was asked for one
// scalar type and refused with `[TCG-POINTEE-DYN-VALUE]`. That refusal cost
// `library/alloc` two roots — `NonNull::<dyn Error + Sync + Send>::new_unchecked`
// and `Unique::<dyn Error + Sync + Send>::new_unchecked` — because
// `assert_unsafe_precondition!(check_language_ub, .., (ptr: *mut () = ptr as *mut
// ()) => !ptr.is_null())` puts exactly this cast in their MIR at EVERY opt level
// (the `ub_checks()` switch is not folded at `-O0`).
//
// WHY THE ROWS ARE VALUES AND NOT A CRASH:
//   * `42` from `read_a` — the thin pointer must be the DATA lane. If the VTABLE
//     lane were taken instead, `(*(t as *const S)).a` reads the vtable's first
//     word (the `drop_in_place` slot, i.e. a code address or 0) and prints that.
//   * `99` from `read_b` — the SAME address, read at field offset 8. A thin
//     pointer taken from the wrong lane, or an address off by the fat pointer's
//     own 8-byte metadata offset, prints `42` here instead of `99` (the
//     off-by-one-lane signature) or garbage.
//   * `42` from `nn.as_ref().v()` — the fat pointer that the same function
//     TRANSMUTES into `NonNull<dyn Trait>` must keep BOTH lanes: a dropped vtable
//     makes the virtual call jump through whatever is in the slot. This is the
//     "what WRITES the same bytes" half of the read fixed above: the narrowing
//     cast must not disturb the source's two lanes.
//
// The `*mut dyn Trait` is produced through `black_box` so rustc's `-O2` pipeline
// cannot const-fold the unsize into a constant operand (which refuses for an
// unrelated reason, `trait-object unsize source is not a place operand`) and the
// row stays live at both opt levels. Arithmetic-free on purpose: a multiply or a
// comparison lowers to `AArch64::CSet`, which this host's opcode-proof inventory
// does not map, and the `[TCG-PROOF-465]` refusal would hide the real verdict.
#![allow(dead_code)]

use core::ptr::NonNull;

trait Tr {
    fn v(&self) -> i64;
}

struct S {
    a: i64,
    b: i64,
}

impl Tr for S {
    fn v(&self) -> i64 {
        self.a
    }
}

static mut G: S = S { a: 42, b: 99 };

/// Builds the `*mut dyn Tr`. `black_box` keeps the unsize source a runtime PLACE.
#[inline(never)]
fn ptr_of() -> *mut dyn Tr {
    let q: *mut S = core::hint::black_box(unsafe { &raw mut G });
    q
}

/// The narrowing cast itself.
#[inline(never)]
unsafe fn thin_of(p: *mut dyn Tr) -> *mut () {
    p as *mut ()
}

/// The same shape `NonNull::new_unchecked` has: the narrowing cast for the null
/// probe, then a two-lane transmute of the untouched source.
#[inline(never)]
unsafe fn nn_of(p: *mut dyn Tr) -> NonNull<dyn Tr> {
    unsafe { NonNull::new_unchecked(p) }
}

#[inline(never)]
fn read_a(t: *mut ()) -> i64 {
    unsafe { (*(t as *const S)).a }
}
#[inline(never)]
fn read_b(t: *mut ()) -> i64 {
    unsafe { (*(t as *const S)).b }
}
#[inline(never)]
fn emit(x: i64) {
    println!("{}", x);
}

fn main() {
    let p = ptr_of();
    let t = unsafe { thin_of(p) };
    emit(read_a(t));
    emit(read_b(t));
    let nn = unsafe { nn_of(p) };
    emit(unsafe { nn.as_ref().v() });
}
