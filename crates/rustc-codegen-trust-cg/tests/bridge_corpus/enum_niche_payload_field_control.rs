// TRAP CONTROL, STRUCT-FIELD POSITION — the companion to
// `enum_niche_payload_control.rs`.
//
// The tag-only-enum widening opens up exactly one new position: an enum as a
// FIELD of a memory-candidate aggregate (`core::fmt::builders::DebugStruct`'s
// `result: fmt::Result`), where the type mapper is asked "what scalar is this
// struct field". `Option<NonZeroU8>` has that lane's exact repr signature —
// `size 1`, `align 1`, `BackendRepr::Scalar(Primitive::Int(I8, unsigned))` —
// and is `TagEncoding::Niche`, where the scalar IS THE PAYLOAD.
//
// So the control has to occupy the NEW position, not just the old ones. On the
// unpatched backend this fixture fails closed (`Ty::core::option::Option<
// core::num::nonzero::NonZero<u8>>`), which is an honest INCOMPLETE. What it
// forbids is the other outcome: a predicate written on the repr alone would
// make this COMPILE and write a 0/1 tag where the payload belongs, and the
// census would score that miscompile as PROGRESS. Every payload below is
// value-checked against LLVM.
//
// All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;
use core::num::NonZeroU8;

#[inline(never)]
fn unwrap_or_zero(o: Option<NonZeroU8>) -> u8 {
    match o {
        Some(n) => n.get(),
        None => 0,
    }
}

/// `Option<NonZeroU8>` as a field of a memory-candidate aggregate, alongside an
/// ordinary scalar so the aggregate really has several leaves.
struct Slots {
    a: Option<NonZeroU8>,
    b: Option<NonZeroU8>,
    seq: u32,
}

#[inline(never)]
fn slots(x: u8, y: u8) -> Slots {
    let mut s = Slots {
        a: None,
        b: None,
        seq: 0,
    };
    s.a = NonZeroU8::new(x);
    if s.a.is_some() {
        s.seq += 1;
    }
    s.b = NonZeroU8::new(y);
    if s.b.is_some() {
        s.seq += 1;
    }
    s
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let s = slots(black_box(200), black_box(0));
    let t = slots(black_box(1), black_box(255));
    let ok = unwrap_or_zero(s.a) == 200
        && unwrap_or_zero(s.b) == 0
        && s.seq == 1
        && unwrap_or_zero(t.a) == 1
        && unwrap_or_zero(t.b) == 255
        && t.seq == 2;
    if ok { 7 } else { 13 }
}
