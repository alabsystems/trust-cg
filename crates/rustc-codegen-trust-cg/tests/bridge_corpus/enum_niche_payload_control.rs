// TRAP CONTROL — `Option<NonZeroU8>` has an IDENTICAL repr signature to
// `Result<(), fmt::Error>`: `size 1`, `align 1`,
// `BackendRepr::Scalar(Primitive::Int(I8, unsigned))`. Its semantics are the
// OPPOSITE: `TagEncoding::Niche`, where the scalar IS THE PAYLOAD and `None` is
// one unused bit pattern.
//
// A tag-only-enum widening written on the REPR alone would admit this type and
// silently miscompile every `Some(x)` construction and every `discriminant()`
// — and the census would score the miscompile as PROGRESS. This fixture is the
// falsifier: every check below is value-checked against LLVM, so an admitted
// niche shows up as a wrong exit code rather than as a green count.
//
// This half uses only BY-VALUE positions, which COMPILE AND MATCH on the
// unpatched backend — so it is a LIVE falsifier, not a row that passes by
// refusing. The struct-FIELD position the widening actually opens up is the
// separate `enum_niche_payload_field_control.rs` (which refuses today).
//
// All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;
use core::mem::discriminant;
use core::num::NonZeroU8;

#[inline(never)]
fn wrap(v: u8) -> Option<NonZeroU8> {
    NonZeroU8::new(v)
}

#[inline(never)]
fn unwrap_or_zero(o: Option<NonZeroU8>) -> u8 {
    match o {
        Some(n) => n.get(),
        None => 0,
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // Round-trip: the payload must survive, not be replaced by a tag.
    let ok_a = unwrap_or_zero(wrap(black_box(200))) == 200
        && unwrap_or_zero(wrap(black_box(1))) == 1
        && unwrap_or_zero(wrap(black_box(255))) == 255
        && unwrap_or_zero(wrap(black_box(0))) == 0;

    // `discriminant` must distinguish None from Some, and must NOT distinguish
    // two different Some payloads.
    let ok_b = discriminant(&wrap(black_box(1))) == discriminant(&wrap(black_box(200)))
        && discriminant(&wrap(black_box(1))) != discriminant(&wrap(black_box(0)));

    // A branch-varying niche value through a join.
    let joined = if black_box(3u32) == 3 { wrap(black_box(9)) } else { None };
    let ok_c = unwrap_or_zero(joined) == 9;

    if ok_a && ok_b && ok_c {
        7
    } else {
        13
    }
}
