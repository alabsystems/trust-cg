// SOUNDNESS-EDGE CONTROL — a payload-bearing enum with an UNINHABITED sibling
// variant. `Result<Infallible, u64>` is `size 8`, `Variants::Single` on the
// `Err` variant (the `Ok` variant is uninhabited and carries no layout), so its
// value IS its payload, not a tag. A tag-only widening that keyed on "one
// inhabited variant" or on the layout's scalar-ness would return 0/1 here.
//
// `g(Err(7))` must exit 7. A second, MULTI-FIELD payload (`Report`) is held
// alongside it: `Result<Infallible, Report>` is the shape the type mapper's
// existing ZST-enum comment names as the one that must KEEP its memory-backed
// path, and a tag-only widening that looked only at inhabited-variant COUNT
// would take it.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::convert::Infallible;
use core::hint::black_box;

#[inline(never)]
fn g(r: Result<Infallible, u64>) -> u64 {
    match r {
        Err(e) => e,
    }
}

#[derive(Clone, Copy)]
struct Report {
    code: u16,
    detail: u32,
}

#[inline(never)]
fn report_of(code: u16, detail: u32) -> u32 {
    // An uninhabited `Ok` sibling with a MULTI-FIELD payload `Err`: the value is
    // the payload, and there is no tag at all (`Variants::Single`). Built as a
    // LOCAL rather than taken as a parameter so the fixture is not blocked by
    // the unrelated `[TCG-ARG-ABI]` by-value-aggregate class — and matched BY
    // VALUE, because exhaustiveness over an uninhabited sibling is only granted
    // to a by-value match (E0004 otherwise).
    let r: Result<Infallible, Report> = Err(Report { code, detail });
    match r {
        Err(e) => e.detail + u32::from(e.code),
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let v = g(Err(black_box(7u64)));
    if v != 7 {
        return 13;
    }
    let d = report_of(black_box(11u16), black_box(31u32));
    if d != 42 {
        return 14;
    }
    v as i32
}
