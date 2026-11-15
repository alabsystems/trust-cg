// CORPUS FIXTURE — a TAG-ONLY enum: every variant carries only ZERO-SIZED
// fields, so the value is nothing but its tag.
//
// `Result<(), core::fmt::Error>` is the shape: `Ok(())` and `Err(fmt::Error)`
// are both zero-sized payloads, `size == 1`, `align == 1`, one Direct-encoded
// `u8` tag. It is the return type of every `core::fmt::Write` / `Debug` method,
// and before this lowering `rust_ty_to_trust_ir_ty` had no arm for it: the
// fieldless-enum arm demanded `v.fields.is_empty()`, which `Ok(())` fails by
// HAVING a field — a zero-sized one. The census showed 16 `library/core` roots
// stopping there, all in `core::fmt::builders` (`DebugStruct::finish`,
// `DebugMap::key_with`, ...).
//
// THE SHAPE THAT ACTUALLY REFUSED is (f): the type as a STRUCT FIELD.
// `core::fmt::builders::DebugStruct` is `{ fmt: &mut Formatter, result:
// fmt::Result, has_fields: bool }`, and the type mapper is asked "what scalar
// is this struct field" from `memory_aggregate_layout` /
// `validate_memory_aggregate_field_leaves`. Measured on the unpatched
// integration backend: the by-value shapes (a)-(e) ALREADY compiled and matched
// LLVM through the memory-backed enum path — only (f) refused, with exactly the
// census's `Ty::core::result::Result<(), core::fmt::Error>`. (a)-(e) are kept
// as the regression half: the widening moves them from the memory path onto the
// scalar path, so they must keep agreeing with LLVM.
//
// Checks, all value-checked so a wrong tag is visible rather than merely
// compiling: (a) construct + match both variants; (b) `?` on the type (the
// `FromResidual` path a `write!` chain takes); (c) pass BY VALUE across a
// `#[inline(never)]` boundary in both directions; (d) `mem::discriminant`
// equality/inequality; (e) a branch-varying value threaded through a join;
// (f) the `DebugStruct` shape — the type as a struct FIELD, written and read
// across a loop so the field carries a runtime-varying tag.
// All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::fmt;
use core::hint::black_box;
use core::mem::discriminant;

type R = Result<(), fmt::Error>;

#[inline(never)]
fn take_by_value(r: R) -> bool {
    matches!(r, Err(fmt::Error))
}

#[inline(never)]
fn make(fail: bool) -> R {
    if fail { Err(fmt::Error) } else { Ok(()) }
}

#[inline(never)]
fn chain(a: bool, b: bool) -> R {
    make(a)?;
    make(b)?;
    Ok(())
}

/// The `core::fmt::builders::DebugStruct` shape: a struct carrying a
/// `fmt::Result` FIELD alongside other scalars, short-circuiting on the first
/// `Err` exactly as `DebugStruct::field` does.
struct Builder {
    result: R,
    written: u32,
}

#[inline(never)]
fn build(fail_at: u32) -> Builder {
    let mut b = Builder {
        result: Ok(()),
        written: 0,
    };
    let mut i = 0u32;
    while i < 4 {
        if b.result.is_ok() {
            b.written += 1;
            if i == fail_at {
                b.result = Err(fmt::Error);
            }
        }
        i += 1;
    }
    b
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) construct + match both variants.
    let ok_a = matches!(make(black_box(false)), Ok(())) && matches!(make(black_box(true)), Err(_));

    // (b) `?` short-circuits on the first Err and only then.
    let ok_b = chain(black_box(false), black_box(false)).is_ok()
        && chain(black_box(true), black_box(false)).is_err()
        && chain(black_box(false), black_box(true)).is_err();

    // (c) by-value across a call boundary, both directions.
    let ok_c = take_by_value(make(black_box(true))) && !take_by_value(make(black_box(false)));

    // (d) discriminant identity.
    let ok_d = discriminant(&make(black_box(true))) == discriminant(&make(black_box(true)))
        && discriminant(&make(black_box(true))) != discriminant(&make(black_box(false)));

    // (e) a BRANCH-VARYING tag-only value surviving a join: the compile-time
    // discriminant binding is dropped at a join, so only a real runtime scalar
    // gets this right.
    let joined: R = if black_box(1u32) == 1 { Err(fmt::Error) } else { Ok(()) };
    let ok_e = joined.is_err();

    // (f) the struct-FIELD shape — the one the census measured refusing.
    let stop_early = build(black_box(2));
    let never_fails = build(black_box(9));
    let ok_f = stop_early.result.is_err()
        && stop_early.written == 3
        && never_fails.result.is_ok()
        && never_fails.written == 4;

    if ok_a && ok_b && ok_c && ok_d && ok_e && ok_f {
        7
    } else {
        13
    }
}
