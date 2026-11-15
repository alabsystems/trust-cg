// CORPUS FIXTURE — the rest of the TAG-ONLY enum class (see
// `enum_tag_only_result_fmt_error.rs` for the class and why it was refused).
//
// (a) `Option<()>`   — `Some(())` HAS a field; it is zero-sized.
// (b) `Option<PhantomData<u64>>` — a generic parameter that instantiates to a
//     ZST, which is why the predicate must ask the INSTANTIATED field type
//     (`f.ty(tcx, args)`) and not the declared one.
// (c) a user enum whose variants carry zero-sized payloads of three different
//     shapes (unit struct, `()`, `[u8; 0]`) under `#[repr(i8)]` with NEGATIVE
//     explicit discriminants — the width AND signedness must come from rustc's
//     own layout, never from the variant count or the `repr` attribute.
// (d) the same enum threaded through a `match` that returns its discriminant,
//     so a sign-extension mistake on the negative tag is value-visible.
// (e) each of them as a STRUCT FIELD — the shape the census actually measured
//     refusing (see `enum_tag_only_result_fmt_error.rs`): the type mapper is
//     asked "what scalar is this struct field", and the by-value shapes above
//     already compiled through the memory-backed enum path.
//
// All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;
use core::marker::PhantomData;

#[derive(Clone, Copy)]
struct Marker;

#[derive(Clone, Copy)]
#[repr(i8)]
enum Sign {
    Neg(Marker) = -3,
    Zero(()) = 0,
    Pos([u8; 0]) = 5,
}

#[inline(never)]
fn pick(k: u32) -> Sign {
    match k {
        0 => Sign::Neg(Marker),
        1 => Sign::Zero(()),
        _ => Sign::Pos([]),
    }
}

#[inline(never)]
fn code(s: Sign) -> i32 {
    match s {
        Sign::Neg(_) => -3,
        Sign::Zero(_) => 0,
        Sign::Pos(_) => 5,
    }
}

#[inline(never)]
fn opt_unit(some: bool) -> Option<()> {
    if some { Some(()) } else { None }
}

#[inline(never)]
fn opt_phantom(some: bool) -> Option<PhantomData<u64>> {
    if some { Some(PhantomData) } else { None }
}

/// Each tag-only type as a struct FIELD, alongside an ordinary scalar so the
/// aggregate really is a multi-leaf memory candidate.
struct Slots {
    unit: Option<()>,
    phantom: Option<PhantomData<u64>>,
    sign: Sign,
    seq: u32,
}

#[inline(never)]
fn slots(k: u32) -> Slots {
    let mut s = Slots {
        unit: None,
        phantom: None,
        sign: Sign::Zero(()),
        seq: 0,
    };
    if k > 0 {
        s.unit = Some(());
        s.seq += 1;
    }
    if k > 1 {
        s.phantom = Some(PhantomData);
        s.seq += 1;
    }
    if k > 2 {
        s.sign = Sign::Neg(Marker);
        s.seq += 1;
    }
    s
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a)
    let ok_a = opt_unit(black_box(true)).is_some() && opt_unit(black_box(false)).is_none();

    // (b)
    let ok_b = opt_phantom(black_box(true)).is_some() && opt_phantom(black_box(false)).is_none();

    // (c)/(d) — negative discriminant round-trip, by value across a boundary.
    let ok_c = code(pick(black_box(0))) == -3
        && code(pick(black_box(1))) == 0
        && code(pick(black_box(2))) == 5;

    // A branch-varying tag-only value surviving a join.
    let joined = if black_box(2u32) == 2 { Sign::Neg(Marker) } else { Sign::Pos([]) };
    let ok_d = code(joined) == -3;

    // (e) the struct-FIELD shape.
    let none = slots(black_box(0));
    let all = slots(black_box(3));
    let ok_e = none.unit.is_none()
        && none.phantom.is_none()
        && code(none.sign) == 0
        && none.seq == 0
        && all.unit.is_some()
        && all.phantom.is_some()
        && code(all.sign) == -3
        && all.seq == 3;

    if ok_a && ok_b && ok_c && ok_d && ok_e {
        7
    } else {
        13
    }
}
