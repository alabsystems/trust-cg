// A CELLED return local: `&_0` is taken in the body, then `_0` is returned.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is `core::io::error::repr::Repr::new_custom` reduced to its MIR shape:
//
//     bb5:  _0 = Repr(copy _6, const PhantomData);
//           _9 = &_0;                       // <- the `&res` of the assert
//           _8 = Repr::tag(move _9) -> bb6;
//     ...
//     bb7: return;
//
// NRVO makes `res` BE `_0` (`debug res => _0`), so `&res` is `&_0`:
// `compute_scalar_cell_locals` gives `_0` a stack cell, and every whole-local
// write to `_0` then STORES into that cell (`lower_assign`'s cell arm /
// `finish_assign_target`'s) instead of binding an SSA scalar.
// `TerminatorKind::Return` asked `value_for_scalar_binding` for `_0`, found
// nothing in `scalar_values`, and FABRICATED the synthetic `ValueId(0)` — a
// never-defined SSA use, so the whole function failed closed at
//
//     [TCG-SSA-071] value ValueId(0) used in bb16 is never defined
//
// That was the one genuine capability loss of the reference-return cell
// widening: `new_custom` compiled BEFORE `cellable_reference_referent_ty`
// admitted `Repr`. The definition was never missing — it was in the cell, and
// the return was not looking there. The fix LOADS it (CAPABILITY, not
// soundness).
//
// The runtime value is load-bearing twice over: reading an uninitialized cell
// returns garbage (so `same`/`payload` move), and returning a STALE value would
// miss the `+ TAG_CUSTOM` the cell store carried (so `tag` moves).
use core::marker::PhantomData;
use core::ptr::NonNull;

const TAG_MASK: usize = 0b11;
const TAG_CUSTOM: usize = 0b01;

#[repr(align(8))]
struct Payload(u64);

static mut PAYLOAD: Payload = Payload(0xABCD_1234);

#[repr(transparent)]
struct Repr(NonNull<()>, PhantomData<u64>);

impl Repr {
    #[inline(never)]
    fn tag(&self) -> usize {
        (self.0.as_ptr() as usize) & TAG_MASK
    }

    // A `&self` method whose RETURN TYPE CARRIES A REFERENCE — the trigger for
    // the widened reference-escaping arm of `compute_scalar_cell_locals`, and
    // exactly what `Repr::data(&self) -> ErrorData<&Custom>` is in `library/core`.
    // A `&self` method returning a plain scalar (`tag()` below) does NOT cell the
    // receiver, so it does not reproduce this bug — that is the control on the
    // fixture itself.
    #[inline(never)]
    unsafe fn peek(&self) -> &u64 {
        unsafe { &*((((self.0.as_ptr() as usize) & !TAG_MASK) as *const u64)) }
    }

    // `&res` inside the body + `res` as the tail expression: the celled-`_0`
    // shape. `#[inline(never)]` keeps it a real body at every opt level.
    #[inline(never)]
    fn new_custom(base: *mut u8) -> Self {
        let p = base;
        let tagged = p.wrapping_add(TAG_CUSTOM).cast::<()>();
        let ptr = unsafe { NonNull::new_unchecked(tagged) };
        let res = Self(ptr, PhantomData);
        // The `&res` that cells `_0`. A plain `assert!` keeps it live at every
        // opt level (a `debug_assert!` is compiled out at -O2/-O3).
        assert!(unsafe { *res.peek() } != 0);
        res
    }

    #[inline(never)]
    fn addr_without_tag(&self) -> usize {
        (self.0.as_ptr() as usize) & !TAG_MASK
    }
}

fn main() {
    let raw = (&raw mut PAYLOAD) as *mut u8;
    let raw = std::hint::black_box(raw);
    let r = Repr::new_custom(raw);
    // 1. the tag survived the round trip through the cell,
    // 2. the pointer still addresses the SAME object (a garbage or stale load
    //    would not), and
    // 3. the payload is readable through it.
    let tag = r.tag();
    let base = r.addr_without_tag();
    let same = (base == raw as usize) as usize;
    let payload = unsafe { *(base as *const u64) };
    // One checksum: a garbage or stale cell load moves `tag` (1), `same` (1) or
    // `payload` (0xABCD1234) and the number changes.
    println!("{}", payload ^ ((tag as u64) << 40) ^ ((same as u64) << 48));
}
