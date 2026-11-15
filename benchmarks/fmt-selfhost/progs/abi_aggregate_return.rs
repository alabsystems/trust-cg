// abi_aggregate_return — the RETURN CONVENTION of an `rt::Argument`-shaped
// aggregate: the hidden caller-allocated return buffer, running.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `ArgTy` has the layout of `core::fmt::rt::ArgumentType`: a two-variant,
// niche-encoded, 16-byte `BackendRepr::Memory` enum. Under the RUST ABI rustc
// returns it through the hidden return buffer (`PassMode::Indirect`, `x8` on
// AAPCS64) — NOT in `x0`/`x1`, which is what the C aggregate-return rule for a
// 16-byte value would say. A whole-program differential like this one cannot
// see the difference: it compiles caller and callee with the same backend, so a
// calling-convention disagreement is self-consistent. Measured 2026-09-10, with
// the callee in a separately compiled rlib and trust-cg returning the value in
// `x0`/`x1`:
//
//     caller  callee    result
//     LLVM    LLVM      42          (the oracle)
//     trust-cg trust-cg 42          (self-consistent)
//     LLVM    trust-cg  0           a SILENT WRONG VALUE
//     trust-cg LLVM     exit 138    a crash
//
// This program was, for that reason, pinned as a NAMED REFUSAL: `[TCG-RET-ABI]`
// declined it rather than emit a divergent object.
//
// It is a RUNNING row again as of 2026-09-11: the indirect-return convention is
// implemented end to end (the callee writes through the `x8` buffer, the caller
// allocates the buffer and passes its address there), and all four mixed-link
// directions now exit 42 at `-Copt-level=0` and `-Copt-level=2`. The
// `[TCG-RET-ABI]` gate is UNCHANGED and still runs on every by-value aggregate
// return — it is silent here because the two classifiers now agree, which is the
// only evidence that they do. The mixed-link table itself is measured by
// `../sret-xback/run.sh`, which links across backends; this program pins that
// the shape compiles and produces the right value.
use std::marker::PhantomData;
use std::ptr::NonNull;

pub enum ArgTy<'a> {
    Placeholder {
        value: NonNull<()>,
        formatter: unsafe fn(NonNull<()>, &mut u32) -> u32,
        _lifetime: PhantomData<&'a ()>,
    },
    Count(usize),
}

unsafe fn formatter_stub(_v: NonNull<()>, _f: &mut u32) -> u32 {
    0
}

#[inline(never)]
fn make(x: &i32) -> ArgTy<'_> {
    if *x < 0 {
        ArgTy::Count(11)
    } else {
        ArgTy::Placeholder {
            value: NonNull::from(x).cast(),
            formatter: formatter_stub,
            _lifetime: PhantomData,
        }
    }
}

fn main() {
    let v = 42i32;
    match make(&v) {
        ArgTy::Placeholder { value, .. } => {
            println!("placeholder={}", unsafe { *value.cast::<i32>().as_ptr() })
        }
        ArgTy::Count(n) => println!("count={n}"),
    }
}
