// The CALLEE half of the indirect-return cross-boundary gate.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `ArgTy` has the layout of `core::fmt::rt::ArgumentType`: a two-variant,
// niche-encoded, 16-byte `BackendRepr::Memory` enum. rustc's Rust ABI returns
// it `PassMode::Indirect` — through a buffer the CALLER allocates, whose
// address arrives in `x8` (AAPCS64) or `rdi` (System V). The C rule for a
// 16-byte aggregate would say `x0`/`x1` instead, so a backend that applies the
// C rule here is self-consistent and wrong.
//
// `#[inline(never)]` plus a separate crate is what makes the call cross a
// codegen boundary: without both, the caller inlines the callee and the two
// halves can never disagree.
#![crate_type = "rlib"]
#![crate_name = "sretcallee"]

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
pub fn probe_make(x: &i32) -> ArgTy<'_> {
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
