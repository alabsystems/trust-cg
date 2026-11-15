// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Compiled by the bridge (and by LLVM for the oracle). A `Vec<u32, Fwd>` with a
// non-Global allocator is not the bridge's modeled Vec, so its `Vec::drain`, its
// `vec::Drain<u32, Fwd>` and that Drain's drop are std's own code end to end:
// the bridge must not apply its Global Drain model to any of them.
#![feature(allocator_api)]
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::ptr::NonNull;
use std::vec::Drain;

/// Forwards to `Global`; a distinct allocator type all the same.
#[derive(Clone, Copy)]
pub struct Fwd;

unsafe impl Allocator for Fwd {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unsafe { Global.deallocate(ptr, layout) }
    }
}

#[inline(never)]
pub fn make(v: &mut Vec<u32, Fwd>, k: usize) -> Drain<'_, u32, Fwd> {
    v.drain(k..)
}

#[inline(never)]
pub fn sink(_d: Drain<'_, u32, Fwd>) {}

#[inline(never)]
pub fn sum_from(v: &mut Vec<u32, Fwd>, k: usize) -> u32 {
    let mut s = 0;
    for x in v.drain(k..) {
        s = s * 10 + x;
    }
    s
}
