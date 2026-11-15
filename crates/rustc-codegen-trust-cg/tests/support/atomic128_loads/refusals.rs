#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::{AtomicOrdering, atomic_cxchg};
#[unsafe(no_mangle)]
pub unsafe fn cas_u128(p: *mut u128, old: u128, value: u128) -> bool {
    unsafe {
        atomic_cxchg::<u128, { AtomicOrdering::SeqCst }, { AtomicOrdering::Acquire }>(p, old, value)
            .1
    }
}
#[unsafe(no_mangle)]
pub unsafe fn cas_i128(p: *mut i128, old: i128, value: i128) -> bool {
    unsafe {
        atomic_cxchg::<i128, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(
            p, old, value,
        )
        .1
    }
}
