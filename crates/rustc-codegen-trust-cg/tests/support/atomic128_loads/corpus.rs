#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::{AtomicOrdering, atomic_load};
#[unsafe(no_mangle)]
pub unsafe fn load_u128_relaxed(p: *const u128) -> u128 {
    unsafe { atomic_load::<u128, { AtomicOrdering::Relaxed }>(p) }
}
#[unsafe(no_mangle)]
pub unsafe fn load_u128_acquire(p: *const u128) -> u128 {
    unsafe { atomic_load::<u128, { AtomicOrdering::Acquire }>(p) }
}
#[unsafe(no_mangle)]
pub unsafe fn load_u128_seqcst(p: *const u128) -> u128 {
    unsafe { atomic_load::<u128, { AtomicOrdering::SeqCst }>(p) }
}
#[unsafe(no_mangle)]
pub unsafe fn load_i128_relaxed(p: *const i128) -> i128 {
    unsafe { atomic_load::<i128, { AtomicOrdering::Relaxed }>(p) }
}
#[unsafe(no_mangle)]
pub unsafe fn load_i128_acquire(p: *const i128) -> i128 {
    unsafe { atomic_load::<i128, { AtomicOrdering::Acquire }>(p) }
}
#[unsafe(no_mangle)]
pub unsafe fn load_i128_seqcst(p: *const i128) -> i128 {
    unsafe { atomic_load::<i128, { AtomicOrdering::SeqCst }>(p) }
}
