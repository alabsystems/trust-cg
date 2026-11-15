#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::{AtomicOrdering, atomic_load, atomic_store, atomic_xadd};
#[unsafe(no_mangle)]
pub unsafe fn store_u128(p: *mut u128, value: u128) {
    unsafe { atomic_store::<u128, { AtomicOrdering::Release }>(p, value) }
}
#[unsafe(no_mangle)]
pub unsafe fn store_i128(p: *mut i128, value: i128) {
    unsafe { atomic_store::<i128, { AtomicOrdering::SeqCst }>(p, value) }
}
#[unsafe(no_mangle)]
pub unsafe fn add_u128(p: *mut u128, value: u128) -> u128 {
    unsafe { atomic_xadd::<u128, u128, { AtomicOrdering::AcqRel }>(p, value) }
}
#[unsafe(no_mangle)]
pub unsafe fn add_i128(p: *mut i128, value: i128) -> i128 {
    unsafe { atomic_xadd::<i128, i128, { AtomicOrdering::Relaxed }>(p, value) }
}
#[unsafe(no_mangle)]
pub unsafe fn load_u128_acquire(p: *const u128) -> u128 {
    unsafe { atomic_load::<u128, { AtomicOrdering::Acquire }>(p) }
}
