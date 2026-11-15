// Compiled only by LLVM. Reading a borrowed Chain through its real core
// implementation checks the producer's Option tags, payloads and relocations.
#![no_std]

use core::iter::Chain;
use core::ops::Range;
use core::slice::Iter;
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static OBSERVATIONS: AtomicUsize = AtomicUsize::new(0);

#[inline(never)]
pub unsafe extern "C" fn observe_u64(ptr: *const Chain<Range<u64>, Range<u64>>) -> u64 {
    OBSERVATIONS.fetch_add(1, Relaxed);
    unsafe { &*ptr }
        .clone()
        .fold(0u64, |sum, value| sum.wrapping_mul(31).wrapping_add(value))
}

#[inline(never)]
pub unsafe extern "C" fn observe_u32(ptr: *const Chain<Range<u32>, Range<u32>>) -> u64 {
    OBSERVATIONS.fetch_add(1, Relaxed);
    unsafe { &*ptr }.clone().fold(0u64, |sum, value| {
        sum.wrapping_mul(31).wrapping_add(u64::from(value))
    })
}

#[inline(never)]
pub unsafe extern "C" fn observe_i64(ptr: *const Chain<Range<i64>, Range<i64>>) -> u64 {
    OBSERVATIONS.fetch_add(1, Relaxed);
    unsafe { &*ptr }.clone().fold(0u64, |sum, value| {
        sum.wrapping_mul(31).wrapping_add(value as u64)
    })
}

#[inline(never)]
pub unsafe extern "C" fn observe_slices(
    ptr: *const Chain<Iter<'static, u64>, Iter<'static, u64>>,
) -> u64 {
    OBSERVATIONS.fetch_add(1, Relaxed);
    unsafe { &*ptr }
        .clone()
        .fold(0u64, |sum, value| sum.wrapping_mul(31).wrapping_add(*value))
}

#[inline(never)]
pub extern "C" fn observations() -> usize {
    OBSERVATIONS.load(Relaxed)
}
