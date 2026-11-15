//! Independent LLVM opaque call after the argument is explicitly rebound.
#[inline(never)]
pub fn after_write(value: usize) -> u64 {
    core::hint::black_box(value as u64)
}
