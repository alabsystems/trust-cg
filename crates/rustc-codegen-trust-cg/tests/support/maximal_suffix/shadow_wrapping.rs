#![no_std]
#[inline(never)]
fn wrapping_add(a: u64, b: u64) -> u64 {
    a ^ b
}
#[unsafe(no_mangle)]
pub fn shadow_wrapping(mut n: u64, mut a: u64, mut b: u64) -> (u64, u64) {
    while n != 0 {
        let old_a = a;
        a = b;
        b = wrapping_add(old_a, b);
        n -= 1;
    }
    (a, b)
}
