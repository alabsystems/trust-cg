#![no_std]

trait DifferentOverflow {
    fn overflowing_add(self, rhs: Self) -> (Self, bool)
    where
        Self: Sized;
}
impl DifferentOverflow for u64 {
    #[inline(never)]
    fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        (self ^ rhs, true)
    }
}

#[unsafe(no_mangle)]
pub fn shadow_loop(mut a: u64, mut b: u64, mut n: u32) -> (u64, bool) {
    let mut overflow = false;
    while n != 0 {
        let (next, flag) = DifferentOverflow::overflowing_add(a, b);
        a = b;
        b = next;
        overflow |= flag;
        n = n.wrapping_sub(1);
    }
    (a ^ b, overflow)
}
