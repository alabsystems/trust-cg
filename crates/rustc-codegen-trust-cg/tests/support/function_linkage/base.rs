#![no_std]

#[inline]
pub fn shared(x: u64) -> u64 {
    x.rotate_left(13).wrapping_add(0x7351aef926cb804d)
}

pub static CALLBACK: fn(u64) -> u64 = shared;

pub trait Evaluate {
    fn evaluate(&self, x: u64) -> u64;
}
pub struct Item(pub u64);
impl Evaluate for Item {
    #[inline]
    fn evaluate(&self, x: u64) -> u64 {
        shared(x ^ self.0)
    }
}

#[unsafe(no_mangle)]
pub fn linkage_base(x: u64) -> u64 {
    shared(x)
}

#[inline(always)]
pub fn repeated(x: u64) -> u64 {
    x.wrapping_mul(5).wrapping_add(7)
}
