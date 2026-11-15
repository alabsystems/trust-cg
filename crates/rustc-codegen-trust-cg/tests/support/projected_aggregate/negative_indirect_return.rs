#![no_std]
#[repr(C)]
pub struct Triple {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}
#[unsafe(no_mangle)]
pub fn indirect(v: Triple, cb: fn(Triple) -> Triple) -> Triple {
    cb(v)
}
