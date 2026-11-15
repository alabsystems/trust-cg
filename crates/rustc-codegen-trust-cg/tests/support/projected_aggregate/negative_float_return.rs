#![no_std]
#[repr(C)]
pub struct Float4 {
    pub a: f32,
    pub b: f32,
    pub c: f32,
    pub d: f32,
}
#[unsafe(no_mangle)]
pub fn indirect(v: Float4, cb: fn(Float4) -> Float4) -> Float4 {
    cb(v)
}
