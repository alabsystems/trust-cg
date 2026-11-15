#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn wide_s32(x: i128) -> f32 {
    x as f32
}
#[unsafe(no_mangle)]
pub extern "C" fn wide_s64(x: i128) -> f64 {
    x as f64
}
#[unsafe(no_mangle)]
pub extern "C" fn wide_u32(x: u128) -> f32 {
    x as f32
}
#[unsafe(no_mangle)]
pub extern "C" fn wide_u64(x: u128) -> f64 {
    x as f64
}

#[repr(C)]
pub struct Results {
    pub s32: f32,
    pub u32: f32,
    pub s64: f64,
    pub u64: f64,
    pub saved: f64,
    pub word: u64,
}
unsafe extern "C" {
    fn wide_float_observe(word: u64, saved: f64) -> u64;
}
// Exhaust the integer argument registers, keep the output pointer and integer
// and floating values live across four conversion calls and an ordinary call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn wide_pressure(
    x: i128,
    y: u128,
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    saved: f64,
    out: *mut Results,
) -> u64 {
    let s32 = x as f32;
    let s64 = x as f64;
    let u32 = y as f32;
    let u64 = y as f64;
    let stamp = unsafe { wide_float_observe(a ^ b ^ c ^ d ^ e ^ f, saved) };
    let word = stamp ^ (x as u128 >> 64) as u64 ^ y as u64 ^ (y >> 64) as u64;
    unsafe {
        (*out).s32 = s32;
        (*out).u32 = u32;
        (*out).s64 = s64;
        (*out).u64 = u64;
        (*out).saved = saved;
        (*out).word = word;
    }
    word
}
