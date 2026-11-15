#![no_std]
#[repr(C)]
pub struct Words {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}
#[repr(C)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}
#[repr(C)]
pub struct Floats {
    pub a: f64,
    pub b: f64,
    pub c: f64,
}
unsafe extern "Rust" {
    fn aggregate_read_union(slot: &mut core::mem::MaybeUninit<u64>) -> u64;
}
unsafe extern "C" {
    fn aggregate_event(kind: u64, value: u64);
}
struct Guard(*const u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { aggregate_event(5, *self.0) }
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_words(
    callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> Words,
    v: u64,
) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let words = unsafe { callback(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    words.a ^ words.b ^ words.c ^ words.d ^ cell
}
