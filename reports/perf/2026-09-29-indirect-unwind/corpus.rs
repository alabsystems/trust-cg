#![no_std]
unsafe extern "C" { fn indirect_event(kind: u64, value: u64); }
struct Guard(*const u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) { unsafe { indirect_event(5, *self.0) } }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_indirect(
    callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> u64,
    value: u64,
) -> u64 {
    let mut cell = value ^ 0x55;
    let _guard = Guard(&raw const cell);
    let result = unsafe { callback(&mut cell, value) };
    unsafe { indirect_event(2, cell) }
    result ^ cell
}
