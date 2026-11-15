#![no_std]
unsafe extern "C" { fn fat_event(value: u64); }
struct Guard;
impl Drop for Guard { fn drop(&mut self) { unsafe { fat_event(1) } } }
#[unsafe(no_mangle)]
pub fn virtual_str(op: &dyn Fn(&str, u64, bool) -> u64, text: &str, seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(text, seed, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_slice(op: &mut dyn FnMut(&mut [u64], u64, bool) -> u64, data: &mut [u64], seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(data, seed, fail)
}
