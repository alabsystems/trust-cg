#![no_std]
extern crate alloc;
use alloc::boxed::Box;
unsafe extern "C" {
    fn dyn_event(kind: u64, value: u64);
}
struct Guard(u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            dyn_event(5, self.0);
        }
    }
}
#[unsafe(no_mangle)]
pub fn check_dyn(item: Box<dyn core::any::Any>, value: u64) {
    let _guard = Guard(value);
    drop(item);
    unsafe {
        dyn_event(2, value);
    }
}
