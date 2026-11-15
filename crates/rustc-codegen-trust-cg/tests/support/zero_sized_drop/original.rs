#![no_std]
use core::ops::ControlFlow;
unsafe extern "C-unwind" {
    fn maybe_panic(item: u64, enabled: u64);
}
unsafe extern "C" {
    fn note_drop();
}
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe {
            note_drop();
        }
    }
}
pub enum Never {}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn try_pair(enabled: u64) -> u64 {
    let _guard = Guard;
    let result: ControlFlow<u64, u64> = (0..5_u64).try_fold(7_u64, |acc, item| {
        unsafe {
            maybe_panic(item, enabled);
        }
        if item == 4 {
            ControlFlow::Break(acc)
        } else {
            ControlFlow::Continue(acc.wrapping_mul(3).wrapping_add(item))
        }
    });
    match result {
        ControlFlow::Break(value) => value,
        ControlFlow::Continue(value) => value ^ 0xff,
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn try_single(enabled: u64) -> u64 {
    let _guard = Guard;
    let result: ControlFlow<Never, u64> = (0..5_u64).try_fold(7_u64, |acc, item| {
        unsafe {
            maybe_panic(item, enabled);
        }
        ControlFlow::Continue(acc.wrapping_mul(3).wrapping_add(item))
    });
    match result {
        ControlFlow::Continue(value) => value,
        ControlFlow::Break(never) => match never {},
    }
}
