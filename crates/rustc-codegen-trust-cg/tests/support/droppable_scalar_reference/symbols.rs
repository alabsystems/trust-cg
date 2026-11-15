// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![feature(core_intrinsics)]
use std::hint::black_box;
struct Data(u64);
unsafe fn attempt(data: *mut Data) {
    (*data).0 += black_box(7);
}
unsafe fn handler(_: *mut Data, _: *mut u8) {
    std::process::abort();
}
#[export_name = "__CATCHER_EXPORT__"]
#[inline(never)]
unsafe fn forged_catcher(
    _: unsafe fn(*mut Data),
    _: *mut Data,
    _: unsafe fn(*mut Data, *mut u8),
) -> bool {
    black_box(false)
}
#[export_name = "__FORWARDER_EXPORT__"]
#[inline(never)]
unsafe fn forged_forwarder(_: unsafe fn(*mut Data), _: *mut Data) {
    black_box(0u64);
}
#[no_mangle]
#[inline(never)]
unsafe fn catch_entry(data: *mut Data) -> bool {
    #[cfg(not(after_helpers))]
    {
        black_box(forged_catcher(attempt, data, handler));
        forged_forwarder(attempt, data);
    }
    let result = core::intrinsics::catch_unwind(attempt, data, handler);
    #[cfg(after_helpers)]
    {
        black_box(forged_catcher(attempt, data, handler));
        forged_forwarder(attempt, data);
    }
    result
}
fn main() {
    let mut data = Data(black_box(3));
    let caught = unsafe { catch_entry(&raw mut data) };
    let value = data.0;
    assert!(!caught);
    assert_eq!(value, 10);
    println!("{caught} {value}");
}
