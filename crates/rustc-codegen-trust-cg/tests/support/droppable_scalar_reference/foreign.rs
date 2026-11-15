// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![feature(core_intrinsics)]
use std::hint::black_box;
extern "C-unwind" {
    fn raise_foreign();
}
extern "C" {
    fn finish_foreign(exception: *mut u8) -> u64;
    fn foreign_drops() -> u64;
}
struct Data(u64);
unsafe fn try_foreign(data: *mut Data) {
    (*data).0 = black_box(7);
    raise_foreign();
}
unsafe fn catch_foreign(data: *mut Data, exception: *mut u8) {
    assert_eq!((*data).0, 7);
    (*data).0 = finish_foreign(exception);
}
fn main() {
    let mut data = Data(black_box(3));
    let caught =
        unsafe { std::intrinsics::catch_unwind(try_foreign, &raw mut data, catch_foreign) };
    assert!(caught);
    assert_eq!(data.0, 91);
    assert_eq!(unsafe { foreign_drops() }, 1);
    let value = data.0;
    let drops = unsafe { foreign_drops() };
    println!("{caught} {value} {drops}");
}
