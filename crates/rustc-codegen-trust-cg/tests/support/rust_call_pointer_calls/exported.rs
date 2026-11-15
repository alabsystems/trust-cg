// A `(bool, u64)` `extern "rust-call"` item a library DEFINES, which an LLVM
// binary calls directly and through a pointer. rustc's caller zero-extends the
// `bool`, and the bridge declares the item with the tuple's elements, so its
// body reads the `bool` argument at its own width. Must match LLVM at O0-O3.
#![feature(unboxed_closures)]
#![allow(improper_ctypes_definitions)]

#[inline(never)]
pub extern "rust-call" fn flag(a: (bool, u64)) -> u64 {
    if a.0 { a.1 * 3 } else { 7 }
}

#[inline(never)]
pub fn get_flag() -> extern "rust-call" fn((bool, u64)) -> u64 {
    flag
}
