#![no_std]
extern crate alloc;
use alloc::{string::String, vec::Vec};
#[allow(improper_ctypes_definitions)]
#[unsafe(no_mangle)]
pub extern "C" fn tcg_string_convert(bytes: Vec<u8>) -> String {
    unsafe { String::from_utf8_unchecked(bytes) }
}
