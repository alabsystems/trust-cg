#![no_std]
#![feature(unsized_fn_params)]
extern crate alloc;
use alloc::string::String;
// `[String]` needs drop: the view must never make its destruction disappear.
#[unsafe(no_mangle)]
pub fn owned_strings(s: [String]) -> usize {
    s.len()
}
