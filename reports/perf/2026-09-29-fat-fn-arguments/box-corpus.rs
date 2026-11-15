#![no_std]
extern crate alloc;
use alloc::boxed::Box;
#[unsafe(no_mangle)]
pub fn virtual_box(op: &Box<dyn Fn(&str, u64) -> u64>, text: &str, seed: u64) -> u64 {
    op(text, seed)
}
#[unsafe(no_mangle)]
pub fn virtual_box_mut(op: &mut Box<dyn FnMut(&mut [u64], u64) -> u64>, data: &mut [u64], seed: u64) -> u64 {
    op(data, seed)
}
