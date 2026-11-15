#![no_std]
extern crate alloc;
use alloc::vec::Vec;
pub struct Owner {
    words: Vec<u64>,
    tag: u64,
}
#[unsafe(no_mangle)]
pub fn store_collection(dst: &mut Owner, src: Owner) {
    *dst = src;
}
