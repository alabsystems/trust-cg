#![no_std]
extern crate alloc;
use alloc::vec::Vec;
use core::ptr::NonNull;
#[repr(transparent)]
pub struct Ptr<T: ?Sized>(pub NonNull<T>);
pub struct Mixed {
    pub values: Vec<u64>,
    pub pointer: Ptr<[u64]>,
}
#[unsafe(no_mangle)]
pub fn set(p: &mut Mixed, v: Ptr<[u64]>) {
    p.pointer = v;
}
