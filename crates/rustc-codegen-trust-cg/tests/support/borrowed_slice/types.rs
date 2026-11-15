#![no_std]
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Wide {
    pub a: u64,
    pub b: u64,
}
#[repr(align(32))]
#[derive(Clone, Copy)]
pub struct Zero;
