#![no_std]
#![feature(unsized_fn_params)]
#[repr(C, align(64))]
#[derive(Clone, Copy)]
pub struct Wide {
    pub a: u64,
    pub b: u64,
}
#[repr(align(32))]
#[derive(Clone, Copy)]
pub struct Zero;
pub trait Sink {
    fn consume(&self, s: [u64], seed: u64) -> u64;
}
