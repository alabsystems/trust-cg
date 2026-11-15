#![no_std]
#![feature(unsized_fn_params)]
pub enum Void {}
#[unsafe(no_mangle)]
pub fn uninhabited(_s: [u64], v: Void) -> usize {
    match v {}
}
