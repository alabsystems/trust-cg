#![no_std]
extern crate alloc;
pub struct Owner {
    pub value: alloc::vec::Vec<u64>,
    pub marker: u64,
}
#[unsafe(no_mangle)]
pub fn rejected(owner: Owner) {
    drop(owner);
}
