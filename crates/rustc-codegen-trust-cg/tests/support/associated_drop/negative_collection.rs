#![no_std]
extern crate alloc;
pub trait Family {
    type Owned;
}
pub struct Kind;
impl Family for Kind {
    type Owned = alloc::vec::Vec<u64>;
}
pub enum Associated<T: Family> {
    Borrowed(*const u64),
    Owned(T::Owned),
}
#[unsafe(no_mangle)]
pub fn rejected(value: Associated<Kind>) {
    drop(value);
}
