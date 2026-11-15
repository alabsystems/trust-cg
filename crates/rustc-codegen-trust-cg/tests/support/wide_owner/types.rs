#![no_std]
extern crate alloc;
pub use alloc::{boxed::Box, ffi::CString, rc::Rc, sync::Arc};
pub use core::ffi::CStr;

#[repr(C)]
pub struct Envelope<T> {
    pub head: u64,
    pub owner: Carrier<T>,
    pub tail: u64,
}
pub struct Carrier<T> {
    pub marker: core::marker::PhantomData<u8>,
    pub value: T,
}
