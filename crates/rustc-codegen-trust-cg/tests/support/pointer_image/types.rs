#![no_std]
extern crate alloc;
pub use alloc::boxed::Box;
pub use alloc::rc::Rc;
pub use alloc::sync::Arc;
pub use core::ffi::CStr;
use core::marker::PhantomData;
#[repr(C)]
pub struct Header<T: ?Sized> {
    pub head: u64,
    pub tail: T,
}
pub struct Carrier<P> {
    pub marker: PhantomData<u8>,
    pub value: P,
}
#[repr(C)]
pub struct Envelope<P> {
    pub head: u64,
    pub item: Carrier<P>,
    pub tail: u64,
}
