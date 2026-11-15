#![no_std]
#![feature(coerce_unsized, unsize)]
use core::{marker::Unsize, ops::CoerceUnsized, ptr::NonNull};
#[repr(C)]
pub struct State<T: ?Sized> {
    pub pointer: NonNull<T>,
    pub state: u64,
}
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<State<U>> for State<T> {}
#[unsafe(no_mangle)]
pub fn grow(v: State<[u64; 3]>) -> State<[u64]> {
    v
}
