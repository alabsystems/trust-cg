#[repr(C)]
#[derive(Clone, Copy)]
pub struct Pair<T> {
    pub hi: T,
    pub lo: T,
}
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Outer<T> {
    pub lead: u8,
    pub inner: Pair<T>,
    pub tail: u64,
}

pub trait Observe {
    fn take(&self, value: Outer<u8>) -> u64;
}
