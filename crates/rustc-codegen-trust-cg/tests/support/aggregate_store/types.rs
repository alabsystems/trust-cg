#![no_std]
use core::num::NonZeroU64;
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C)]
pub struct Pad {
    pub a: u8,
    pub b: u64,
    pub c: u16,
}
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C)]
pub struct Inner {
    pub a: u64,
    pub b: u32,
    pub c: u8,
}
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C)]
pub struct Nested {
    pub head: u8,
    pub inner: Inner,
    pub tail: u16,
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RustNested {
    pub head: u8,
    pub inner: [u32; 3],
    pub tail: u16,
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Tuple {
    pub inner: (u8, u64, u32),
    pub tail: u16,
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Array {
    pub inner: [[u16; 3]; 3],
}
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C, packed)]
pub struct Packed {
    pub head: u8,
    pub inner: [u32; 3],
    pub tail: u16,
}
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C, align(16))]
pub struct Wide {
    pub head: u8,
    pub inner: u128,
    pub tail: [u16; 3],
}
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C, u8)]
pub enum Tagged {
    Empty,
    Left { inner: Inner, tail: u16 },
    Right { data: [u64; 3] },
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Pair {
    pub a: NonZeroU64,
    pub b: u64,
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Niche {
    pub inner: Option<Pair>,
    pub tail: u16,
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Fat {
    pub data: &'static [u8],
    pub text: &'static str,
    pub tail: u64,
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Zst {
    pub first: (),
    pub inner: Inner,
    pub last: core::marker::PhantomData<u8>,
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Single {
    Payload { inner: Inner, tail: u64 },
}
