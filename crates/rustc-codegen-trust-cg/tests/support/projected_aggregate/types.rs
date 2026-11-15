#![no_std]
pub use core::alloc::Layout;
#[derive(Clone, Copy, PartialEq)]
#[repr(C)]
pub struct Pair64 {
    pub a: u64,
    pub b: u64,
}
#[derive(Clone, Copy, PartialEq)]
#[repr(C)]
pub struct Triple64 {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}
#[derive(Clone, Copy, PartialEq)]
#[repr(C)]
pub struct Small4 {
    pub a: u16,
    pub b: u16,
}
#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct Packed5 {
    pub a: u8,
    pub b: u32,
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Float2 {
    pub a: f64,
    pub b: f64,
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Float4 {
    pub a: f32,
    pub b: f32,
    pub c: f32,
    pub d: f32,
}
#[derive(Clone, Copy)]
#[repr(C)]
pub struct WideRecord {
    pub head: u64,
    pub bytes: &'static [u8],
    pub tail: u16,
}
#[derive(Clone, Copy, PartialEq)]
#[repr(C)]
pub enum Choice {
    Small { a: u64, b: u8 },
    Large { a: u64, b: u64, c: u64 },
}
#[derive(Clone, Copy, PartialEq)]
#[repr(C)]
pub struct Aligned32 {
    pub a: u128,
    pub b: u64,
}
#[derive(Clone, Copy)]
#[repr(C)]
pub union Union24 {
    pub words: [u64; 3],
    pub floats: [f64; 3],
}

#[derive(Clone, Copy, PartialEq)]
#[repr(Rust)]
pub struct WithZst {
    pub z: (),
    pub a: u64,
    pub marker: (),
    pub b: u16,
}
#[derive(Clone, Copy, PartialEq)]
#[repr(Rust)]
pub struct Nested {
    pub z: (),
    pub a: Small4,
    pub b: Pair64,
    pub c: u8,
}
