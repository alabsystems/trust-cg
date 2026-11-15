#![no_std]
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pod {
    pub a: u8,
    pub b: u64,
    pub c: u16,
}
#[derive(Clone, Copy)]
#[repr(C, packed)]
pub struct Packed {
    pub a: u8,
    pub b: u32,
}
#[derive(Clone, Copy)]
#[repr(align(64))]
pub struct Wide(pub [u8; 3]);
#[derive(Clone, Copy)]
#[repr(align(32))]
pub struct Empty;
#[repr(C)]
pub struct Pair<'a, T> {
    pub first: &'a [T],
    pub second: &'a [T],
}
#[repr(C)]
pub struct StrPair<'a> {
    pub first: &'a str,
    pub second: &'a str,
}
