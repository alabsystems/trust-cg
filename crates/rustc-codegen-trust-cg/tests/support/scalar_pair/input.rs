#![no_std]
#![allow(dead_code)]

#[repr(C)]
pub struct CInts {
    pub small: u8,
    pub wide: u64,
}
pub struct RustInts {
    pub small: u8,
    pub wide: u64,
}
#[repr(C, packed)]
pub struct PackedInts {
    pub small: u8,
    pub wide: u64,
}
#[repr(C, align(32))]
pub struct AlignedInts {
    pub small: u8,
    pub wide: u64,
}
#[repr(C)]
pub struct CFloat {
    pub a: f32,
    pub b: f32,
}
#[repr(transparent)]
pub struct Wide(*const [u32]);
pub struct ZstInts {
    pub empty: (),
    pub small: u8,
    pub wide: u64,
}
pub trait Marker {}

pub type CaseU8 = u8;
pub type CaseU64 = u64;
pub type CaseBool = bool;
pub type CaseF64 = f64;
pub type CaseThin = *const u8;
pub type CaseTupleInts = (u8, u64);
pub type CaseTupleReversed = (u64, u8);
pub type CaseF32Pair = (f32, f32);
pub type CaseF64Pair = (f64, f64);
pub type CaseCStruct = CInts;
pub type CaseRustStruct = RustInts;
pub type CasePacked = PackedInts;
pub type CaseAligned = AlignedInts;
pub type CaseCFloat = CFloat;
pub type CaseTransparent = Wide;
pub type CaseSlice = &'static [u32];
pub type CaseStr = &'static str;
pub type CaseDyn = &'static dyn Marker;
pub type CaseNullableSlice = Option<&'static [u32]>;
pub type CaseNonNull = core::ptr::NonNull<[u8]>;
pub type CaseZstStruct = ZstInts;
