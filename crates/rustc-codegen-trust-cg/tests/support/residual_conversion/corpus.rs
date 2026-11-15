#![no_std]
#![feature(try_trait_v2)]
use core::{convert::Infallible, num::NonZeroU64, ops::FromResidual};
unsafe extern "C" {
    fn residual_record(kind: u64, a: u64, b: u64);
    fn residual_allocate(value: u64) -> *mut u64;
    fn residual_release(ptr: *mut u64);
}
struct Final(u64);
impl From<u64> for Final {
    #[inline(never)]
    fn from(value: u64) -> Self {
        unsafe { residual_record(1, value, 0) };
        Final(value.wrapping_add(17))
    }
}
#[inline(never)]
fn inner(value: u64, fail: bool) -> Result<u64, u64> {
    if fail { Err(value) } else { Ok(value) }
}
#[inline(never)]
fn scalar(value: u64, fail: bool) -> Result<u64, Final> {
    let n = inner(value, fail)?;
    Ok(n ^ 123)
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_scalar(value: u64, fail: bool) -> u64 {
    match scalar(value, fail) {
        Ok(x) => x,
        Err(Final(e)) => e,
    }
}
struct Wide {
    first: NonZeroU64,
    second: u64,
}
impl From<u8> for Wide {
    #[inline(never)]
    fn from(value: u8) -> Self {
        unsafe { residual_record(2, value as u64, 0) };
        Wide {
            first: unsafe { NonZeroU64::new_unchecked(value as u64 + 1) },
            second: (value as u64) ^ 0xfedcba9876543210,
        }
    }
}
#[inline(never)]
fn narrow_inner(value: u8, fail: bool) -> Result<(), u8> {
    if fail { Err(value) } else { Ok(()) }
}
#[inline(never)]
fn narrow(value: u8, fail: bool) -> Result<(), Wide> {
    narrow_inner(value, fail)?;
    Ok(())
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_narrow(value: u64, fail: bool) -> u64 {
    match narrow(value as u8, fail) {
        Ok(()) => 123,
        Err(e) => e.first.get() ^ e.second,
    }
}
struct SourcePair {
    first: NonZeroU64,
    second: u64,
}
impl From<SourcePair> for Final {
    #[inline(never)]
    fn from(e: SourcePair) -> Self {
        unsafe { residual_record(3, e.first.get(), e.second) };
        Final(e.first.get() ^ e.second ^ 0x7351)
    }
}
#[inline(never)]
fn pair_inner(value: u64, fail: bool) -> Result<(), SourcePair> {
    if fail {
        Err(SourcePair {
            first: unsafe { NonZeroU64::new_unchecked(value | 1) },
            second: value.wrapping_add(123),
        })
    } else {
        Ok(())
    }
}
#[inline(never)]
fn pair(value: u64, fail: bool) -> Result<(), Final> {
    pair_inner(value, fail)?;
    Ok(())
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_pair(value: u64, fail: bool) -> u64 {
    match pair(value, fail) {
        Ok(()) => 123,
        Err(Final(e)) => e,
    }
}
enum Small {
    A(u32),
    B { tag: u8, value: u32 },
}
impl From<Small> for Final {
    #[inline(never)]
    fn from(e: Small) -> Self {
        let (a, b) = match e {
            Small::A(v) => (v as u64, 0),
            Small::B { tag, value } => (value as u64, tag as u64),
        };
        unsafe { residual_record(4, a, b) };
        Final(a.wrapping_mul(17) ^ b)
    }
}
#[inline(never)]
fn enum_inner(value: u64, fail: bool) -> Result<(), Small> {
    if fail {
        Err(if value & 1 == 0 {
            Small::A(value as u32)
        } else {
            Small::B {
                tag: (value >> 32) as u8,
                value: value as u32,
            }
        })
    } else {
        Ok(())
    }
}
#[inline(never)]
fn enumeration(value: u64, fail: bool) -> Result<(), Final> {
    enum_inner(value, fail)?;
    Ok(())
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_enum(value: u64, fail: bool) -> u64 {
    match enumeration(value, fail) {
        Ok(()) => 123,
        Err(Final(e)) => e,
    }
}
struct Zero;
impl From<Zero> for Final {
    #[inline(never)]
    fn from(_: Zero) -> Self {
        unsafe { residual_record(5, 0, 0) };
        Final(0x12345678)
    }
}
#[inline(never)]
fn zero_inner(fail: bool) -> Result<u64, Zero> {
    if fail { Err(Zero) } else { Ok(123) }
}
#[inline(never)]
fn zero(fail: bool) -> Result<u64, Final> {
    let n = zero_inner(fail)?;
    Ok(n)
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_zero(_: u64, fail: bool) -> u64 {
    match zero(fail) {
        Ok(x) => x,
        Err(Final(e)) => e,
    }
}
struct Owned(*mut u64);
impl Drop for Owned {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { residual_release(self.0) }
    }
}
impl From<Owned> for Final {
    #[inline(never)]
    fn from(e: Owned) -> Self {
        let value = unsafe { *e.0 };
        unsafe { residual_record(6, value, 0) };
        Final(value ^ 0xdead)
    }
}
#[inline(never)]
fn owned_inner(value: u64, fail: bool) -> Result<u64, Owned> {
    if fail {
        Err(Owned(unsafe { residual_allocate(value) }))
    } else {
        Ok(value)
    }
}
#[inline(never)]
fn owned(value: u64, fail: bool) -> Result<u64, Final> {
    let n = owned_inner(value, fail)?;
    Ok(n ^ 123)
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_owned(value: u64, fail: bool) -> u64 {
    match owned(value, fail) {
        Ok(x) => x,
        Err(Final(e)) => e,
    }
}
struct Middle(u64);
impl From<u64> for Middle {
    #[inline(never)]
    fn from(v: u64) -> Self {
        unsafe { residual_record(8, v, 0) };
        Middle(v ^ 0x4567)
    }
}
impl From<Middle> for Final {
    #[inline(never)]
    fn from(v: Middle) -> Self {
        unsafe { residual_record(9, v.0, 0) };
        Final(v.0.wrapping_add(37))
    }
}
#[inline(never)]
fn middle(value: u64, fail: bool) -> Result<u64, Middle> {
    let n = inner(value, fail)?;
    Ok(n ^ 123)
}
#[inline(never)]
fn chain(value: u64, fail: bool) -> Result<u64, Final> {
    let n = middle(value, fail)?;
    Ok(n)
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_chain(value: u64, fail: bool) -> u64 {
    match chain(value, fail) {
        Ok(x) => x,
        Err(Final(e)) => e,
    }
}
#[inline(never)]
fn identity(value: u64, fail: bool) -> Result<u64, u64> {
    let n = inner(value, fail)?;
    Ok(n ^ 123)
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_identity(value: u64, fail: bool) -> u64 {
    match identity(value, fail) {
        Ok(x) => x,
        Err(e) => e,
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_direct(value: u64, fail: bool) -> u64 {
    if !fail {
        return value ^ 123;
    }
    let r: Result<u64, Final> = FromResidual::from_residual(Result::<Infallible, u64>::Err(value));
    match r {
        Ok(x) => x,
        Err(Final(e)) => e,
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_indirect(value: u64, fail: bool) -> u64 {
    if !fail {
        return value ^ 123;
    }
    let f: fn(Result<Infallible, u64>) -> Result<u64, Final> = FromResidual::from_residual;
    match f(Err(value)) {
        Ok(x) => x,
        Err(Final(e)) => e,
    }
}
