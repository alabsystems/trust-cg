#![no_std]
unsafe extern "C" { fn virtual_event(code: u64); }
struct Guard;
impl Drop for Guard { fn drop(&mut self) { unsafe { virtual_event(1) } } }
pub trait Operation { fn run(&mut self, value: u64, fail: bool) -> u64; }
#[repr(C)]
pub struct Pair { pub a: u64, pub b: u64 }
pub trait PairOperation { fn run(&mut self, value: u64, fail: bool) -> Pair; }

#[unsafe(no_mangle)]
pub fn virtual_scalar(op: &mut dyn Operation, value: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op.run(value, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_pair(op: &mut dyn PairOperation, value: u64, fail: bool) -> u64 {
    let _guard = Guard;
    let pair = op.run(value, fail);
    pair.a ^ pair.b
}
#[unsafe(no_mangle)]
pub fn virtual_fn(op: &dyn Fn(u64, bool) -> u64, value: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(value, fail)
}
