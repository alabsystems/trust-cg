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

#[unsafe(no_mangle)]
pub fn virtual_fn_mut(op: &mut dyn FnMut(u64, bool) -> u64, value: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(value, fail)
}

pub trait Mutation { fn run(&self, out: &mut u64, value: u64, fail: bool) -> u64; }
#[unsafe(no_mangle)]
pub fn virtual_mutation(op: &dyn Mutation, out: &mut u64, value: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op.run(out, value, fail)
}

pub trait Tracked { #[track_caller] fn run(&self, value: u64, fail: bool) -> u64; }
#[unsafe(no_mangle)]
pub fn virtual_tracked(op: &dyn Tracked, value: u64, fail: bool) -> u64 {
    let _guard = Guard;
    let expected = line!() as u64 + 1;
    let actual = op.run(value, fail);
    actual.wrapping_sub(expected)
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Large { pub words: [u64; 4] }
pub trait LargeOperation { fn run(&self, value: Large, fail: bool) -> u64; }
#[unsafe(no_mangle)]
pub fn virtual_large(op: &dyn LargeOperation, value: u64, fail: bool) -> u64 {
    let _guard = Guard;
    let image = Large { words: [value, !value, value.rotate_left(13), value.wrapping_add(17)] };
    let result = op.run(image, fail);
    result ^ image.words[1]
}

#[unsafe(no_mangle)]
pub extern "C" fn virtual_terminate(op: &mut dyn Operation, value: u64) -> u64 {
    op.run(value, true)
}
