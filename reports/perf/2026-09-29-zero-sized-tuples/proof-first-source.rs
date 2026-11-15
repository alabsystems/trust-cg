#![no_std]
use core::ops::ControlFlow;

unsafe extern "C" {
    fn zst_event(code: u64);
}

#[inline(never)]
fn from_unit(_: ()) -> u64 {
    17
}
#[inline(never)]
fn call<F: FnOnce(()) -> u64>(f: F) -> u64 {
    f(())
}
#[unsafe(no_mangle)]
pub extern "C" fn unit_call(seed: u64) -> u64 {
    call(from_unit).wrapping_add(seed)
}

#[unsafe(no_mangle)]
pub extern "C" fn flow_map(seed: u64) -> u64 {
    let flow = if seed & 1 == 0 {
        ControlFlow::Break(())
    } else {
        ControlFlow::Continue(())
    };
    match flow.map_break(ControlFlow::<(), core::cmp::Ordering>::Break) {
        ControlFlow::Break(ControlFlow::Break(())) => seed.wrapping_add(7),
        ControlFlow::Break(ControlFlow::Continue(_)) => 123,
        ControlFlow::Continue(()) => seed.wrapping_add(11),
    }
}

#[inline(never)]
fn call_mut<F: FnMut(((), ())) -> u64>(mut f: F) -> u64 {
    f(((), ())) ^ f(((), ()))
}
#[unsafe(no_mangle)]
pub extern "C" fn nested_mut(seed: u64) -> u64 {
    let mut value = seed;
    call_mut(|_: ((), ())| {
        value = value.wrapping_add(19);
        value
    })
}

#[inline(never)]
fn tuple_fn(_: ((), ())) -> u64 {
    31
}
#[inline(never)]
fn indirect(f: fn(((), ())) -> u64, arg: ((), ())) -> u64 {
    f(arg)
}
#[unsafe(no_mangle)]
pub extern "C" fn tuple_pointer(seed: u64) -> u64 {
    indirect(tuple_fn, ((), ())).wrapping_add(seed)
}

#[inline(never)]
fn mixed_zst_arg(_: ((), [(); 4]), seed: u64, _: (((),), ())) -> u64 {
    seed.rotate_left(23)
}
#[unsafe(no_mangle)]
pub extern "C" fn tuple_arguments(seed: u64) -> u64 {
    mixed_zst_arg(((), [(); 4]), seed, (((),), ()))
}

struct A;
struct B;
impl Drop for A {
    fn drop(&mut self) {
        unsafe { zst_event(3) }
    }
}
impl Drop for B {
    fn drop(&mut self) {
        unsafe { zst_event(5) }
    }
}
#[inline(never)]
fn take_drop(_: (A, B), seed: u64) -> u64 {
    seed.wrapping_add(23)
}
#[unsafe(no_mangle)]
pub extern "C" fn tuple_drop(seed: u64) -> u64 {
    take_drop((A, B), seed)
}

#[repr(align(16))]
struct Aligned;
#[unsafe(no_mangle)]
pub extern "C" fn tuple_alignment(seed: u64) -> u64 {
    let tuple = (Aligned, ());
    let address = &tuple as *const (Aligned, ()) as usize;
    seed ^ ((address & 15) as u64)
}

#[inline(never)]
fn return_tuple() -> ((), [(); 3], (((),),)) {
    ((), [(); 3], (((),),))
}
#[unsafe(no_mangle)]
pub extern "C" fn tuple_return(seed: u64) -> u64 {
    let (a, b, c) = return_tuple();
    let copied = (a, b, c);
    seed.wrapping_add(core::mem::size_of_val(&copied) as u64)
}
