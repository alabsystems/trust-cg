#![no_std]
use core::ops::ControlFlow;
#[inline(never)]
fn from_unit(_: ()) -> u64 { 17 }
#[inline(never)]
fn call<F: FnOnce(()) -> u64>(f: F) -> u64 { f(()) }
#[unsafe(no_mangle)]
pub extern "C" fn unit_call(seed:u64) -> u64 { call(from_unit).wrapping_add(seed) }
#[unsafe(no_mangle)]
pub extern "C" fn flow_map(seed:u64) -> u64 {
    let flow = if seed & 1 == 0 { ControlFlow::Break(()) } else { ControlFlow::Continue(()) };
    match flow.map_break(ControlFlow::<(), core::cmp::Ordering>::Break) {
        ControlFlow::Break(ControlFlow::Break(())) => seed.wrapping_add(7),
        ControlFlow::Break(ControlFlow::Continue(_)) => 123,
        ControlFlow::Continue(()) => seed.wrapping_add(11),
    }
}
