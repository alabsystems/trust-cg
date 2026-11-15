#![no_std]

#[track_caller]
#[inline(never)]
pub fn outside() -> &'static core::panic::Location<'static> {
    core::panic::Location::caller()
}

#[track_caller]
#[inline(never)]
pub fn raise() {
    panic!("track_caller boundary");
}
