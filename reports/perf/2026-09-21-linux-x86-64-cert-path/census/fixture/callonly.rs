#![no_std]
#![feature(fmt_arguments_from_str, panic_internals, core_intrinsics)]
#![allow(internal_features)]

// Shape 1: panic_const_* — from_str + panic_fmt, track_caller, diverging.
#[inline(never)]
#[cold]
#[track_caller]
pub fn shape_panic_const() -> ! {
    core::panicking::panic_fmt(core::fmt::Arguments::from_str("attempt to add with overflow"));
}

// Shape 2: panic_already_borrowed — a ZST-arg diverging wrapper calling a nested diverging fn.
#[derive(Clone, Copy)]
pub struct ZstErr;

#[inline(never)]
#[cold]
#[track_caller]
pub fn shape_wrapper(err: ZstErr) -> ! {
    #[inline(never)]
    #[cold]
    #[track_caller]
    fn do_panic(_err: ZstErr) -> ! {
        core::panicking::panic_fmt(core::fmt::Arguments::from_str("RefCell already borrowed"));
    }
    do_panic(err)
}

// Shape 3: abort_immediate — an intrinsic trap.
#[inline(never)]
#[cold]
pub fn shape_abort() -> ! {
    core::intrinsics::abort()
}

// Shape 4: a plain `panic!` literal (core::panicking::panic(&str)).
#[inline(never)]
#[cold]
#[track_caller]
pub fn shape_panic_str() -> ! {
    panic!("explicit literal")
}

// Shape 5: control — one ALU row; must still be non-vacuous-rejected or verified.
#[inline(never)]
pub fn shape_alu(x: u64) -> u64 {
    x.wrapping_add(7)
}
