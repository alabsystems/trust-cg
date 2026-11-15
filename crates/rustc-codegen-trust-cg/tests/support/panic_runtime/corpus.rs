#![no_std]
#![feature(panic_internals, fmt_arguments_from_str, rustc_attrs)]
#![allow(internal_features)]

unsafe extern "C" {
    fn runtime_drop(kind: u64, value: u64);
}
struct Guard {
    kind: u64,
    value: u64,
}
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { runtime_drop(self.kind, self.value) }
    }
}

pub mod panicking {
    #[inline(never)]
    #[track_caller]
    #[unsafe(no_mangle)]
    pub fn runtime_literal(message: &'static str) -> ! {
        core::panicking::panic_fmt(core::fmt::Arguments::from_str(message))
    }

    #[inline(never)]
    #[track_caller]
    #[unsafe(no_mangle)]
    pub fn runtime_formatted(value: u64) -> ! {
        core::panicking::panic_fmt(format_args!("value={value}"))
    }

    #[inline(never)]
    #[track_caller]
    #[unsafe(no_mangle)]
    pub fn runtime_guarded(value: u64) -> ! {
        let _guard = super::Guard { kind: 7, value };
        core::panicking::panic_fmt(format_args!("guard={value}"))
    }

    #[inline(never)]
    #[track_caller]
    #[rustc_nounwind]
    #[unsafe(no_mangle)]
    pub fn runtime_nounwind(message: &'static str) -> ! {
        core::panicking::panic_nounwind_fmt(core::fmt::Arguments::from_str(message), false)
    }
}

pub mod panic {
    #[inline(never)]
    #[track_caller]
    #[unsafe(no_mangle)]
    pub fn runtime_arguments(args: core::fmt::Arguments<'_>) -> ! {
        core::panicking::panic_fmt(args)
    }
}

pub mod helpers {
    #[inline(never)]
    #[track_caller]
    #[unsafe(no_mangle)]
    pub fn helper_literal(message: &'static str) -> ! {
        core::panicking::panic(message)
    }

    #[inline(never)]
    #[track_caller]
    #[unsafe(no_mangle)]
    pub fn helper_formatted(value: u64) -> ! {
        panic!("helper={value}")
    }
}
