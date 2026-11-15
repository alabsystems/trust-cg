// Ruling OD-216, control of `div_split.rs`: the crate declares `__udivti3`
// and defines none, so the division binds to the sysroot's (or the
// platform's) routine elsewhere in the link, which OD-202 trusts.
#![no_std]

pub mod routine {
    unsafe extern "C" {
        /// Declared only.
        pub fn __udivti3(a: u128, b: u128) -> u128;
    }
}

pub mod user {
    /// `a / b`, rustc's zero check and the selector's `call __udivti3`.
    #[unsafe(no_mangle)]
    pub extern "C" fn div(a: u128, b: u128) -> u128 {
        a / b
    }
}
