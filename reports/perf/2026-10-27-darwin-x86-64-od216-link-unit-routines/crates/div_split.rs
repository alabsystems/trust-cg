// Ruling OD-216, residual 1 of OD-210: the crate's own `__udivti3` (every
// quotient 0) in one module, a `u128` division in another. Compiled with
// `-Ccodegen-units=16` the two modules are two codegen units, so `div`'s module
// does not define the routine its division calls; the object's definition is
// what that call binds to.
#![no_std]

pub mod routine {
    /// The crate's own `__udivti3`: every quotient is 0.
    #[unsafe(no_mangle)]
    pub extern "C" fn __udivti3(_a: u128, _b: u128) -> u128 {
        0
    }
}

pub mod user {
    /// `a / b`, rustc's zero check and the selector's `call __udivti3`.
    #[unsafe(no_mangle)]
    pub extern "C" fn div(a: u128, b: u128) -> u128 {
        a / b
    }
}
