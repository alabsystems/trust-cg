// A coroutine whose upvar aggregate holds a borrow of a captured scalar
// (`seed`): the aggregate-stored reference cell pass must NOT follow a
// coroutine aggregate, so this keeps "borrowed scalar reference used without
// deref" (the shape of `coroutine_generator_linux.rs`'s `ay_gen_resume_args`).
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[no_mangle]
pub extern "C" fn cap_coroutine(seed: i64) -> i64 {
    let mut g = #[coroutine]
    |mut x: i64| {
        let mut total = seed;
        loop {
            total += x;
            if x < 0 {
                return total;
            }
            x = yield total * 2;
        }
    };
    let mut input = 3i64;
    let mut acc = 0i64;
    loop {
        match Pin::new(&mut g).resume(input) {
            CoroutineState::Yielded(v) => acc = acc.wrapping_add(v),
            CoroutineState::Complete(r) => return acc.wrapping_add(r),
        }
        input = if input >= 5 { -1 } else { input + 1 };
    }
}
