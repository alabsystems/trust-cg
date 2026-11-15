// Corpus: an intrinsic the backends DO NOT IMPLEMENT must be lowered as its own
// FALLBACK BODY, not refused.
//
// `core::intrinsics::type_of` is declared WITH a body and documented, in
// `library/core/src/intrinsics/mod.rs`, as:
//
//     /// Compute the type information of a concrete type.
//     /// It can only be called at compile time, the backends do
//     /// not implement it.
//     #[rustc_intrinsic]
//     pub const fn type_of(_id: TypeId) -> Type {
//         panic!("`TypeId::info` can only be called at compile-time")
//     }
//
// LLVM does not lower it either — measured, a runtime call under the LLVM
// backend runs that `panic!`. So "this backend does not implement `type_of`" is
// NOT a reason to refuse a body containing a call to it: the fallback body IS
// the implementation, and `intrinsic_fallback_body_instance` already redirects
// to it for exactly this case.
//
// The bug this pins is that the redirect is guarded on the refusal string being
// EXACTLY "unsupported intrinsic `<name>`", and `type_of` was refused by name
// with a longer message — so the by-name refusal SUPPRESSED the fallback path
// rustc itself uses, and any body mentioning `type_of` became a failed root even
// when the call is never executed.
//
// WHY THE CALL IS NOT TAKEN: reaching it aborts (the fallback body panics, and
// under `-Cpanic=abort` this backend's accepted pre-existing deviation is that
// the panic TEXT is absent while the process-visible end, SIGABRT, matches). The
// observable here is therefore COMPILATION plus the not-taken path's value —
// which is the actual regression: the baseline refuses this file outright.
//   * `n 2` — the guarded `type_of` call is not taken and the other arm's value
//     is returned. Under the baseline the program does not compile at all.
//   * `k 11 12` — the same shape reached twice with different data, so a body
//     that lowered the branch away would be caught.
#![feature(type_info)]
#![allow(dead_code)]

use core::hint::black_box;
use std::any::TypeId;

#[inline(never)]
fn info_or(t: TypeId, take: bool, other: i64) -> i64 {
    if take {
        // Never executed here. Its presence alone used to fail the whole body
        // closed; it must now lower as the intrinsic's own panicking body.
        let i = t.info();
        black_box(&i);
        1
    } else {
        other
    }
}

fn main() {
    let n = info_or(TypeId::of::<u32>(), black_box(false), 2);
    println!("n {}", n); // 2

    let k1 = info_or(TypeId::of::<i64>(), black_box(false), 11);
    let k2 = info_or(TypeId::of::<(u8, i64)>(), black_box(false), 12);
    println!("k {} {}", k1, k2); // 11 12
}
