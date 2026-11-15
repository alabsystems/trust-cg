// selfhost_live_reader — a CRATE-LOCAL `core::fmt` plumbing local with a
// genuine, NON-intercepted reader.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the only program in the repo that reaches the SELF-HOST deadness
// seeding from a user crate. `is_local_fmt_internal_ty` recognizes
// `core::fmt::rt::ArgumentType` by its crate-qualified def path plus
// `DefId::is_local`, so compiling THIS file with `--crate-name core` (see
// `extra_flags` in ../run.sh) makes the `ArgumentType` below crate-local — an
// ordinary ADT the backend must lower from rustc's layout, exactly as when
// `core` itself is the crate under compilation.
//
// WHAT IT PINS. The fmt-dead region is rooted at the calls an interception
// consumes, including every projection-free argument of a DIVERGING PANIC
// block. `live_reader`'s `a` flows into such a root (it is formatted by the
// `panic!`), so it is REACHABLE from an interception — but `observe(&a)` reads
// it for real. Seeding it dead on reachability alone skips `let a = ...` and
// hands `observe` an uninitialized value. `stays_dead`'s `b` is the converse: no
// reader but the panic, so the whole construction chain must still vanish.
#![allow(dead_code)]
use std::marker::PhantomData;
use std::ptr::NonNull;

pub mod fmt {
    pub mod rt {
        use std::marker::PhantomData;
        use std::ptr::NonNull;
        /// Shaped like the real `core::fmt::rt::ArgumentType`: a two-variant,
        /// niche-encoded 16-byte enum carrying a non-null data pointer and a
        /// function pointer.
        pub enum ArgumentType<'a> {
            Placeholder {
                value: NonNull<()>,
                formatter: unsafe fn(NonNull<()>, &mut u32) -> u32,
                _lifetime: PhantomData<&'a ()>,
            },
            Count(usize),
        }
    }
}

use fmt::rt::ArgumentType;

unsafe fn formatter_stub(_v: NonNull<()>, _f: &mut u32) -> u32 {
    0
}

impl std::fmt::Display for ArgumentType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("argty")
    }
}

/// A reader the `format!`/`write!`/`panic!` interception does not touch.
#[inline(never)]
fn observe(a: &ArgumentType<'_>) -> usize {
    match a {
        ArgumentType::Count(n) => *n,
        ArgumentType::Placeholder { .. } => 1_000,
    }
}

/// `a` is crate-local fmt plumbing, is READ for real, and ALSO reaches a
/// diverging panic block's argument.
#[inline(never)]
fn live_reader(n: usize, boom: bool) -> usize {
    let a = ArgumentType::Count(n);
    let seen = observe(&a);
    if boom {
        panic!("{}", a);
    }
    seen
}

/// The converse: the panic is `b`'s ONLY consumer, so its construction is
/// genuinely decoded at compile time and must stay skipped.
#[inline(never)]
fn stays_dead(n: usize, boom: bool) -> usize {
    let b = ArgumentType::Placeholder {
        value: NonNull::dangling(),
        formatter: formatter_stub,
        _lifetime: PhantomData,
    };
    if boom {
        panic!("{}", b);
    }
    n + 1
}

fn main() {
    println!("live={}", live_reader(7, false));
    println!("live={}", live_reader(41, false));
    println!("dead={}", stays_dead(9, false));
}
