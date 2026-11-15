// Row: an `Fn*`-call SHIM over a fn ITEM whose untupled arguments are PROJECTED
// places.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// rustc's `build_call_shim` builds `<f as FnOnce<(A, ..)>>::call_once` for a fn
// ITEM `f` by UNTUPLING its second parameter: every argument operand is
// `move (_2.i)` — a place with a `Field` projection. Every argument path in this
// backend admitted only a WHOLE local, so each of these shims refused, in four
// different messages that are all the same defect:
//
//   by-value aggregate call argument 0 uses a projected operand
//   direct call aggregate reference arg 0 uses projected reference operand
//   direct call scalar reference arg 0 uses projected reference operand
//   direct call enum reference arg 0 uses projected reference operand
//
// A `Fn*` bound instantiated with a fn ITEM is reached by STATIC monomorphized
// dispatch, so before that refusal was made honest these shims were emitted as
// REACHABLE trapping `ud2` stubs — these programs did not fail to compile, they
// compiled into traps. Each case below therefore checks a VALUE at runtime
// against LLVM, not merely that the compile succeeds.
//
// Every call goes through a generic `F: Fn*` bound instantiated with a fn ITEM
// (never a closure), so the shim is the only thing that can produce the value.

#[derive(Clone, Copy)]
struct Big {
    a: u64,
    b: u64,
    c: u64,
    d: u64,
}

#[derive(Clone, Copy)]
enum Tag {
    Small(u64),
    Wide(u64, u64),
}

// by-value MEMORY aggregate argument -> `by-value aggregate call argument 0 uses
// a projected operand`.
fn sum_array(v: [u64; 4]) -> u64 {
    v[0] + v[1] * 10 + v[2] * 100 + v[3] * 1000
}

// shared AGGREGATE reference -> `direct call aggregate reference arg 0 uses
// projected reference operand`.
fn weigh(b: &Big) -> u64 {
    b.a + b.b * 10 + b.c * 100 + b.d * 1000
}

// shared SCALAR reference -> `direct call scalar reference arg 0 uses projected
// reference operand`.
fn triple(r: &u8) -> u8 {
    r.wrapping_mul(3)
}

// `&mut` ENUM reference -> `direct call enum reference arg 0 uses projected
// reference operand`. It MUTATES through the reference, so a shim that dropped
// the write (or wrote a copy) shows up in the second call's answer.
fn bump(t: &mut Tag) -> u64 {
    match *t {
        Tag::Small(v) => {
            *t = Tag::Wide(v, v + 1);
            v
        }
        Tag::Wide(x, y) => {
            *t = Tag::Small(x + y);
            x * 10 + y
        }
    }
}

fn once<A, R, F: FnOnce(A) -> R>(f: F, a: A) -> R {
    f(a)
}
fn call_mut<A, R, F: FnMut(A) -> R>(mut f: F, a: A) -> R {
    f(a)
}

fn main() {
    println!("{}", once(sum_array, [1u64, 2, 3, 4]));
    println!("{}", call_mut(sum_array, [9u64, 8, 7, 6]));

    let b = Big {
        a: 4,
        b: 3,
        c: 2,
        d: 1,
    };
    println!("{}", once(weigh, &b));

    let byte: u8 = 41;
    println!("{}", once(triple, &byte));
    println!("{}", call_mut(triple, &byte));

    let mut t = Tag::Small(5);
    let first = call_mut(bump, &mut t);
    let second = call_mut(bump, &mut t);
    let third = call_mut(bump, &mut t);
    println!("{first} {second} {third}");
}
