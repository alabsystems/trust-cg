// Row: a LOOP-CARRIED ZERO-SIZED local.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `loop_carried_completeness_error` refuses a local that is live-in at a loop
// header, mutated inside the loop, and neither memory-backed nor threaded
// through the header phi: its update would be dropped across the back-edge. A
// trust-ir `Unit` carrier is EXEMPT — it has no lanes, so there is no update to
// drop — and this row is the shape that made that reachable: a GENERIC
// accumulator instantiated at `()`. (rustc's MIR builder elides a
// monomorphically-`()` local entirely — `debug u => const ()` — so only the
// generic, then monomorphized, body has a real `_n: ()` local. That is why every
// instance of this refusal in a `library/core` census is an
// `Iterator::try_fold::<(), ..>` / `try_for_each` accumulator.)
//
// The exemption must not cost the loop its real work, which is what this row
// checks: every value below depends on the exact iteration count and order, so a
// loop that ran the wrong number of times, exited early, or dropped a real
// update prints a different number than LLVM.

enum Step<A> {
    Go(A),
    Stop,
}

/// The generic driver. `accum` is `_4` in the monomorphized MIR: live-in at the
/// loop header and re-assigned inside the loop by the `Step::Go(a) => accum = a`
/// arm — a STATEMENT def of an unprojected local, exactly the `?`-desugared
/// `accum = ((_t as Continue).0: A)` of `Iterator::try_fold`.
fn drive<A, I: Iterator<Item = u64>>(
    mut it: I,
    init: A,
    mut f: impl FnMut(A, u64) -> Step<A>,
) -> Option<A> {
    let mut accum = init;
    loop {
        match it.next() {
            Some(x) => match f(accum, x) {
                Step::Go(a) => accum = a,
                Step::Stop => return None,
            },
            None => return Some(accum),
        }
    }
}

static mut HASH: u64 = 0;
static mut TURNS: u64 = 0;

fn main() {
    // A = () — the zero-sized carrier. The loop's observable effect lives in the
    // statics, so a dropped iteration or an early exit is visible.
    let done = drive(0..9u64, (), |(), x| {
        unsafe {
            HASH = HASH.wrapping_mul(31).wrapping_add(x);
            TURNS += 1;
        }
        Step::Go(())
    });
    println!(
        "{} {} {}",
        unsafe { HASH },
        unsafe { TURNS },
        done.is_some()
    );

    // Same carrier, with a genuine early exit: the count must stop exactly at 5.
    let stopped = drive(0..9u64, (), |(), x| {
        if x == 5 {
            return Step::Stop;
        }
        unsafe {
            HASH = HASH.rotate_left(7) ^ x;
            TURNS += 1;
        }
        Step::Go(())
    });
    println!(
        "{} {} {}",
        unsafe { HASH },
        unsafe { TURNS },
        stopped.is_some()
    );

    // The zero-iteration path of the same carrier: the loop header is still a
    // loop header, and the carrier must survive to the `Some(accum)` exit.
    let empty = drive(0..0u64, (), |(), _| Step::Go(()));
    println!("{} {}", unsafe { TURNS }, empty.is_some());
}
