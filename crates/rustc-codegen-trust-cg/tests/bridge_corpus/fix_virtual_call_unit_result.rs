// A VIRTUAL call returning a by-value aggregate into a MEMORY-BACKED destination
// — the `core::fmt::Result` shape, and the one all 18 `core` census roots
// returned.
//
// `Result<(), Sink>` is a ONE-BYTE, all-ZST-payload enum: rustc's `FnAbi` places
// it `PassMode::Direct` (a scalar), the bridge's slot layout is a single 1-byte
// lane, and `copy_memory_aggregate_call_result`'s `align 1 => I8` arm moves it.
// The destination is memory-backed because the returned value is bound to a whole
// local that is read back afterwards.
//
// Deliberately free of `&[&str]` and other fat-pointer-inside-aggregate shapes:
// those are refused by a DIFFERENT gate (`[TCG-FAT-POINTEE-LANE]`), which would
// mask the one this fixture exists to exercise.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[derive(Debug, PartialEq)]
pub struct Sink;

pub trait Emit {
    // The `<Formatter as Write>::write_str` shape: a `&mut dyn` receiver, a
    // borrowed `&str` argument, a one-byte aggregate return.
    fn emit(&mut self, s: &str) -> Result<(), Sink>;
    fn tick(&mut self) -> Result<(), Sink>;
}

pub struct Counter {
    seen: u64,
    fail_at: u64,
}

impl Emit for Counter {
    fn emit(&mut self, s: &str) -> Result<(), Sink> {
        self.seen += s.len() as u64;
        if self.seen >= self.fail_at {
            Err(Sink)
        } else {
            Ok(())
        }
    }
    fn tick(&mut self) -> Result<(), Sink> {
        self.seen += 1;
        Ok(())
    }
}

// Each virtual call's destination is a WHOLE local read back by a later `match`,
// which is exactly the memory-backed-destination shape the removed gate refused.
#[inline(never)]
fn drive(e: &mut dyn Emit, a: &str, b: &str) -> u64 {
    let mut ok = 0u64;
    let r0 = e.emit(a);
    match r0 {
        Ok(()) => ok += 1,
        Err(Sink) => return ok,
    }
    let r1 = e.emit(b);
    match r1 {
        Ok(()) => ok += 10,
        Err(Sink) => return ok,
    }
    // A third virtual call whose aggregate result is inspected rather than
    // matched immediately.
    let t = e.tick();
    if t.is_ok() {
        ok += 100
    } else {
        ok += 1000
    }
    ok
}

// The same shape with the result compared as a VALUE, so a wrong byte in the
// relocated slot is observable and not merely a taken/untaken branch.
#[inline(never)]
fn classify(e: &mut dyn Emit, s: &str) -> u64 {
    let r = e.emit(s);
    let mut code = 0u64;
    if r == Ok(()) {
        code += 1;
    }
    if r == Err(Sink) {
        code += 2;
    }
    if r.is_ok() {
        code += 4;
    }
    code
}

fn main() {
    let mut c = Counter { seen: 0, fail_at: 9 };
    println!("{}", drive(&mut c, "ab", "cd"));

    let mut d = Counter { seen: 0, fail_at: 3 };
    println!("{}", drive(&mut d, "ab", "cd"));

    let mut e = Counter { seen: 0, fail_at: 1 };
    println!("{}", drive(&mut e, "x", "y"));

    let mut f = Counter { seen: 0, fail_at: 3 };
    let c0 = classify(&mut f, "ab");
    let c1 = classify(&mut f, "cd");
    let seen = f.seen;
    println!("{c0}");
    println!("{c1}");
    println!("{seen}");

    // The result of an explicitly-spelled `&mut dyn` dispatch, read as a VALUE.
    // (Printed as a number rather than with `{:?}`, and through plain locals: a
    // `Debug` format, or a field read in the argument position, stops at an
    // unrelated pre-existing gate — "format! arg reference does not trace to a
    // value local" — which would mask the one this fixture exercises.)
    let mut g = Counter { seen: 0, fail_at: 100 };
    let gr: Result<(), Sink> = (&mut g as &mut dyn Emit).emit("hello");
    let ok = if gr == Ok(()) { 1u64 } else { 0u64 };
    let gseen = g.seen;
    println!("{ok}");
    println!("{gseen}");
}
