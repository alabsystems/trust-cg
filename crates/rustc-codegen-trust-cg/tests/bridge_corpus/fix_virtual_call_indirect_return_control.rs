// CONTROL — the HALF-B shape that must STILL be refused.
//
// `[i64; 8]` is 64 bytes: rustc's Rust ABI keeps every `BackendRepr::Memory`
// aggregate larger than one pointer on `PassMode::Indirect`, so the callee
// writes it through the hidden `x8` buffer. trust-cg cannot lower that
// convention on an INDIRECT lane — the selector marker that puts the buffer
// address in the target's indirect-result register is keyed by callee SYMBOL and
// a vtable slot has none — so this program must FAIL CLOSED, by name, rather
// than compile.
//
// It is a differential CONTROL, not a differential row: the harness asserts that
// the bridge refuses it and that the refusal names the ABI gate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

pub trait Bulk {
    fn block(&self, k: i64) -> [i64; 8];
}

pub struct Ramp(i64);

impl Bulk for Ramp {
    fn block(&self, k: i64) -> [i64; 8] {
        let mut out = [0i64; 8];
        let mut i = 0;
        while i < 8 {
            out[i] = self.0 + k + i as i64;
            i += 1;
        }
        out
    }
}

#[inline(never)]
fn total(b: &dyn Bulk, k: i64) -> i64 {
    let blk = b.block(k);
    let mut s = 0i64;
    for v in blk.iter() {
        s = s.wrapping_add(*v);
    }
    s
}

fn main() {
    let r = Ramp(5);
    println!("{}", total(&r, 3));
}
