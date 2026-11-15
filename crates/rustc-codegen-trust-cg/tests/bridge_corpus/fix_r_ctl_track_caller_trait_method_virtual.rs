// `#[track_caller]` on a trait method, reached through its vtable.
// The virtual-call lane forwards the hidden Location on AArch64 and wasm32,
// and the program must AGREE with LLVM there. x86-64 retains the named
// TCG-ABI-TRACKCALLER-VIRTUAL refusal until that boundary is measured.
// The call-site line is intentionally observed at runtime: forwarding a
// garbage pointer or the callee's own location must never pass this fixture.
#![allow(dead_code)]

use std::panic::Location;

trait T {
    #[track_caller]
    fn m(&self) -> u32;
}

struct S;
impl T for S {
    fn m(&self) -> u32 {
        Location::caller().line()
    }
}

#[inline(never)]
fn via_dyn(t: &dyn T) -> u32 {
    t.m()
}

fn main() {
    let s = S;
    println!("virt {}", via_dyn(&s));
}
