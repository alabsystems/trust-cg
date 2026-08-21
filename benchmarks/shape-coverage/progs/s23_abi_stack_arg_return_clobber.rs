// P0 WRONG-CODE: a dead load of an unused STACK-PASSED parameter is scheduled
// after the ABI return value is materialised, and regalloc then hands that dead
// load x0 — clobbering the return register.
//
// The function body is `p0 as u32` and contains NO arithmetic, so the program
// cannot be undefined: any divergence is the compiler's.
//
// Root cause: `Ret [PReg(x30)]` does not list the return register as a use, so
// nothing downstream knows x0 is live-out. Pre-pass MIR:
//     InstId(9):  LdrRI [VReg(9), x29, IncomingArg(8)]   ; dead load of p9
//     InstId(11): Uxtw  [PReg(x0), VReg(10)]             ; return value -> x0
//     InstId(12): Ret   [PReg(x30)]                      ; x0 not a use
// `sched` moves the dead load past inst 11; regalloc sees x0 as free and
// assigns it. Emitted: `mov w0,w1 ; ldr x0,[x29,#24] ; ret`.
//
// Needs >8 integer args (so some are stack-passed) AND a sub-word arg.
// Was: LLVM 1000, trust-cg 1009 (== p9) at O1/O2/O3 — INCLUDING the
// proofs-on production lane, which did not fail closed.
// Found by benchmarks/bridge-fuzz once its generator emitted wide arg lists.
use std::hint::black_box as bb;
#[inline(never)]
fn f(p0: u64, p1: u64, p2: u64, p3: u64, p4: u64, p5: u64, p6: u64, p7: u16, p8: u64, p9: u64) -> u32 {
    let _ = (p1, p2, p3, p4, p5, p6, p7, p8, p9);
    p0 as u32
}
fn main() {
    let v = f(bb(1000u64), bb(1001u64), bb(1002u64), bb(1003u64), bb(1004u64),
              bb(1005u64), bb(1006u64), bb(1007u16), bb(1008u64), bb(1009u64));
    std::process::exit((v % 251) as i32);
}
