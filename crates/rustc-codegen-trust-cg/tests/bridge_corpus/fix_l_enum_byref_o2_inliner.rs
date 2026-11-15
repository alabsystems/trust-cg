// (l) FIXED — trust-cg-opt's multi-block IR inliner (`ir_inline.rs`), not a ZST
// lane-index defect. A callee of the shape `fn rd(e: &E) -> u8 { match e { … } }`
// has TWO `Return` blocks (the match join and the unreachable default arm), so
// the splice defines the call RESULT once per returning clone — and the result
// is also the continuation's block PARAM. ISel joins block params by vreg REUSE,
// which only `select_copy` implements; the wiring used `Trunc` for an
// ABI-widened NARROW return, and `select_trunc` allocates a fresh vreg and
// rebinds the value, so the last returning clone stole the join and machine DCE
// deleted the other paths' values: `48 0` for `100 200` at -O2, correct at -O0
// (no inlining). The narrowing now lands in a fresh temp that a `Copy` carries
// into the result. Differential-OK at -O0 and -O2.
enum E { A, B(u8) }
#[inline(never)] fn rd(e: &E) -> u8 { match e { E::A => 100, E::B(_) => 200 } }
fn main() { let e1 = E::A; let e2 = E::B(9); println!("{} {}", rd(&e1), rd(&e2)); }
