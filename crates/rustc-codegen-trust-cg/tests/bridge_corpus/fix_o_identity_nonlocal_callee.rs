// (o) THE NON-LOCAL-CALLEE FALSIFIER for the reference-escaping cell widening
// (4c961dcbb). The same dead-temp hazard as `fix_refret_cell_nonprimitive.rs`,
// through a NON-LOCAL callee, which `direct_scalar_ref_select_return` never
// inspects (`is_local()` is its first gate): `core::convert::identity::<&mut
// Cur>(&mut tmp)` returns its argument unchanged, so a store through the result
// must reach `tmp`. The widened cell rule is locality-agnostic — it cells the
// referent because the callee's return type carries a reference — so the store
// lands. LLVM: `seen=9`, exit 0.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHY THIS ROW IS LOAD-BEARING, measured on trust-cg main `ad7ee9c4e`
// (aarch64-apple-darwin, driver `0cb693917`): restore the pre-widening
// `Int/Uint/Float/Bool/Char` narrowing in `cellable_reference_referent_ty` and
// this program COMPILES at -O0 and prints `seen=5`, exit 1 — a SILENT wrong
// value, because with a non-local callee no refusal exists to catch the missing
// address (-O3 inlines `identity` and happens to match). The LOCAL-callee twin
// `fix_refret_cell_nonprimitive.rs` is REFUSED by name under the same mutation
// ("promoted mutable scalar reference return is unsupported"), so it cannot see
// a narrowing regression; this row turns one into a hard divergence.
#![allow(dead_code)]
struct Cur(u32);
fn main() {
    let mut tmp = Cur(5);
    let r = core::convert::identity::<&mut Cur>(&mut tmp);
    *r = Cur(9);
    let seen = tmp.0;
    println!("seen={}", seen);
    std::process::exit((seen != 9) as i32);
}
