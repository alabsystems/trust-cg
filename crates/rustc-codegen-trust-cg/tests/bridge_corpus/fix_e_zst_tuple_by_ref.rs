// (e) A by-reference TUPLE with a `[u8; 0]` element BEFORE its sized elements
// (`&([u8; 0], u32, u32)`): at -O2 the slices lane read `t.1` as `20` for `10`
// (the ZST lane dropped, the MIR index kept).
//
// UPDATED 2026-09-14 (sized-array value-type lane), and the previous sentence
// here was a PREMISE that stopped being true: this used to read "Now REFUSED by
// name (`[TCG-ZST-LANE-INDEX]` on the tuple pointee) at every opt level — a
// tuple pointee has no rustc-layout byte-walker fallback, unlike a struct." The
// second half was the reason for the first, and it is what changed. A bare tuple
// pointee the scalar-field flattening cannot represent now takes the SAME
// byte-offset memory-slot path a nested-field STRUCT pointee already took
// (`memory_aggregate_reference_pointee_lane_ty`'s new tuple arm), and that path
// addresses every field at rustc's OWN layout offset, so the ZST lane/index
// disagreement the refusal existed to avoid cannot arise on it.
//
// MEASURED at that change: this program COMPILES and prints `10 20` — LLVM's
// exact output — at BOTH `-Copt-level=0` and `-Copt-level=2`, where the
// unpatched backend refuses with `[TCG-ZST-LANE-INDEX]` and the pre-refusal
// backend printed `20` for `t.1`. The struct twin
// (`fix_e_zst_first_field_by_ref.rs`) is byte-identical across the change.
//
// The refusal itself is NOT removed: `zero_sized_field_precedes_sized_field`
// still rejects the FLAT LANE TUPLE for these shapes, and a tuple whose layout
// the byte model cannot address still fails closed by that name.
#[inline(never)] fn t1(t: &([u8; 0], u32, u32)) -> u32 { t.1 }
#[inline(never)] fn t2(t: &([u8; 0], u32, u32)) -> u32 { t.2 }
fn main() {
    let tp = ([0u8; 0], 10u32, 20u32);
    println!("{} {}", t1(&tp), t2(&tp));
}
