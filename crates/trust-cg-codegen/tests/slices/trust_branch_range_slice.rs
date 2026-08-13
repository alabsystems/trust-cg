// Trust-toolchain slice — the AArch64 BRANCH-RANGE / VENEER decider,
// transcribed VERBATIM from trust-cg/crates/trust-cg-codegen/src/relax.rs
//   branch_range (relax.rs:266-274)  — per-opcode (min,max) displacement range
//   in_range     (relax.rs:278-281)  — "does this displacement FIT" decider
//   the range constants B_/BCOND_/TBZ_ (relax.rs:53-62)
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 24, TRUST BATCH
// 11). This is the decider the branch-relaxation pass uses to answer "does this
// branch reach its target, or must a veneer/trampoline be inserted?" A wrong
// range either (a) emits an un-relaxed branch that OVERFLOWS its imm field at
// link time (a miscompile), or (b) needlessly relaxes an in-range branch. The
// three ranges are the exact AArch64 encoding limits:
//   B (imm26*4):        +/-128 MB   ([-(1<<27), (1<<27)-4])
//   B.cond/CBZ/CBNZ (imm19*4): +/-1 MB  ([-(1<<20), (1<<20)-4])
//   TBZ/TBNZ (imm14*4): +/-32 KB   ([-(1<<15), (1<<15)-4])
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure branch_range_root` per the
// README recipe; `-C overflow-checks=off -C debug-assertions=off`.
//
// MODELED BOUNDARIES:
//   [F5-repr] production `branch_range` matches over the real `AArch64Opcode`
//        (219 fieldless variants, NO `#[repr]`) — subject to the F5 sext-i8 tag
//        miscompile for variants >= 128 when lowered through the emit-closure
//        frontend. The six branch opcodes it matches (B=62, BCond=63, Cbz=64,
//        Cbnz=65, Tbz=66, Tbnz=67) are ALL < 128, so branch_range is in fact
//        F5-SAFE (a >=128 opcode sext-negates and correctly falls to the `_`
//        wildcard). This slice nonetheless models the opcode as a SMALL
//        `#[repr(u8)]` enum (the R21/R22 declared F5 workaround) carrying only
//        the branch-relevant variants + `Other`; the native dual-oracle drives
//        the REAL production `branch_range` over the REAL no-`repr`
//        `AArch64Opcode` (run natively -> no F5), proving the model matches —
//        AND asserts production `branch_range(BL=201)` (a >=128 opcode) returns
//        the Other range, confirming the F5-safety directly.
//   [B-tuple] production returns `(i64, i64)`; the root writes the pair + the
//        `in_range` bool into a POD out-struct. `in_range` is a PRIVATE `fn`
//        (not linkable): transcribed VERBATIM and cross-checked against the
//        linked `branch_range` (`d >= min && d <= max`).
//   [F3/const] the range constants are spelled as their explicit i64 literal
//        values (per the lhs==rhs validator rule); value-identical to the
//        `1<<27` / `1<<20` / `1<<15` production forms.

// ── range constants (relax.rs:53-62, VERBATIM values) ─────────────────────────
const B_MAX_RANGE: i64 = 134_217_724; // (1 << 27) - 4
const B_MIN_RANGE: i64 = -134_217_728; // -(1 << 27)
const BCOND_MAX_RANGE: i64 = 1_048_572; // (1 << 20) - 4
const BCOND_MIN_RANGE: i64 = -1_048_576; // -(1 << 20)
const TBZ_MAX_RANGE: i64 = 32_764; // (1 << 15) - 4
const TBZ_MIN_RANGE: i64 = -32_768; // -(1 << 15)

// ── opcode model ([F5-repr] small #[repr(u8)] carrier) ────────────────────────
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum BrOp {
    B,
    BCond,
    Cbz,
    Cbnz,
    Tbz,
    Tbnz,
    Other,
}

fn br_op_from_tag(tag: u32) -> BrOp {
    match tag {
        0 => BrOp::B,
        1 => BrOp::BCond,
        2 => BrOp::Cbz,
        3 => BrOp::Cbnz,
        4 => BrOp::Tbz,
        5 => BrOp::Tbnz,
        _ => BrOp::Other,
    }
}

// ── branch_range (relax.rs:266-274, VERBATIM) ─────────────────────────────────
fn branch_range(opcode: BrOp) -> (i64, i64) {
    match opcode {
        BrOp::B => (B_MIN_RANGE, B_MAX_RANGE),
        BrOp::BCond => (BCOND_MIN_RANGE, BCOND_MAX_RANGE),
        BrOp::Cbz | BrOp::Cbnz => (BCOND_MIN_RANGE, BCOND_MAX_RANGE),
        BrOp::Tbz | BrOp::Tbnz => (TBZ_MIN_RANGE, TBZ_MAX_RANGE),
        _ => (i64::MIN, i64::MAX), // not a branch, always in range
    }
}

// ── in_range (relax.rs:278-281, VERBATIM) ─────────────────────────────────────
fn in_range(opcode: BrOp, displacement: i64) -> bool {
    let (min, max) = branch_range(opcode);
    displacement >= min && displacement <= max
}

// ── POD out-vector ────────────────────────────────────────────────────────────
#[repr(C)]
pub struct BrRangeOut {
    pub min: i64,
    pub max: i64,
    pub in_range: u32,
}

// ── #[no_mangle] mono ROOT ────────────────────────────────────────────────────
/// ROOT: one call yields the (min,max) range for the opcode + whether the given
/// signed byte displacement fits.
#[no_mangle]
pub fn branch_range_root(op_tag: u32, disp: i64, out: &mut BrRangeOut) {
    let op = br_op_from_tag(op_tag);
    let (min, max) = branch_range(op);
    out.min = min;
    out.max = max;
    out.in_range = if in_range(op, disp) { 1u32 } else { 0u32 };
}
