// Trust-toolchain slice — the production trust-ir `CastOp::shape` and
// `CastOp::is_layout_sensitive` (trust-ir/crates/trust-ir/src/shape.rs:352 / :367)
// lowered VERBATIM over the real `CastOp` and `CastShape` enums.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (3rd batch, fn #3).
//
// `CastOp::shape` classifies every cast op into one of 8 `CastShape` categories;
// `CastOp::is_layout_sensitive` flags the four casts (`PtrToPtr`, `Bitcast`,
// `Transmute`, `ReifyFnPointer`) whose CORRECTNESS depends on the source/dest
// LAYOUTS agreeing. Both are genuine SOUNDNESS predicates — the trust-ir layout
// pass (`shape.rs::layout_sensitive_cast_evidence`) gates which casts must carry
// a layout-equality obligation off `is_layout_sensitive`, and `shape` drives the
// per-category lowering selection. Mis-classifying a `Transmute` as a plain
// `Bitcast` (or dropping a layout obligation) is a direct miscompile.
//
// PURE, deterministic, closure-free, self-contained:
//   * `shape`: a TOTAL dense match over all 15 `CastOp` variants -> a u8-discriminant
//     `CastShape` (8 variants); `is_layout_sensitive`: a 4-of-15 `matches!` mask,
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals.
//
// TRANSCRIBED VERBATIM:
//   * `CastOp` enum (inst.rs:105-123) — every variant in order.
//   * `CastShape` enum (shape.rs:323-334) — every variant in order.
//   * `CastOp::shape` (shape.rs:352-365) — THE EMIT ROOT, byte-for-byte.
//   * `CastOp::is_layout_sensitive` (shape.rs:367-372) — byte-for-byte.
// The only adaptation is dropping the serde cfg_attr derives.

#![allow(dead_code)]

// ── CastOp (inst.rs:105-123) — VERBATIM variant set & order (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CastOp {
    Trunc,
    ZExt,
    SExt,
    FPTrunc,
    FPExt,
    FPToUI,
    FPToSI,
    UIToFP,
    SIToFP,
    PtrToInt,
    IntToPtr,
    PtrToPtr,
    Bitcast,
    Transmute,
    ReifyFnPointer,
}

// ── CastShape (shape.rs:323-334) — VERBATIM variant set & order (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CastShape {
    IntegerResize,
    FloatResize,
    FloatInteger,
    PointerInteger,
    Pointer,
    Bitcast,
    Transmute,
    ReifyFnPointer,
}

impl CastOp {
    /// (shape.rs:352-365, VERBATIM — THE EMIT ROOT.)
    pub fn shape(self) -> CastShape {
        match self {
            CastOp::Trunc | CastOp::ZExt | CastOp::SExt => CastShape::IntegerResize,
            CastOp::FPTrunc | CastOp::FPExt => CastShape::FloatResize,
            CastOp::FPToUI | CastOp::FPToSI | CastOp::UIToFP | CastOp::SIToFP => {
                CastShape::FloatInteger
            }
            CastOp::PtrToInt | CastOp::IntToPtr => CastShape::PointerInteger,
            CastOp::PtrToPtr => CastShape::Pointer,
            CastOp::Bitcast => CastShape::Bitcast,
            CastOp::Transmute => CastShape::Transmute,
            CastOp::ReifyFnPointer => CastShape::ReifyFnPointer,
        }
    }

    /// (shape.rs:367-372, VERBATIM.)
    pub fn is_layout_sensitive(self) -> bool {
        matches!(
            self,
            CastOp::PtrToPtr | CastOp::Bitcast | CastOp::Transmute | CastOp::ReifyFnPointer
        )
    }
}

/// Map a small tag to a `CastOp` (covers every arm).
fn cast_op_for_tag(tag: u32) -> CastOp {
    match tag {
        0 => CastOp::Trunc,
        1 => CastOp::ZExt,
        2 => CastOp::SExt,
        3 => CastOp::FPTrunc,
        4 => CastOp::FPExt,
        5 => CastOp::FPToUI,
        6 => CastOp::FPToSI,
        7 => CastOp::UIToFP,
        8 => CastOp::SIToFP,
        9 => CastOp::PtrToInt,
        10 => CastOp::IntToPtr,
        11 => CastOp::PtrToPtr,
        12 => CastOp::Bitcast,
        13 => CastOp::Transmute,
        _ => CastOp::ReifyFnPointer,
    }
}

/// Map a `CastShape` back to a small tag so the C-ABI entry returns one scalar.
/// (This discriminator is OUTSIDE the verified body; it only reads the enum the
/// real `shape` produced.)
fn cast_shape_tag(s: CastShape) -> u32 {
    match s {
        CastShape::IntegerResize => 0,
        CastShape::FloatResize => 1,
        CastShape::FloatInteger => 2,
        CastShape::PointerInteger => 3,
        CastShape::Pointer => 4,
        CastShape::Bitcast => 5,
        CastShape::Transmute => 6,
        CastShape::ReifyFnPointer => 7,
    }
}

// ── C-ABI entrypoint. The verified bodies are `shape` / `is_layout_sensitive`;
//    this wrapper selects a `CastOp` from a tag, calls the REAL fn, and returns
//    one scalar: `which==0` -> the `CastShape` tag (0..7); `which==1` -> the
//    `is_layout_sensitive` bit (0/1). No closures.
#[no_mangle]
pub extern "C" fn cast_shape_entry(op_tag: u32, which: u32) -> u32 {
    let op = cast_op_for_tag(op_tag);
    if which == 0 {
        cast_shape_tag(op.shape())
    } else {
        op.is_layout_sensitive() as u32
    }
}

fn main() {
    println!("{}", cast_shape_entry(0, 0)); // Trunc -> IntegerResize tag 0
    println!("{}", cast_shape_entry(13, 0)); // Transmute -> tag 6
    println!("{}", cast_shape_entry(13, 1)); // Transmute is layout-sensitive -> 1
    println!("{}", cast_shape_entry(0, 1)); // Trunc NOT layout-sensitive -> 0
}
