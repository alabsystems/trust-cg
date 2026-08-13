// Trust-toolchain slice — the APPLE AArch64 (AAPCS64 / DarwinPCS) ABI
// ARGUMENT/RETURN CLASSIFICATION deciders, transcribed VERBATIM from
//   trust-cg/crates/trust-cg-lower/src/abi.rs  (`AppleAArch64ABI`)
//   trust-cg/crates/trust-cg-lower/src/types.rs (`Type::{bytes,align,align_to}`)
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 23, TRUST
// BATCH 10 — the ABI / calling-convention classification surface, a NEW area:
// prior rounds did encoders (1/7/16), register files (5/16), opt/analysis +
// addr-mode predicates (20/21), and scheduler/regalloc deciders (22). The ABI
// classifier — how the backend decides WHERE a function argument / return
// value is placed for the target ABI — was UNTOUCHED until this round.
//
// WHY SOUNDNESS-CRITICAL: a wrong classification produces a WRONG CALL — the
// argument ends up in the wrong register / stack slot, or an sret pointer is
// mishandled, silently corrupting the ABI contract between caller and callee.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure abi_aa_root` per the README
// recipe (NO extra flags needed; EXTERN-FREE; re-emits byte-identical).
//
// SCOPE — why this slice is SCALAR-DRIVEN (the Vec<Type> recursion blocker):
//   The production aggregate-layout functions (`Type::bytes`/`align` on
//   Struct/Array, `detect_hfa`, `flatten_hfa_fields`, `classify_hfa`, and the
//   HFA branch of `classify_aggregate`) recurse over `fields: Vec<Type>` /
//   `Box<Type>`. Those aggregate `Type` values EMIT cleanly (validate_module =
//   0) but their `Vec<Type>::{len,is_empty,index,iter}` / `Box<Type>` methods
//   lower to EMPTY-BODIED library leaves (a non-crate-local `alloc`/`core`
//   method has no body pulled into the closure), so the in-process JIT cannot
//   resolve them: `Jit(UnresolvedSymbol("...Vec<t>::len..."))`. This is the
//   F4 / owner-#6 empty-bodied-leaf class, now observed for the whole `Vec<
//   non-scalar-enum>` recursion family (reported). Consequently this slice:
//     * verifies the SCALAR-shaped deciders VERBATIM in JIT machine code
//       (`Type::bytes`/`align` on scalars, `classify_fp_arg`, `align_up`);
//     * verifies the aggregate SIZE-THRESHOLD DECISION (`classify_aggregate`'s
//       non-HFA <=8 / 9..=16 / >16 register-pair-split + Indirect(sret) rule)
//       in a SCALAR-DRIVEN transcription that takes the size as an argument
//       [B-aggsize] — the DECISION (the two threshold comparisons) is
//       byte-for-byte the production body; only `ty.bytes()` (the size) and the
//       `is_aggregate` gate are supplied by the caller. The native oracle
//       computes those from REAL aggregate `Type`s via the LINKED production
//       `Type::bytes` + `classify_aggregate`, so native==JIT proves the JIT's
//       threshold decision correct at the exact 8 / 16 / 17 byte boundaries.
//
// MODELED BOUNDARIES:
//   [B1] `PReg` modeled as its `u16` hardware-encoding (transparent newtype-
//        elision; the register the classifier SELECTS is the observable). H0=165
//        S0=128 D0=96 V0=64, contiguous views.
//   [B-scalaronly] the sliced `Type` carries ONLY the scalar variants (no
//        Struct/Array/Enum), so it never references the Vec<Type>/Box<Type>
//        leaves. `Type::bytes`/`align` keep their scalar match arms verbatim;
//        the aggregate arms are elided (they are the Vec-recursion blocked
//        above). `sysv`/HFA classifiers reached via those arms are covered by
//        the SIZE-DRIVEN transcription instead.
//   [B5] production `classify_fp_arg` indexes the const arrays
//        `H_ARG_REGS[fpr_idx]` etc.; const-array indexing by a RUNTIME index
//        does not lower ("constant value not a single scalar", confirmed by
//        `probe_arridx.rs`). The four FPR argument-register views are CONTIGUOUS
//        (view[i] == base + i), so `classify_fp_arg` uses the equivalent
//        base+index arithmetic; the LINKED production `classify_fp_arg` is the
//        second oracle proving identity over every fpr_idx.
//   [B-aggsize] see SCOPE: the aggregate size-threshold decider is transcribed
//        taking the scalar size (production computes it via `ty.bytes()`).
//   [B4] `Type::{bytes,align}` + `classify_{aggregate,fp_arg}` are PUBLIC and
//        LINKED as the SECOND oracle; `align_up` + the size-decider are cross-
//        checked against a verbatim native transcription + the linked oracle on
//        real aggregates.

// ── PReg model [B1] ──────────────────────────────────────────────────────────
type PReg = u16;
const FPR_ARG_LEN: usize = 8;
const H_ARG_BASE: PReg = 165; // H0
const S_ARG_BASE: PReg = 128; // S0
const D_ARG_BASE: PReg = 96; // D0
const V_ARG_BASE: PReg = 64; // V0

// ── Type (types.rs:34-67 scalar variants; aggregate variants elided [B-scalaronly]) ─
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Type {
    I8,
    I16,
    I32,
    I64,
    I128,
    F16,
    F32,
    F64,
    B1,
    V128,
}

impl Type {
    /// types.rs:99-105, VERBATIM scalar arms.
    pub fn bytes(&self) -> u32 {
        match self {
            Type::B1 | Type::I8 => 1,
            Type::I16 | Type::F16 => 2,
            Type::I32 | Type::F32 => 4,
            Type::I64 | Type::F64 => 8,
            Type::I128 | Type::V128 => 16,
        }
    }

    /// types.rs:308-328, VERBATIM scalar path (V128 + I128 arms + the `_`
    /// fall-through). Production spells the two 16-byte arms separately
    /// (`Type::V128 => 16, Type::I128 => 16`); constant-identical arms are
    /// transcribed as one or-pattern (result-identical, one arm body — the
    /// same shape `bytes` above uses). The I128 arm is the e3b23194 layout
    /// fix: a 128-bit scalar is 16-byte aligned (AAPCS64 quad-word; stock
    /// rustc `align_of::<u128>() == 16`), where the `_` fall-through's
    /// `min(8)` cap used to swallow it and answer 8.
    /// [B-min] `u32::min` lowers to an empty `Ord::min` library leaf the JIT
    /// cannot resolve; `bytes().min(8)` is transcribed as the result-identical
    /// `if b < 8 { b } else { 8 }` (both branches verified native==JIT).
    pub fn align(&self) -> u32 {
        match self {
            Type::I128 | Type::V128 => 16,
            _ => {
                let b = self.bytes();
                if b < 8 {
                    b
                } else {
                    8
                }
            }
        }
    }
}

// ── ArgLocation (abi.rs:131-166 subset actually produced; PReg=u16 [B1]) ───────
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgLocation {
    Reg(PReg),
    Stack { offset: i64, size: u32 },
    Indirect { ptr_reg: PReg },
    RegPair(PReg, PReg),
}

// ── classify_fp_arg (abi.rs:820-831, VERBATIM logic; array-index -> base+idx [B5]) ─
pub fn classify_fp_arg(ty: &Type, fpr_idx: usize) -> Option<(ArgLocation, usize)> {
    if fpr_idx >= FPR_ARG_LEN {
        return None;
    }
    let i = fpr_idx as PReg;
    match ty {
        Type::F16 => Some((ArgLocation::Reg(H_ARG_BASE + i), fpr_idx + 1)),
        Type::F32 => Some((ArgLocation::Reg(S_ARG_BASE + i), fpr_idx + 1)),
        Type::F64 => Some((ArgLocation::Reg(D_ARG_BASE + i), fpr_idx + 1)),
        Type::V128 => Some((ArgLocation::Reg(V_ARG_BASE + i), fpr_idx + 1)),
        _ => None,
    }
}

// ── align_up (abi.rs:1006-1008, VERBATIM) ─────────────────────────────────────
fn align_up(value: i64, align: i64) -> i64 {
    (value + align - 1) & !(align - 1)
}

// ── classify_aggregate non-HFA size path (abi.rs:952-960; scalar size [B-aggsize]) ─
// Returns (kind, nregs): kind 0=InRegs, 1=Indirect. The two threshold
// comparisons (`0..=8`, `9..=16`, else) are VERBATIM the production match.
fn classify_aggregate_by_size(size: u32) -> (u32, u32) {
    match size {
        0..=8 => (0, 1),  // InRegs { regs: vec![X0] }
        9..=16 => (0, 2), // InRegs { regs: vec![X0, X1] }
        _ => (1, 0),      // Indirect { ptr_reg: X0 }
    }
}

// ── scalar Type builder (tag -> scalar Type) ──────────────────────────────────
fn build_type(tag: u32) -> Type {
    match tag {
        0 => Type::I8,
        1 => Type::I16,
        2 => Type::I32,
        3 => Type::I64,
        4 => Type::I128,
        5 => Type::F16,
        6 => Type::F32,
        7 => Type::F64,
        8 => Type::B1,
        _ => Type::V128,
    }
}

// ── POD out-vector + #[no_mangle] mono ROOT ───────────────────────────────────
#[repr(C)]
pub struct AbiAaOut {
    pub bytes: u32,
    pub align: u32,
    pub fp_present: u32,
    pub fp_reg: u32,
    pub fp_next: u32,
    pub agg_kind: u32, // classify_aggregate_by_size kind (0=InRegs 1=Indirect)
    pub agg_nregs: u32,
    pub align_up: i64,
}

/// ROOT: one call exercises every scalar-shaped AArch64 ABI decider.
///   ty_tag  -> build_type(ty_tag) (scalar): bytes / align / classify_fp_arg
///   fpr_idx -> classify_fp_arg(ty, fpr_idx)
///   size    -> classify_aggregate_by_size(size)  [aggregate size threshold]
///   av, aa  -> align_up(av, aa)
#[no_mangle]
pub fn abi_aa_root(ty_tag: u32, fpr_idx: u32, size: u32, av: i64, aa: i64, out: &mut AbiAaOut) {
    let ty = build_type(ty_tag);
    out.bytes = ty.bytes();
    out.align = ty.align();

    match classify_fp_arg(&ty, fpr_idx as usize) {
        None => {
            out.fp_present = 0;
            out.fp_reg = 9999;
            out.fp_next = 9999;
        }
        Some((loc, next)) => {
            out.fp_present = 1;
            out.fp_reg = match loc {
                ArgLocation::Reg(r) => r as u32,
                _ => 8888,
            };
            out.fp_next = next as u32;
        }
    }

    let (kind, nregs) = classify_aggregate_by_size(size);
    out.agg_kind = kind;
    out.agg_nregs = nregs;

    out.align_up = align_up(av, aa);
}
