// Trust-toolchain slice — the OPCODE-CATEGORY OPTIMIZATION PREDICATE layer,
// transcribed VERBATIM from two crates:
//   * trust-cg/crates/trust-cg-ir/src/target_info.rs  (OpcodeCategory + its
//     is_arithmetic/is_logical/is_shift/is_move/is_reg_imm/is_reg_reg_binary
//     algebraic-simplification match predicates)                 (36-190)
//   * trust-cg/crates/trust-cg-opt/src/effects.rs      (MemoryEffect +
//     its is_pure/reads_memory/writes_memory/is_barrier, and the target-
//     independent category classifiers category_memory_effect /
//     category_is_removable / category_reads_flags /
//     category_writes_flags)                        (26-68, 853-917)
// working tree @ 8e48d2e.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 20,
// TRUST BATCH 7, part 1 of 2 — the OPTIMIZATION / ANALYSIS PREDICATE layer,
// a NEW surface: rounds 1/7/16 did encoders, 5/16 did register files, 4 the
// interpreter int core — the opt/analysis predicate deciders were UNTOUCHED).
//
// WHY SOUNDNESS-CRITICAL: these predicates decide WHEN an optimization is
// legal. A wrong answer lets an UNSOUND transformation through:
//   * `category_memory_effect` -> `is_pure` is the gate DCE/CSE/LICM consult
//     to decide an instruction may be deleted/reordered/hoisted — a false
//     "Pure" on a Load/Store/Call drops or reorders a memory access;
//   * `category_is_removable` is the target-independent DCE removability
//     decider (pure AND not a compare AND not flag-writing AND not control
//     flow) — a false "removable" deletes a live instruction;
//   * `category_reads_flags`/`category_writes_flags` gate flag-clobber
//     reordering — a wrong answer moves an instruction across a flags def/use;
//   * `OpcodeCategory::is_reg_reg_binary` marks the ops where `op x,x` has a
//     special identity (sub x,x=0, and x,x=x, xor x,x=0) — a false positive
//     rewrites a non-idempotent op to a wrong constant;
//   * `is_arithmetic`/`is_logical`/`is_shift`/`is_move`/`is_reg_imm` are the
//     strength-reduction / const-fold / peephole MATCH predicates.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure cat_props_root` per the
// README recipe; `-C overflow-checks=off -C debug-assertions=off`.
//
// MODELED BOUNDARIES:
//   [B1] `OpcodeCategory` is fed to the root as a u32 tag and reconstructed
//        by the total `cat_from_tag` (round-5/16 enum<->tag plumbing); the
//        transcribed predicates themselves are UNMODIFIED. `MemoryEffect` is
//        returned as a u32 tag via `mem_effect_tag`.
//   [B2] `category_is_removable`'s `target_writes_flags: bool` argument is a
//        pass-supplied input (from `TargetInfo::writes_flags`); the root
//        evaluates it at BOTH false and true so one sweep covers the arg.
//   [B3] The doc comments reference `AArch64Opcode`/`X86Opcode` opcode-level
//        classifiers (`opcode_effect`, `is_removable`, ...); those are the
//        per-ISA leaves and are out of scope here — this slice verifies the
//        TARGET-INDEPENDENT category layer that the generic passes consult.

// ── OpcodeCategory (target_info.rs:36-116, VERBATIM) ─────────────────────────
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OpcodeCategory {
    // -- Arithmetic --
    AddRR,
    AddRI,
    SubRR,
    SubRI,
    MulRR,
    Neg,
    // -- Logical --
    AndRR,
    AndRI,
    OrRR,
    OrRI,
    XorRR,
    XorRI,
    // -- Shifts --
    ShlRR,
    ShlRI,
    ShrRR,
    ShrRI,
    SarRR,
    SarRI,
    // -- Move --
    MovRR,
    MovRI,
    // -- Compare --
    CmpRR,
    CmpRI,
    // -- Control flow --
    Nop,
    Ret,
    Call,
    Branch,
    CondBranch,
    // -- Memory --
    Load,
    Store,
    // -- SSA --
    Phi,
    // -- Catch-all --
    Other,
}

impl OpcodeCategory {
    /// target_info.rs:121-127, VERBATIM
    #[inline]
    pub fn is_arithmetic(self) -> bool {
        matches!(
            self,
            Self::AddRR | Self::AddRI | Self::SubRR | Self::SubRI | Self::MulRR | Self::Neg
        )
    }

    /// target_info.rs:130-136, VERBATIM
    #[inline]
    pub fn is_logical(self) -> bool {
        matches!(
            self,
            Self::AndRR | Self::AndRI | Self::OrRR | Self::OrRI | Self::XorRR | Self::XorRI
        )
    }

    /// target_info.rs:139-145, VERBATIM
    #[inline]
    pub fn is_shift(self) -> bool {
        matches!(
            self,
            Self::ShlRR | Self::ShlRI | Self::ShrRR | Self::ShrRI | Self::SarRR | Self::SarRI
        )
    }

    /// target_info.rs:148-151, VERBATIM
    #[inline]
    pub fn is_move(self) -> bool {
        matches!(self, Self::MovRR | Self::MovRI)
    }

    /// target_info.rs:155-170, VERBATIM
    #[inline]
    pub fn is_reg_imm(self) -> bool {
        matches!(
            self,
            Self::AddRI
                | Self::SubRI
                | Self::AndRI
                | Self::OrRI
                | Self::XorRI
                | Self::ShlRI
                | Self::ShrRI
                | Self::SarRI
                | Self::CmpRI
                | Self::MovRI
        )
    }

    /// target_info.rs:175-189, VERBATIM
    #[inline]
    pub fn is_reg_reg_binary(self) -> bool {
        matches!(
            self,
            Self::AddRR
                | Self::SubRR
                | Self::MulRR
                | Self::AndRR
                | Self::OrRR
                | Self::XorRR
                | Self::ShlRR
                | Self::ShrRR
                | Self::SarRR
        )
    }
}

// ── MemoryEffect (effects.rs:26-68, VERBATIM) ────────────────────────────────
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MemoryEffect {
    Pure,
    Load,
    Store,
    Call,
}

impl MemoryEffect {
    /// effects.rs:45-48. Production is `self == Self::Pure`.
    /// [B4] The trust-ir MIR frontend cannot lower `x == Enum::Variant` for a
    ///      fieldless enum (derived PartialEq): the variant-constant lowers to
    ///      an aggregate `Const`, and the Eq-binop constant operand asserts a
    ///      single scalar — "constant value not a single scalar" (isolated in
    ///      a 2-line repro; `matches!` form lowers, `==` form does not). For a
    ///      fieldless enum `self == Self::Pure` is DEFINITIONALLY
    ///      `matches!(self, Self::Pure)` (derived Eq = same discriminant), so
    ///      the equivalent `matches!` is transcribed here; RESULT-IDENTICAL,
    ///      and the dual oracle links the real `==`-based `is_pure` so any
    ///      drift is caught. REPORTED as a frontend finding.
    #[inline]
    pub fn is_pure(self) -> bool {
        matches!(self, Self::Pure)
    }

    /// effects.rs:51-54, VERBATIM
    #[inline]
    pub fn reads_memory(self) -> bool {
        matches!(self, Self::Load | Self::Call)
    }

    /// effects.rs:57-60, VERBATIM
    #[inline]
    pub fn writes_memory(self) -> bool {
        matches!(self, Self::Store | Self::Call)
    }

    /// effects.rs:64-67, VERBATIM
    #[inline]
    pub fn is_barrier(self) -> bool {
        matches!(self, Self::Call)
    }
}

// ── category classifiers (effects.rs:853-917, VERBATIM) ──────────────────────

/// effects.rs:853-864, VERBATIM
pub fn category_memory_effect(cat: OpcodeCategory) -> MemoryEffect {
    use OpcodeCategory::*;
    match cat {
        Load => MemoryEffect::Load,
        Store => MemoryEffect::Store,
        Call => MemoryEffect::Call,
        // All other categories are pure computation.
        AddRR | AddRI | SubRR | SubRI | MulRR | Neg | AndRR | AndRI | OrRR | OrRI | XorRR
        | XorRI | ShlRR | ShlRI | ShrRR | ShrRI | SarRR | SarRI | MovRR | MovRI | CmpRR | CmpRI
        | Nop | Ret | Branch | CondBranch | Phi | Other => MemoryEffect::Pure,
    }
}

/// effects.rs:876-899, VERBATIM
pub fn category_is_removable(cat: OpcodeCategory, target_writes_flags: bool) -> bool {
    if !category_memory_effect(cat).is_pure() {
        return false;
    }
    // Compare instructions always set flags — not removable.
    if matches!(cat, OpcodeCategory::CmpRR | OpcodeCategory::CmpRI) {
        return false;
    }
    // If the target says this opcode writes flags, not removable.
    if target_writes_flags {
        return false;
    }
    // Control flow is not removable.
    if matches!(
        cat,
        OpcodeCategory::Branch
            | OpcodeCategory::CondBranch
            | OpcodeCategory::Ret
            | OpcodeCategory::Call
    ) {
        return false;
    }
    true
}

/// effects.rs:907-909, VERBATIM
pub fn category_reads_flags(cat: OpcodeCategory) -> bool {
    matches!(cat, OpcodeCategory::CondBranch)
}

/// effects.rs:915-917, VERBATIM
pub fn category_writes_flags(cat: OpcodeCategory) -> bool {
    matches!(cat, OpcodeCategory::CmpRR | OpcodeCategory::CmpRI)
}

// ── [B1] tag plumbing ────────────────────────────────────────────────────────

/// Total reconstruction of OpcodeCategory from its declaration-order u32 tag.
fn cat_from_tag(tag: u32) -> OpcodeCategory {
    use OpcodeCategory::*;
    match tag {
        0 => AddRR,
        1 => AddRI,
        2 => SubRR,
        3 => SubRI,
        4 => MulRR,
        5 => Neg,
        6 => AndRR,
        7 => AndRI,
        8 => OrRR,
        9 => OrRI,
        10 => XorRR,
        11 => XorRI,
        12 => ShlRR,
        13 => ShlRI,
        14 => ShrRR,
        15 => ShrRI,
        16 => SarRR,
        17 => SarRI,
        18 => MovRR,
        19 => MovRI,
        20 => CmpRR,
        21 => CmpRI,
        22 => Nop,
        23 => Ret,
        24 => Call,
        25 => Branch,
        26 => CondBranch,
        27 => Load,
        28 => Store,
        29 => Phi,
        _ => Other,
    }
}

fn mem_effect_tag(e: MemoryEffect) -> u32 {
    match e {
        MemoryEffect::Pure => 0,
        MemoryEffect::Load => 1,
        MemoryEffect::Store => 2,
        MemoryEffect::Call => 3,
    }
}

// ── out-POD + #[no_mangle] mono ROOT ─────────────────────────────────────────

/// POD property vector for one OpcodeCategory.
#[repr(C)]
pub struct CatProps {
    pub is_arithmetic: u32,
    pub is_logical: u32,
    pub is_shift: u32,
    pub is_move: u32,
    pub is_reg_imm: u32,
    pub is_reg_reg_binary: u32,
    pub mem_effect_tag: u32,
    pub eff_is_pure: u32,
    pub eff_reads_mem: u32,
    pub eff_writes_mem: u32,
    pub eff_is_barrier: u32,
    pub is_removable_wf0: u32,
    pub is_removable_wf1: u32,
    pub reads_flags: u32,
    pub writes_flags: u32,
}

/// ROOT: the target-independent opcode-category predicate vector.
#[no_mangle]
pub fn cat_props_root(tag: u32, out: &mut CatProps) {
    let c = cat_from_tag(tag);
    let eff = category_memory_effect(c);
    out.is_arithmetic = c.is_arithmetic() as u32;
    out.is_logical = c.is_logical() as u32;
    out.is_shift = c.is_shift() as u32;
    out.is_move = c.is_move() as u32;
    out.is_reg_imm = c.is_reg_imm() as u32;
    out.is_reg_reg_binary = c.is_reg_reg_binary() as u32;
    out.mem_effect_tag = mem_effect_tag(eff);
    out.eff_is_pure = eff.is_pure() as u32;
    out.eff_reads_mem = eff.reads_memory() as u32;
    out.eff_writes_mem = eff.writes_memory() as u32;
    out.eff_is_barrier = eff.is_barrier() as u32;
    out.is_removable_wf0 = category_is_removable(c, false) as u32;
    out.is_removable_wf1 = category_is_removable(c, true) as u32;
    out.reads_flags = category_reads_flags(c) as u32;
    out.writes_flags = category_writes_flags(c) as u32;
}
