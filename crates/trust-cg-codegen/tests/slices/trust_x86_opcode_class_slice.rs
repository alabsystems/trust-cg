// Trust-toolchain slice — the x86-64 OPCODE CLASSIFIER layer, transcribed
// VERBATIM from:
//   * trust-cg/crates/trust-cg-ir/src/x86_64_ops.rs     (the X86Opcode enum)
//   * trust-cg/crates/trust-cg-opt/src/effects.rs        (x86_opcode_effect,
//     x86_is_removable, x86_writes_flags, x86_reads_flags, x86_produces_value)
// working tree @ b2c58eb.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 21,
// TRUST BATCH 8, part 1 — the x86 COMPANION to R20's target-independent
// category classifiers). R20 (batch 7) verified the target-INDEPENDENT
// OpcodeCategory layer (category_memory_effect/is_removable/reads_flags/
// writes_flags); this slice verifies the per-ISA x86-64 LEAF classifiers that
// R20 explicitly scoped OUT ([B3] there: "the per-ISA leaves are out of
// scope here"). These are the deciders the x86 DCE / scheduler / CSE / GVN /
// LICM passes consult directly.
//
// WHY SOUNDNESS-CRITICAL: exhaustive over ALL 193 X86Opcode variants —
//   * `x86_opcode_effect` — the Load/Store/Call/Pure memory-effect classifier
//     the x86 alias/reordering analysis is built on; a false "Pure" on a
//     load/store/call drops or reorders a memory access;
//   * `x86_is_removable` — the x86 DCE removability gate (conservative: pure
//     AND in the flag-clobber-free whitelist); a false positive deletes a
//     live flag-setting instruction;
//   * `x86_writes_flags` / `x86_reads_flags` — the RFLAGS def/use classifiers
//     the scheduler uses to add flag-dependency edges (the ADC/SBB i128 carry
//     chain); a wrong answer reorders across a flags def/use — a miscompile;
//   * `x86_produces_value` — whether operand[0] is a def (drives def-use maps
//     across the x86 passes); a wrong answer corrupts liveness.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure x86_class_props_root` per the
// README recipe; `-C overflow-checks=off -C debug-assertions=off`.
//
// MODELED BOUNDARIES:
//   [B1] `X86Opcode` is fed to the root as a u32 tag and reconstructed by the
//        total `x86_from_tag` (declaration-order tag, R16 x86-encoder enum<->tag
//        plumbing); the transcribed classifiers themselves are UNMODIFIED.
//        `MemoryEffect` is returned as a u32 tag via `mem_effect_tag`.
//   [B2] `MemoryEffect::is_pure` (consumed by `x86_is_removable`) is production
//        `self == Self::Pure`. The trust-ir MIR frontend cannot lower
//        `x == Enum::Variant` for a fieldless enum (owner item #6 / R20 [F1]):
//        the variant-constant lowers to an aggregate `Const` and the Eq-binop
//        asserts a single scalar. For a fieldless enum `self == Self::Pure` is
//        DEFINITIONALLY `matches!(self, Self::Pure)` (derived Eq = same
//        discriminant), so the RESULT-IDENTICAL `matches!` is transcribed;
//        the dual oracle links the real `==`-based classifiers so any drift is
//        caught. RE-DECLARED (not re-pinned) per the R21 handoff.
//   [B3] All five classifiers are `pub` in production and are LINKED into the
//        test binary as the SECOND oracle (dual-oracle discipline); the sweep
//        is EXHAUSTIVE over all 193 declared X86Opcode variants.
//   [B4] `#[repr(u8)]` is added to this slice's X86Opcode (production has no
//        repr). It works around frontend finding [F5]: a fieldless enum with
//        >128 variants gets an 8-bit tag, but the default (no-repr) lowering
//        reads it with `sext i8` while emitting the SwitchInt keys as the
//        UNSIGNED discriminants 0..192 — so variants 128..192 never match their
//        arm, fall through to the exhaustive-match `unreachable`, and the JIT
//        machine code `abort()`s at runtime. `#[repr(u8)]` forces the correct
//        UNSIGNED treatment (`bitcast i8->u8`, unsigned switch) so tag 192
//        matches key 192. The classifier match arms are UNMODIFIED and the dual
//        oracle uses the PRODUCTION (no-repr) enum computed natively, so any
//        drift is caught. [F5] is REPORTED as a frontend finding.


// ── X86Opcode (x86_64_ops.rs:26-, VERBATIM variant order; per-variant docs
//    dropped — they do not affect codegen) ──────────────────────────────────
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum X86Opcode {
        AddRR,
        AddRI,
        AddRM,
        SubRR,
        SubRI,
        SubRM,
        ImulRR,
        ImulRRI,
        ImulRM,
        Idiv,
        Div,
        Neg,
        Inc,
        Dec,
        Cdq,
        Cqo,
        AndRR,
        AndRI,
        OrRR,
        OrRI,
        XorRR,
        XorRI,
        Not,
        ShlRR,
        ShlRI,
        ShrRR,
        ShrRI,
        SarRR,
        SarRI,
        MovRR,
        MovRI,
        MovRM8,
        MovRM16,
        MovRM32,
        MovRM,
        MovMR8,
        MovMR16,
        MovMR32,
        MovMR,
        Movzx,
        MovzxW,
        MovsxB,
        MovsxW,
        Movsx,
        Lea,
        LeaSib,
        MovRMSib,
        MovMRSib,
        LeaRip,
        CmpRR,
        CmpRI,
        CmpRI8,
        CmpRM,
        TestRR,
        TestRI,
        TestRM,
        Jmp,
        Jcc,
        Call,
        CallR,
        CallM,
        Ret,
        Addsd,
        Subsd,
        Mulsd,
        Divsd,
        Sqrtsd,
        Andpd,
        MovsdRR,
        MovsdRM,
        MovsdMR,
        Ucomisd,
        MovdquRM,
        MovdquMR,
        Addss,
        Subss,
        Mulss,
        Divss,
        Sqrtss,
        Andps,
        MovssRR,
        MovssRM,
        MovssMR,
        Ucomiss,
        Roundsd,
        Roundss,
        Minsd,
        Maxsd,
        Minss,
        Maxss,
        Cmpsd,
        Cmpss,
        MovssRipRel,
        MovsdRipRel,
        Cmovcc,
        Setcc,
        Cvtsi2sd,
        Cvtsd2si,
        Cvtsi2ss,
        Cvtss2si,
        Cvtsd2ss,
        Cvtss2sd,
        Bsf,
        Bsr,
        Tzcnt,
        Lzcnt,
        Popcnt,
        BtRI,
        Bswap,
        Xchg,
        Cmpxchg,
        Mfence,
        MovdToXmm,
        MovdFromXmm,
        MovqToXmm,
        MovqFromXmm,
        Push,
        Pop,
        Phi,
        StackAlloc,
        Nop,
        NopMulti,
        MovRR32,
        MovRipRel,
        Cmovcc32,
        Mul,
        Ud2,
        Cvttsd2si,
        Cvttss2si,
        AtomicRmwCasLoop,
        AtomicRmwCasLoop8,
        AtomicRmwCasLoop16,
        Pand,
        Pandn,
        Por,
        Pxor,
        Pcmpeqd,
        Pshufd,
        Pmovmskb,
        MovdqaRR,
        Pcmpgtd,
        MovdqaRM,
        MovdqaMR,
        Paddd,
        Psubd,
        Punpckldq,
        Punpcklqdq,
        Paddq,
        Psubq,
        Paddb,
        Paddw,
        Psubb,
        Psubw,
        Pinsrd,
        Pextrd,
        V4I32MaskExtract,
        Pmulld,
        Pcmpeqq,
        Pcmpgtq,
        Ptest,
        Pinsrq,
        Pextrq,
        V2I64MaskExtract,
        Pblendvb,
        V128BoolSelect,
        Pmuludq,
        Pmullw,
        Pcmpeqb,
        Pcmpeqw,
        Pcmpgtb,
        Pcmpgtw,
        V16I8MaskExtract,
        V8I16MaskExtract,
        Pslld,
        Psrld,
        Psrad,
        AdcRR,
        SbbRR,
        Addps,
        Subps,
        Mulps,
        Divps,
        Addpd,
        Subpd,
        Mulpd,
        Divpd,
        Punpcklbw,
        Punpckhbw,
        Packuswb,
        TrapBoundsCheckExact,
        TrapNullIfZeroExact,
        TrapDivZeroExact,
        TrapShiftRangeExact,
}

// ── MemoryEffect (effects.rs:26-68; is_pure is [B2] matches!-form) ───────────
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MemoryEffect {
    Pure,
    Load,
    Store,
    Call,
}

impl MemoryEffect {
    /// effects.rs:45-48. Production is `self == Self::Pure`; [B2] matches!-form.
    #[inline]
    pub fn is_pure(self) -> bool {
        matches!(self, Self::Pure)
    }

    /// effects.rs:57-60, VERBATIM
    #[inline]
    pub fn writes_memory(self) -> bool {
        matches!(self, Self::Store | Self::Call)
    }

    /// effects.rs:51-54, VERBATIM
    #[inline]
    pub fn reads_memory(self) -> bool {
        matches!(self, Self::Load | Self::Call)
    }

    /// effects.rs:64-67, VERBATIM
    #[inline]
    pub fn is_barrier(self) -> bool {
        matches!(self, Self::Call)
    }
}

// ── x86_opcode_effect (effects.rs:539-634, VERBATIM) ─────────────────────────
pub fn x86_opcode_effect(opcode: X86Opcode) -> MemoryEffect {
    use X86Opcode::*;
    match opcode {
        // -- Loads: read memory --
        MovRM8 | MovRM16 | MovRM32 | MovRM | MovsdRM | MovssRM | MovdquRM | MovdqaRM | MovRMSib
        | AddRM | SubRM | CmpRM | ImulRM | TestRM | Ptest | MovRipRel | MovssRipRel
        | MovsdRipRel | Pop => MemoryEffect::Load,

        // -- Stores: write memory --
        MovMR8 | MovMR16 | MovMR32 | MovMR | MovsdMR | MovssMR | MovdquMR | MovdqaMR | MovMRSib
        | Push => MemoryEffect::Store,

        // -- Calls / barriers: full memory ordering barrier --
        Call | CallR | CallM | Mfence => MemoryEffect::Call,

        // -- Everything else: pure computation --
        // Arithmetic
        AddRR | AddRI | SubRR | SubRI | ImulRR | ImulRRI | Neg | Inc | Dec => MemoryEffect::Pure,

        // Division (has side effects but no memory access)
        Idiv | Div | Mul => MemoryEffect::Pure,

        // Sign-extend implicit (CDQ/CQO)
        Cdq | Cqo => MemoryEffect::Pure,

        // Add/subtract with carry (i128): read+write the carry flag, no memory.
        AdcRR | SbbRR => MemoryEffect::Pure,

        // Logical
        AndRR | AndRI | OrRR | OrRI | XorRR | XorRI | Not | Pand | Pandn | Por | Pxor => {
            MemoryEffect::Pure
        }

        // Shifts
        ShlRR | ShlRI | ShrRR | ShrRI | SarRR | SarRI => MemoryEffect::Pure,

        // Compare/test (set flags, no memory access)
        CmpRR | CmpRI | CmpRI8 | TestRR | TestRI | Ucomisd | Ucomiss | BtRI => MemoryEffect::Pure,

        // Moves (register-register and register-immediate)
        MovRR | MovRR32 | MovRI | Movzx | MovzxW | MovsxB | MovsxW | Movsx | MovsdRR | MovssRR
        | MovdqaRR => MemoryEffect::Pure,

        // LEA (address computation, no memory access)
        Lea | LeaSib | LeaRip => MemoryEffect::Pure,

        // Conditional move/set
        Cmovcc | Cmovcc32 | Setcc => MemoryEffect::Pure,

        // SSE register-register arithmetic
        Addsd | Subsd | Mulsd | Divsd | Sqrtsd | Roundsd | Andpd | Addss | Subss | Mulss | Divss
        | Sqrtss | Roundss | Minsd | Maxsd | Minss | Maxss | Cmpsd | Cmpss
        | Andps | Pcmpeqb | Pcmpeqw | Pcmpgtb | Pcmpgtw | Pcmpeqd | Pcmpgtd | Paddb | Paddw
        | Paddd | Psubb | Psubw | Psubd | Paddq | Psubq | Pmullw | Pmuludq | Punpcklbw
        | Punpckldq | Packuswb | Punpckhbw | Punpcklqdq | Pmulld | Pcmpeqq | Pcmpgtq | Pshufd
        | Pmovmskb | Pinsrd | Pextrd | Pinsrq | Pextrq | Pblendvb | Pslld | Psrld | Psrad
        | Addps | Subps | Mulps | Divps | Addpd | Subpd | Mulpd | Divpd => MemoryEffect::Pure,

        // SSE type conversions
        Cvtsi2sd | Cvtsd2si | Cvttsd2si | Cvtsi2ss | Cvtss2si | Cvttss2si | Cvtsd2ss | Cvtss2sd => {
            MemoryEffect::Pure
        }

        // GPR <-> XMM transfers
        MovdToXmm | MovdFromXmm | MovqToXmm | MovqFromXmm => MemoryEffect::Pure,

        // Bit manipulation
        Bsf | Bsr | Tzcnt | Lzcnt | Popcnt | Bswap => MemoryEffect::Pure,

        // Atomic: conservative (read + write memory)
        Xchg => MemoryEffect::Store,
        Cmpxchg => MemoryEffect::Store,
        AtomicRmwCasLoop | AtomicRmwCasLoop8 | AtomicRmwCasLoop16 => MemoryEffect::Store,

        // Branches / control flow (no memory ops; DCE uses InstFlags)
        Jmp | Jcc | Ret | Ud2 => MemoryEffect::Pure,

        // Pseudo-instructions
        Phi => MemoryEffect::Pure,
        StackAlloc => MemoryEffect::Store,
        Nop | NopMulti | V4I32MaskExtract | V16I8MaskExtract | V8I16MaskExtract
        | V2I64MaskExtract | V128BoolSelect => MemoryEffect::Pure,
        // Proof-only guard carriers (Sentinel S5): touch no memory.
        TrapBoundsCheckExact | TrapNullIfZeroExact | TrapDivZeroExact | TrapShiftRangeExact => {
            MemoryEffect::Pure
        }
    }
}

// ── x86_produces_value (effects.rs:683-708, VERBATIM) ────────────────────────
pub fn x86_produces_value(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    !matches!(
        opcode,
        // Compare/test: only set flags
        CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM
        | Ucomisd | Ucomiss | BtRI | Ptest
        // Stores
        | MovMR8 | MovMR16 | MovMR32 | MovMR | MovsdMR | MovssMR | MovdquMR | MovdqaMR
        | MovMRSib
        // Branches and control flow
        | Jmp | Jcc | Call | CallR | CallM | Ret
        // Stack store
        | Push
        // Pseudo with no value
        | Nop | NopMulti | StackAlloc
        // Memory fence
        | Mfence
        // Atomic exchange (complex implicit operands)
        | Cmpxchg
        // Fixed-register implicit writes
        | Cdq | Cqo | Idiv | Div | Mul
        // Trap terminator
        | Ud2
        // Proof-only trap carriers: every operand is a READ of the guarded
        // value (the expansion emits TEST/CMP on them); nothing is defined.
        // P0 (2026-07-18, b14/b18 runtime ud2): treating operand[0] as a def
        // gave a single-operand `TrapDivZeroExact [divisor]` ZERO reads once
        // magic-sdiv replaced the Div — liveness/DCE then dropped the
        // divisor's MovRI while the carrier expanded into a real test of a
        // never-written spill slot.
        | TrapBoundsCheckExact | TrapNullIfZeroExact | TrapDivZeroExact
        | TrapShiftRangeExact
    )
}

// ── x86_is_removable (effects.rs:717-787, VERBATIM) ──────────────────────────
pub fn x86_is_removable(opcode: X86Opcode) -> bool {
    let effect = x86_opcode_effect(opcode);
    if !effect.is_pure() {
        return false;
    }

    use X86Opcode::*;
    matches!(
        opcode,
        MovRR
            | MovRR32
            | MovRI
            | Movzx
            | MovzxW
            | MovsxB
            | MovsxW
            | Movsx
            | MovsdRR
            | MovssRR
            | MovdqaRR
            | Pand
            | Pandn
            | Por
            | Pxor
            | Pcmpeqb
            | Pcmpeqw
            | Pcmpgtb
            | Pcmpgtw
            | Pcmpeqd
            | Pcmpgtd
            | Paddb
            | Paddw
            | Psubb
            | Psubw
            | Paddq
            | Psubq
            | Pcmpeqq
            | Pcmpgtq
            | Punpckldq
            | Punpcklqdq
            | Pshufd
            | Pmovmskb
            | Pinsrd
            | Pextrd
            | Pinsrq
            | Pextrq
            | Pblendvb
            | V128BoolSelect
            | Lea
            | LeaSib
            | LeaRip
            | Cvtsi2sd
            | Cvtsd2si
            | Cvttsd2si
            | Cvtsi2ss
            | Cvtss2si
            | Cvttss2si
            | Cvtsd2ss
            | Cvtss2sd
            | MovdToXmm
            | MovdFromXmm
            | MovqToXmm
            | MovqFromXmm
            | Bswap
            | Phi
            | Nop
    )
}

// ── x86_writes_flags (effects.rs:795-825, VERBATIM) ──────────────────────────
pub fn x86_writes_flags(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        // Arithmetic
        AddRR | AddRI | AddRM | SubRR | SubRI | SubRM
        | AdcRR | SbbRR
        | ImulRR | ImulRRI | ImulRM | Idiv | Div | Mul
        | Neg | Inc | Dec
        // Logical
        | AndRR | AndRI | OrRR | OrRI | XorRR | XorRI | Not
        // Shifts
        | ShlRR | ShlRI | ShrRR | ShrRI | SarRR | SarRI
        // Compare/test
        | CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM
        | Ptest
        // FP compare
        | Ucomisd | Ucomiss
        // Bit manipulation that sets flags
        | Bsf | Bsr | Tzcnt | Lzcnt | Popcnt | BtRI
        // Atomic
        | Cmpxchg
        | AtomicRmwCasLoop
        | AtomicRmwCasLoop8
        | AtomicRmwCasLoop16
        | V4I32MaskExtract
        | V16I8MaskExtract
        | V8I16MaskExtract
        | V2I64MaskExtract
    )
}

// ── x86_reads_flags (effects.rs:836-839, VERBATIM) ───────────────────────────
pub fn x86_reads_flags(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(opcode, Cmovcc | Cmovcc32 | Setcc | Jcc | AdcRR | SbbRR)
}

// ── [B1] tag plumbing ────────────────────────────────────────────────────────

/// Total reconstruction of X86Opcode from its declaration-order u32 tag.
fn x86_from_tag(tag: u32) -> X86Opcode {
    use X86Opcode::*;
    match tag {
        0 => AddRR,
        1 => AddRI,
        2 => AddRM,
        3 => SubRR,
        4 => SubRI,
        5 => SubRM,
        6 => ImulRR,
        7 => ImulRRI,
        8 => ImulRM,
        9 => Idiv,
        10 => Div,
        11 => Neg,
        12 => Inc,
        13 => Dec,
        14 => Cdq,
        15 => Cqo,
        16 => AndRR,
        17 => AndRI,
        18 => OrRR,
        19 => OrRI,
        20 => XorRR,
        21 => XorRI,
        22 => Not,
        23 => ShlRR,
        24 => ShlRI,
        25 => ShrRR,
        26 => ShrRI,
        27 => SarRR,
        28 => SarRI,
        29 => MovRR,
        30 => MovRI,
        31 => MovRM8,
        32 => MovRM16,
        33 => MovRM32,
        34 => MovRM,
        35 => MovMR8,
        36 => MovMR16,
        37 => MovMR32,
        38 => MovMR,
        39 => Movzx,
        40 => MovzxW,
        41 => MovsxB,
        42 => MovsxW,
        43 => Movsx,
        44 => Lea,
        45 => LeaSib,
        46 => MovRMSib,
        47 => MovMRSib,
        48 => LeaRip,
        49 => CmpRR,
        50 => CmpRI,
        51 => CmpRI8,
        52 => CmpRM,
        53 => TestRR,
        54 => TestRI,
        55 => TestRM,
        56 => Jmp,
        57 => Jcc,
        58 => Call,
        59 => CallR,
        60 => CallM,
        61 => Ret,
        62 => Addsd,
        63 => Subsd,
        64 => Mulsd,
        65 => Divsd,
        66 => Sqrtsd,
        67 => Andpd,
        68 => MovsdRR,
        69 => MovsdRM,
        70 => MovsdMR,
        71 => Ucomisd,
        72 => MovdquRM,
        73 => MovdquMR,
        74 => Addss,
        75 => Subss,
        76 => Mulss,
        77 => Divss,
        78 => Sqrtss,
        79 => Andps,
        80 => MovssRR,
        81 => MovssRM,
        82 => MovssMR,
        83 => Ucomiss,
        84 => Roundsd,
        85 => Roundss,
        86 => Minsd,
        87 => Maxsd,
        88 => Minss,
        89 => Maxss,
        90 => Cmpsd,
        91 => Cmpss,
        92 => MovssRipRel,
        93 => MovsdRipRel,
        94 => Cmovcc,
        95 => Setcc,
        96 => Cvtsi2sd,
        97 => Cvtsd2si,
        98 => Cvtsi2ss,
        99 => Cvtss2si,
        100 => Cvtsd2ss,
        101 => Cvtss2sd,
        102 => Bsf,
        103 => Bsr,
        104 => Tzcnt,
        105 => Lzcnt,
        106 => Popcnt,
        107 => BtRI,
        108 => Bswap,
        109 => Xchg,
        110 => Cmpxchg,
        111 => Mfence,
        112 => MovdToXmm,
        113 => MovdFromXmm,
        114 => MovqToXmm,
        115 => MovqFromXmm,
        116 => Push,
        117 => Pop,
        118 => Phi,
        119 => StackAlloc,
        120 => Nop,
        121 => NopMulti,
        122 => MovRR32,
        123 => MovRipRel,
        124 => Cmovcc32,
        125 => Mul,
        126 => Ud2,
        127 => Cvttsd2si,
        128 => Cvttss2si,
        129 => AtomicRmwCasLoop,
        130 => AtomicRmwCasLoop8,
        131 => AtomicRmwCasLoop16,
        132 => Pand,
        133 => Pandn,
        134 => Por,
        135 => Pxor,
        136 => Pcmpeqd,
        137 => Pshufd,
        138 => Pmovmskb,
        139 => MovdqaRR,
        140 => Pcmpgtd,
        141 => MovdqaRM,
        142 => MovdqaMR,
        143 => Paddd,
        144 => Psubd,
        145 => Punpckldq,
        146 => Punpcklqdq,
        147 => Paddq,
        148 => Psubq,
        149 => Paddb,
        150 => Paddw,
        151 => Psubb,
        152 => Psubw,
        153 => Pinsrd,
        154 => Pextrd,
        155 => V4I32MaskExtract,
        156 => Pmulld,
        157 => Pcmpeqq,
        158 => Pcmpgtq,
        159 => Ptest,
        160 => Pinsrq,
        161 => Pextrq,
        162 => V2I64MaskExtract,
        163 => Pblendvb,
        164 => V128BoolSelect,
        165 => Pmuludq,
        166 => Pmullw,
        167 => Pcmpeqb,
        168 => Pcmpeqw,
        169 => Pcmpgtb,
        170 => Pcmpgtw,
        171 => V16I8MaskExtract,
        172 => V8I16MaskExtract,
        173 => Pslld,
        174 => Psrld,
        175 => Psrad,
        176 => AdcRR,
        177 => SbbRR,
        178 => Addps,
        179 => Subps,
        180 => Mulps,
        181 => Divps,
        182 => Addpd,
        183 => Subpd,
        184 => Mulpd,
        185 => Divpd,
        186 => Punpcklbw,
        187 => Punpckhbw,
        188 => Packuswb,
        189 => TrapBoundsCheckExact,
        190 => TrapNullIfZeroExact,
        191 => TrapDivZeroExact,
        192 => TrapShiftRangeExact,
        _ => Nop,
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

/// POD property vector for one X86Opcode.
#[repr(C)]
pub struct X86ClassProps {
    pub mem_effect_tag: u32,
    pub eff_is_pure: u32,
    pub eff_reads_mem: u32,
    pub eff_writes_mem: u32,
    pub eff_is_barrier: u32,
    pub is_removable: u32,
    pub writes_flags: u32,
    pub reads_flags: u32,
    pub produces_value: u32,
}

/// ROOT: the x86-64 opcode classifier vector for one opcode tag.
#[no_mangle]
pub fn x86_class_props_root(tag: u32, out: &mut X86ClassProps) {
    let op = x86_from_tag(tag);
    let eff = x86_opcode_effect(op);
    out.mem_effect_tag = mem_effect_tag(eff);
    out.eff_is_pure = eff.is_pure() as u32;
    out.eff_reads_mem = eff.reads_memory() as u32;
    out.eff_writes_mem = eff.writes_memory() as u32;
    out.eff_is_barrier = eff.is_barrier() as u32;
    out.is_removable = x86_is_removable(op) as u32;
    out.writes_flags = x86_writes_flags(op) as u32;
    out.reads_flags = x86_reads_flags(op) as u32;
    out.produces_value = x86_produces_value(op) as u32;
}
