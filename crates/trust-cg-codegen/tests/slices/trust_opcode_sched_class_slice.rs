// Trust-toolchain slice — the INSTRUCTION-SCHEDULER AArch64Opcode CLASSIFIER
// layer, transcribed VERBATIM from trust-cg/crates/trust-cg-opt/src/scheduler.rs:
//   `opcode_latency`                     (100-236) — (latency,port) classifier;
//   `call_opcode_clobbers_registers`     (1011-1016) — call-clobber predicate;
//   `is_proof_reorderable_ordinary_load` (343-361) — load-load edge-drop gate;
//   `is_proof_reorderable_ordinary_ldr_ri`(363-376)— LdrRI reorder gate;
//   `is_proof_reorderable_ordinary_str_ri`(378-392)— StrRI store-load edge gate;
//   `ExecutionPort`                      (76-90);  `InstFlags`(trust-cg-ir).
// working tree @ (see report). REGENERATED for the 260-variant enum (the
// LSE A/L exact-ordering forms, Casl/Swpa/Swpl, FmaddRR, LdrbRO/LdrhRO/
// LdrswRO, TailCall, and the NEON lane/reduction/FP-vector ops joined the
// enum after the original 219-variant snapshot; several were INSERTED
// mid-declaration, so every index from 61 up shifted — the fixture and the
// test's `prod_opcode` table must always be regenerated together).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 22, TRUST
// BATCH 9, part 2 of 2 — the scheduler's OPCODE-KEYED deciders).
//
// WHY SOUNDNESS-CRITICAL: `is_proof_reorderable_ordinary_{load,ldr_ri,str_ri}`
// decide whether the list scheduler may DROP a memory-ordering edge (load-load,
// or a proven-disjoint store->load). A false positive reorders a memory access
// past a dependent one — an UNSOUND miscompile. `opcode_latency` drives the
// critical-path priority; `call_opcode_clobbers_registers` marks the call
// opcodes whose implicit clobbers force live values to be preserved.
//
// [F5] FRONTEND MISCOMPILE (KNOWN CLASS, round-21) — FIXED since (see
//   e2e_trust_fns_round9.rs `trust_f5_norepr_call_clobbers_fixed_bl_blr`): a
//   no-repr fieldless enum's tag used to be read `sext i8`, so variants >=128
//   sign-extended NEGATIVE and never matched an unsigned switch key. The fix
//   reads the tag unsigned; the no-repr companion fixture
//   (trust_f5_norepr_clobbers_slice.rs) pins the fixed behavior. This slice
//   still carries an explicit repr ([B3]) so the tag width is DECLARED, not
//   layout-inferred.
//
// MODELED BOUNDARIES:
//   [B1] `AArch64Opcode`/`ExecutionPort` fed to the root as a u32 index/tag and
//        reconstructed by the total `opcode_from_index` / returned via
//        `port_tag` (round-5/16 enum<->tag plumbing); predicates UNMODIFIED.
//   [B2] `InstFlags` is transcribed locally (the trust-cg-ir manual bitflags
//        u16 newtype: contains/intersection/is_empty/union, same bit values);
//        the dual oracle links the production `trust_cg_ir::InstFlags`.
//   [B3] `#[repr(u16)]` is the ONLY deviation from the production enum decl
//        (which has no repr): 260 variants NO LONGER FIT `#[repr(u8)]` (max
//        256), so the original [B3] u8 workaround is now u16 — matching the
//        u16 tag layout rustc itself gives the 260-variant no-repr enum. The
//        native oracle uses the real no-repr enum.
//   [B5] the production reorder gates now open with a
//        `validator_guard_replay_authority_available() && !cfg!(test)`
//        environment preamble (guard-replay authority gating, orthogonal to
//        the opcode/flags DECISION verified here). The slice transcribes the
//        decision body only; the native oracle in the test binary hits the
//        same short-circuit via `cfg!(test)`, so native==JIT compares the
//        identical decision function.

// ── ExecutionPort (scheduler.rs:76-90, VERBATIM) ─────────────────────────────
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExecutionPort {
    IntAlu,
    IntMul,
    IntDiv,
    LoadStore,
    Branch,
    FpAlu,
}

// ── InstFlags ([B2] trust-cg-ir inst.rs:929-985, VERBATIM bit values/methods) ─
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct InstFlags(u16);
impl InstFlags {
    pub const IS_CALL: Self = Self(0x01);
    pub const HAS_SIDE_EFFECTS: Self = Self(0x10);
    pub const IS_PSEUDO: Self = Self(0x20);
    pub const READS_MEMORY: Self = Self(0x40);
    pub const WRITES_MEMORY: Self = Self(0x80);
    pub const PROOF_REORDERABLE: Self = Self(0x200);
    #[inline]
    pub const fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
    #[inline]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
    #[inline]
    pub const fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
    #[inline]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
    #[inline]
    pub const fn from_bits(bits: u16) -> Self {
        Self(bits)
    }
}
impl std::ops::BitOr for InstFlags {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        self.union(rhs)
    }
}

// ── AArch64Opcode ([B3] #[repr(u16)]; 260 variants VERBATIM order) ──────────
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u16)]
pub enum AArch64Opcode {
    AddRR,
    AddRI,
    AddRIShift12,
    SubRR,
    SubRI,
    MulRR,
    Msub,
    Smull,
    Umull,
    SDiv,
    UDiv,
    Neg,
    AndRR,
    AndRI,
    OrrRR,
    OrrRI,
    EorRR,
    EorRI,
    OrnRR,
    BicRR,
    LslRR,
    LsrRR,
    AsrRR,
    LslRI,
    LsrRI,
    AsrRI,
    RorRI,
    Rbit,
    CmpRR,
    CmpRI,
    Tst,
    Csel,
    Csinc,
    Csinv,
    Csneg,
    MovR,
    MovI,
    Movz,
    Movn,
    Movk,
    FmovImm,
    LdrRI,
    StrRI,
    LdrPreIndex,
    StrPreIndex,
    LdrPostIndex,
    StrPostIndex,
    LdrbRI,
    LdrhRI,
    LdrsbRI,
    LdrshRI,
    StrbRI,
    StrhRI,
    LdrLiteral,
    LdpRI,
    StpRI,
    StpPreIndex,
    LdpPostIndex,
    LdrRO,
    StrRO,
    LdrbRO,
    LdrhRO,
    LdrGot,
    LdrTlvp,
    B,
    BCond,
    Cbz,
    Cbnz,
    Tbz,
    Tbnz,
    Br,
    Bl,
    Blr,
    Ret,
    CSet,
    Sxtw,
    Uxtw,
    Sxtb,
    Sxth,
    Uxtb,
    Uxth,
    Ubfm,
    Sbfm,
    Bfm,
    FaddRR,
    FsubRR,
    FmulRR,
    FdivRR,
    FmaddRR,
    FminnmRR,
    FmaxnmRR,
    FnegRR,
    FabsRR,
    FsqrtRR,
    FrintmRR,
    FrintpRR,
    FrintzRR,
    Fcmp,
    FcvtzsRR,
    FcvtzuRR,
    ScvtfRR,
    UcvtfRR,
    FcvtSD,
    FcvtDS,
    FcvtHS,
    FcvtHD,
    FcvtSH,
    FcvtDH,
    FmovGprFpr,
    FmovFprGpr,
    FmovFprFpr,
    NeonAddV,
    NeonSubV,
    NeonMulV,
    NeonSmaxV,
    NeonSminV,
    NeonUmaxV,
    NeonUminV,
    NeonFaddV,
    NeonFsubV,
    NeonFmulV,
    NeonFdivV,
    NeonFcmgtV,
    NeonAndV,
    NeonOrrV,
    NeonEorV,
    NeonBicV,
    NeonNotV,
    NeonRbitV,
    NeonRev32V,
    NeonRev64V,
    NeonCmeqV,
    NeonCmgtV,
    NeonCmgeV,
    NeonCmhiV,
    NeonCmhsV,
    NeonUmaxv,
    NeonAddpScalar,
    NeonDupElem,
    NeonDupGen,
    NeonInsGen,
    NeonUmovGen,
    NeonMovi,
    NeonLd1Post,
    NeonLdpQPost,
    NeonSt1Post,
    NeonStpQPost,
    NeonCntV,
    NeonUaddlpV,
    NeonSaddlpV,
    NeonAbsV,
    NeonBitV,
    NeonUdotV,
    NeonExtV,
    NeonFmlaV,
    NeonFmlsV,
    NeonUcvtfV,
    NeonScvtfV,
    NeonDupScalarD,
    Ldar,
    Ldarb,
    Ldarh,
    Stlr,
    Stlrb,
    Stlrh,
    Ldadd,
    Ldadda,
    Ldaddal,
    Ldaddl,
    Ldclr,
    Ldclra,
    Ldclral,
    Ldclrl,
    Ldeor,
    Ldeora,
    Ldeoral,
    Ldeorl,
    Ldset,
    Ldseta,
    Ldsetal,
    Ldsetl,
    Ldsmax,
    Ldsmaxa,
    Ldsmaxal,
    Ldsmaxl,
    Ldsmin,
    Ldsmina,
    Ldsminal,
    Ldsminl,
    Ldumax,
    Ldumaxa,
    Ldumaxal,
    Ldumaxl,
    Ldumin,
    Ldumina,
    Lduminal,
    Lduminl,
    Swp,
    Swpa,
    Swpal,
    Swpl,
    Cas,
    Casa,
    Casal,
    Casl,
    Ldaxr,
    Stlxr,
    Dmb,
    Dsb,
    Isb,
    Adrp,
    Adr,
    AddPCRel,
    LdrswRO,
    AddsRR,
    AddsRI,
    SubsRR,
    SubsRI,
    Adc,
    Sbc,
    Umulh,
    Smulh,
    Madd,
    Brk,
    TrapOverflow,
    TrapBoundsCheck,
    TrapBoundsCheckExact,
    TrapNull,
    TrapNullIfZero,
    TrapDivZero,
    TrapDivZeroIfZero,
    TrapShiftRange,
    TrapShiftRangeIfOOB,
    Retain,
    Release,
    MOVWrr,
    MOVXrr,
    STRWui,
    STRXui,
    STRSui,
    STRDui,
    BL,
    BLR,
    CMPWrr,
    CMPXrr,
    CMPWri,
    CMPXri,
    MOVZWi,
    MOVZXi,
    Bcc,
    Mrs,
    Phi,
    StackAlloc,
    Copy,
    Nop,
    NeonShlVImm,
    NeonUshrVImm,
    NeonSshrVImm,
    TrapOverflowExact,
    TailCall,
}

// ── opcode_latency (scheduler.rs:100-236, VERBATIM) ─────────────────────────
fn opcode_latency(opcode: AArch64Opcode) -> (u32, ExecutionPort) {
    use AArch64Opcode::*;
    match opcode {
        // Integer ALU: 1 cycle
        AddRR | AddRI | AddRIShift12 | SubRR | SubRI | Neg => (1, ExecutionPort::IntAlu),
        AndRR | AndRI | OrrRR | OrrRI | EorRR | EorRI | OrnRR | BicRR => (1, ExecutionPort::IntAlu),
        LslRR | LsrRR | AsrRR | LslRI | LsrRI | AsrRI | RorRI | Rbit => (1, ExecutionPort::IntAlu),
        CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri | Tst => (1, ExecutionPort::IntAlu),
        Csel | CSet | Csinc | Csinv | Csneg => (1, ExecutionPort::IntAlu),
        MovR | MovI | Movz | Movn | Movk | MOVWrr | MOVXrr | MOVZWi | MOVZXi => {
            (1, ExecutionPort::IntAlu)
        }
        Sxtw | Uxtw | Sxtb | Sxth | Uxtb | Uxth | Ubfm | Sbfm | Bfm => (1, ExecutionPort::IntAlu),
        Adrp | Adr | AddPCRel => (1, ExecutionPort::IntAlu),
        AddsRR | AddsRI | SubsRR | SubsRI => (1, ExecutionPort::IntAlu),
        // i128 multi-register: ADC/SBC are 1-cycle ALU, UMULH/MADD are 3-cycle multiply
        Adc | Sbc => (1, ExecutionPort::IntAlu),
        Umulh | Smulh | Madd => (3, ExecutionPort::IntMul),

        // Integer multiply: 3 cycles
        MulRR | Msub | Smull | Umull => (3, ExecutionPort::IntMul),

        // Integer divide: 10 cycles
        SDiv | UDiv => (10, ExecutionPort::IntDiv),

        // Loads: 4 cycles (L1 hit)
        LdrRI | LdrPreIndex | LdrPostIndex | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO
        | LdrbRO | LdrhRO | LdrswRO | LdrLiteral | LdpRI | LdpPostIndex | LdrGot | LdrTlvp => {
            (4, ExecutionPort::LoadStore)
        }

        // Stores: 1 cycle (non-blocking dispatch)
        StrRI | StrPreIndex | StrPostIndex | StrbRI | StrhRI | StrRO | StpRI | StpPreIndex
        | STRWui | STRXui | STRSui | STRDui => (1, ExecutionPort::LoadStore),

        // Stack allocation pseudo
        StackAlloc => (1, ExecutionPort::IntAlu),

        // Branches
        B | BCond | Bcc | Cbz | Cbnz | Tbz | Tbnz | Br => (1, ExecutionPort::Branch),

        // Calls / return
        Bl | Blr | BL | BLR | TailCall | Ret => (1, ExecutionPort::Branch),

        // Floating-point arithmetic: 3 cycles
        FaddRR | FsubRR | FmulRR | FdivRR | FnegRR | FabsRR | Fcmp => (3, ExecutionPort::FpAlu),
        // FMADD fused multiply-add: 4-cycle FP mul/FMA unit.
        FmaddRR => (4, ExecutionPort::FpAlu),
        FminnmRR | FmaxnmRR => (3, ExecutionPort::FpAlu),
        FrintmRR | FrintpRR | FrintzRR => (3, ExecutionPort::FpAlu),
        FsqrtRR => (12, ExecutionPort::FpAlu),
        FcvtzsRR | FcvtzuRR | ScvtfRR | UcvtfRR => (3, ExecutionPort::FpAlu),
        FcvtSD | FcvtDS | FcvtHS | FcvtHD | FcvtSH | FcvtDH => (3, ExecutionPort::FpAlu),
        FmovGprFpr | FmovFprGpr | FmovFprFpr | FmovImm => (1, ExecutionPort::FpAlu),

        // NEON SIMD: uses FP/NEON ALU units
        NeonAddV | NeonSubV => (2, ExecutionPort::FpAlu),
        NeonMulV => (3, ExecutionPort::FpAlu),
        NeonFaddV | NeonFsubV => (3, ExecutionPort::FpAlu),
        NeonFmulV => (4, ExecutionPort::FpAlu),
        // FP vector fused multiply-accumulate: 4-cycle FP mul/FMA unit (the
        // vector sibling of FmaddRR). Tied operand 0 (see has_tied_def_use)
        // gives the RAW edge to the accumulator's setter.
        NeonFmlaV | NeonFmlsV => (4, ExecutionPort::FpAlu),
        // Vector int->FP conversion: 3-cycle FP convert (like scalar UCVTF/SCVTF).
        NeonUcvtfV | NeonScvtfV => (3, ExecutionPort::FpAlu),
        // FP lane extract to a scalar D register (MOV Dd, Vn.D[lane]): SIMD
        // copy/permute latency.
        NeonDupScalarD => (3, ExecutionPort::FpAlu),
        NeonFdivV => (10, ExecutionPort::FpAlu),
        NeonAndV | NeonOrrV | NeonEorV | NeonBicV | NeonNotV | NeonRbitV | NeonRev32V
        | NeonRev64V => (1, ExecutionPort::FpAlu),
        NeonCmeqV | NeonCmgtV | NeonCmgeV | NeonCmhiV | NeonCmhsV | NeonFcmgtV => (2, ExecutionPort::FpAlu),
        NeonSmaxV | NeonSminV | NeonUmaxV | NeonUminV => (2, ExecutionPort::FpAlu),
        NeonUmaxv | NeonAddpScalar => (3, ExecutionPort::FpAlu),
        NeonDupElem | NeonDupGen | NeonMovi => (2, ExecutionPort::FpAlu),
        NeonInsGen | NeonUmovGen => (3, ExecutionPort::FpAlu),
        NeonShlVImm | NeonUshrVImm | NeonSshrVImm => (2, ExecutionPort::FpAlu),
        NeonCntV => (2, ExecutionPort::FpAlu),
        NeonUaddlpV => (3, ExecutionPort::FpAlu),
        NeonSaddlpV => (3, ExecutionPort::FpAlu),
        NeonAbsV => (2, ExecutionPort::FpAlu),
        // Unsigned dot-product accumulate (FEAT_DotProd): multiply-class SIMD
        // latency. The RAW edge on the tied operand 0 (see has_tied_def_use)
        // keeps it ordered after the accumulator's setter.
        NeonUdotV => (3, ExecutionPort::FpAlu),
        NeonBitV => (2, ExecutionPort::FpAlu),
        // Byte-wise extract/concatenate (EXT sliding window): permute-class
        // SIMD latency, plain 2-source def (no tied operand).
        NeonExtV => (2, ExecutionPort::FpAlu),
        NeonLd1Post => (4, ExecutionPort::LoadStore),
        NeonLdpQPost => (4, ExecutionPort::LoadStore),
        NeonSt1Post => (1, ExecutionPort::LoadStore),
        // STP Q-pair post-index: one store-unit op writing 32 bytes.
        NeonStpQPost => (1, ExecutionPort::LoadStore),

        // Trap pseudo-instructions: treated as branches
        Brk | TrapOverflow | TrapBoundsCheck | TrapBoundsCheckExact | TrapNull | TrapNullIfZero
        | TrapDivZero | TrapDivZeroIfZero | TrapShiftRange | TrapShiftRangeIfOOB
        | TrapOverflowExact => (1, ExecutionPort::Branch),

        // Reference counting: memory-like
        Retain | Release => (1, ExecutionPort::LoadStore),

        // Atomic loads: 4 cycles (like regular load + ordering)
        Ldar | Ldarb | Ldarh | Ldaxr => (4, ExecutionPort::LoadStore),

        // Atomic stores: 2 cycles (like regular store + ordering)
        Stlr | Stlrb | Stlrh | Stlxr => (2, ExecutionPort::LoadStore),

        // Atomic RMW (LSE): 6 cycles
        Ldadd | Ldadda | Ldaddal | Ldaddl | Ldclr | Ldclra | Ldclral | Ldclrl | Ldeor | Ldeora
        | Ldeoral | Ldeorl | Ldset | Ldseta | Ldsetal | Ldsetl | Ldsmax | Ldsmaxa | Ldsmaxal
        | Ldsmaxl | Ldsmin | Ldsmina | Ldsminal | Ldsminl | Ldumax | Ldumaxa | Ldumaxal
        | Ldumaxl | Ldumin | Ldumina | Lduminal | Lduminl | Swp | Swpa | Swpal | Swpl => {
            (6, ExecutionPort::LoadStore)
        }

        // Compare-and-swap: 8 cycles
        Cas | Casa | Casal | Casl => (8, ExecutionPort::LoadStore),

        // Barriers: 4-12 cycles
        Dmb => (4, ExecutionPort::LoadStore),
        Dsb => (8, ExecutionPort::LoadStore),
        Isb => (12, ExecutionPort::LoadStore),

        // System register read: modeled as 4-cycle ALU op. TPIDR_EL0 on
        // Apple Silicon (Firestorm/Icestorm) is effectively ~3-4 cycles; the
        // broader MRS family varies, but 4 is a safe, scheduler-friendly
        // default.
        Mrs => (4, ExecutionPort::IntAlu),

        // Pseudo-instructions
        Phi | Copy | Nop => (1, ExecutionPort::IntAlu),
    }
}

// ── is_proof_reorderable_ordinary_load (scheduler.rs:343-361; [B5] body) ─────
fn is_proof_reorderable_ordinary_load(opcode: AArch64Opcode, flags: InstFlags) -> bool {
    use AArch64Opcode::*;

    let disqualifying_flags =
        InstFlags::WRITES_MEMORY | InstFlags::HAS_SIDE_EFFECTS | InstFlags::IS_CALL;

    flags.contains(InstFlags::PROOF_REORDERABLE)
        && flags.intersection(disqualifying_flags).is_empty()
        && matches!(
            opcode,
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO | LdrswRO | LdrLiteral | LdpRI
        )
}

// ── is_proof_reorderable_ordinary_ldr_ri (scheduler.rs:363-376; [B5]+[F1]) ───
fn is_proof_reorderable_ordinary_ldr_ri(opcode: AArch64Opcode, flags: InstFlags) -> bool {
    let disqualifying_flags =
        InstFlags::WRITES_MEMORY | InstFlags::HAS_SIDE_EFFECTS | InstFlags::IS_CALL;

    flags.contains(InstFlags::PROOF_REORDERABLE)
        && flags.intersection(disqualifying_flags).is_empty()
        // [F1] production is `opcode == AArch64Opcode::LdrRI`; the frontend
        // rejects a fieldless-enum variant-constant as a scalar `==` operand
        // ("constant value not a single scalar"). For a fieldless enum
        // `x == V` is DEFINITIONALLY `matches!(x, V)` (derived Eq = same
        // discriminant) — RESULT-IDENTICAL; native oracle runs the real `==`.
        && matches!(opcode, AArch64Opcode::LdrRI)
}

// ── is_proof_reorderable_ordinary_str_ri (scheduler.rs:378-392; [B5]+[F1]) ───
fn is_proof_reorderable_ordinary_str_ri(opcode: AArch64Opcode, flags: InstFlags) -> bool {
    let disqualifying_flags = InstFlags::READS_MEMORY | InstFlags::IS_CALL | InstFlags::IS_PSEUDO;

    flags.contains(InstFlags::PROOF_REORDERABLE)
        && flags.contains(InstFlags::WRITES_MEMORY)
        && flags.intersection(disqualifying_flags).is_empty()
        // [F1] see is_proof_reorderable_ordinary_ldr_ri.
        && matches!(opcode, AArch64Opcode::StrRI)
}

// ── call_opcode_clobbers_registers (scheduler.rs:945-950, VERBATIM) ──────────
fn call_opcode_clobbers_registers(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Bl | AArch64Opcode::Blr | AArch64Opcode::BL | AArch64Opcode::BLR
    )
}

// ── [B1] tag plumbing ────────────────────────────────────────────────────────
fn opcode_from_index(idx: u32) -> AArch64Opcode {
    use AArch64Opcode::*;
    match idx {
        0 => AddRR,
        1 => AddRI,
        2 => AddRIShift12,
        3 => SubRR,
        4 => SubRI,
        5 => MulRR,
        6 => Msub,
        7 => Smull,
        8 => Umull,
        9 => SDiv,
        10 => UDiv,
        11 => Neg,
        12 => AndRR,
        13 => AndRI,
        14 => OrrRR,
        15 => OrrRI,
        16 => EorRR,
        17 => EorRI,
        18 => OrnRR,
        19 => BicRR,
        20 => LslRR,
        21 => LsrRR,
        22 => AsrRR,
        23 => LslRI,
        24 => LsrRI,
        25 => AsrRI,
        26 => RorRI,
        27 => Rbit,
        28 => CmpRR,
        29 => CmpRI,
        30 => Tst,
        31 => Csel,
        32 => Csinc,
        33 => Csinv,
        34 => Csneg,
        35 => MovR,
        36 => MovI,
        37 => Movz,
        38 => Movn,
        39 => Movk,
        40 => FmovImm,
        41 => LdrRI,
        42 => StrRI,
        43 => LdrPreIndex,
        44 => StrPreIndex,
        45 => LdrPostIndex,
        46 => StrPostIndex,
        47 => LdrbRI,
        48 => LdrhRI,
        49 => LdrsbRI,
        50 => LdrshRI,
        51 => StrbRI,
        52 => StrhRI,
        53 => LdrLiteral,
        54 => LdpRI,
        55 => StpRI,
        56 => StpPreIndex,
        57 => LdpPostIndex,
        58 => LdrRO,
        59 => StrRO,
        60 => LdrbRO,
        61 => LdrhRO,
        62 => LdrGot,
        63 => LdrTlvp,
        64 => B,
        65 => BCond,
        66 => Cbz,
        67 => Cbnz,
        68 => Tbz,
        69 => Tbnz,
        70 => Br,
        71 => Bl,
        72 => Blr,
        73 => Ret,
        74 => CSet,
        75 => Sxtw,
        76 => Uxtw,
        77 => Sxtb,
        78 => Sxth,
        79 => Uxtb,
        80 => Uxth,
        81 => Ubfm,
        82 => Sbfm,
        83 => Bfm,
        84 => FaddRR,
        85 => FsubRR,
        86 => FmulRR,
        87 => FdivRR,
        88 => FmaddRR,
        89 => FminnmRR,
        90 => FmaxnmRR,
        91 => FnegRR,
        92 => FabsRR,
        93 => FsqrtRR,
        94 => FrintmRR,
        95 => FrintpRR,
        96 => FrintzRR,
        97 => Fcmp,
        98 => FcvtzsRR,
        99 => FcvtzuRR,
        100 => ScvtfRR,
        101 => UcvtfRR,
        102 => FcvtSD,
        103 => FcvtDS,
        104 => FcvtHS,
        105 => FcvtHD,
        106 => FcvtSH,
        107 => FcvtDH,
        108 => FmovGprFpr,
        109 => FmovFprGpr,
        110 => FmovFprFpr,
        111 => NeonAddV,
        112 => NeonSubV,
        113 => NeonMulV,
        114 => NeonSmaxV,
        115 => NeonSminV,
        116 => NeonUmaxV,
        117 => NeonUminV,
        118 => NeonFaddV,
        119 => NeonFsubV,
        120 => NeonFmulV,
        121 => NeonFdivV,
        122 => NeonFcmgtV,
        123 => NeonAndV,
        124 => NeonOrrV,
        125 => NeonEorV,
        126 => NeonBicV,
        127 => NeonNotV,
        128 => NeonRbitV,
        129 => NeonRev32V,
        130 => NeonRev64V,
        131 => NeonCmeqV,
        132 => NeonCmgtV,
        133 => NeonCmgeV,
        134 => NeonCmhiV,
        135 => NeonCmhsV,
        136 => NeonUmaxv,
        137 => NeonAddpScalar,
        138 => NeonDupElem,
        139 => NeonDupGen,
        140 => NeonInsGen,
        141 => NeonUmovGen,
        142 => NeonMovi,
        143 => NeonLd1Post,
        144 => NeonLdpQPost,
        145 => NeonSt1Post,
        146 => NeonStpQPost,
        147 => NeonCntV,
        148 => NeonUaddlpV,
        149 => NeonSaddlpV,
        150 => NeonAbsV,
        151 => NeonBitV,
        152 => NeonUdotV,
        153 => NeonExtV,
        154 => NeonFmlaV,
        155 => NeonFmlsV,
        156 => NeonUcvtfV,
        157 => NeonScvtfV,
        158 => NeonDupScalarD,
        159 => Ldar,
        160 => Ldarb,
        161 => Ldarh,
        162 => Stlr,
        163 => Stlrb,
        164 => Stlrh,
        165 => Ldadd,
        166 => Ldadda,
        167 => Ldaddal,
        168 => Ldaddl,
        169 => Ldclr,
        170 => Ldclra,
        171 => Ldclral,
        172 => Ldclrl,
        173 => Ldeor,
        174 => Ldeora,
        175 => Ldeoral,
        176 => Ldeorl,
        177 => Ldset,
        178 => Ldseta,
        179 => Ldsetal,
        180 => Ldsetl,
        181 => Ldsmax,
        182 => Ldsmaxa,
        183 => Ldsmaxal,
        184 => Ldsmaxl,
        185 => Ldsmin,
        186 => Ldsmina,
        187 => Ldsminal,
        188 => Ldsminl,
        189 => Ldumax,
        190 => Ldumaxa,
        191 => Ldumaxal,
        192 => Ldumaxl,
        193 => Ldumin,
        194 => Ldumina,
        195 => Lduminal,
        196 => Lduminl,
        197 => Swp,
        198 => Swpa,
        199 => Swpal,
        200 => Swpl,
        201 => Cas,
        202 => Casa,
        203 => Casal,
        204 => Casl,
        205 => Ldaxr,
        206 => Stlxr,
        207 => Dmb,
        208 => Dsb,
        209 => Isb,
        210 => Adrp,
        211 => Adr,
        212 => AddPCRel,
        213 => LdrswRO,
        214 => AddsRR,
        215 => AddsRI,
        216 => SubsRR,
        217 => SubsRI,
        218 => Adc,
        219 => Sbc,
        220 => Umulh,
        221 => Smulh,
        222 => Madd,
        223 => Brk,
        224 => TrapOverflow,
        225 => TrapBoundsCheck,
        226 => TrapBoundsCheckExact,
        227 => TrapNull,
        228 => TrapNullIfZero,
        229 => TrapDivZero,
        230 => TrapDivZeroIfZero,
        231 => TrapShiftRange,
        232 => TrapShiftRangeIfOOB,
        233 => Retain,
        234 => Release,
        235 => MOVWrr,
        236 => MOVXrr,
        237 => STRWui,
        238 => STRXui,
        239 => STRSui,
        240 => STRDui,
        241 => BL,
        242 => BLR,
        243 => CMPWrr,
        244 => CMPXrr,
        245 => CMPWri,
        246 => CMPXri,
        247 => MOVZWi,
        248 => MOVZXi,
        249 => Bcc,
        250 => Mrs,
        251 => Phi,
        252 => StackAlloc,
        253 => Copy,
        254 => Nop,
        255 => NeonShlVImm,
        256 => NeonUshrVImm,
        257 => NeonSshrVImm,
        258 => TrapOverflowExact,
        259 => TailCall,
        _ => Nop,
    }
}

fn port_tag(p: ExecutionPort) -> u32 {
    match p {
        ExecutionPort::IntAlu => 0,
        ExecutionPort::IntMul => 1,
        ExecutionPort::IntDiv => 2,
        ExecutionPort::LoadStore => 3,
        ExecutionPort::Branch => 4,
        ExecutionPort::FpAlu => 5,
    }
}

// ── out-POD + #[no_mangle] mono ROOT ─────────────────────────────────────────
#[repr(C)]
pub struct OpcodeOut {
    pub latency: u32,
    pub port_tag: u32,
    pub call_clobbers: u32,
    pub reorder_load: u32,
    pub reorder_ldr_ri: u32,
    pub reorder_str_ri: u32,
}

#[no_mangle]
pub fn opcode_root(idx: u32, flags_bits: u32, out: &mut OpcodeOut) {
    let op = opcode_from_index(idx);
    let (lat, port) = opcode_latency(op);
    out.latency = lat;
    out.port_tag = port_tag(port);
    out.call_clobbers = call_opcode_clobbers_registers(op) as u32;
    let flags = InstFlags::from_bits(flags_bits as u16);
    out.reorder_load = is_proof_reorderable_ordinary_load(op, flags) as u32;
    out.reorder_ldr_ri = is_proof_reorderable_ordinary_ldr_ri(op, flags) as u32;
    out.reorder_str_ri = is_proof_reorderable_ordinary_str_ri(op, flags) as u32;
}
