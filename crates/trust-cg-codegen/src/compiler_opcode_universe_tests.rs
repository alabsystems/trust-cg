//! Every x86-64 and every AArch64 opcode, for unit tests that pin a property
//! over the whole opcode universe (X-OPCODES-P13: which covered-elsewhere
//! certificates cite a per-compile decode check).
//!
//! trust-cg-verify's opcode-coverage gate enumerates both enums too, but no
//! crate outside trust-cg-verify may name that gate in its sources, unit tests
//! included: the gate's rows are not instruction credit, and the guard
//! `coverage_gate_is_not_consulted_by_any_promotion_crate` (E0.2) keeps every
//! promotion crate free of it. So this crate keeps its own lists.
//! Each list is declared once and matched exhaustively over the same names, so
//! a variant added to trust-cg-ir and missing here, or a name listed twice, is
//! a compile error in this crate's test build.

use trust_cg_ir::inst::AArch64Opcode;
use trust_cg_ir::x86_64_ops::X86Opcode;

macro_rules! opcode_universe {
    ($list:ident, $exhaustive:ident, $ty:ident { $($op:ident),+ $(,)? }) => {
        pub(super) const $list: &[$ty] = &[$($ty::$op),+];

        /// Compile-time completeness: a missing variant fails this match, and
        /// a repeated one is an unreachable pattern.
        #[allow(dead_code)]
        #[deny(unreachable_patterns)]
        fn $exhaustive(opcode: $ty) {
            match opcode {
                $($ty::$op)|+ => {}
            }
        }
    };
}

opcode_universe! {
    ALL_X86_OPCODES, x86_universe_is_exhaustive, X86Opcode {
        AddRR, AddRI, AddRM, SubRR, SubRI, SubRM, ImulRR, ImulRRI, ImulRM, Idiv, Div, Neg,
        Inc, Dec, Cdq, Cqo, AndRR, AndRI, OrRR, OrRI, XorRR, XorRI, Not, ShlRR, ShlRI,
        ShrRR, ShrRI, SarRR, SarRI, MovRR, MovRI, MovRM8, MovRM16, MovRM32, MovRM, MovMR8,
        MovMR16, MovMR32, MovMR, Movzx, MovzxW, MovsxB, MovsxW, Movsx, Lea, LeaSib,
        MovRMSib, MovMRSib, LeaRip, CmpRR, CmpRI, CmpRI8, CmpRM, TestRR, TestRI, TestRM,
        Jmp, Jcc, Call, CallR, CallM, Ret, Addsd, Subsd, Mulsd, Divsd, Sqrtsd, Andpd,
        MovsdRR, MovsdRM, MovsdMR, Ucomisd, MovdquRM, MovdquMR, Addss, Subss, Mulss, Divss,
        Sqrtss, Andps, MovssRR, MovssRM, MovssMR, Ucomiss, Roundsd, Roundss, Minsd, Maxsd,
        Minss, Maxss, Cmpsd, Cmpss, MovssRipRel, MovsdRipRel, Cmovcc, Setcc, Cvtsi2sd,
        Cvtsd2si, Cvtsi2ss, Cvtss2si, Cvtsd2ss, Cvtss2sd, Bsf, Bsr, Tzcnt, Lzcnt, Popcnt,
        BtRI, Bswap, Xchg, Cmpxchg, Mfence, MovdToXmm, MovdFromXmm, MovqToXmm, MovqFromXmm,
        Push, Pop, Phi, StackAlloc, Nop, NopMulti, MovRR32, MovRipRel, Cmovcc32, Mul, Ud2,
        Cvttsd2si, Cvttss2si, AtomicRmwCasLoop, AtomicRmwCasLoop8, AtomicRmwCasLoop16, Pand,
        Pandn, Por, Pxor, Pcmpeqd, Pshufd, Pmovmskb, MovdqaRR, Pcmpgtd, MovdqaRM, MovdqaMR,
        Paddd, Psubd, Punpckldq, Punpcklqdq, Paddq, Psubq, Paddb, Paddw, Psubb, Psubw,
        Pinsrd, Pextrd, V4I32MaskExtract, Pmulld, Pcmpeqq, Pcmpgtq, Ptest, Pinsrq, Pextrq,
        V2I64MaskExtract, Pblendvb, V128BoolSelect, Pmuludq, Pmullw, Pcmpeqb, Pcmpeqw,
        Pcmpgtb, Pcmpgtw, V16I8MaskExtract, V8I16MaskExtract, Pslld, Psrld, Psrad, AdcRR,
        SbbRR, Addps, Subps, Mulps, Divps, Addpd, Subpd, Mulpd, Divpd, Punpcklbw, Punpckhbw,
        Packuswb, TrapBoundsCheckExact, TrapNullIfZeroExact, TrapDivZeroExact,
        TrapShiftRangeExact, Psllq, Psrlq, JmpR, MovsxdRMSib, MovRipRelTlv, Cmpxchg8,
        Cmpxchg16, Psadbw, ImulRMSib, MovRM32Sib, MovMR32Sib, VolatileMovRM8,
        VolatileMovRM16, VolatileMovRM32, VolatileMovRM, VolatileMovMR8, VolatileMovMR16,
        VolatileMovMR32, VolatileMovMR, VolatileMovssRM, VolatileMovssMR, VolatileMovsdRM,
        VolatileMovsdMR, VolatileMovdquRM, VolatileMovdquMR, VolatileMovdqaRM,
        VolatileMovdqaMR, MovsdRMSib, MovssRMSib, RolRI, MovRM8Sib, MovMR8Sib, XorMR, AddMR,
        XorMRSib, AddMRSib, RolRCl, MovdquRMSib, MovdquMRSib, AtomicLoadCmpxchg16b,
        MovzxRM8, MovzxRM16, MovzxRM8Sib, VolatileMovzxRM8, VolatileMovzxRM16,
    }
}

opcode_universe! {
    ALL_AARCH64_OPCODES, aarch64_universe_is_exhaustive, AArch64Opcode {
        AddRR, AddRI, AddRIShift12, SubRR, SubRI, MulRR, Msub, Smull, Umull, SDiv, UDiv,
        Neg, AndRR, AndRI, OrrRR, OrrRI, EorRR, EorRI, EorRRShift, AddRRShift, SubRRShift,
        EorRRLsl, EorRRLsr, AddRRShiftLsr, OrnRR, BicRR, LslRR, LsrRR, AsrRR, LslRI, LsrRI,
        AsrRI, RorRI, Rbit, CmpRR, CmpRI, Tst, Csel, Csinc, Csinv, Csneg, FcselRR, MovR,
        MovI, Movz, Movn, Movk, FmovImm, LdrRI, StrRI, LdrPreIndex, StrPreIndex,
        LdrPostIndex, StrPostIndex, LdrbRI, LdrhRI, LdrsbRI, LdrshRI, StrbRI, StrhRI,
        LdrLiteral, LdpRI, StpRI, StpPreIndex, LdpPostIndex, LdrRO, StrRO, LdrbRO, LdrhRO,
        StrbRO, StrhRO, LdrGot, LdrTlvp, B, BCond, Cbz, Cbnz, Tbz, Tbnz, Br, Bl, Blr, Ret,
        CSet, Sxtw, Uxtw, Sxtb, Sxth, Uxtb, Uxth, Ubfm, Sbfm, Bfm, FaddRR, FsubRR, FmulRR,
        FdivRR, FmaddRR, FminnmRR, FmaxnmRR, FnegRR, FabsRR, FsqrtRR, FrintmRR, FrintpRR,
        FrintzRR, Fcmp, FcvtzsRR, FcvtzuRR, ScvtfRR, UcvtfRR, FcvtSD, FcvtDS, FcvtHS,
        FcvtHD, FcvtSH, FcvtDH, FmovGprFpr, FmovFprGpr, FmovFprFpr, NeonAddV, NeonSubV,
        NeonMulV, NeonSmaxV, NeonSminV, NeonUmaxV, NeonUminV, NeonFaddV, NeonFsubV,
        NeonFmulV, NeonFdivV, NeonFcmgtV, NeonAndV, NeonOrrV, NeonEorV, NeonBicV, NeonNotV,
        NeonRbitV, NeonRev32V, NeonRev64V, NeonCmeqV, NeonCmgtV, NeonCmgeV, NeonCmhiV,
        NeonCmhsV, NeonUmaxv, NeonAddpScalar, NeonDupElem, NeonDupGen, NeonInsGen,
        NeonUmovGen, NeonMovi, NeonLd1Post, NeonLdpQPost, NeonSt1Post, NeonStpQPost,
        NeonCntV, NeonUaddlpV, NeonSaddlpV, NeonAbsV, NeonBitV, NeonUdotV, NeonExtV,
        NeonSmlalV, NeonSmlal2V, NeonUmlalV, NeonUmlal2V, NeonUaddwV, NeonUaddw2V,
        NeonSaddwV, NeonSaddw2V, NeonMlaV, NeonUadalpV, NeonFmlaV, NeonFmlsV, NeonUcvtfV,
        NeonScvtfV, NeonFcvtlV, NeonFcvtl2V, NeonDupScalarD, Ldar, Ldarb, Ldarh, Stlr,
        Stlrb, Stlrh, Ldadd, Ldadda, Ldaddal, Ldaddl, Ldclr, Ldclra, Ldclral, Ldclrl, Ldeor,
        Ldeora, Ldeoral, Ldeorl, Ldset, Ldseta, Ldsetal, Ldsetl, Ldsmax, Ldsmaxa, Ldsmaxal,
        Ldsmaxl, Ldsmin, Ldsmina, Ldsminal, Ldsminl, Ldumax, Ldumaxa, Ldumaxal, Ldumaxl,
        Ldumin, Ldumina, Lduminal, Lduminl, Swp, Swpa, Swpal, Swpl, Cas, Casa, Casal, Casl,
        Ldaxr, Stlxr, Dmb, Dsb, Isb, Adrp, Adr, AddPCRel, AddTprelHi12, AddTprelLo12,
        LdrswRO, AddsRR, AddsRI, SubsRR, SubsRI, Adc, Sbc, Adcs, Sbcs, Umulh, Smulh, Madd,
        Brk, TrapOverflow, TrapBoundsCheck, TrapBoundsCheckExact, TrapNull, TrapNullIfZero,
        TrapDivZero, TrapDivZeroIfZero, TrapShiftRange, TrapShiftRangeIfOOB, Retain,
        Release, MOVWrr, MOVXrr, STRWui, STRXui, STRSui, STRDui, BL, BLR, CMPWrr, CMPXrr,
        CMPWri, CMPXri, MOVZWi, MOVZXi, Bcc, Mrs, Phi, StackAlloc, Copy, Nop, NeonShlVImm,
        NeonUshrVImm, NeonSshrVImm, TrapOverflowExact, TailCall, LdrGottprel, NeonFmlaLaneV,
        VolatileLdrRI, VolatileLdrbRI, VolatileLdrhRI, VolatileStrRI, VolatileStrbRI,
        VolatileStrhRI, AlignNop, TlsDescCall, LdrTlsdesc, AddTlsdescLo12, BlrTlsdesc, Ldxr,
        Ldxrb, Ldxrh, Ldaxrb, Ldaxrh, Stxr, Stxrb, Stxrh, Stlxrb, Stlxrh, Clrex, LlscRmw8,
        LlscRmw16, LlscRmw32, LlscRmw64, LlscCmpSwap8, LlscCmpSwap16, LlscCmpSwap32,
        LlscCmpSwap64, Ldxp, Ldaxp, Stxp, Stlxp, LlscLoad128, LlscStore128, LlscRmw128,
        LlscCmpSwap128, FrintnRR, Crc32B, Crc32H, Crc32W, Crc32X, Crc32Cb, Crc32Ch, Crc32Cw,
        Crc32Cx,
    }
}
