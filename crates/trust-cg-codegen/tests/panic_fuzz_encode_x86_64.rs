// trust-cg-codegen/tests/panic_fuzz_encode_x86_64.rs
// Property-based panic-fuzz harness for `X86Encoder::encode_instruction` (x86-64).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
//! Part of #473 (x86-64 encoder panic-fuzz) / Part of #445 (per-target
//! harness gap) / Lineage: #387 (proptest panic-fuzz), #447 (panic-fix
//! hardening), #450 (widen opcode coverage >= 80%).
//!
//! This is the x86-64 sibling of `panic_fuzz_encode.rs`.
//
// Reference: `designs/2026-04-18-crash-free-codegen-plan.md` §5 (proptest
// as primary defense) and §6 (per-crate harness).
//
// Contract under test: for *any* `(X86Opcode, X86InstOperands)` value,
// `X86Encoder::encode_instruction` must either return `Ok(usize)` or
// `Err(X86EncodeError)` — it must NEVER panic, abort, overflow (in
// debug), or trigger a slice-index panic. This is the empirical half of
// the Phase-1 boundary conversion: Phase 1 replaced in-function
// `unwrap()` / `unreachable!()` sites with typed `X86EncodeError`
// returns; this harness proves the replacement is exhaustive over
// random-but-valid and random-malformed inputs.
//
// Run:
//   cargo test -p trust-cg-codegen --test panic_fuzz_encode_x86_64
// Increase case count via env:
//   PROPTEST_CASES=100000 cargo test -p trust-cg-codegen --test panic_fuzz_encode_x86_64
//
// ---------------------------------------------------------------------------
// Coverage (#473 / #450)
// ---------------------------------------------------------------------------
//
// `opcode_strategy()` below enumerates **every** variant of `X86Opcode`
// (current as of 2026-05-04), giving 100% static opcode coverage. This
// closes the x86-64 sibling gap tracked under #445. The guardrail is now
// exhaustive: adding a new enum variant without updating the table below
// causes a compile error rather than silently passing a low coverage
// floor.
//
// `valid_operands_strategy()` below composes per-category "well-shaped"
// strategies (arithmetic, logical, shift, move, memory base + SIB +
// RIP-relative, compare/test, branch, SSE scalar + conversion, CMOV/SET,
// bit-manip, atomic, GPR↔XMM transfers, stack, pseudos, hardware NOP).
// These exercise the happy path for every dispatched arm in
// `encode_instruction`.

use std::panic;

use proptest::prelude::*;
use trust_cg_codegen::x86_64::encode::*;
use trust_cg_ir::x86_64_ops::*;
use trust_cg_ir::x86_64_regs::*;

// ---------------------------------------------------------------------------
// Opcode strategy — full enumeration of every `X86Opcode` variant.
// ---------------------------------------------------------------------------
//
// The list is intentionally exhaustive (#450/#473). The macro defines both
// the sampling table and an exhaustive `match`; a future `X86Opcode` enum
// addition must be added here before this test target can compile.
macro_rules! x86_opcode_table {
    ($($opcode:ident),+ $(,)?) => {
        const ALL_X86_OPCODES: &[X86Opcode] = &[$(X86Opcode::$opcode),+];

        fn assert_opcode_enum_variant_accounted_for(opcode: X86Opcode) {
            match opcode {
                $(X86Opcode::$opcode)|+ => {}
            }
        }
    };
}

x86_opcode_table! {
    AddRR, AddRI, AddRM, SubRR, SubRI, SubRM, AdcRR, SbbRR, ImulRR, ImulRRI, ImulRM, Idiv, Div, Mul, Neg, Inc, Dec,
    Cdq, Cqo,
    AndRR, AndRI, OrRR, OrRI, XorRR, XorRI, Not,
    ShlRR, ShlRI, ShrRR, ShrRI, SarRR, SarRI, RolRI,
    MovRR, MovRR32, MovRI, MovRM8, MovRM16, MovRM32, MovRM, MovMR8, MovMR16, MovMR32, MovMR,
    MovRM8Sib, MovMR8Sib,
    VolatileMovRM8, VolatileMovRM16, VolatileMovRM32, VolatileMovRM,
    VolatileMovMR8, VolatileMovMR16, VolatileMovMR32, VolatileMovMR,
    VolatileMovssRM, VolatileMovssMR, VolatileMovsdRM, VolatileMovsdMR,
    VolatileMovdquRM, VolatileMovdquMR, VolatileMovdqaRM, VolatileMovdqaMR,
    Movzx,
    MovzxW, MovsxB, MovsxW, Movsx, MovsxdRMSib, Lea, LeaSib, MovRMSib, MovMRSib, LeaRip, MovRipRel, MovRipRelTlv,
    CmpRR, CmpRI, CmpRI8, CmpRM, TestRR, TestRI, TestRM,
    Jmp, JmpR, Jcc, Call, CallR, CallM, Ret,
    Addsd, Subsd, Mulsd, Divsd, Sqrtsd, Andpd, MovsdRR, MovsdRM, MovsdMR, Ucomisd, MovdquRM,
    MovdquMR, MovsdRMSib, MovssRMSib,
    Addss, Subss, Mulss, Divss, Sqrtss, Andps, MovssRR, MovssRM, MovssMR, Ucomiss,
    MovssRipRel, MovsdRipRel,
    Addps, Subps, Mulps, Divps, Addpd, Subpd, Mulpd, Divpd,
    Cmovcc, Cmovcc32, Setcc,
    Cvtsi2sd, Cvtsd2si, Cvttsd2si, Cvtsi2ss, Cvtss2si, Cvttss2si, Cvtsd2ss, Cvtss2sd,
    Roundsd, Roundss,
    Minsd, Maxsd, Minss, Maxss, Cmpsd, Cmpss,
    Bsf, Bsr, Tzcnt, Lzcnt, Popcnt, BtRI, Bswap,
    Xchg, Cmpxchg, Cmpxchg8, Cmpxchg16, AtomicRmwCasLoop, AtomicRmwCasLoop8, AtomicRmwCasLoop16, Mfence,
    MovdToXmm, MovdFromXmm, MovqToXmm, MovqFromXmm,
    Pand, Pandn, Por, Pxor, Pcmpeqb, Pcmpeqw, Pcmpgtb, Pcmpgtw, Pcmpeqd, Pshufd, Pmovmskb, MovdqaRR, Pcmpgtd, MovdqaRM, MovdqaMR,
    Paddd, Psubd, Paddq, Psubq, Pmuludq, Pmullw, Pslld, Psrld, Psrad, Psllq, Psrlq, Paddb, Paddw, Psubb, Psubw, Punpcklbw, Punpckldq, Packuswb, Punpckhbw, Punpcklqdq, Psadbw, Pinsrd, Pextrd, V4I32MaskExtract,
    Pmulld, Pcmpeqq, Pcmpgtq, Ptest, Pblendvb, Pinsrq, Pextrq, V2I64MaskExtract,
    V16I8MaskExtract, V8I16MaskExtract,
    V128BoolSelect,
    Push, Pop,
    Phi, StackAlloc, Nop,
    NopMulti, Ud2,
    TrapBoundsCheckExact,
    TrapNullIfZeroExact,
    TrapDivZeroExact,
    TrapShiftRangeExact,
    ImulRMSib,
    MovRM32Sib,
    MovMR32Sib,
}

fn opcode_strategy() -> impl Strategy<Value = X86Opcode> {
    prop::sample::select(ALL_X86_OPCODES.to_vec())
}

// ---------------------------------------------------------------------------
// SSE2 packed opcode strategy — direct encoder surface, not X86Opcode.
// ---------------------------------------------------------------------------

macro_rules! x86_sse2_packed_opcode_table {
    ($($opcode:ident),+ $(,)?) => {
        const ALL_X86_SSE2_PACKED_OPCODES: &[X86Sse2PackedOpcode] =
            &[$(X86Sse2PackedOpcode::$opcode),+];

        fn assert_sse2_packed_opcode_accounted_for(opcode: X86Sse2PackedOpcode) {
            match opcode {
                $(X86Sse2PackedOpcode::$opcode)|+ => {}
            }
        }
    };
}

x86_sse2_packed_opcode_table! {
    Pand, Pandn, Por, Pxor, Pcmpeqb, Pcmpeqw, Pcmpgtb, Pcmpgtw, Pcmpeqd, Pshufd, Pmovmskb, MovdqaRR, Pcmpgtd, Paddd, Psubd,
    Paddq, Psubq, Paddb, Paddw, Psubb, Psubw, Pcmpeqq, Pcmpgtq, Punpcklbw, Punpckldq, Packuswb, Punpckhbw, Punpcklqdq,
    Pmuludq, Pslld, Psrld, Psrad, Psllq, Psrlq, Pmullw,
}

fn sse2_packed_opcode_strategy() -> impl Strategy<Value = X86Sse2PackedOpcode> {
    prop::sample::select(ALL_X86_SSE2_PACKED_OPCODES.to_vec())
}

// ---------------------------------------------------------------------------
// Operand strategy
// ---------------------------------------------------------------------------

fn x86_preg_strategy() -> impl Strategy<Value = X86PReg> {
    // Cover the full legitimate data-register range (0..=79) plus a
    // beyond-the-end zone (80..=255) so we also exercise "unknown" regs
    // that may slip through from a buggy regalloc and hit `hw_enc()`
    // fallback logic.
    (0u16..=255u16).prop_map(X86PReg::new)
}

/// Restricted GPR64 range (0..=15) — matches the canonical `RAX..R15`
/// encodings used by the well-shaped category strategies below.
fn gpr64_strategy() -> impl Strategy<Value = X86PReg> {
    (0u16..=15u16).prop_map(X86PReg::new)
}

/// Restricted GPR32 range (16..=31) — matches `EAX..R15D`. Used for
/// the MOVD transfer and MOVSXD categories.
fn gpr32_strategy() -> impl Strategy<Value = X86PReg> {
    (16u16..=31u16).prop_map(X86PReg::new)
}

/// Restricted GPR16 range (32..=47) — matches `AX..R15W`. Used for the
/// `MovzxW` / `MovsxW` happy-path shapes.
fn gpr16_strategy() -> impl Strategy<Value = X86PReg> {
    (32u16..=47u16).prop_map(X86PReg::new)
}

/// Restricted GPR8 range (48..=63) — matches `AL..R15B`. Used for
/// `Setcc`, `Movzx`, and `MovsxB`.
fn gpr8_strategy() -> impl Strategy<Value = X86PReg> {
    (48u16..=63u16).prop_map(X86PReg::new)
}

/// Restricted XMM range (64..=79) — matches `XMM0..XMM15`. Used for SSE
/// scalar, conversion, and GPR↔XMM transfer categories.
fn xmm_strategy() -> impl Strategy<Value = X86PReg> {
    (64u16..=79u16).prop_map(X86PReg::new)
}

/// SIB index register range — excludes encodings whose low 3 bits are 4
/// (`RSP` / `R12`), since x86 SIB uses that encoding for "no index".
fn sib_index_strategy() -> impl Strategy<Value = X86PReg> {
    prop_oneof![0u16..=3u16, 5u16..=11u16, 13u16..=15u16].prop_map(X86PReg::new)
}

fn x86_cond_code_strategy() -> impl Strategy<Value = X86CondCode> {
    use X86CondCode::*;
    prop_oneof![
        Just(O),
        Just(NO),
        Just(B),
        Just(AE),
        Just(E),
        Just(NE),
        Just(BE),
        Just(A),
        Just(S),
        Just(NS),
        Just(P),
        Just(NP),
        Just(L),
        Just(GE),
        Just(LE),
        Just(G),
    ]
}

fn operands_strategy() -> impl Strategy<Value = X86InstOperands> {
    (
        prop::option::of(x86_preg_strategy()),
        prop::option::of(x86_preg_strategy()),
        prop::option::of(x86_preg_strategy()),
        prop::option::of(x86_preg_strategy()),
        // Arbitrary scale intentionally exercises the encoder's
        // silent-fallback branch in `Sib::scaled`.
        any::<u8>(),
        any::<i64>(),
        any::<i64>(),
        prop::option::of(x86_cond_code_strategy()),
    )
        .prop_map(
            |(dst, src, base, index, scale, disp, imm, cc)| X86InstOperands {
                dst,
                src,
                base,
                index,
                scale,
                disp,
                imm,
                cc,
            },
        )
}

// ---------------------------------------------------------------------------
// Well-shaped operand strategy (happy path — per-category shape fns)
// ---------------------------------------------------------------------------
//
// Each category strategy yields `(X86Opcode, X86InstOperands)` with
// operand shapes that plausibly match the opcode. We keep each function
// flat (no shared state) so proptest's `Map` clone-bound is trivially
// met.
//
// The overall `valid_operands_strategy` composes them via
// `proptest::strategy::Union::new`.

type OpPair = (X86Opcode, X86InstOperands);
type Sse2PackedPair = (X86Sse2PackedOpcode, X86InstOperands);

fn strat_arith_rr() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![
            Just(AddRR),
            Just(SubRR),
            Just(AndRR),
            Just(OrRR),
            Just(XorRR),
            Just(CmpRR),
            Just(TestRR),
            Just(MovRR),
            Just(ImulRR),
        ],
        gpr64_strategy(),
        gpr64_strategy(),
    )
        .prop_map(|(op, dst, src)| (op, X86InstOperands::rr(dst, src)))
}

fn strat_arith_ri() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![
            Just(AddRI),
            Just(SubRI),
            Just(AndRI),
            Just(OrRI),
            Just(XorRI),
            Just(CmpRI),
            Just(TestRI),
        ],
        gpr64_strategy(),
        any::<i32>().prop_map(i64::from),
    )
        .prop_map(|(op, dst, imm)| (op, X86InstOperands::ri(dst, imm)))
}

fn strat_cmp_ri8() -> impl Strategy<Value = OpPair> {
    (gpr64_strategy(), any::<i8>().prop_map(i64::from))
        .prop_map(|(dst, imm)| (X86Opcode::CmpRI8, X86InstOperands::ri(dst, imm)))
}

fn strat_imul_rri() -> impl Strategy<Value = OpPair> {
    (
        gpr64_strategy(),
        gpr64_strategy(),
        any::<i32>().prop_map(i64::from),
    )
        .prop_map(|(dst, src, imm)| (X86Opcode::ImulRRI, X86InstOperands::rri(dst, src, imm)))
}

fn strat_mem_rm() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![
            Just(AddRM),
            Just(SubRM),
            Just(CmpRM),
            Just(TestRM),
            Just(ImulRM),
            Just(MovRM),
            Just(MovMR),
            Just(VolatileMovRM),
            Just(VolatileMovMR),
        ],
        gpr64_strategy(),
        gpr64_strategy(),
        any::<i64>(),
    )
        .prop_map(|(op, reg, base, disp)| (op, X86InstOperands::rm(reg, base, disp)))
}

fn strat_width_mem_mov() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (gpr8_strategy(), gpr64_strategy(), any::<i64>())
            .prop_map(|(reg, base, disp)| { (MovRM8, X86InstOperands::rm(reg, base, disp)) }),
        (gpr16_strategy(), gpr64_strategy(), any::<i64>())
            .prop_map(|(reg, base, disp)| { (MovRM16, X86InstOperands::rm(reg, base, disp)) }),
        (gpr32_strategy(), gpr64_strategy(), any::<i64>())
            .prop_map(|(reg, base, disp)| { (MovRM32, X86InstOperands::rm(reg, base, disp)) }),
        (gpr8_strategy(), gpr64_strategy(), any::<i64>())
            .prop_map(|(reg, base, disp)| { (MovMR8, X86InstOperands::rm(reg, base, disp)) }),
        (gpr16_strategy(), gpr64_strategy(), any::<i64>())
            .prop_map(|(reg, base, disp)| { (MovMR16, X86InstOperands::rm(reg, base, disp)) }),
        (gpr32_strategy(), gpr64_strategy(), any::<i64>())
            .prop_map(|(reg, base, disp)| { (MovMR32, X86InstOperands::rm(reg, base, disp)) }),
        (gpr8_strategy(), gpr64_strategy(), any::<i64>()).prop_map(|(reg, base, disp)| {
            (VolatileMovRM8, X86InstOperands::rm(reg, base, disp))
        }),
        (gpr16_strategy(), gpr64_strategy(), any::<i64>()).prop_map(|(reg, base, disp)| {
            (VolatileMovRM16, X86InstOperands::rm(reg, base, disp))
        }),
        (gpr32_strategy(), gpr64_strategy(), any::<i64>()).prop_map(|(reg, base, disp)| {
            (VolatileMovRM32, X86InstOperands::rm(reg, base, disp))
        }),
        (gpr8_strategy(), gpr64_strategy(), any::<i64>()).prop_map(|(reg, base, disp)| {
            (VolatileMovMR8, X86InstOperands::rm(reg, base, disp))
        }),
        (gpr16_strategy(), gpr64_strategy(), any::<i64>()).prop_map(|(reg, base, disp)| {
            (VolatileMovMR16, X86InstOperands::rm(reg, base, disp))
        }),
        (gpr32_strategy(), gpr64_strategy(), any::<i64>()).prop_map(|(reg, base, disp)| {
            (VolatileMovMR32, X86InstOperands::rm(reg, base, disp))
        }),
    ]
}

fn strat_mem_rm_sib() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![
            Just(MovRMSib),
            Just(MovsxdRMSib),
            Just(MovMRSib),
            Just(LeaSib)
        ],
        gpr64_strategy(),
        gpr64_strategy(),
        sib_index_strategy(),
        prop_oneof![Just(1u8), Just(2u8), Just(4u8), Just(8u8)],
        any::<i64>(),
    )
        .prop_map(|(op, reg, base, index, scale, disp)| {
            (op, X86InstOperands::rm_sib(reg, base, index, scale, disp))
        })
}

/// Scalar-FP scaled-index loads. Separate from [`strat_mem_rm_sib`] because the
/// destination is an XMM register, not a GPR.
fn strat_fp_rm_sib() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![Just(MovsdRMSib), Just(MovssRMSib)],
        xmm_strategy(),
        gpr64_strategy(),
        sib_index_strategy(),
        prop_oneof![Just(1u8), Just(2u8), Just(4u8), Just(8u8)],
        any::<i64>(),
    )
        .prop_map(|(op, reg, base, index, scale, disp)| {
            (op, X86InstOperands::rm_sib(reg, base, index, scale, disp))
        })
}

fn strat_rip_rel() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (gpr64_strategy(), any::<i64>())
            .prop_map(|(dst, disp)| { (LeaRip, X86InstOperands::rip_rel(dst, disp)) }),
        (gpr64_strategy(), any::<i64>())
            .prop_map(|(dst, disp)| { (MovRipRel, X86InstOperands::rip_rel(dst, disp)) }),
        (gpr64_strategy(), any::<i64>())
            .prop_map(|(dst, disp)| { (MovRipRelTlv, X86InstOperands::rip_rel(dst, disp)) }),
        (xmm_strategy(), any::<i64>())
            .prop_map(|(dst, disp)| { (MovssRipRel, X86InstOperands::rip_rel(dst, disp)) }),
        (xmm_strategy(), any::<i64>())
            .prop_map(|(dst, disp)| { (MovsdRipRel, X86InstOperands::rip_rel(dst, disp)) }),
    ]
}

fn strat_shift_rr() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![Just(ShlRR), Just(ShrRR), Just(SarRR)],
        gpr64_strategy(),
    )
        .prop_map(|(op, dst)| (op, X86InstOperands::r(dst)))
}

fn strat_shift_ri() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    // Shift-immediate: arbitrary `i64` is intentional. The encoder
    // truncates to `i8`; the only property under test here is "never
    // panic" under the full signed range.
    (
        prop_oneof![Just(ShlRI), Just(ShrRI), Just(SarRI)],
        gpr64_strategy(),
        any::<i64>(),
    )
        .prop_map(|(op, dst, imm)| (op, X86InstOperands::ri(dst, imm)))
}

fn strat_mov_r() -> impl Strategy<Value = OpPair> {
    // x86-64 has no dedicated unary `MovR`; keep the sibling harness
    // category by using degenerate register-copy shapes.
    prop_oneof![
        gpr64_strategy().prop_map(|dst| (X86Opcode::MovRR, X86InstOperands::rr(dst, dst))),
        gpr32_strategy().prop_map(|dst| (X86Opcode::MovRR32, X86InstOperands::rr(dst, dst))),
    ]
}

fn strat_mov_ri() -> impl Strategy<Value = OpPair> {
    (gpr64_strategy(), any::<i64>())
        .prop_map(|(dst, imm)| (X86Opcode::MovRI, X86InstOperands::ri(dst, imm)))
}

fn strat_mov_ext() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (gpr64_strategy(), gpr8_strategy())
            .prop_map(|(dst, src)| { (Movzx, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), gpr16_strategy())
            .prop_map(|(dst, src)| { (MovzxW, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), gpr8_strategy())
            .prop_map(|(dst, src)| { (MovsxB, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), gpr16_strategy())
            .prop_map(|(dst, src)| { (MovsxW, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), gpr32_strategy())
            .prop_map(|(dst, src)| { (Movsx, X86InstOperands::rr(dst, src)) }),
    ]
}

fn strat_lea() -> impl Strategy<Value = OpPair> {
    (gpr64_strategy(), gpr64_strategy(), any::<i64>())
        .prop_map(|(dst, base, disp)| (X86Opcode::Lea, X86InstOperands::rm(dst, base, disp)))
}

fn strat_stack() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (prop_oneof![Just(Push), Just(Pop)], gpr64_strategy())
        .prop_map(|(op, reg)| (op, X86InstOperands::r(reg)))
}

fn strat_nullary() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        Just((Ret, X86InstOperands::none())),
        Just((Cdq, X86InstOperands::none())),
        Just((Cqo, X86InstOperands::none())),
        Just((Mfence, X86InstOperands::none())),
        Just((Ud2, X86InstOperands::none())),
    ]
}

fn strat_unary_r() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![Just(Neg), Just(Inc), Just(Dec), Just(Not), Just(Bswap)],
        gpr64_strategy(),
    )
        .prop_map(|(op, reg)| (op, X86InstOperands::r(reg)))
}

fn strat_div() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![Just(Div), Just(Idiv), Just(Mul)],
        gpr64_strategy(),
    )
        .prop_map(|(op, reg)| (op, X86InstOperands::r(reg)))
}

fn strat_bitmanip() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![Just(Bsf), Just(Bsr), Just(Tzcnt), Just(Lzcnt), Just(Popcnt)],
        gpr64_strategy(),
        gpr64_strategy(),
    )
        .prop_map(|(op, dst, src)| (op, X86InstOperands::rr(dst, src)))
}

fn strat_bt_ri() -> impl Strategy<Value = OpPair> {
    (gpr64_strategy(), any::<i8>().prop_map(i64::from))
        .prop_map(|(dst, imm)| (X86Opcode::BtRI, X86InstOperands::ri(dst, imm)))
}

fn strat_jmp() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![Just(Jmp), Just(Call)],
        any::<i32>().prop_map(i64::from),
    )
        .prop_map(|(op, disp)| (op, X86InstOperands::rel(disp)))
}

fn strat_jcc() -> impl Strategy<Value = OpPair> {
    (x86_cond_code_strategy(), any::<i32>().prop_map(i64::from))
        .prop_map(|(cc, disp)| (X86Opcode::Jcc, X86InstOperands::jcc(cc, disp)))
}

fn strat_call_indirect() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (prop_oneof![Just(CallR), Just(JmpR)], gpr64_strategy())
            .prop_map(|(op, reg)| (op, X86InstOperands::r(reg))),
        (gpr64_strategy(), any::<i64>()).prop_map(|(base, disp)| {
            (
                CallM,
                X86InstOperands {
                    base: Some(base),
                    disp,
                    ..X86InstOperands::none()
                },
            )
        }),
    ]
}

fn strat_cmovcc() -> impl Strategy<Value = OpPair> {
    (x86_cond_code_strategy(), gpr64_strategy(), gpr64_strategy()).prop_map(|(cc, dst, src)| {
        (
            X86Opcode::Cmovcc,
            X86InstOperands {
                dst: Some(dst),
                src: Some(src),
                cc: Some(cc),
                ..X86InstOperands::none()
            },
        )
    })
}

fn strat_cmovcc32() -> impl Strategy<Value = OpPair> {
    (x86_cond_code_strategy(), gpr32_strategy(), gpr32_strategy()).prop_map(|(cc, dst, src)| {
        (
            X86Opcode::Cmovcc32,
            X86InstOperands {
                dst: Some(dst),
                src: Some(src),
                cc: Some(cc),
                ..X86InstOperands::none()
            },
        )
    })
}

fn strat_setcc() -> impl Strategy<Value = OpPair> {
    (x86_cond_code_strategy(), gpr8_strategy()).prop_map(|(cc, dst)| {
        (
            X86Opcode::Setcc,
            X86InstOperands {
                dst: Some(dst),
                cc: Some(cc),
                ..X86InstOperands::none()
            },
        )
    })
}

fn strat_sse_rr() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![
            Just(Addsd),
            Just(Subsd),
            Just(Mulsd),
            Just(Divsd),
            Just(Sqrtsd),
            Just(Andpd),
            Just(MovsdRR),
            Just(Ucomisd),
            Just(Addss),
            Just(Subss),
            Just(Mulss),
            Just(Divss),
            Just(Sqrtss),
            Just(Andps),
            Just(MovssRR),
            Just(Ucomiss),
            // SSE/SSE2 packed floating-point arithmetic (XMM reg-reg).
            Just(Addps),
            Just(Subps),
            Just(Mulps),
            Just(Divps),
            Just(Addpd),
            Just(Subpd),
            Just(Mulpd),
            Just(Divpd),
        ],
        xmm_strategy(),
        xmm_strategy(),
    )
        .prop_map(|(op, dst, src)| (op, X86InstOperands::rr(dst, src)))
}

fn strat_sse_mem() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    (
        prop_oneof![
            Just(MovsdRM),
            Just(MovsdMR),
            Just(MovssRM),
            Just(MovssMR),
            Just(MovdqaRM),
            Just(MovdqaMR),
            Just(VolatileMovssRM),
            Just(VolatileMovssMR),
            Just(VolatileMovsdRM),
            Just(VolatileMovsdMR),
            Just(VolatileMovdquRM),
            Just(VolatileMovdquMR),
            Just(VolatileMovdqaRM),
            Just(VolatileMovdqaMR),
        ],
        xmm_strategy(),
        gpr64_strategy(),
        any::<i32>(),
    )
        .prop_map(|(op, reg, base, disp)| (op, X86InstOperands::rm(reg, base, i64::from(disp))))
}

fn strat_cvt() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (xmm_strategy(), gpr64_strategy())
            .prop_map(|(dst, src)| { (Cvtsi2sd, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| { (Cvtsd2si, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| { (Cvttsd2si, X86InstOperands::rr(dst, src)) }),
        (xmm_strategy(), gpr64_strategy())
            .prop_map(|(dst, src)| { (Cvtsi2ss, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| { (Cvtss2si, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| { (Cvttss2si, X86InstOperands::rr(dst, src)) }),
        (xmm_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| { (Cvtsd2ss, X86InstOperands::rr(dst, src)) }),
        (xmm_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| { (Cvtss2sd, X86InstOperands::rr(dst, src)) }),
    ]
}

fn strat_gpr_xmm() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (xmm_strategy(), gpr32_strategy())
            .prop_map(|(dst, src)| { (MovdToXmm, X86InstOperands::rr(dst, src)) }),
        (gpr32_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| { (MovdFromXmm, X86InstOperands::rr(dst, src)) }),
        (xmm_strategy(), gpr64_strategy())
            .prop_map(|(dst, src)| { (MovqToXmm, X86InstOperands::rr(dst, src)) }),
        (gpr64_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| { (MovqFromXmm, X86InstOperands::rr(dst, src)) }),
    ]
}

fn strat_sse2_packed() -> impl Strategy<Value = Sse2PackedPair> {
    use X86Sse2PackedOpcode::*;
    prop_oneof![
        (
            prop_oneof![
                Just(Pand),
                Just(Pandn),
                Just(Por),
                Just(Pxor),
                Just(Pcmpeqb),
                Just(Pcmpeqw),
                Just(Pcmpgtb),
                Just(Pcmpgtw),
                Just(Pcmpeqd),
                Just(MovdqaRR),
                Just(Pcmpgtd),
                Just(Paddb),
                Just(Paddw),
                Just(Paddd),
                Just(Psubb),
                Just(Psubw),
                Just(Psubd),
                Just(Paddq),
                Just(Psubq),
                Just(Pmullw),
                Just(Pcmpeqq),
                Just(Pcmpgtq),
            ],
            xmm_strategy(),
            xmm_strategy(),
        )
            .prop_map(|(op, dst, src)| (op, X86InstOperands::rr(dst, src))),
        (
            prop_oneof![
                Just(Pand),
                Just(Pandn),
                Just(Por),
                Just(Pxor),
                Just(Pcmpeqb),
                Just(Pcmpeqw),
                Just(Pcmpgtb),
                Just(Pcmpgtw),
                Just(Pcmpeqd),
                Just(Pcmpgtd),
                Just(Paddb),
                Just(Paddw),
                Just(Paddd),
                Just(Psubb),
                Just(Psubw),
                Just(Psubd),
                Just(Paddq),
                Just(Psubq),
                Just(Pmullw),
                Just(Pmuludq),
                Just(Punpckldq),
                Just(Punpcklqdq),
            ],
            xmm_strategy(),
            gpr64_strategy(),
            any::<i32>(),
        )
            .prop_map(|(op, dst, base, disp)| {
                (op, X86InstOperands::rm(dst, base, i64::from(disp)))
            }),
        (xmm_strategy(), xmm_strategy(), any::<u8>()).prop_map(|(dst, src, imm)| {
            (Pshufd, X86InstOperands::rri(dst, src, i64::from(imm)))
        }),
        (xmm_strategy(), gpr64_strategy(), any::<i32>(), any::<u8>()).prop_map(
            |(dst, base, disp, imm)| {
                let mut ops = X86InstOperands::rm(dst, base, i64::from(disp));
                ops.imm = i64::from(imm);
                (Pshufd, ops)
            },
        ),
        (
            prop_oneof![Just(Pslld), Just(Psrld), Just(Psrad)],
            xmm_strategy(),
            any::<u8>(),
        )
            .prop_map(|(op, dst, imm)| (op, X86InstOperands::ri(dst, i64::from(imm)))),
        (gpr32_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| (Pmovmskb, X86InstOperands::rr(dst, src))),
    ]
}

fn strat_x86_sse2_packed() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (
            prop_oneof![
                Just(Pand),
                Just(Pandn),
                Just(Por),
                Just(Pxor),
                Just(Pcmpeqb),
                Just(Pcmpeqw),
                Just(Pcmpgtb),
                Just(Pcmpgtw),
                Just(Pcmpeqd),
                Just(MovdqaRR),
                Just(Pcmpgtd),
                Just(Paddb),
                Just(Paddw),
                Just(Paddd),
                Just(Psubb),
                Just(Psubw),
                Just(Psubd),
                Just(Paddq),
                Just(Psubq),
                Just(Pmullw),
                Just(Pmuludq),
                Just(Punpckldq),
                Just(Punpcklqdq),
                Just(Pmulld),
                Just(Pcmpeqq),
                Just(Pcmpgtq),
                Just(Ptest),
                Just(Pblendvb),
            ],
            xmm_strategy(),
            xmm_strategy(),
        )
            .prop_map(|(op, dst, src)| (op, X86InstOperands::rr(dst, src))),
        (
            prop_oneof![
                Just(Pand),
                Just(Pandn),
                Just(Por),
                Just(Pxor),
                Just(Pcmpeqb),
                Just(Pcmpeqw),
                Just(Pcmpgtb),
                Just(Pcmpgtw),
                Just(Pcmpeqd),
                Just(Pcmpgtd),
                Just(Paddb),
                Just(Paddw),
                Just(Paddd),
                Just(Psubb),
                Just(Psubw),
                Just(Psubd),
                Just(Paddq),
                Just(Psubq),
                Just(Pmullw),
                Just(Pmuludq),
                Just(Punpckldq),
                Just(Punpcklqdq),
            ],
            xmm_strategy(),
            gpr64_strategy(),
            any::<i32>(),
        )
            .prop_map(|(op, dst, base, disp)| {
                (op, X86InstOperands::rm(dst, base, i64::from(disp)))
            }),
        (xmm_strategy(), gpr64_strategy(), any::<i32>()).prop_map(|(dst, base, disp)| {
            (Ptest, X86InstOperands::rm(dst, base, i64::from(disp)))
        }),
        (xmm_strategy(), xmm_strategy(), any::<u8>()).prop_map(|(dst, src, imm)| {
            (Pshufd, X86InstOperands::rri(dst, src, i64::from(imm)))
        }),
        (xmm_strategy(), gpr64_strategy(), any::<i32>(), any::<u8>()).prop_map(
            |(dst, base, disp, imm)| {
                let mut ops = X86InstOperands::rm(dst, base, i64::from(disp));
                ops.imm = i64::from(imm);
                (Pshufd, ops)
            },
        ),
        (
            prop_oneof![Just(Pslld), Just(Psrld), Just(Psrad)],
            xmm_strategy(),
            any::<u8>(),
        )
            .prop_map(|(op, dst, imm)| (op, X86InstOperands::ri(dst, i64::from(imm)))),
        (gpr32_strategy(), xmm_strategy())
            .prop_map(|(dst, src)| (Pmovmskb, X86InstOperands::rr(dst, src))),
    ]
}

fn strat_sse41_lane() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (xmm_strategy(), gpr32_strategy(), 0i64..=3i64)
            .prop_map(|(dst, src, lane)| (Pinsrd, X86InstOperands::rri(dst, src, lane))),
        (gpr32_strategy(), xmm_strategy(), 0i64..=3i64)
            .prop_map(|(dst, src, lane)| (Pextrd, X86InstOperands::rri(dst, src, lane))),
        (xmm_strategy(), gpr64_strategy(), 0i64..=1i64)
            .prop_map(|(dst, src, lane)| (Pinsrq, X86InstOperands::rri(dst, src, lane))),
        (gpr64_strategy(), xmm_strategy(), 0i64..=1i64)
            .prop_map(|(dst, src, lane)| (Pextrq, X86InstOperands::rri(dst, src, lane))),
    ]
}

fn strat_atomic() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    prop_oneof![
        (
            prop_oneof![Just(Xchg), Just(Cmpxchg)],
            gpr64_strategy(),
            gpr64_strategy(),
        )
            .prop_map(|(op, dst, src)| (op, X86InstOperands::rr(dst, src))),
        (
            prop_oneof![Just(Cmpxchg8), Just(Cmpxchg16)],
            gpr64_strategy(),
            gpr64_strategy(),
            any::<i64>(),
        )
            .prop_map(|(op, src, base, disp)| (op, X86InstOperands::rm(src, base, disp))),
        (0i64..=4i64).prop_map(|kind| (
            AtomicRmwCasLoop,
            X86InstOperands {
                dst: Some(RCX),
                src: Some(RDX),
                base: Some(RBX),
                imm: kind,
                ..X86InstOperands::none()
            }
        )),
        (0i64..=5i64).prop_map(|kind| (
            AtomicRmwCasLoop8,
            X86InstOperands {
                dst: Some(RCX),
                src: Some(RDX),
                base: Some(RBX),
                imm: kind,
                ..X86InstOperands::none()
            }
        )),
        (0i64..=5i64).prop_map(|kind| (
            AtomicRmwCasLoop16,
            X86InstOperands {
                dst: Some(RCX),
                src: Some(RDX),
                base: Some(RBX),
                imm: kind,
                ..X86InstOperands::none()
            }
        )),
    ]
}

fn strat_nop_multi() -> impl Strategy<Value = OpPair> {
    (1i64..=9i64).prop_map(|imm| {
        (
            X86Opcode::NopMulti,
            X86InstOperands {
                imm,
                ..X86InstOperands::none()
            },
        )
    })
}

fn strat_pseudos() -> impl Strategy<Value = OpPair> {
    use X86Opcode::*;
    // Pseudo opcodes that must cleanly return `Ok(0)` or `Err`, never
    // panic.
    prop_oneof![
        Just((Phi, X86InstOperands::none())),
        Just((StackAlloc, X86InstOperands::none())),
        Just((Nop, X86InstOperands::none())),
        Just((V4I32MaskExtract, X86InstOperands::rr(EAX, XMM0))),
        Just((V16I8MaskExtract, X86InstOperands::rr(EAX, XMM0))),
        Just((V8I16MaskExtract, X86InstOperands::rr(EAX, XMM0))),
        Just((V2I64MaskExtract, X86InstOperands::rr(EAX, XMM0))),
        Just((V128BoolSelect, X86InstOperands::rr(XMM0, XMM1))),
    ]
}

/// "Well-shaped" generator: produces an `(X86Opcode, X86InstOperands)`
/// pair with a field population that at least plausibly matches the
/// opcode. Exercises the happy path so any panic here is a definite P1
/// bug (the corresponding malformed-input path below catches latent
/// panics in error-handling code).
fn valid_operands_strategy() -> impl Strategy<Value = OpPair> {
    // Proptest requires uniform branch types for `Union::new`. Boxing
    // each per-category strategy to `BoxedStrategy<OpPair>` unifies them.
    let cats: Vec<BoxedStrategy<OpPair>> = vec![
        strat_arith_rr().boxed(),
        strat_arith_ri().boxed(),
        strat_cmp_ri8().boxed(),
        strat_imul_rri().boxed(),
        strat_mem_rm().boxed(),
        strat_width_mem_mov().boxed(),
        strat_mem_rm_sib().boxed(),
        strat_fp_rm_sib().boxed(),
        strat_rip_rel().boxed(),
        strat_shift_rr().boxed(),
        strat_shift_ri().boxed(),
        strat_mov_r().boxed(),
        strat_mov_ri().boxed(),
        strat_mov_ext().boxed(),
        strat_lea().boxed(),
        strat_stack().boxed(),
        strat_nullary().boxed(),
        strat_unary_r().boxed(),
        strat_div().boxed(),
        strat_bitmanip().boxed(),
        strat_bt_ri().boxed(),
        strat_jmp().boxed(),
        strat_jcc().boxed(),
        strat_call_indirect().boxed(),
        strat_cmovcc().boxed(),
        strat_cmovcc32().boxed(),
        strat_setcc().boxed(),
        strat_sse_rr().boxed(),
        strat_sse_mem().boxed(),
        strat_x86_sse2_packed().boxed(),
        strat_sse41_lane().boxed(),
        strat_cvt().boxed(),
        strat_gpr_xmm().boxed(),
        strat_atomic().boxed(),
        strat_nop_multi().boxed(),
        strat_pseudos().boxed(),
    ];
    proptest::strategy::Union::new(cats)
}

// ---------------------------------------------------------------------------
// Property
// ---------------------------------------------------------------------------

/// Run `encode_instruction` inside `catch_unwind` and assert no panic.
///
/// The returned `Result<usize, X86EncodeError>` is discarded; the *only*
/// failure mode tracked here is "panic reached the caller".
fn assert_no_panic(opcode: X86Opcode, ops: &X86InstOperands) {
    // Clone inputs into the closure so `catch_unwind`'s UnwindSafe bound
    // is trivially satisfied for these POD-ish types.
    let opcode_copy = opcode;
    let ops_copy = ops.clone();
    let result = panic::catch_unwind(panic::AssertUnwindSafe(move || {
        let mut enc = X86Encoder::new();
        let _ = enc.encode_instruction(opcode_copy, &ops_copy);
    }));
    if let Err(payload) = result {
        let msg = if let Some(s) = payload.downcast_ref::<&'static str>() {
            (*s).to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "<non-string panic payload>".to_string()
        };
        panic!(
            "encode_instruction panicked on input {:?}: {}",
            (opcode, ops),
            msg
        );
    }
}

fn assert_sse2_packed_no_panic(opcode: X86Sse2PackedOpcode, ops: &X86InstOperands) {
    let opcode_copy = opcode;
    let ops_copy = ops.clone();
    let result = panic::catch_unwind(panic::AssertUnwindSafe(move || {
        let mut enc = X86Encoder::new();
        let _ = enc.encode_sse2_packed_instruction(opcode_copy, &ops_copy);
    }));
    if let Err(payload) = result {
        let msg = if let Some(s) = payload.downcast_ref::<&'static str>() {
            (*s).to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "<non-string panic payload>".to_string()
        };
        panic!(
            "encode_sse2_packed_instruction panicked on input {:?}: {}",
            (opcode, ops),
            msg
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256),
        max_shrink_iters: 500,
        .. ProptestConfig::default()
    })]

    /// Random-but-plausible inputs — the happy path.
    #[test]
    fn encode_never_panics_on_valid((opcode, ops) in valid_operands_strategy()) {
        assert_no_panic(opcode, &ops);
    }

    /// Random-malformed inputs — arbitrary opcode paired with arbitrary
    /// operand shapes. This is the main totality property: the encoder
    /// should convert *any* malformed shape into `Err`, never a panic.
    #[test]
    fn encode_never_panics_on_malformed(
        opcode in opcode_strategy(),
        ops in operands_strategy(),
    ) {
        assert_no_panic(opcode, &ops);
    }

    #[test]
    fn encode_sse2_packed_never_panics_on_valid(
        (opcode, ops) in strat_sse2_packed(),
    ) {
        assert_sse2_packed_no_panic(opcode, &ops);
    }

    #[test]
    fn encode_sse2_packed_never_panics_on_malformed(
        opcode in sse2_packed_opcode_strategy(),
        ops in operands_strategy(),
    ) {
        assert_sse2_packed_no_panic(opcode, &ops);
    }
}

// ---------------------------------------------------------------------------
// Static coverage sanity check (#450 acceptance criterion)
// ---------------------------------------------------------------------------
//
// Guardrail test: if a future enum variant is added, the exhaustive match
// generated by `x86_opcode_table!` fails compilation until the single
// all-opcode table is updated. The runtime half checks the table itself is
// duplicate-free and still covers the current variant count.
#[test]
fn opcode_strategy_covers_all_variants() {
    use std::collections::HashSet;

    for &opcode in ALL_X86_OPCODES {
        assert_opcode_enum_variant_accounted_for(opcode);
    }

    let seen: HashSet<X86Opcode> = ALL_X86_OPCODES.iter().copied().collect();
    assert_eq!(
        seen.len(),
        ALL_X86_OPCODES.len(),
        "ALL_X86_OPCODES must not contain duplicate variants"
    );
    assert!(
        seen.len() >= 107,
        "ALL_X86_OPCODES only lists {} variants; expected at least the 107 variants present on 2026-04-25",
        seen.len()
    );
}

#[test]
fn sse2_packed_opcode_strategy_covers_all_variants() {
    use std::collections::HashSet;

    for &opcode in ALL_X86_SSE2_PACKED_OPCODES {
        assert_sse2_packed_opcode_accounted_for(opcode);
    }

    let seen: HashSet<X86Sse2PackedOpcode> = ALL_X86_SSE2_PACKED_OPCODES.iter().copied().collect();
    assert_eq!(
        seen.len(),
        ALL_X86_SSE2_PACKED_OPCODES.len(),
        "ALL_X86_SSE2_PACKED_OPCODES must not contain duplicate variants"
    );
    // The exhaustive `match` in `assert_sse2_packed_opcode_accounted_for`
    // already guarantees `ALL_X86_SSE2_PACKED_OPCODES` lists every enum variant
    // (a new variant breaks compilation until added here). This pins the
    // current surface size so silent over/under-counting is caught too: 29
    // original packed helpers plus the packed dword shifts (PSLLD/PSRLD/PSRAD)
    // and PMULLW added later = 33, plus the packed qword shifts (PSLLQ/PSRLQ,
    // the SSE2 vectorizer's 64-bit multiply compose) = 35.
    assert_eq!(
        seen.len(),
        35,
        "direct SSE2 packed opcode surface must cover packed helpers, MOVDQA RR, \
         the packed dword and qword shifts, and PMULLW"
    );
}

// ---------------------------------------------------------------------------
// Regression reproducers for known panics found by this harness
// ---------------------------------------------------------------------------
//
// These pin-down tests are hand-reduced shrinks of failing proptest cases.
// Each asserts the post-fix behavior (a typed `Err(X86EncodeError::..)`)
// rather than the original crash.

/// `NopMulti` with a large positive `imm` previously recursed via
/// `encode_multibyte_nop(size - 9)` without a bound, overflowing the stack
/// on the x86-64 encoder and aborting the process with SIGABRT. Surfaced
/// by the malformed-input proptest harness on 2026-04-20 under #473.
///
/// Fixed two ways: (1) `encode_multibyte_nop` converted to iteration so
/// stack depth is O(1) regardless of `size`; (2) dispatch site in
/// `encode_instruction` clamps `ops.imm` to `[1, 15]` and returns
/// `Err(X86EncodeError::InvalidOperands)` for anything outside that range.
#[test]
fn regression_nopmulti_large_imm_stack_overflow() {
    let mut enc = X86Encoder::new();
    let ops = X86InstOperands {
        imm: i64::MAX,
        ..X86InstOperands::none()
    };
    let err = enc
        .encode_instruction(X86Opcode::NopMulti, &ops)
        .expect_err("i64::MAX imm must be rejected, not recursed on");
    assert!(
        matches!(err, X86EncodeError::InvalidOperands(_)),
        "expected InvalidOperands on oversized NopMulti imm, got {err:?}"
    );
}

/// Negative `NopMulti` `imm` previously collapsed to the default size (3)
/// via `if ops.imm > 0 { ops.imm as usize } else { 3 }`. That branch is
/// still exercised deliberately as the happy-path fallback — this test
/// just pins the documented contract: a negative imm must NOT be treated
/// as a giant `usize` via wrap-around, and must emit a valid 3-byte NOP.
#[test]
fn regression_nopmulti_negative_imm_falls_back_to_default() {
    let mut enc = X86Encoder::new();
    let ops = X86InstOperands {
        imm: -1,
        ..X86InstOperands::none()
    };
    let n = enc
        .encode_instruction(X86Opcode::NopMulti, &ops)
        .expect("negative imm must fall back to default 3-byte NOP");
    assert_eq!(n, 3, "default NopMulti size must be 3 bytes");
    assert_eq!(enc.bytes, vec![0x0F, 0x1F, 0x00]);
}

/// `NopMulti` with size in the accepted alignment-padding range (1..=15)
/// must emit bit-identical output to the previous recursive implementation.
/// Sizes 10..=15 exercise the post-refactor iteration path.
#[test]
fn regression_nopmulti_alignment_range_emits_expected_bytes() {
    // Size 10: one 9-byte NOP followed by one 1-byte NOP.
    let mut enc10 = X86Encoder::new();
    let ops10 = X86InstOperands {
        imm: 10,
        ..X86InstOperands::none()
    };
    enc10
        .encode_instruction(X86Opcode::NopMulti, &ops10)
        .expect("size=10 must encode");
    assert_eq!(enc10.bytes.len(), 10, "size=10 must emit 10 bytes");
    assert_eq!(
        &enc10.bytes[0..9],
        &[0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00],
        "first 9 bytes must be the canonical 9-byte NOP"
    );
    assert_eq!(enc10.bytes[9], 0x90, "trailing byte must be 1-byte NOP");

    // Size 15: one 9-byte NOP followed by one 6-byte NOP.
    let mut enc15 = X86Encoder::new();
    let ops15 = X86InstOperands {
        imm: 15,
        ..X86InstOperands::none()
    };
    enc15
        .encode_instruction(X86Opcode::NopMulti, &ops15)
        .expect("size=15 must encode");
    assert_eq!(enc15.bytes.len(), 15, "size=15 must emit 15 bytes");
    assert_eq!(
        &enc15.bytes[0..9],
        &[0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00],
        "first 9 bytes must be the canonical 9-byte NOP"
    );
    assert_eq!(
        &enc15.bytes[9..15],
        &[0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00],
        "trailing 6 bytes must be the canonical 6-byte NOP"
    );

    // Size 16 (just out of range): rejected with typed error.
    let mut enc16 = X86Encoder::new();
    let ops16 = X86InstOperands {
        imm: 16,
        ..X86InstOperands::none()
    };
    let err = enc16
        .encode_instruction(X86Opcode::NopMulti, &ops16)
        .expect_err("size=16 must be rejected");
    assert!(
        matches!(err, X86EncodeError::InvalidOperands(_)),
        "size=16 must yield InvalidOperands, got {err:?}"
    );
}
