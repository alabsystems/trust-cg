// a64_interp_narrow_cmp.rs — the on-host AArch64 CORRECTNESS harness for the
// narrow (i8/i16) signed/unsigned compare + checked-overflow class [A64HARNESS-1].
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// This is the fail-CLOSED counterpart to `e2e_aarch64_narrow_signed_cmp.rs`,
// whose link-and-run body SILENTLY SKIPS on a non-aarch64 host. Here the emitted
// AArch64 `__text` is DECODED (`trust_cg_lift::disasm::aarch64::decode`) and
// INTERPRETED on this x86 box, and the result is asserted against TWO independent
// oracles:
//   1. the faithful `trust_ir::Interpreter` (fixed-width integer semantics), and
//   2. a hand-computed known-answer key (e.g. `i16(-1) < 0 == true`).
// A `teeth` test corrupts the emitted sign-extension (SBFM→UBFM) to reproduce the
// original U1 unsigned-compare miscompile and confirms the harness DETECTS it —
// proving the assertions cannot false-pass.

mod common;
use common::a64_interp::{A64Interp, extract_text, symbol_addrs};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_ir::{
    Block as B, CastOp, Constant, FuncTy, Function as F, ICmpOp, Inst, InstrNode, InterpretValue,
    Interpreter, Module as M, OverflowOp, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

// ---------------------------------------------------------------------------
// trust_ir module builders (single-function so __text entry is at offset 0)
// ---------------------------------------------------------------------------

const FN: &str = "_c";
// Mach-O prepends a leading underscore to the C-level symbol.
const SYM: &str = "__c";

/// `fn _c(a:i32,b:i32)->i32 { ((a as N) cmp (b as N)) as i32 }`
fn build_trunc_cmp(narrow: Ty, cmp: ICmpOp) -> M {
    let mut m = M::new("narrow_cmp");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), FN, ft, BlockId::new(0));
    f.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::ICmp {
                op: cmp,
                ty: narrow,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: ValueId::new(4),
                then_val: ValueId::new(5),
                else_val: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

/// `fn _c(a:i32,b:i32)->i32 { (a as N).overflowing_add(b as N).1 as i32 }`
fn build_add_ovf(narrow: Ty) -> M {
    let mut m = M::new("narrow_ovf");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), FN, ft, BlockId::new(0));
    f.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: narrow,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_results([ValueId::new(4), ValueId::new(5)]),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: ValueId::new(5),
                then_val: ValueId::new(6),
                else_val: ValueId::new(7),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(8)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

// ---------------------------------------------------------------------------
// oracle + harness plumbing
// ---------------------------------------------------------------------------

fn compile(m: &M, opt: OptLevel) -> Vec<u8> {
    // Explicit Darwin spec: the a64 interp harness parses Mach-O, and the
    // default target spec is host-OS-aware (ELF on a Linux host).
    // Cross-emission only; same pattern as a64_abi_probe.
    let c = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("parse aarch64-apple-darwin target spec"),
    );
    c.compile(m).expect("compile").object_code
}

/// The faithful `trust_ir::Interpreter` oracle: run `_c(a, b)` on the SAME
/// trust_ir module (no codegen involved), returning the i32 result.
fn oracle(m: &M, a: i32, b: i32) -> i32 {
    let args = [
        InterpretValue::int(Ty::I32, a as i128).unwrap(),
        InterpretValue::int(Ty::I32, b as i128).unwrap(),
    ];
    let out = Interpreter::with_module(m)
        .execute_func(FuncId::new(0), args)
        .expect("oracle executes");
    out.returns[0].as_int().expect("int result").as_signed() as i32
}

/// Decode + interpret the emitted AArch64 `_c(a, b)` on this host, returning i32.
fn a64(obj: &[u8], a: i32, b: i32) -> i32 {
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let n_value = *addrs.get(SYM).expect("_c symbol present");
    let entry = (n_value - text.addr) as usize;
    let mut interp = A64Interp::new(text.bytes);
    interp.set_x(0, a as u32 as u64);
    interp.set_x(1, b as u32 as u64);
    interp.run(entry).expect("interpret _c") as u32 as i32
}

/// One assertion: the AArch64 codegen output MUST equal the faithful oracle AND
/// the hand-computed key, at BOTH O0 and O2.
fn check(m: &M, a: i32, b: i32, key: i32) {
    let want = oracle(m, a, b);
    assert_eq!(
        want, key,
        "oracle disagrees with known-answer key for ({a:#x},{b:#x})"
    );
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile(m, opt);
        let got = a64(&obj, a, b);
        assert_eq!(
            got, key,
            "AArch64 codegen MISCOMPILE at {opt:?}: _c({a:#x},{b:#x}) = {got}, want {key}",
        );
    }
}

#[test]
fn i16_signed_compare_matches_oracle_and_key() {
    let slt = build_trunc_cmp(Ty::I16, ICmpOp::Slt);
    let sgt = build_trunc_cmp(Ty::I16, ICmpOp::Sgt);
    // low16(0xFFFF) = i16 -1 ; low16(0) = i16 0
    check(&slt, 0xFFFF, 0x0000, 1); // -1 <s 0  -> true   (THE key: i16(-1)<0)
    check(&slt, 0x0000, 0xFFFF, 0); //  0 <s -1 -> false
    check(&sgt, 0x0000, 0xFFFF, 1); //  0 >s -1 -> true
    check(&slt, 0x7FFF, 0x8000, 0); //  32767 <s -32768 -> false
    check(&sgt, 0x7FFF, 0x8000, 1); //  32767 >s -32768 -> true
}

#[test]
fn i8_signed_compare_matches_oracle_and_key() {
    let slt = build_trunc_cmp(Ty::I8, ICmpOp::Slt);
    // low8(0x12FF) = i8 -1 ; low8(0x3400) = i8 0 (upper junk must be ignored)
    check(&slt, 0x12FF, 0x3400, 1); // -1 <s 0 -> true
    check(&slt, 0x007F, 0x0080, 0); // 127 <s -128 -> false
}

#[test]
fn narrow_unsigned_compare_stays_correct() {
    let u16_ult = build_trunc_cmp(Ty::U16, ICmpOp::Ult);
    let u8_ult = build_trunc_cmp(Ty::U8, ICmpOp::Ult);
    check(&u16_ult, 0xFFFF, 0x0000, 0); // 65535 <u 0 -> false
    check(&u16_ult, 0x0000, 0xFFFF, 1); // 0 <u 65535 -> true
    check(&u8_ult, 0x00FF, 0x0000, 0); // 255 <u 0 -> false
}

#[test]
fn narrow_checked_overflow_matches_oracle() {
    let i8 = build_add_ovf(Ty::I8);
    let u8 = build_add_ovf(Ty::U8);
    let i16 = build_add_ovf(Ty::I16);
    check(&i8, 127, 1, 1); // i8 127+1 overflows
    check(&i8, 10, 20, 0); // no overflow
    check(&i8, -128, -1, 1); // i8 MIN + -1 overflows
    check(&u8, 200, 100, 1); // u8 200+100=300 wraps
    check(&u8, 100, 50, 0); // no overflow
    check(&i16, 32767, 1, 1); // i16 MAX+1 overflows
    check(&i16, 100, 200, 0); // no overflow
}

// ---------------------------------------------------------------------------
// TEETH: the harness must DETECT a known-bad codegen, not just confirm a good one
// ---------------------------------------------------------------------------

/// Corrupt the FIRST sign-extend (SBFM, opc=00) in the text into a zero-extend
/// (UBFM, opc=10) by setting bit 30. This reproduces the ORIGINAL U1 miscompile
/// (a signed compare performed on a zero-extended operand: i16 0xFFFF read as
/// +65535 instead of -1). The instruction is located by DECODING (robust to
/// register allocation), never by a fixed byte offset.
fn corrupt_first_sxt(text: &mut [u8]) -> bool {
    use trust_cg_lift::disasm::aarch64::{Instruction, decode};
    let mut i = 0;
    while i + 4 <= text.len() {
        let w = u32::from_le_bytes([text[i], text[i + 1], text[i + 2], text[i + 3]]);
        if let Ok(Instruction::BitfieldMove(b)) = decode(w)
            && b.opc == 0b00
        {
            // SBFM -> UBFM: set bit 30.
            let bad = w | (1u32 << 30);
            text[i..i + 4].copy_from_slice(&bad.to_le_bytes());
            return true;
        }
        i += 4;
    }
    false
}

#[test]
fn teeth_harness_detects_sxt_to_uxt_miscompile() {
    // A correct signed compare: i16(-1) <s 0 == 1.
    let slt = build_trunc_cmp(Ty::I16, ICmpOp::Slt);
    let obj = compile(&slt, OptLevel::O0);

    // (A) The pristine object matches the key — the harness passes a KNOWN-GOOD.
    assert_eq!(
        a64(&obj, 0xFFFF, 0x0000),
        1,
        "pristine codegen must be correct"
    );

    // (B) Corrupt the sign-extension and confirm the harness now sees the WRONG
    //     answer (0), i.e. it disagrees with the oracle. If the harness had no
    //     teeth (e.g. silently skipped the SBFM) this would still read 1.
    let mut text = extract_text(&obj).bytes;
    assert!(
        corrupt_first_sxt(&mut text),
        "expected an SBFM sign-extend in the emitted narrow-compare code"
    );
    let mut interp = A64Interp::new(text);
    interp.set_x(0, 0xFFFFu64);
    interp.set_x(1, 0x0000u64);
    let corrupted = interp.run(0).expect("corrupted body still decodes") as u32 as i32;

    assert_eq!(
        corrupted, 0,
        "the SBFM->UBFM corruption must flip i16(-1)<0 from 1 to 0"
    );
    assert_ne!(
        corrupted,
        oracle(&slt, 0xFFFF, 0x0000),
        "TEETH: the harness must detect the injected miscompile (got == oracle means no teeth)"
    );
}
