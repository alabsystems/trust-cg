//! TRUST-SELF ROUND 35 (thread R35): AUDIT THE BACKEND int->float CONVERSION
//! ROUNDING / SIGNEDNESS LOWERING (SCVTF/UCVTF) against the Rust `i as f64` /
//! `i as f32` oracle (IEEE round-to-nearest-even).
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! CONTEXT — the REVERSE of round 34
//! ═══════════════════════════════════════════════════════════════════════════════
//! R34 audited the backend f->int SATURATION lowering (FCVTZS/FCVTZU) and found the
//! full-width path clean. THIS round audits the OPPOSITE direction: int->float
//! ROUNDING (SCVTF/UCVTF on aarch64). Two things can go wrong in int->float:
//!   (1) ROUNDING: values that overflow the destination mantissa (f64: |i| > 2^53;
//!       f32: |i| > 2^24) must round to nearest, ties-to-even (RNE). A truncation
//!       or wrong tie-break is a bug.
//!   (2) SIGNEDNESS: a u64 with the high bit set (>= 2^63) via UIToFP must be the
//!       UNSIGNED value (u64::MAX ~ 1.8e19), NOT the signed interpretation (-1).
//!       If UIToFP lowered to a signed SCVTF, that is a real miscompile.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! THE ORACLE — Rust `i as f64` / `i as f32` (INDEPENDENT, computed at test time)
//! ═══════════════════════════════════════════════════════════════════════════════
//! Rust's `as` from an integer to a float is the correct IEEE-754 round-to-nearest-
//! even conversion (int->float never overflows to inf/NaN for the widths here, and
//! is never UB). This is a clean, independent oracle: native Rust, evaluated here at
//! test time. (interpret() is NOT used: interpreter.rs eval_cast is a 128-bit-wide
//! model and is not the target-width codegen we audit.)
//!
//! trust-ir CastOp semantics (inst.rs): `SIToFP` = signed int -> float; `UIToFP` =
//! unsigned int -> float — both round-to-nearest-even. The backend must implement
//! both faithfully at every source width.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! WHAT THE BACKEND ACTUALLY DOES (read from source; verified empirically below)
//! ═══════════════════════════════════════════════════════════════════════════════
//!  * SIToFP -> Opcode::FcvtFromInt -> select_fcvt_from_int -> ScvtfRR (isel.rs:9478).
//!    UIToFP -> Opcode::FcvtFromUint -> select_fcvt_from_uint -> UcvtfRR (isel.rs:9551).
//!    Signedness IS routed by opcode: SCVTF (signed) vs UCVTF (unsigned). GOOD.
//!  * The MACHINE ENCODER hardcodes `sf_64 = true` for BOTH ScvtfRR and UcvtfRR
//!    (encode.rs:2003 / :2031) -> the source integer register is ALWAYS read as the
//!    64-bit Xn form, regardless of the IR source width. The destination float
//!    precision (S/D) IS correctly derived from the FP dest register class
//!    (fp_size_from_source, operand 0). Rounding is hardware SCVTF/UCVTF = RNE
//!    (FPCR default), matching Rust `as`.
//!  * select_fcvt_from_int / _from_uint do NOT sign/zero-extend a NARROW source
//!    before the always-64-bit conversion (contrast extend_narrow_for_width_op,
//!    which the codebase applies for width-sensitive DIV/SHR consumers).
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! VERDICT MAP (this file machine-checks every cell native==JIT vs Rust `as`)
//! ═══════════════════════════════════════════════════════════════════════════════
//!  CLEAN (bit-exact vs Rust `as`):
//!    * (SIToFP, i64, {f64,f32})   — RNE rounding correct at 2^53±k / 2^24±k / i64::MAX/MIN.
//!    * (UIToFP, u64, {f64,f32})   — incl. the u64 HIGH-BIT signedness site: 2^63,
//!      u64::MAX etc. give the UNSIGNED value. UCVTF is genuinely unsigned. The
//!      highest-value bug site is CLEAN.
//!    * (UIToFP, {u8,u16,u32}, {f64,f32}) — narrow unsigned: the source is
//!      zero-extended in-register (Trunc/ABI) and UCVTF reads it unsigned -> correct.
//!      BUG #1 (NEW, pinned fail-loud in `narrow_signed_int_to_float_miscompile_pin`):
//!    * (SIToFP, {i8,i16,i32}, {f64,f32}) MISCOMPILES every NEGATIVE narrow value.
//!      The narrow source sits ZERO-extended in its register (Trunc -> UXTB/UXTH/
//!      MOV Wd,Wn; a 32-bit-op producer; or an i32 ABI param), and the always-sf=1
//!      SCVTF reads the full 64-bit Xn as SIGNED. So i32 -1 (0xFFFF_FFFF, zero-ext to
//!      0x0000_0000_FFFF_FFFF) is read as +4294967295 -> 4294967295.0 instead of
//!      -1.0. Witnessed via BOTH the canonical `(x as i32) as f64` Trunc pattern AND
//!      a direct i32 parameter. Not UB (every iN is in-range for f64). Fix: sign-
//!      extend narrow signed sources (SXTB/SXTH/SXTW -> Xd) before SCVTF, or honor
//!      the isel's already-intended `SCVTF Sd, Wn` (sf=0) form for i32 (the isel
//!      comment says Wn; the encoder overrides to Xn).
//!      BUG #2 (128-bit source class, owner-#3 family; pinned in `i128_to_float_low64_truncation_pin`):
//!    * (SIToFP/UIToFP, {i128,u128}, f64) LOWERS (does NOT fail-closed) but reads
//!      only the LOW 64 bits, dropping the high 64 -> miscompiles all |value| >= 2^64
//!      (e.g. (2^64+1) -> 1.0). A silent truncation, not a saturating conversion.
//!
//! No emit-from-Rust: the emit-closure frontend has NO float support (R31 Finding A —
//! `scalar_tir_ty` returns None for `ty::Float`). Everything here is hand-built
//! trust-ir driven through the trust-cg JIT; the oracle is native Rust `as`.
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine is
//! not thread-safe at suite scale (jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, CastOp, FuncId, ValueId};

// ── module builder ────────────────────────────────────────────────────────────────
//
// fn(param_ty) -> {f64|f32}:
//   if narrow_ty != param_ty: v1 = Trunc(param -> narrow_ty)   [Trunc zero-extends]
//   vr = Cast(SIToFP|UIToFP, src=narrow_ty, dst=f)             [the op under test]
//   return vr                                                  [float returned in d0/s0]
//
// The float BITS are read on the Rust side via f64::to_bits()/f32::to_bits().
fn build_conv(
    func_id: u32,
    name: &str,
    m: &mut TrustIrModule,
    param_ty: Ty,
    narrow_ty: Ty,
    signed: bool,
    dst_f32: bool,
) {
    let dst = if dst_f32 { Ty::F32 } else { Ty::F64 };
    let ft = m.add_func_type(FuncTy {
        params: vec![param_ty.clone()],
        returns: vec![dst.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));

    let mut body = vec![];
    let (src_val, src_ty) = if narrow_ty == param_ty {
        (ValueId::new(0), param_ty.clone())
    } else {
        body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: param_ty.clone(),
                dst_ty: narrow_ty.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
        );
        (ValueId::new(1), narrow_ty.clone())
    };
    body.push(
        InstrNode::new(Inst::Cast {
            op: if signed {
                CastOp::SIToFP
            } else {
                CastOp::UIToFP
            },
            src_ty,
            dst_ty: dst.clone(),
            operand: src_val,
        })
        .with_result(ValueId::new(2)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));

    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), param_ty)],
        body,
    }];
    m.add_function(f);
}

// ── JIT harness ─────────────────────────────────────────────────────────────────
fn jit_buffer(m: &TrustIrModule) -> trust_cg_codegen::jit::ExecutableBuffer {
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(m, &HashMap::new())
        .expect("hand-built int->float module must JIT-compile (backend supports SCVTF/UCVTF)")
        .buffer
}
fn bind(buf: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buf.get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

type F64FromI64 = unsafe extern "C" fn(i64) -> f64;
type F32FromI64 = unsafe extern "C" fn(i64) -> f32;
type F64FromU64 = unsafe extern "C" fn(u64) -> f64;
type F32FromU64 = unsafe extern "C" fn(u64) -> f32;

// ── boundary sweeps ───────────────────────────────────────────────────────────────

/// Signed i64 inputs crafted to hit exact / RNE-tie / round-up / round-even /
/// sign / i64::MAX / i64::MIN cases at BOTH the f64 (2^53) and f32 (2^24) mantissa
/// boundaries.
fn i64_inputs() -> Vec<i64> {
    let m53 = 1i64 << 53; // f64 mantissa boundary
    let m24 = 1i64 << 24; // f32 mantissa boundary
    vec![
        0,
        1,
        -1,
        2,
        -2,
        3,
        -3,
        5,
        -5,
        127,
        -128,
        255,
        -256,
        1000,
        -1000,
        (1 << 30),
        (1 << 31),
        (1 << 32),
        (1 << 52),
        (1 << 53),
        (1 << 62),
        // f64 RNE window at 2^53
        m53 - 1,
        m53 + 1,
        m53 + 2,
        m53 + 3,
        m53 + 5,
        m53 + 7,
        (m53 << 1) + 1,
        (m53 << 1) + 2,
        (m53 << 1) + 3,
        -(m53 + 1),
        -(m53 + 3),
        -((m53 << 1) + 3),
        // f32 RNE window at 2^24
        m24 - 1,
        m24 + 1,
        m24 + 2,
        m24 + 3,
        m24 + 5,
        (m24 << 1) + 1,
        (m24 << 1) + 3,
        -(m24 + 1),
        -(m24 + 3),
        // extremes / high-bit / alternating patterns
        i64::MAX,
        i64::MIN,
        i64::MAX - 1,
        i64::MIN + 1,
        0x7FFF_FFFF_FFFF_FFFF,
        -0x7FFF_FFFF_FFFF_FFFF,
        6148914691236517205, // 0x5555...5
        -6148914691236517205,
        0x0123_4567_89AB_CDEF,
    ]
}

/// Unsigned u64 inputs — the SIGNEDNESS bug site: everything with the high bit set
/// (>= 2^63) must convert as UNSIGNED, plus the f32/f64 RNE windows near 2^64/2^53.
fn u64_inputs() -> Vec<u64> {
    let m53 = 1u64 << 53;
    let m24 = 1u64 << 24;
    vec![
        0,
        1,
        2,
        3,
        5,
        127,
        255,
        1000,
        (1 << 52),
        (1 << 53),
        (1 << 62),
        (1 << 63),
        // ── HIGH-BIT-SET (the classic signed-vs-unsigned UCVTF bug site) ──
        0x8000_0000_0000_0000, // 2^63
        0x8000_0000_0000_0001,
        0x8000_0000_0000_0400,
        0xC000_0000_0000_0000, // 3*2^62
        0xFFFF_FFFF_FFFF_FFFF, // u64::MAX
        0xFFFF_FFFF_FFFF_F800, // largest u64 strictly < 2^64 exactly representable-ish
        0xFFFF_FFFF_FFFF_F801,
        0xFFFF_FFFF_FFFF_FC00,
        0xAAAA_AAAA_AAAA_AAAB, // high-bit-set alternating
        // f64 RNE window at 2^53
        m53 + 1,
        m53 + 2,
        m53 + 3,
        m53 + 5,
        // f32 RNE window at 2^24
        m24 + 1,
        m24 + 2,
        m24 + 3,
        m24 + 5,
        // near 2^64 (f32/f64 rounding of the top of the u64 range)
        0xFFFF_FF00_0000_0000,
        0xFFFF_FFFF_0000_0000,
    ]
}

// ============================================================================
// TEST 1 — 64-BIT CLEAN BILL (the crux).  SIToFP i64->{f64,f32} and
//   UIToFP u64->{f64,f32} must equal Rust `i as f64` / `i as f32` BIT-EXACT
//   across the full rounding + signedness sweep. Also asserts the RNE-rounding
//   cells and the u64-high-bit cells are genuinely exercised (>0).
// ============================================================================
#[test]
fn fullwidth_64_clean_bill_native_eq_jit() {
    let mut m = TrustIrModule::new("i2f_fullwidth".to_string());
    build_conv(0, "s64f64", &mut m, Ty::I64, Ty::I64, true, false);
    build_conv(1, "s64f32", &mut m, Ty::I64, Ty::I64, true, true);
    build_conv(2, "u64f64", &mut m, Ty::U64, Ty::U64, false, false);
    build_conv(3, "u64f32", &mut m, Ty::U64, Ty::U64, false, true);
    let buf = jit_buffer(&m);

    let s64f64: F64FromI64 = unsafe { std::mem::transmute(bind(&buf, "s64f64")) };
    let s64f32: F32FromI64 = unsafe { std::mem::transmute(bind(&buf, "s64f32")) };
    let u64f64: F64FromU64 = unsafe { std::mem::transmute(bind(&buf, "u64f64")) };
    let u64f32: F32FromU64 = unsafe { std::mem::transmute(bind(&buf, "u64f32")) };

    let mut checked = 0usize;
    let mut round64_cells = 0usize; // |i| > 2^53 rounding cells (f64)
    let mut round32_cells = 0usize; // |i| > 2^24 rounding cells (f32)
    let mut highbit_u64_cells = 0usize; // u64 >= 2^63 signedness cells

    for &x in &i64_inputs() {
        let (j64, w64) = (unsafe { s64f64(x) }.to_bits(), (x as f64).to_bits());
        assert_eq!(
            j64, w64,
            "SIToFP i64->f64 MISCOMPILE at x={x} ({x:#018x}): jit={j64:#018x} want(x as f64)={w64:#018x}"
        );
        let (j32, w32) = (unsafe { s64f32(x) }.to_bits(), (x as f32).to_bits());
        assert_eq!(
            j32, w32,
            "SIToFP i64->f32 MISCOMPILE at x={x} ({x:#018x}): jit={j32:#010x} want(x as f32)={w32:#010x}"
        );
        checked += 2;
        if x.unsigned_abs() > (1u64 << 53) {
            round64_cells += 1;
        }
        if x.unsigned_abs() > (1u64 << 24) {
            round32_cells += 1;
        }
    }
    for &x in &u64_inputs() {
        let (j64, w64) = (unsafe { u64f64(x) }.to_bits(), (x as f64).to_bits());
        assert_eq!(
            j64, w64,
            "UIToFP u64->f64 MISCOMPILE at x={x:#018x}: jit={j64:#018x} want(x as f64)={w64:#018x} \
             — if x>=2^63 this is the signed-vs-unsigned UCVTF bug"
        );
        let (j32, w32) = (unsafe { u64f32(x) }.to_bits(), (x as f32).to_bits());
        assert_eq!(
            j32, w32,
            "UIToFP u64->f32 MISCOMPILE at x={x:#018x}: jit={j32:#010x} want(x as f32)={w32:#010x}"
        );
        checked += 2;
        if x >= (1u64 << 63) {
            highbit_u64_cells += 1;
            // sanity: the oracle for a high-bit u64 is the UNSIGNED value, which is
            // strictly positive and far larger than any signed reading.
            assert!(
                x as f64 > 9.2e18,
                "oracle sanity: high-bit u64 must be ~1e19"
            );
        }
        if x > (1u64 << 53) {
            round64_cells += 1;
        }
        if x > (1u64 << 24) {
            round32_cells += 1;
        }
    }

    assert!(
        round64_cells >= 12,
        "f64 RNE-rounding cells under-exercised ({round64_cells})"
    );
    assert!(
        round32_cells >= 12,
        "f32 RNE-rounding cells under-exercised ({round32_cells})"
    );
    assert!(
        highbit_u64_cells >= 8,
        "u64 high-bit signedness cells under-exercised ({highbit_u64_cells}) — the UCVTF \
         signed-vs-unsigned site must be swept"
    );
    eprintln!(
        "64-BIT CLEAN BILL: SIToFP i64->{{f64,f32}} / UIToFP u64->{{f64,f32}} == Rust `as` \
         bit-exact on {checked} cells; {round64_cells} f64 RNE-rounding cells (2^53±k, i64::MAX/MIN), \
         {round32_cells} f32 RNE-rounding cells (2^24±k), {highbit_u64_cells} u64 high-bit \
         signedness cells (2^63 .. u64::MAX all convert UNSIGNED, not -1). Rounding = RNE, \
         signedness routed by SCVTF vs UCVTF. No under-saturation, no wrong tie-break."
    );
}

// ============================================================================
// TEST 2 — u64 HIGH-BIT SIGNEDNESS, dedicated + ARMED CONTROL. UIToFP (UCVTF)
//   over high-bit-set u64 must give the UNSIGNED value; a SIToFP (SCVTF) view of
//   the SAME bits must DIVERGE (unsigned ~ +1.8e19 vs signed negative), proving
//   the SCVTF/UCVTF opcode routing is load-bearing (not both mapping to one op).
// ============================================================================
#[test]
fn u64_high_bit_signedness_and_armed_control() {
    let mut m = TrustIrModule::new("i2f_signness".to_string());
    build_conv(0, "u_f64", &mut m, Ty::U64, Ty::U64, false, false); // UIToFP (UCVTF)
    build_conv(1, "s_f64", &mut m, Ty::I64, Ty::I64, true, false); // SIToFP (SCVTF) — same bits
    build_conv(2, "u_f32", &mut m, Ty::U64, Ty::U64, false, true);
    build_conv(3, "s_f32", &mut m, Ty::I64, Ty::I64, true, true);
    let buf = jit_buffer(&m);
    let u_f64: F64FromU64 = unsafe { std::mem::transmute(bind(&buf, "u_f64")) };
    let s_f64: F64FromI64 = unsafe { std::mem::transmute(bind(&buf, "s_f64")) };
    let u_f32: F32FromU64 = unsafe { std::mem::transmute(bind(&buf, "u_f32")) };
    let s_f32: F32FromI64 = unsafe { std::mem::transmute(bind(&buf, "s_f32")) };

    let highbit: &[u64] = &[
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0001,
        0x9000_0000_0000_0000,
        0xC000_0000_0000_0000,
        0xFFFF_FFFF_FFFF_FFFF,
        0xFFFF_FFFF_FFFF_F800,
        0xAAAA_AAAA_AAAA_AAAB,
    ];
    let mut diverged = 0usize;
    for &bits in highbit {
        // UIToFP == Rust unsigned `as` (the correct result).
        let (uj, uw) = (unsafe { u_f64(bits) }.to_bits(), (bits as f64).to_bits());
        assert_eq!(
            uj, uw,
            "UIToFP high-bit u64 {bits:#018x}: jit != (u64 as f64)"
        );
        assert!(
            unsafe { u_f64(bits) } > 9.2e18,
            "unsigned high-bit must be ~1e19"
        );
        let (uj32, uw32) = (unsafe { u_f32(bits) }.to_bits(), (bits as f32).to_bits());
        assert_eq!(
            uj32, uw32,
            "UIToFP high-bit u64 {bits:#018x}->f32: jit != (u64 as f32)"
        );

        // ARMED CONTROL: the SIToFP (signed) reading of the SAME bit pattern is the
        // NEGATIVE signed value and MUST differ — else signedness routing is dead.
        let signed_val = bits as i64;
        let (sj, sw) = (
            unsafe { s_f64(signed_val) }.to_bits(),
            (signed_val as f64).to_bits(),
        );
        assert_eq!(sj, sw, "SIToFP {signed_val}: jit != (i64 as f64)");
        assert!(
            unsafe { s_f64(signed_val) } < 0.0,
            "signed high-bit must be negative"
        );
        assert_ne!(
            uj, sj,
            "SIGNEDNESS CONTROL DEAD: UIToFP and SIToFP agree on high-bit bits {bits:#018x} \
             (both would be mapping to one CVTF op)"
        );
        assert_ne!(
            uj32,
            unsafe { s_f32(signed_val) }.to_bits(),
            "signedness control dead (f32)"
        );
        diverged += 1;
    }
    assert!(diverged >= 7);
    eprintln!(
        "SIGNEDNESS: UIToFP(UCVTF) high-bit u64 == unsigned `as` on {diverged} values \
         (2^63..u64::MAX -> ~1e19, NOT negative); the SIToFP(SCVTF) view of the same bits is \
         negative and DIVERGES every time -> opcode routing load-bearing. No signedness bug."
    );
}

// ============================================================================
// TEST 3 — f32 RNE ROUNDING BOUNDARY, dense. f32's 24-bit mantissa rounds far
//   sooner than f64's 53-bit. Densely sweep the 2^24 region and a wide band of
//   i64/u64 values -> f32; every cell must be bit-exact to Rust `as f32` (RNE,
//   incl. ties-to-even and round-up).
// ============================================================================
#[test]
fn f32_rounding_boundary_dense() {
    let mut m = TrustIrModule::new("i2f_f32round".to_string());
    build_conv(0, "s_f32", &mut m, Ty::I64, Ty::I64, true, true);
    build_conv(1, "u_f32", &mut m, Ty::U64, Ty::U64, false, true);
    let buf = jit_buffer(&m);
    let s_f32: F32FromI64 = unsafe { std::mem::transmute(bind(&buf, "s_f32")) };
    let u_f32: F32FromU64 = unsafe { std::mem::transmute(bind(&buf, "u_f32")) };

    let m24 = 1i64 << 24;
    let mut checked = 0usize;
    let mut tie_or_round = 0usize;
    // dense band straddling 2^24 (where consecutive ints stop being representable)
    for d in -4i64..=64 {
        let x = m24 + d;
        let (j, w) = (unsafe { s_f32(x) }.to_bits(), (x as f32).to_bits());
        assert_eq!(
            j, w,
            "f32 rounding SIToFP at x={x} (2^24{d:+}): jit={j:#010x} want={w:#010x}"
        );
        let xu = x as u64;
        let (ju, wu) = (unsafe { u_f32(xu) }.to_bits(), (xu as f32).to_bits());
        assert_eq!(
            ju, wu,
            "f32 rounding UIToFP at x={xu}: jit={ju:#010x} want={wu:#010x}"
        );
        checked += 2;
        // a "must round" cell: the low bit is lost above 2^24, so odd offsets round.
        if d > 0 && (x & 1) == 1 {
            tie_or_round += 1;
        }
    }
    // wider magnitudes: powers of two ± small, and the top-of-range roundings.
    for k in 25..=62u32 {
        for off in [-1i64, 1, 3] {
            let x = (1i64 << k) + off;
            let (j, w) = (unsafe { s_f32(x) }.to_bits(), (x as f32).to_bits());
            assert_eq!(
                j, w,
                "f32 rounding SIToFP at 2^{k}{off:+} = {x}: jit={j:#010x} want={w:#010x}"
            );
            checked += 1;
            if off != -1 {
                tie_or_round += 1;
            }
        }
    }
    // explicit witnesses (documented in the report):
    assert_eq!(unsafe { s_f32((1i64 << 24) + 1) }.to_bits(), 0x4b80_0000); // 2^24+1 -> 2^24 (ties to even)
    assert_eq!(unsafe { s_f32((1i64 << 24) + 3) }.to_bits(), 0x4b80_0002); // 2^24+3 -> 2^24+4 (round up)
    assert!(
        tie_or_round >= 20,
        "f32 tie/round cells under-exercised ({tie_or_round})"
    );
    eprintln!(
        "f32 RNE BOUNDARY: {checked} SIToFP/UIToFP -> f32 cells bit-exact vs Rust `as f32` across \
         the dense 2^24 band + powers-of-two 2^25..2^62; {tie_or_round} genuine tie/round cells. \
         2^24+1 ties-to-even (->2^24), 2^24+3 rounds up (->2^24+4). RNE correct."
    );
}

// ============================================================================
// TEST 4 — NARROW UNSIGNED CLEAN BILL. UIToFP u8/u16/u32 -> f64/f32 (via Trunc
//   from a 64-bit param, the canonical `(x as uN) as f` shape). The narrow source
//   is zero-extended in-register and UCVTF reads it unsigned, so every cell is
//   bit-exact to Rust `(x as uN) as f`. (Contrast the SIGNED narrow bug, Test 5.)
// ============================================================================
#[test]
fn narrow_unsigned_clean_bill() {
    let mut m = TrustIrModule::new("i2f_narrow_u".to_string());
    build_conv(0, "u8f64", &mut m, Ty::U64, Ty::U8, false, false);
    build_conv(1, "u16f64", &mut m, Ty::U64, Ty::U16, false, false);
    build_conv(2, "u32f64", &mut m, Ty::U64, Ty::U32, false, false);
    build_conv(3, "u32f32", &mut m, Ty::U64, Ty::U32, false, true);
    let buf = jit_buffer(&m);
    let u8f64: F64FromU64 = unsafe { std::mem::transmute(bind(&buf, "u8f64")) };
    let u16f64: F64FromU64 = unsafe { std::mem::transmute(bind(&buf, "u16f64")) };
    let u32f64: F64FromU64 = unsafe { std::mem::transmute(bind(&buf, "u32f64")) };
    let u32f32: F32FromU64 = unsafe { std::mem::transmute(bind(&buf, "u32f32")) };

    let probe: &[u64] = &[
        0,
        1,
        5,
        100,
        127,
        128,
        200,
        255,
        256,
        1000,
        65535,
        65536,
        0xFFFF_FFFE,
        0xFFFF_FFFF,
        0x8000_0000,
        0x1234_5678,
        // high garbage bits that Trunc must discard:
        0xDEAD_BEEF_0000_00FF,
        0xFFFF_FFFF_FFFF_FFFF,
        0xABCD_0000_8000_0001,
    ];
    let mut checked = 0usize;
    for &x in probe {
        assert_eq!(
            unsafe { u8f64(x) }.to_bits(),
            ((x as u8) as f64).to_bits(),
            "u8->f64 x={x:#018x}"
        );
        assert_eq!(
            unsafe { u16f64(x) }.to_bits(),
            ((x as u16) as f64).to_bits(),
            "u16->f64 x={x:#018x}"
        );
        assert_eq!(
            unsafe { u32f64(x) }.to_bits(),
            ((x as u32) as f64).to_bits(),
            "u32->f64 x={x:#018x}"
        );
        assert_eq!(
            unsafe { u32f32(x) }.to_bits(),
            ((x as u32) as f32).to_bits(),
            "u32->f32 x={x:#018x}"
        );
        checked += 4;
    }
    eprintln!(
        "NARROW UNSIGNED CLEAN BILL: UIToFP u8/u16/u32 -> f64/f32 == Rust `(x as uN) as f` \
         bit-exact on {checked} cells (incl. inputs with dirty high bits Trunc must discard). \
         Zero-extension + UCVTF-unsigned-read is correct."
    );
}

// ============================================================================
// TEST 5 — owner #12 FIXED (clean bill): NARROW SIGNED int->float.
//   SIToFP i8/i16/i32 -> f64/f32 now sign-extends the source (SXTB/SXTH/SXTW) before
//   SCVTF, so every value — including negatives — matches the Rust `as` oracle. (Was
//   a fail-loud PIN: the zero-extended source was read as 64-bit signed by the sf=1
//   SCVTF, so negatives became large positives. The isel select_fcvt_from_int
//   owner-#12 fix flipped it.) Verified via BOTH the Trunc pattern and a direct i32
//   parameter, and that the result is NO LONGER the old zero-extended-read value.
// ============================================================================
#[test]
fn narrow_signed_int_to_float_clean_bill() {
    // ── (a) via Trunc from i64: the `(x as iN) as f` shape ──
    let mut m = TrustIrModule::new("i2f_narrow_s".to_string());
    build_conv(0, "s8f64", &mut m, Ty::I64, Ty::I8, true, false);
    build_conv(1, "s16f64", &mut m, Ty::I64, Ty::I16, true, false);
    build_conv(2, "s32f64", &mut m, Ty::I64, Ty::I32, true, false);
    build_conv(3, "s32f32", &mut m, Ty::I64, Ty::I32, true, true);
    let buf = jit_buffer(&m);
    let s8f64: F64FromI64 = unsafe { std::mem::transmute(bind(&buf, "s8f64")) };
    let s16f64: F64FromI64 = unsafe { std::mem::transmute(bind(&buf, "s16f64")) };
    let s32f64: F64FromI64 = unsafe { std::mem::transmute(bind(&buf, "s32f64")) };
    let s32f32: F32FromI64 = unsafe { std::mem::transmute(bind(&buf, "s32f32")) };

    // The buggy "zero-extended read" model: the narrow value's UNSIGNED bit pattern
    // (0..2^N), zero-extended to 64 bits, read as a (positive) i64, then `as f`.
    let bug_f64 = |x: i64, n: u32| -> u64 {
        let pat: u64 = match n {
            8 => (x as i8 as u8) as u64,
            16 => (x as i16 as u16) as u64,
            32 => (x as i32 as u32) as u64,
            _ => unreachable!(),
        };
        (pat as f64).to_bits()
    };
    let want_f64 = |x: i64, n: u32| -> u64 {
        match n {
            8 => ((x as i8) as f64).to_bits(),
            16 => ((x as i16) as f64).to_bits(),
            32 => ((x as i32) as f64).to_bits(),
            _ => unreachable!(),
        }
    };

    // NEGATIVE narrow values (sign bit set) — the miscompile class.
    let neg_cases: &[(i64, u32)] = &[
        (-1, 8),
        (-5, 8),
        (-100, 8),
        (-128, 8),
        (-1, 16),
        (-1000, 16),
        (-32768, 16),
        (-1, 32),
        (-5, 32),
        (-100, 32),
        (i32::MIN as i64, 32),
        (-2147483647, 32),
    ];
    let mut fixed = 0usize;
    for &(x, n) in neg_cases {
        let jit = match n {
            8 => unsafe { s8f64(x) }.to_bits(),
            16 => unsafe { s16f64(x) }.to_bits(),
            32 => unsafe { s32f64(x) }.to_bits(),
            _ => unreachable!(),
        };
        // owner #12 FIXED: JIT now matches the Rust `as` oracle (sign-extended source)...
        assert_eq!(
            jit,
            want_f64(x, n),
            "owner #12 REGRESSED: narrow signed i{n}->f64 at x={x} = {jit:#018x} != Rust `as` \
             {:#018x} (sign-extension before SCVTF missing/broken).",
            want_f64(x, n)
        );
        // ...and is NO LONGER the old zero-extended-read value on these negatives.
        assert_ne!(
            jit,
            bug_f64(x, n),
            "owner #12 REGRESSED: narrow signed i{n}->f64 at x={x} still matches the \
             zero-extended-read bug model ({:#018x}).",
            bug_f64(x, n)
        );
        fixed += 1;
    }

    // f32 destination — fixed. i32::MIN witness: now = -2^31 (0xcf00_0000).
    assert_eq!(
        unsafe { s32f32(i32::MIN as i64) }.to_bits(),
        0xcf00_0000,
        "i32::MIN->f32 fixed = -2^31"
    );
    assert_eq!(
        ((i32::MIN) as f32).to_bits(),
        0xcf00_0000,
        "oracle i32::MIN as f32 = -2^31"
    );
    assert_eq!(
        unsafe { s32f32(i32::MIN as i64) }.to_bits(),
        (i32::MIN as f32).to_bits(),
        "JIT == Rust `as` for i32::MIN->f32"
    );

    // NON-negative narrow values are (accidentally) correct — zero-ext == value.
    for &(x, n) in &[
        (0i64, 8u32),
        (5, 8),
        (127, 8),
        (255, 32),
        (1000, 32),
        (i32::MAX as i64, 32),
    ] {
        let jit = match n {
            8 => unsafe { s8f64(x) },
            32 => unsafe { s32f64(x) },
            _ => unreachable!(),
        }
        .to_bits();
        assert_eq!(
            jit,
            want_f64(x, n),
            "non-negative narrow signed must be correct: x={x} n={n}"
        );
    }

    // ── (b) DIRECT i32 parameter (no Trunc): the bug is not an artifact of Trunc ──
    let mut md = TrustIrModule::new("i2f_direct_s32".to_string());
    let ft = md.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "d_s32", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::SIToFP,
                src_ty: Ty::I32,
                dst_ty: Ty::F64,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    md.add_function(f);
    let bufd = jit_buffer(&md);
    let d_s32: unsafe extern "C" fn(i32) -> f64 =
        unsafe { std::mem::transmute(bind(&bufd, "d_s32")) };
    // direct s32(-1) now converts correctly to -1.0 (sign-extended).
    assert_eq!(
        unsafe { d_s32(-1) }.to_bits(),
        (-1.0f64).to_bits(),
        "direct i32 param: -1 -> -1.0"
    );
    assert_ne!(
        unsafe { d_s32(-1) }.to_bits(),
        4294967295_f64.to_bits(),
        "direct i32 param: no longer the zero-ext bug model"
    );
    // direct positive is correct.
    assert_eq!(unsafe { d_s32(1234) }.to_bits(), (1234.0f64).to_bits());

    eprintln!(
        "owner #12 FIXED: narrow SIGNED SIToFP i8/i16/i32 -> f64/f32 now correct on all {fixed} \
         negative cases (source sign-extended SXTB/SXTH/SXTW before SCVTF): i32(-1) = -1.0; \
         i32::MIN->f32 = -2^31 (0xcf00_0000); == Rust `as` via Trunc AND a direct i32 param, and \
         no longer the zero-extended-read value. This clean bill fails loudly if the fix regresses."
    );
}

// ============================================================================
// TEST 6 — owner #13 FIXED (correctly-rounded clean bill): i128/u128 -> float.
//   FcvtFromInt/FcvtFromUint with a 128-bit source now lower via the compiler-rt
//   conversion helpers `__floatti{d,s}f` / `__floatunti{d,s}f` (LLVM's lowering,
//   correctly-rounded RNE over the FULL 128 bits) instead of the old low-64
//   truncation (2^64+1 -> 1.0, 2^70 -> 0.0). Verified native==JIT: the JIT result
//   is bit-exact vs Rust `x as f64/f32` across a hard sweep — the previously-wrong
//   >=2^64 class, RNE rounding boundaries, negatives, and i128/u128 extremes.
// ============================================================================
#[test]
fn i128_to_float_correctly_rounded_clean_bill() {
    let mut m = TrustIrModule::new("i2f_i128".to_string());
    build_conv(0, "s128d", &mut m, Ty::I128, Ty::I128, true, false); // i128 -> f64
    build_conv(1, "s128f", &mut m, Ty::I128, Ty::I128, true, true); // i128 -> f32
    build_conv(2, "u128d", &mut m, Ty::U128, Ty::U128, false, false); // u128 -> f64
    build_conv(3, "u128f", &mut m, Ty::U128, Ty::U128, false, true); // u128 -> f32
    let buf = jit_buffer(&m);
    let s128d: unsafe extern "C" fn(i128) -> f64 =
        unsafe { std::mem::transmute(bind(&buf, "s128d")) };
    let s128f: unsafe extern "C" fn(i128) -> f32 =
        unsafe { std::mem::transmute(bind(&buf, "s128f")) };
    let u128d: unsafe extern "C" fn(u128) -> f64 =
        unsafe { std::mem::transmute(bind(&buf, "u128d")) };
    let u128f: unsafe extern "C" fn(u128) -> f32 =
        unsafe { std::mem::transmute(bind(&buf, "u128f")) };

    // The exact witnesses that USED to be wrong (low-64 truncation): now correct.
    assert_eq!(
        unsafe { s128d((1i128 << 64) + 1) }.to_bits(),
        (((1i128 << 64) + 1) as f64).to_bits(),
        "s128d(2^64+1) fixed (was 1.0)"
    );
    assert_eq!(
        unsafe { s128d(1i128 << 70) }.to_bits(),
        ((1i128 << 70) as f64).to_bits(),
        "s128d(2^70) fixed (was 0.0)"
    );
    assert_eq!(
        unsafe { u128d((1u128 << 64) + 7) }.to_bits(),
        (((1u128 << 64) + 7) as f64).to_bits(),
        "u128d(2^64+7) fixed (was 7.0)"
    );

    // Hard sweep: bit-exact vs Rust `as` for f64 and f32, signed and unsigned.
    let mut checked = 0usize;
    let mut over_2p64 = 0usize;
    let mut rounded = 0usize;
    let mut check = |x_u: u128| {
        let x_i = x_u as i128;
        // unsigned
        assert_eq!(
            unsafe { u128d(x_u) }.to_bits(),
            (x_u as f64).to_bits(),
            "u128->f64 MISCOMPILE x={x_u:#034x}"
        );
        assert_eq!(
            unsafe { u128f(x_u) }.to_bits(),
            (x_u as f32).to_bits(),
            "u128->f32 MISCOMPILE x={x_u:#034x}"
        );
        // signed (reinterpret the same bits as i128)
        assert_eq!(
            unsafe { s128d(x_i) }.to_bits(),
            (x_i as f64).to_bits(),
            "i128->f64 MISCOMPILE x={x_i}"
        );
        assert_eq!(
            unsafe { s128f(x_i) }.to_bits(),
            (x_i as f32).to_bits(),
            "i128->f32 MISCOMPILE x={x_i}"
        );
        if x_u >= (1u128 << 64) {
            over_2p64 += 1;
        }
        // did the f64 conversion actually round (exact value needs > 53 bits)?
        if x_u != 0 && (x_u as f64) as u128 != x_u {
            rounded += 1;
        }
        checked += 1;
    };

    // Explicit boundary witnesses.
    for &x in &[
        0u128,
        1,
        2,
        5,
        100,
        0xFFFF_FFFF,
        u64::MAX as u128,
        1u128 << 52,
        (1u128 << 53) + 1,
        (1u128 << 53) + 3, // f64 RNE ties/round-up
        (1u128 << 24) + 1,
        (1u128 << 24) + 3, // f32 RNE
        1u128 << 63,
        1u128 << 64,
        (1u128 << 64) + 1,
        (1u128 << 64) + 2048, // 2^64 + half-ULP
        1u128 << 70,
        1u128 << 100,
        1u128 << 126,
        1u128 << 127,
        (1u128 << 127) - 1, // i128::MAX
        1u128 << 127,       // i128::MIN (as i128)
        u128::MAX,
        u128::MAX - 1,
        u128::MAX - (1u128 << 74),
        (1u128 << 113) | (1u128 << 60), // mixed high+low
    ] {
        check(x);
    }
    // Dense pseudo-random sweep across the full 128-bit range (xorshift on both halves).
    let mut s0 = 0x1234_5678_9abc_def0u64;
    let mut s1 = 0x0fed_cba9_8765_4321u64;
    for _ in 0..500 {
        s0 ^= s0 << 13;
        s0 ^= s0 >> 7;
        s0 ^= s0 << 17;
        s1 ^= s1 << 13;
        s1 ^= s1 >> 7;
        s1 ^= s1 << 17;
        check(((s1 as u128) << 64) | (s0 as u128));
    }
    assert!(
        over_2p64 > 100,
        "sweep under-exercised the >=2^64 class ({over_2p64})"
    );
    assert!(
        rounded > 100,
        "sweep under-exercised genuine RNE rounding ({rounded})"
    );
    eprintln!(
        "owner #13 FIXED (correctly-rounded): i128/u128 -> f64/f32 bit-exact vs Rust `as` over \
         {checked} cells ({over_2p64} with |value|>=2^64, {rounded} genuinely rounded) via the \
         compiler-rt __float[un]ti{{d,s}}f helpers — the low-64 truncation is gone."
    );
}

// ============================================================================
// TEST 7 — ARMED CONTROLS: the differential is load-bearing.
//   (a) DEST PRECISION: SIToFP i64->f32 vs i64->f64 on 2^24+1 must DIVERGE
//       (f32 rounds to 2^24, f64 is exact), proving the destination float width is
//       genuinely observed end-to-end.
//   (b) ROUNDING is real: 2^53+1 as f64 rounds (ties to even) to 2^53, i.e. the
//       JIT does NOT return the exact-but-unrepresentable value.
// ============================================================================
#[test]
fn armed_controls_precision_and_rounding() {
    let mut m = TrustIrModule::new("i2f_ctrl".to_string());
    build_conv(0, "to_f64", &mut m, Ty::I64, Ty::I64, true, false);
    build_conv(1, "to_f32", &mut m, Ty::I64, Ty::I64, true, true);
    let buf = jit_buffer(&m);
    let to_f64: F64FromI64 = unsafe { std::mem::transmute(bind(&buf, "to_f64")) };
    let to_f32: F32FromI64 = unsafe { std::mem::transmute(bind(&buf, "to_f32")) };

    // (a) dest precision load-bearing.
    let x = (1i64 << 24) + 1; // 16777217
    let f64_val = unsafe { to_f64(x) };
    let f32_val = unsafe { to_f32(x) };
    assert_eq!(f64_val, 16777217.0, "i64->f64 of 2^24+1 is exact");
    assert_eq!(
        f32_val, 16777216.0,
        "i64->f32 of 2^24+1 rounds (ties to even) to 2^24"
    );
    assert_ne!(
        f64_val, f32_val as f64,
        "DEST-PRECISION CONTROL: f64 result (16777217) must differ from the f32 result widened \
         (16777216) — else destination width is ignored"
    );

    // (b) rounding really happens (RNE): 2^53+1 -> 2^53 (ties to even), not a
    //     bogus non-representable pattern.
    let y = (1i64 << 53) + 1;
    assert_eq!(
        unsafe { to_f64(y) },
        9007199254740992.0,
        "2^53+1 ties to even -> 2^53"
    );
    assert_eq!(
        unsafe { to_f64(y) }.to_bits(),
        (y as f64).to_bits(),
        "matches Rust `as`"
    );
    // 2^53+3 rounds UP to 2^53+4 (nearest even).
    let z = (1i64 << 53) + 3;
    assert_eq!(
        unsafe { to_f64(z) },
        9007199254740996.0,
        "2^53+3 rounds up -> 2^53+4"
    );

    eprintln!(
        "ARMED CONTROLS: dest-precision load-bearing (i64->f64(2^24+1)=16777217 exact vs \
         i64->f32(2^24+1)=16777216 rounded); RNE load-bearing (2^53+1 ties-to-even ->2^53, \
         2^53+3 rounds-up ->2^53+4). The differential is real."
    );
}
