// Copyright 2026 Andrew Yates | Apache-2.0
//! Three-way IEEE 754 differential of the scalar floating-point conversion,
//! rounding and arithmetic instructions (ledger `L04-P3`).
//!
//! For every scalar FP instruction form the AArch64 backend emits (FADD, FSUB,
//! FMUL, FDIV, FMADD, FMINNM, FMAXNM, FNEG, FABS, FSQRT, FRINTM/P/Z/N at H, S
//! and D; FCVTZS/FCVTZU and SCVTF/UCVTF at every H/S/D x W/X pairing; the six
//! FCVT precision conversions), plus the FRINTA/FRINTX/FRINTI and FMIN/FMAX
//! forms the backend never emits (assembler words, run only to validate the
//! reference), each input is evaluated three ways:
//!
//! * **the CPU**: the instruction word, produced by the live encoder
//!   (`encode_instruction`) and decoded by ENC-5 first, runs inside a small
//!   JIT loop that clears FPSR before and reads it after every element, so the
//!   result, the untouched other destination, the zeroed upper register bits
//!   and the five cumulative exception flags are all compared;
//! * **the independent reference** (`trust_cg_verify::ieee754_reference`,
//!   integer-only, sharing no code with the models), bit for bit, flags
//!   included;
//! * **the verifier's semantic model**: the `aarch64_semantics` machine-side
//!   expression the reconstruction obligations use (the `aarch64_fcvt_half`
//!   `FPConvert` transcription for the half-precision FCVT forms), over
//!   bit-cast `Var` leaves, evaluated as the sampling path evaluates it (the
//!   compiled `FlatProg` tape for the bit-vector `FPConvert` models,
//!   `SmtExpr::try_eval` for the rest). The FP models have one NaN (QF_FP,
//!   carried as an `f64`), so a NaN result is compared by class;
//!   two further, named boundaries of that single-NaN carrier are counted
//!   apart (a signaling operand of FMINNM/FMAXNM, and the order of signed zeros
//!   in FMINNM/FMAXNM); every other disagreement fails. FPSR is not modeled.
//!
//! Input sets and their strength, printed per form:
//!
//! * every binary16 encoding (65,536) for every H-source form: EXHAUSTIVE;
//! * binary32 sources and 32-bit integer sources: a structured set (every
//!   exponent field with boundary and random significands, every encoding
//!   within 4,096 ulps of each integer-range boundary) plus a stratified
//!   random sample, STATISTICAL, in the default (floor) run; EXHAUSTIVE over
//!   all 2^32 encodings with `TRUST_CG_FP_IEEE_EXHAUSTIVE=1` (run in release);
//! * binary16 pairs: every encoding against a structured edge set plus random
//!   pairs (statistical), and all 2^32 pairs under the exhaustive switch;
//! * binary64 sources, 64-bit integer sources, binary32/binary64 pairs and
//!   every fused multiply-add triple set: boundary classes plus a stratified
//!   random sample, always STATISTICAL.
//!
//! The FPCR the comparisons assume (round to nearest even, no flush to zero,
//! no default NaN, `AH = 0`) is read and required first. This is testing
//! evidence on one CPU over the inputs named; it is not a proof and credits
//! nothing in the coverage gate. `TRUST_CG_FP_IEEE_RECORD=<path>` appends one
//! JSON line per form and set to `<path>`; `TRUST_CG_FP_IEEE_THREADS=<n>`
//! bounds the worker threads.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::collections::BTreeMap;
use std::io::Write as _;
use std::time::Instant;

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand as Arg, PReg};
use trust_cg_verify::aarch64_fcvt_half::{HalfConversion, arm_fpconvert};
use trust_cg_verify::aarch64_semantics::{self as sem, FPSize};
use trust_cg_verify::fp_ieee_evidence::{self as evidence, InputSpace};
use trust_cg_verify::ieee754_reference::{self as ieee, Flags, Format, Outcome, Rounding};
use trust_cg_verify::smt::{EvalEnv, EvalResult, FlatProg, RoundingMode, SmtExpr as E};

#[path = "support/fp_ieee_inputs.rs"]
mod inputs;
use inputs::*;

const RNE: Rounding = Rounding::TiesToEven;

// ===========================================================================
// Executable loop stubs
// ===========================================================================

mod exec {
    /// The loop every form runs, with the form's word at [`OP_SLOT`]
    /// (assembled by `clang -target arm64-apple-macos`, read back with
    /// `otool -tvj`). `x0` walks 24-byte input records `[a, b, c]`, `x1` walks
    /// 32-byte output records `[q3.lo, q3.hi, x10, fpsr]`, `x2` counts:
    ///
    /// ```text
    ///  0 ldr d0, [x0]          ; Vn  <- a
    ///  1 ldr d1, [x0, #8]      ; Vm  <- b
    ///  2 ldr d2, [x0, #16]     ; Va  <- c
    ///  3 ldr x9, [x0]          ; Xn  <- a
    ///  4 movi v3.2d, #-1       ; poison the FP destination
    ///  5 mov x10, #-1          ; poison the GPR destination
    ///  6 msr fpsr, xzr         ; clear the cumulative flags
    ///  7 <the form's word>
    ///  8 mrs x11, fpsr
    ///  9 str q3, [x1]
    /// 10 str x10, [x1, #16]
    /// 11 str x11, [x1, #24]
    /// 12 add x0, x0, #24
    /// 13 add x1, x1, #32
    /// 14 subs x2, x2, #1
    /// 15 b.ne 0
    /// 16 ret
    /// ```
    pub const TEMPLATE: [u32; 17] = [
        0xfd40_0000,
        0xfd40_0401,
        0xfd40_0802,
        0xf940_0009,
        0x6f07_e7e3,
        0x9280_000a,
        0xd51b_443f,
        0xd503_201f,
        0xd53b_442b,
        0x3d80_0023,
        0xf900_082a,
        0xf900_0c2b,
        0x9100_6000,
        0x9100_8021,
        0xf100_0442,
        0x54ff_fe21,
        0xd65f_03c0,
    ];
    pub const OP_SLOT: usize = 7;
    const STUB_BYTES: usize = 128;

    type Stub = unsafe extern "C" fn(*const [u64; 3], *mut [u64; 4], usize);

    #[cfg(target_os = "macos")]
    unsafe extern "C" {
        fn pthread_jit_write_protect_np(enabled: libc::c_int);
        fn sys_icache_invalidate(start: *mut libc::c_void, len: libc::size_t);
    }

    /// An executable mapping holding one loop stub per word.
    pub struct Page {
        base: *mut u8,
        len: usize,
        stubs: usize,
    }

    // SAFETY: the mapping is immutable once published; a stub only reads its
    // input slice and writes its output slice.
    unsafe impl Send for Page {}
    unsafe impl Sync for Page {}

    impl Page {
        pub fn new(words: &[u32]) -> Page {
            let mut code = Vec::with_capacity(words.len() * STUB_BYTES);
            for &word in words {
                let start = code.len();
                for (index, template) in TEMPLATE.iter().enumerate() {
                    let w = if index == OP_SLOT { word } else { *template };
                    code.extend_from_slice(&w.to_le_bytes());
                }
                code.resize(start + STUB_BYTES, 0);
            }
            let page = 16 * 1024;
            let len = code.len().div_ceil(page).max(1) * page;
            // SAFETY: an anonymous private mapping; every pointer below stays
            // inside it.
            unsafe {
                let base = map(len);
                write(base, &code);
                Page {
                    base,
                    len,
                    stubs: words.len(),
                }
            }
        }

        /// Run stub `index` over `input`, writing one record per element.
        pub fn run(&self, index: usize, input: &[[u64; 3]], output: &mut [[u64; 4]]) {
            assert!(index < self.stubs);
            assert_eq!(input.len(), output.len());
            if input.is_empty() {
                return;
            }
            // SAFETY: the stub reads `input.len()` 24-byte records and writes
            // as many 32-byte records, clobbering only caller-saved registers
            // (x0-x2, x9-x11, v0-v3, NZCV, FPSR).
            unsafe {
                let stub: Stub = std::mem::transmute(self.base.add(index * STUB_BYTES));
                stub(input.as_ptr(), output.as_mut_ptr(), input.len());
            }
        }
    }

    impl Drop for Page {
        fn drop(&mut self) {
            // SAFETY: `base`/`len` are exactly the mapping `new` created.
            unsafe {
                libc::munmap(self.base.cast(), self.len);
            }
        }
    }

    #[cfg(target_os = "macos")]
    unsafe fn map(len: usize) -> *mut u8 {
        let base = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
                libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_JIT,
                -1,
                0,
            )
        };
        assert_ne!(base, libc::MAP_FAILED, "MAP_JIT mapping failed");
        base.cast()
    }

    #[cfg(target_os = "macos")]
    unsafe fn write(base: *mut u8, code: &[u8]) {
        unsafe {
            pthread_jit_write_protect_np(0);
            std::ptr::copy_nonoverlapping(code.as_ptr(), base, code.len());
            pthread_jit_write_protect_np(1);
            sys_icache_invalidate(base.cast(), code.len());
        }
    }

    #[cfg(target_os = "linux")]
    unsafe fn map(len: usize) -> *mut u8 {
        let base = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        assert_ne!(base, libc::MAP_FAILED, "mapping failed");
        base.cast()
    }

    #[cfg(target_os = "linux")]
    unsafe fn write(base: *mut u8, code: &[u8]) {
        unsafe {
            std::ptr::copy_nonoverlapping(code.as_ptr(), base, code.len());
            let len = code.len().div_ceil(16 * 1024) * 16 * 1024;
            assert_eq!(
                libc::mprotect(base.cast(), len, libc::PROT_READ | libc::PROT_EXEC),
                0
            );
            // Arm ARM B2.4.4: clean the data lines to the point of
            // unification, invalidate the instruction lines, synchronize.
            let ctr: u64;
            std::arch::asm!("mrs {}, ctr_el0", out(reg) ctr);
            let dline = 4usize << ((ctr >> 16) & 0xf);
            let iline = 4usize << (ctr & 0xf);
            let start = base as usize;
            let end = start + code.len();
            let mut at = start & !(dline - 1);
            while at < end {
                std::arch::asm!("dc cvau, {}", in(reg) at);
                at += dline;
            }
            std::arch::asm!("dsb ish");
            let mut at = start & !(iline - 1);
            while at < end {
                std::arch::asm!("ic ivau, {}", in(reg) at);
                at += iline;
            }
            std::arch::asm!("dsb ish", "isb");
        }
    }
}

/// Require FEAT_FP16: the H-register arithmetic, rounding and conversion
/// forms are undefined instructions without it. Every Apple arm64 part has
/// it; a Linux host must report it in `AT_HWCAP` (FPHP and ASIMDHP).
fn require_fp16() {
    #[cfg(target_os = "macos")]
    {
        let name = c"hw.optional.arm.FEAT_FP16";
        let mut value: libc::c_int = 0;
        let mut len = std::mem::size_of::<libc::c_int>();
        // SAFETY: a read of an integer sysctl into a correctly sized buffer.
        let status = unsafe {
            libc::sysctlbyname(
                name.as_ptr(),
                (&mut value as *mut libc::c_int).cast(),
                &mut len,
                std::ptr::null_mut(),
                0,
            )
        };
        assert!(
            status == 0 && value == 1,
            "this host does not report FEAT_FP16 (hw.optional.arm.FEAT_FP16)"
        );
    }
    #[cfg(target_os = "linux")]
    {
        // SAFETY: getauxval has no preconditions.
        let hwcap = unsafe { libc::getauxval(libc::AT_HWCAP) };
        let need = libc::HWCAP_FPHP | libc::HWCAP_ASIMDHP;
        assert_eq!(
            hwcap & need,
            need,
            "this host does not report FEAT_FP16 (AT_HWCAP FPHP|ASIMDHP); the H forms would trap"
        );
    }
}

/// The FPCR of the calling thread.
fn fpcr() -> u64 {
    let value: u64;
    // SAFETY: reading FPCR has no side effect.
    unsafe { std::arch::asm!("mrs {}, fpcr", out(reg) value) };
    value
}

// ===========================================================================
// Forms
// ===========================================================================

/// What a form computes, in the reference's terms.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Sem {
    Add(Format),
    Sub(Format),
    Mul(Format),
    Div(Format),
    MinNum(Format),
    MaxNum(Format),
    Min(Format),
    Max(Format),
    /// `c + a * b` (FMADD `Rd = Ra + Rn * Rm`).
    Fma(Format),
    Neg(Format),
    Abs(Format),
    Sqrt(Format),
    /// Round to integral; `true` raises Inexact (FRINTX).
    Round(Format, Rounding, bool),
    /// FCVTZS/FCVTZU to a `u32` (W) or 64 (X) bit register, `true` = signed.
    ToInt(Format, u32, bool),
    /// SCVTF/UCVTF from a W or X register, `true` = signed.
    FromInt(Format, u32, bool),
    /// FCVT from the first format to the second.
    Cvt(Format, Format),
}

/// The values a form reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Domain {
    Fp(Format),
    Int(u32),
    Pair(Format),
    Triple(Format),
}

/// Where a form writes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Dest {
    Fp(Format),
    Gpr(u32),
}

impl Sem {
    fn domain(self) -> Domain {
        match self {
            Sem::Add(f)
            | Sem::Sub(f)
            | Sem::Mul(f)
            | Sem::Div(f)
            | Sem::MinNum(f)
            | Sem::MaxNum(f)
            | Sem::Min(f)
            | Sem::Max(f) => Domain::Pair(f),
            Sem::Fma(f) => Domain::Triple(f),
            Sem::Neg(f) | Sem::Abs(f) | Sem::Sqrt(f) | Sem::Round(f, ..) => Domain::Fp(f),
            Sem::ToInt(f, ..) | Sem::Cvt(f, _) => Domain::Fp(f),
            Sem::FromInt(_, width, _) => Domain::Int(width),
        }
    }

    fn dest(self) -> Dest {
        match self {
            Sem::ToInt(_, width, _) => Dest::Gpr(width),
            Sem::FromInt(f, ..) | Sem::Cvt(_, f) => Dest::Fp(f),
            Sem::Add(f)
            | Sem::Sub(f)
            | Sem::Mul(f)
            | Sem::Div(f)
            | Sem::MinNum(f)
            | Sem::MaxNum(f)
            | Sem::Min(f)
            | Sem::Max(f)
            | Sem::Fma(f)
            | Sem::Neg(f)
            | Sem::Abs(f)
            | Sem::Sqrt(f)
            | Sem::Round(f, ..) => Dest::Fp(f),
        }
    }

    /// The independent reference's result for `[a, b, c]`.
    fn reference(self, [a, b, c]: [u64; 3]) -> Outcome<u64> {
        match self {
            Sem::Add(f) => ieee::add(f, a, b, RNE),
            Sem::Sub(f) => ieee::sub(f, a, b, RNE),
            Sem::Mul(f) => ieee::mul(f, a, b, RNE),
            Sem::Div(f) => ieee::div(f, a, b, RNE),
            Sem::MinNum(f) => ieee::min_num(f, a, b),
            Sem::MaxNum(f) => ieee::max_num(f, a, b),
            Sem::Min(f) => ieee::min(f, a, b),
            Sem::Max(f) => ieee::max(f, a, b),
            Sem::Fma(f) => ieee::fma(f, a, b, c, RNE),
            Sem::Neg(f) => ieee::neg(f, a),
            Sem::Abs(f) => ieee::abs(f, a),
            Sem::Sqrt(f) => ieee::sqrt(f, a, RNE),
            Sem::Round(f, rm, exact) => ieee::round_to_integral(f, a, rm, exact),
            Sem::ToInt(f, width, signed) => {
                let o = ieee::to_int(f, a, Rounding::TowardZero, width, signed);
                Outcome {
                    value: o.value as u64,
                    flags: o.flags,
                }
            }
            Sem::FromInt(f, width, signed) => {
                ieee::from_int_bits(f, u128::from(a), width, signed, RNE)
            }
            Sem::Cvt(src, dst) => ieee::convert(src, dst, a, RNE),
        }
    }
}

/// How a model's evaluation is read back.
#[derive(Clone, Copy, Debug)]
enum ModelOut {
    /// An FP value on the `f64` carrier.
    Fp(Format),
    /// Raw result bits of a format (a bit-vector model).
    Bits(Format),
    /// An integer of this width.
    Int(u32),
}

struct Model {
    name: &'static str,
    expr: E,
    out: ModelOut,
}

/// A model ready to evaluate: the sampling path's compiled tape when the
/// expression is in its pure bit-vector subset (`FlatProg::compile`, which a
/// property test pins to `try_eval` arm for arm), else `try_eval` itself,
/// the same dispatch `verify_by_evaluation` makes.
struct Evaluator<'m> {
    model: &'m Model,
    tape: Option<FlatProg>,
}

impl<'m> Evaluator<'m> {
    fn new(model: &'m Model, sem: Sem) -> Evaluator<'m> {
        let width = match sem.domain() {
            Domain::Fp(f) | Domain::Pair(f) | Domain::Triple(f) => f.width(),
            Domain::Int(width) => width,
        };
        let inputs: Vec<(String, u32)> = ["a", "b", "c"]
            .iter()
            .map(|n| (n.to_string(), width))
            .collect();
        Evaluator {
            model,
            tape: FlatProg::compile(&model.expr, &inputs),
        }
    }

    fn eval(
        &self,
        env: &EvalEnv,
        scratch: &mut Vec<trust_cg_verify::smt::SVal>,
    ) -> Result<EvalResult, String> {
        match &self.tape {
            Some(tape) => Ok(tape.eval(env, scratch)),
            None => self.model.expr.try_eval(env).map_err(|e| format!("{e:?}")),
        }
    }

    fn how(&self) -> &'static str {
        if self.tape.is_some() {
            "tape"
        } else {
            "try_eval"
        }
    }
}

/// Where a form's word comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Source {
    /// The live encoder, for an opcode the backend selects; ENC-5 decodes it.
    Encoder(Op),
    /// An assembler word for a form the backend never emits.
    Assembler,
}

struct Form {
    label: String,
    sem: Sem,
    word: u32,
    source: Source,
    model: Option<Model>,
}

fn h(n: u16) -> Arg {
    Arg::PReg(PReg::new(165 + n))
}
fn s(n: u16) -> Arg {
    Arg::PReg(PReg::new(128 + n))
}
fn d(n: u16) -> Arg {
    Arg::PReg(PReg::new(96 + n))
}
fn w(n: u16) -> Arg {
    Arg::PReg(PReg::new(32 + n))
}
fn x(n: u16) -> Arg {
    Arg::PReg(PReg::new(n))
}
fn fpr(f: Format, n: u16) -> Arg {
    match f {
        Format::Half => h(n),
        Format::Single => s(n),
        Format::Double => d(n),
    }
}
fn gpr(width: u32, n: u16) -> Arg {
    if width == 32 { w(n) } else { x(n) }
}
fn reg_letter(f: Format) -> char {
    match f {
        Format::Half => 'H',
        Format::Single => 'S',
        Format::Double => 'D',
    }
}
fn gpr_letter(width: u32) -> char {
    if width == 32 { 'W' } else { 'X' }
}

/// `aarch64_semantics` takes an `FPSize` it ignores; binary16 has none, and
/// the H models are built over binary16 leaves, which is what matters.
fn fp_size(f: Format) -> FPSize {
    if f == Format::Double {
        FPSize::Double
    } else {
        FPSize::Single
    }
}

fn eb_sb(f: Format) -> (u32, u32) {
    (f.exp_bits(), f.precision())
}

/// An FP leaf: the raw bits of input slot `name`, bit-cast to `f`.
fn leaf(name: &str, f: Format) -> E {
    let (eb, sb) = eb_sb(f);
    E::bv_bits_to_fp(E::var(name, f.width()), eb, sb)
}

/// The verifier's machine-side model of a form, where one exists.
fn model_for(sem: Sem) -> Option<Model> {
    let a = |f| leaf("a", f);
    let b = |f| leaf("b", f);
    let c = |f| leaf("c", f);
    let fp = |name, expr, f| {
        Some(Model {
            name,
            expr,
            out: ModelOut::Fp(f),
        })
    };
    match sem {
        Sem::Add(f) => fp(
            "encode_fadd_rr",
            sem::encode_fadd_rr(fp_size(f), a(f), b(f)),
            f,
        ),
        Sem::Sub(f) => fp(
            "encode_fsub_rr",
            sem::encode_fsub_rr(fp_size(f), a(f), b(f)),
            f,
        ),
        Sem::Mul(f) => fp(
            "encode_fmul_rr",
            sem::encode_fmul_rr(fp_size(f), a(f), b(f)),
            f,
        ),
        Sem::Div(f) => fp(
            "encode_fdiv_rr",
            sem::encode_fdiv_rr(fp_size(f), a(f), b(f)),
            f,
        ),
        Sem::MinNum(f) => fp(
            "encode_fminnm_rr",
            sem::encode_fminnm_rr(fp_size(f), a(f), b(f)),
            f,
        ),
        Sem::MaxNum(f) => fp(
            "encode_fmaxnm_rr",
            sem::encode_fmaxnm_rr(fp_size(f), a(f), b(f)),
            f,
        ),
        Sem::Fma(f) => fp(
            "encode_fmadd_rr",
            sem::encode_fmadd_rr(fp_size(f), a(f), b(f), c(f)),
            f,
        ),
        Sem::Neg(f) => fp("encode_fneg", sem::encode_fneg(fp_size(f), a(f)), f),
        Sem::Abs(f) => fp("encode_fabs", sem::encode_fabs(fp_size(f), a(f)), f),
        Sem::Sqrt(f) => fp("encode_fsqrt", sem::encode_fsqrt(fp_size(f), a(f)), f),
        Sem::Round(f, Rounding::TowardNegative, false) => {
            fp("encode_frintm", sem::encode_frintm(fp_size(f), a(f)), f)
        }
        Sem::Round(f, Rounding::TowardPositive, false) => {
            fp("encode_frintp", sem::encode_frintp(fp_size(f), a(f)), f)
        }
        Sem::Round(f, Rounding::TowardZero, false) => {
            fp("encode_frintz", sem::encode_frintz(fp_size(f), a(f)), f)
        }
        // FRINTN has no aarch64_semantics model (its gate row is a named
        // deferral); the evaluator's fp.roundToIntegral(RNE) is what an
        // obligation would use.
        Sem::Round(f, Rounding::TiesToEven, false) => fp(
            "fp_round_to_integral(RNE)",
            E::fp_round_to_integral(RoundingMode::RNE, a(f)),
            f,
        ),
        Sem::Round(..) | Sem::Min(_) | Sem::Max(_) => None,
        Sem::ToInt(f, width, signed) => Some(Model {
            name: if signed {
                "encode_fcvtzs"
            } else {
                "encode_fcvtzu"
            },
            expr: if signed {
                sem::encode_fcvtzs(width, a(f))
            } else {
                sem::encode_fcvtzu(width, a(f))
            },
            out: ModelOut::Int(width),
        }),
        Sem::FromInt(f, width, signed) => {
            let (eb, sb) = eb_sb(f);
            let src = E::var("a", width);
            let (name, expr) = if signed {
                ("encode_scvtf", sem::encode_scvtf(eb, sb, src))
            } else {
                // The reconstruction zero-extends the unsigned source first.
                (
                    "encode_ucvtf(zext)",
                    sem::encode_ucvtf(eb, sb, src.zero_ext(width)),
                )
            };
            fp(name, expr, f)
        }
        Sem::Cvt(src, dst) => {
            let half = match (src, dst) {
                (Format::Half, Format::Single) => Some(HalfConversion::HalfToSingle),
                (Format::Half, Format::Double) => Some(HalfConversion::HalfToDouble),
                (Format::Single, Format::Half) => Some(HalfConversion::SingleToHalf),
                (Format::Double, Format::Half) => Some(HalfConversion::DoubleToHalf),
                _ => None,
            };
            match half {
                Some(conv) => Some(Model {
                    name: "arm_fpconvert",
                    expr: arm_fpconvert(conv, &E::var("a", src.width())),
                    out: ModelOut::Bits(dst),
                }),
                None if dst == Format::Double => {
                    fp("encode_fcvt_sd", sem::encode_fcvt_sd(a(src)), dst)
                }
                None => fp("encode_fcvt_ds", sem::encode_fcvt_ds(a(src)), dst),
            }
        }
    }
}

/// Words for the forms the backend never emits (`clang -target
/// arm64-apple-macos -march=armv8.2-a+fp16`, `otool -tvj`), destination
/// register 3 and sources 0/1, like the encoder forms.
fn assembler_forms() -> Vec<(String, Sem, u32)> {
    let mut forms = Vec::new();
    for (f, base) in [
        (Format::Half, 0x1ee0_0000u32),
        (Format::Single, 0x1e20_0000),
        (Format::Double, 0x1e60_0000),
    ] {
        let r = reg_letter(f);
        forms.push((
            format!("FRINTA {r}"),
            Sem::Round(f, Rounding::TiesToAway, false),
            base | 0x6_4003,
        ));
        forms.push((
            format!("FRINTX {r}"),
            Sem::Round(f, RNE, true),
            base | 0x7_4003,
        ));
        forms.push((
            format!("FRINTI {r}"),
            Sem::Round(f, RNE, false),
            base | 0x7_c003,
        ));
        forms.push((format!("FMIN {r}"), Sem::Min(f), base | 0x1_5803));
        forms.push((format!("FMAX {r}"), Sem::Max(f), base | 0x1_4803));
    }
    forms
}

/// Every form, encoder forms first. Panics unless every encoder word decodes
/// to its intent under ENC-5.
fn all_forms() -> Vec<Form> {
    let mut forms = Vec::new();
    let mut push = |label: String, sem: Sem, inst: MachInst| {
        let word = encode_instruction(&inst)
            .unwrap_or_else(|e| panic!("{label}: the encoder refuses {inst:?}: {e:?}"));
        match A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None) {
            DecodeCheckOutcome::Match => {}
            other => panic!("{label}: ENC-5 does not match {word:#010x}: {other:?}"),
        }
        forms.push(Form {
            label,
            sem,
            word,
            source: Source::Encoder(inst.opcode),
            model: model_for(sem),
        });
    };
    for f in Format::ALL {
        let r = reg_letter(f);
        let rrr = |op| MachInst::new(op, vec![fpr(f, 3), fpr(f, 0), fpr(f, 1)]);
        let rr = |op| MachInst::new(op, vec![fpr(f, 3), fpr(f, 0)]);
        for (op, name, sem) in [
            (Op::FaddRR, "FADD", Sem::Add(f)),
            (Op::FsubRR, "FSUB", Sem::Sub(f)),
            (Op::FmulRR, "FMUL", Sem::Mul(f)),
            (Op::FdivRR, "FDIV", Sem::Div(f)),
            (Op::FminnmRR, "FMINNM", Sem::MinNum(f)),
            (Op::FmaxnmRR, "FMAXNM", Sem::MaxNum(f)),
        ] {
            push(format!("{name} {r}"), sem, rrr(op));
        }
        push(
            format!("FMADD {r}"),
            Sem::Fma(f),
            MachInst::new(
                Op::FmaddRR,
                vec![fpr(f, 3), fpr(f, 0), fpr(f, 1), fpr(f, 2)],
            ),
        );
        for (op, name, sem) in [
            (Op::FnegRR, "FNEG", Sem::Neg(f)),
            (Op::FabsRR, "FABS", Sem::Abs(f)),
            (Op::FsqrtRR, "FSQRT", Sem::Sqrt(f)),
            (
                Op::FrintmRR,
                "FRINTM",
                Sem::Round(f, Rounding::TowardNegative, false),
            ),
            (
                Op::FrintpRR,
                "FRINTP",
                Sem::Round(f, Rounding::TowardPositive, false),
            ),
            (
                Op::FrintzRR,
                "FRINTZ",
                Sem::Round(f, Rounding::TowardZero, false),
            ),
            (Op::FrintnRR, "FRINTN", Sem::Round(f, RNE, false)),
        ] {
            push(format!("{name} {r}"), sem, rr(op));
        }
        for width in [32, 64] {
            let g = gpr_letter(width);
            for (op, name, signed) in [
                (Op::FcvtzsRR, "FCVTZS", true),
                (Op::FcvtzuRR, "FCVTZU", false),
            ] {
                push(
                    format!("{name} {g},{r}"),
                    Sem::ToInt(f, width, signed),
                    MachInst::new(op, vec![gpr(width, 10), fpr(f, 0)]),
                );
            }
            for (op, name, signed) in [(Op::ScvtfRR, "SCVTF", true), (Op::UcvtfRR, "UCVTF", false)]
            {
                push(
                    format!("{name} {r},{g}"),
                    Sem::FromInt(f, width, signed),
                    MachInst::new(op, vec![fpr(f, 3), gpr(width, 9)]),
                );
            }
        }
    }
    for (op, src, dst) in [
        (Op::FcvtSD, Format::Single, Format::Double),
        (Op::FcvtDS, Format::Double, Format::Single),
        (Op::FcvtHS, Format::Half, Format::Single),
        (Op::FcvtHD, Format::Half, Format::Double),
        (Op::FcvtSH, Format::Single, Format::Half),
        (Op::FcvtDH, Format::Double, Format::Half),
    ] {
        push(
            format!("FCVT {},{}", reg_letter(dst), reg_letter(src)),
            Sem::Cvt(src, dst),
            MachInst::new(op, vec![fpr(dst, 3), fpr(src, 0)]),
        );
    }
    for (label, sem, word) in assembler_forms() {
        forms.push(Form {
            label,
            sem,
            word,
            source: Source::Assembler,
            model: model_for(sem),
        });
    }
    forms
}

// ===========================================================================
// Comparisons
// ===========================================================================

/// Check one CPU output record against the reference.
fn check_cpu(sem: Sem, out: [u64; 4], want: Outcome<u64>) -> Result<(), String> {
    let [lo, hi, gpr_out, fpsr] = out;
    let mut problems = Vec::new();
    match sem.dest() {
        Dest::Fp(f) => {
            if lo != want.value || hi != 0 {
                problems.push(format!(
                    "{}: got q3 {hi:#018x}:{lo:#018x}, want {:#x}",
                    f.name(),
                    want.value
                ));
            }
            if gpr_out != u64::MAX {
                problems.push(format!("x10 written: {gpr_out:#x}"));
            }
        }
        Dest::Gpr(width) => {
            let mask = if width == 32 { 0xffff_ffff } else { u64::MAX };
            if gpr_out != want.value & mask {
                problems.push(format!(
                    "got x10 {gpr_out:#x}, want {:#x}",
                    want.value & mask
                ));
            }
            if lo != u64::MAX || hi != u64::MAX {
                problems.push(format!("q3 written: {hi:#x}:{lo:#x}"));
            }
        }
    }
    if fpsr != u64::from(want.flags.bits()) {
        problems.push(format!(
            "FPSR {fpsr:#x} [{}], want [{}]",
            Flags(fpsr as u8),
            want.flags
        ));
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("; "))
    }
}

/// The verdict of one model evaluation against the reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ModelVerdict {
    /// Bit-identical.
    Exact,
    /// Both NaN; payload and sign are outside the single-NaN model.
    NanClass,
    /// A signaling operand of FMINNM/FMAXNM: the instruction quiets and
    /// returns it, the single-NaN model returns the other operand.
    SignalingMinMax,
    /// Equal zeros of opposite sign in FMINNM/FMAXNM: the instruction orders
    /// -0 below +0, the model returns its second operand.
    SignedZeroMinMax,
    Mismatch,
}

/// Exact narrowing of an `f64` carrier value to `f`'s bits, through the
/// reference (no host arithmetic); `None` if the carrier does not hold a
/// value of `f`.
fn carrier_bits(f: Format, carrier: f64) -> Option<u64> {
    let bits = carrier.to_bits();
    if f == Format::Double {
        return Some(bits);
    }
    let narrowed = ieee::convert(Format::Double, f, bits, RNE);
    if ieee::is_nan(Format::Double, bits) {
        return Some(narrowed.value);
    }
    (narrowed.flags == Flags::NONE).then_some(narrowed.value)
}

fn judge_model(
    sem: Sem,
    inputs: [u64; 3],
    model: &Model,
    result: EvalResult,
    want: Outcome<u64>,
) -> (ModelVerdict, String) {
    let got = match (model.out, result) {
        (ModelOut::Fp(f), EvalResult::Float(carrier)) => match carrier_bits(f, carrier) {
            Some(bits) => (f, bits),
            None => {
                return (
                    ModelVerdict::Mismatch,
                    format!("carrier {carrier:e} is not a {} value", f.name()),
                );
            }
        },
        (ModelOut::Bits(f), EvalResult::Bv(bits)) => (f, bits & f.mask()),
        (ModelOut::Int(width), EvalResult::Bv(v)) => {
            let mask = if width == 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            };
            return if v & mask == want.value & mask {
                (ModelVerdict::Exact, String::new())
            } else {
                (
                    ModelVerdict::Mismatch,
                    format!("model {v:#x}, reference {:#x}", want.value),
                )
            };
        }
        (out, other) => {
            return (
                ModelVerdict::Mismatch,
                format!("model {out:?} evaluated to {other:?}"),
            );
        }
    };
    let (f, bits) = got;
    if bits == want.value {
        return (ModelVerdict::Exact, String::new());
    }
    let ref_nan = ieee::is_nan(f, want.value);
    let model_nan = ieee::is_nan(f, bits);
    if ref_nan && model_nan {
        return (ModelVerdict::NanClass, String::new());
    }
    if let Sem::MinNum(g) | Sem::MaxNum(g) = sem {
        let [a, b, _] = inputs;
        let signaling = |v| ieee::classify(g, v) == ieee::Class::SignalingNan;
        if ref_nan && (signaling(a) || signaling(b)) {
            return (ModelVerdict::SignalingMinMax, String::new());
        }
        let zero = |v| ieee::classify(g, v) == ieee::Class::Zero;
        if zero(a) && zero(b) && zero(bits) && a != b {
            return (ModelVerdict::SignedZeroMinMax, String::new());
        }
    }
    (
        ModelVerdict::Mismatch,
        format!("model {bits:#x}, reference {:#x}", want.value),
    )
}

// ===========================================================================
// Runner
// ===========================================================================

#[derive(Clone, Debug, Default)]
struct Tally {
    inputs: u64,
    cpu_mismatch: u64,
    cpu_examples: Vec<String>,
    model_counts: BTreeMap<&'static str, u64>,
    model_examples: Vec<String>,
}

impl Tally {
    fn merge(&mut self, other: Tally) {
        self.inputs += other.inputs;
        self.cpu_mismatch += other.cpu_mismatch;
        for e in other.cpu_examples {
            if self.cpu_examples.len() < 8 {
                self.cpu_examples.push(e);
            }
        }
        for (k, v) in other.model_counts {
            *self.model_counts.entry(k).or_default() += v;
        }
        for e in other.model_examples {
            if self.model_examples.len() < 8 {
                self.model_examples.push(e);
            }
        }
    }

    fn model_mismatch(&self) -> u64 {
        self.model_counts.get("mismatch").copied().unwrap_or(0)
    }
}

const CHUNK: usize = 1 << 14;

fn verdict_key(verdict: ModelVerdict) -> &'static str {
    match verdict {
        ModelVerdict::Exact => "exact",
        ModelVerdict::NanClass => "nan-class",
        ModelVerdict::SignalingMinMax => "boundary:signaling-min/max",
        ModelVerdict::SignedZeroMinMax => "boundary:signed-zero-min/max",
        ModelVerdict::Mismatch => "mismatch",
    }
}

/// Run `form` (stub `index` of `page`) over `set` on every lane.
fn run_form(
    page: &exec::Page,
    index: usize,
    form: &Form,
    set: &InputSet,
    with_model: bool,
) -> Tally {
    let workers = threads() as u64;
    let per = set.len.div_ceil(workers);
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|worker| {
                let start = worker * per;
                let end = (start + per).min(set.len);
                scope.spawn(move || {
                    assert_eq!(fpcr(), 0, "worker FPCR is not the process default");
                    let mut tally = Tally::default();
                    let mut env = EvalEnv::default();
                    for name in ["a", "b", "c"] {
                        env.insert(name.to_string(), 0);
                    }
                    let evaluator = form.model.as_ref().map(|m| Evaluator::new(m, form.sem));
                    let mut scratch = Vec::new();
                    let mut input = vec![[0u64; 3]; CHUNK];
                    let mut output = vec![[0u64; 4]; CHUNK];
                    let mut at = start;
                    while at < end {
                        let n = ((end - at) as usize).min(CHUNK);
                        for (i, slot) in input[..n].iter_mut().enumerate() {
                            *slot = set.get(at + i as u64);
                        }
                        page.run(index, &input[..n], &mut output[..n]);
                        for i in 0..n {
                            let inputs = input[i];
                            let want = form.sem.reference(inputs);
                            if let Err(why) = check_cpu(form.sem, output[i], want) {
                                tally.cpu_mismatch += 1;
                                if tally.cpu_examples.len() < 8 {
                                    tally
                                        .cpu_examples
                                        .push(format!("{} {:x?}: {why}", form.label, inputs));
                                }
                            }
                            if let (true, Some(evaluator)) = (with_model, &evaluator) {
                                let model = evaluator.model;
                                for (slot, value) in inputs.iter().enumerate() {
                                    env.set_at(slot, *value);
                                }
                                let (verdict, why) = match evaluator.eval(&env, &mut scratch) {
                                    Ok(result) => {
                                        judge_model(form.sem, inputs, model, result, want)
                                    }
                                    Err(e) => {
                                        (ModelVerdict::Mismatch, format!("evaluation error {e}"))
                                    }
                                };
                                *tally.model_counts.entry(verdict_key(verdict)).or_default() += 1;
                                if verdict == ModelVerdict::Mismatch
                                    && tally.model_examples.len() < 8
                                {
                                    tally.model_examples.push(format!(
                                        "{} [{}] {:x?}: {why}",
                                        form.label, model.name, inputs
                                    ));
                                }
                            }
                        }
                        tally.inputs += n as u64;
                        at += n as u64;
                    }
                    tally
                })
            })
            .collect();
        let mut total = Tally::default();
        for handle in handles {
            total.merge(handle.join().expect("worker"));
        }
        total
    })
}

struct Outcomes {
    lines: Vec<String>,
    failures: Vec<String>,
}

/// Run every form whose domain `select` accepts, print one line per form and
/// return the failures.
fn run_domain(select: impl Fn(Domain) -> Option<InputSet>, with_model: bool) -> Outcomes {
    require_fp16();
    assert_eq!(
        fpcr(),
        0,
        "FPCR is not the process default (RN, no FZ/DN/AH)"
    );
    let forms = all_forms();
    let page = exec::Page::new(&forms.iter().map(|f| f.word).collect::<Vec<_>>());
    let mut sets: BTreeMap<Domain, InputSet> = BTreeMap::new();
    let mut outcomes = Outcomes {
        lines: Vec::new(),
        failures: Vec::new(),
    };
    for (index, form) in forms.iter().enumerate() {
        let domain = form.sem.domain();
        let set = match sets.get(&domain) {
            Some(set) => set.clone(),
            None => match select(domain) {
                Some(set) => {
                    sets.insert(domain, set.clone());
                    set
                }
                None => continue,
            },
        };
        let started = Instant::now();
        let tally = run_form(&page, index, form, &set, with_model);
        let secs = started.elapsed().as_secs_f64();
        let model = match (&form.model, with_model) {
            (Some(m), true) => format!(
                "{} [{}] {}",
                m.name,
                Evaluator::new(m, form.sem).how(),
                tally
                    .model_counts
                    .iter()
                    .map(|(k, v)| format!("{k}={v}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            (Some(_), false) => "model not run".into(),
            (None, _) => "no verifier model".into(),
        };
        let source = match form.source {
            Source::Encoder(op) => format!("encoder {op:?}, ENC-5 match"),
            Source::Assembler => "assembler word, not emitted".into(),
        };
        let line = format!(
            "{:<14} {:<11} inputs={:<11} cpu+reference mismatches={} | {model} | {source} | {secs:.1}s | {}",
            form.label,
            set.strength(),
            tally.inputs,
            tally.cpu_mismatch,
            set.name
        );
        println!("{line}");
        record(form, &set, &tally, secs);
        outcomes.lines.push(line);
        for e in tally.cpu_examples.iter().chain(tally.model_examples.iter()) {
            println!("    {e}");
        }
        if tally.cpu_mismatch != 0 {
            outcomes.failures.push(format!(
                "{}: {} CPU/reference mismatches, e.g. {:?}",
                form.label, tally.cpu_mismatch, tally.cpu_examples
            ));
        }
        if tally.model_mismatch() != 0 {
            outcomes.failures.push(format!(
                "{}: {} model/reference mismatches, e.g. {:?}",
                form.label,
                tally.model_mismatch(),
                tally.model_examples
            ));
        }
        assert_eq!(tally.inputs, set.len, "{}: not every input ran", form.label);
    }
    outcomes
}

/// Append one JSON line for a run when `TRUST_CG_FP_IEEE_RECORD` names a file.
fn record(form: &Form, set: &InputSet, tally: &Tally, secs: f64) {
    let Ok(path) = std::env::var("TRUST_CG_FP_IEEE_RECORD") else {
        return;
    };
    let line = serde_json::json!({
        "form": form.label,
        "source": match form.source {
            Source::Encoder(op) => format!("{op:?}"),
            Source::Assembler => "assembler".into(),
        },
        "set": set.name,
        "strength": set.strength(),
        "inputs": tally.inputs,
        "cpu_reference_mismatches": tally.cpu_mismatch,
        "model": form.model.as_ref().map(|m| m.name),
        "model_verdicts": tally.model_counts,
        "seconds": (secs * 10.0).round() / 10.0,
        "threads": threads(),
    });
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .unwrap_or_else(|e| panic!("open {path}: {e}"));
    writeln!(file, "{line}").expect("record line");
}

#[track_caller]
fn require_clean(outcomes: Outcomes) {
    assert!(
        outcomes.failures.is_empty(),
        "differential failures:\n{}",
        outcomes.failures.join("\n")
    );
    assert!(!outcomes.lines.is_empty(), "no form ran");
}

// ===========================================================================
// Tests
// ===========================================================================

/// The comparisons assume the default FPCR; every encoder word decodes to its
/// intent under ENC-5, the inventory of forms is pinned, and every form the
/// backend emits has a verifier model except FMIN/FMAX/FRINTA/X/I, which it
/// never emits.
#[test]
fn fpcr_and_form_inventory() {
    require_fp16();
    assert_eq!(fpcr(), 0, "FPCR is not the process default");
    let forms = all_forms();
    let encoder = forms
        .iter()
        .filter(|f| matches!(f.source, Source::Encoder(_)))
        .count();
    let assembler = forms.len() - encoder;
    // Per format: 6 binary + FMADD + 7 unary + 4 FCVTZ* + 4 *CVTF = 22, and
    // the 6 precision conversions.
    assert_eq!((encoder, assembler), (3 * 22 + 6, 15));
    for form in &forms {
        let modeled = form.model.is_some();
        match form.source {
            Source::Encoder(_) => assert!(modeled, "{}: emitted form without a model", form.label),
            Source::Assembler => assert!(
                !modeled
                    || matches!(
                        form.sem,
                        Sem::Round(_, RNE, _) | Sem::Round(_, Rounding::TiesToAway, _)
                    ),
                "{}",
                form.label
            ),
        }
    }
    let mut words: Vec<u32> = forms.iter().map(|f| f.word).collect();
    words.sort_unstable();
    words.dedup();
    assert_eq!(words.len(), forms.len(), "two forms share a word");
    // The coverage gate's named evidence names exactly these encoder forms,
    // with the input space each one runs over.
    let named: Vec<(String, Op, Domain)> = evidence::forms()
        .into_iter()
        .map(|f| {
            let domain = match f.space {
                InputSpace::Fp(g) => Domain::Fp(g),
                InputSpace::Int(width) => Domain::Int(width),
                InputSpace::Pairs(g) => Domain::Pair(g),
                InputSpace::Triples(g) => Domain::Triple(g),
            };
            (f.label, f.opcode, domain)
        })
        .collect();
    let run: Vec<(String, Op, Domain)> = forms
        .iter()
        .filter_map(|f| match f.source {
            Source::Encoder(op) => Some((f.label.clone(), op, f.sem.domain())),
            Source::Assembler => None,
        })
        .collect();
    assert_eq!(
        run, named,
        "the gate's named FP evidence and the differential disagree"
    );
}

/// Every binary16-source form over every binary16 encoding: EXHAUSTIVE.
#[test]
fn binary16_sources_exhaustive() {
    require_clean(run_domain(
        |domain| matches!(domain, Domain::Fp(Format::Half)).then(|| single_set(Format::Half)),
        true,
    ));
}

/// Every binary32-source form: statistical here, every encoding under the
/// exhaustive switch.
#[test]
fn binary32_sources() {
    require_clean(run_domain(
        |domain| matches!(domain, Domain::Fp(Format::Single)).then(|| single_set(Format::Single)),
        true,
    ));
}

/// Every binary64-source form: boundary classes and a stratified sample.
#[test]
fn binary64_sources() {
    require_clean(run_domain(
        |domain| matches!(domain, Domain::Fp(Format::Double)).then(|| single_set(Format::Double)),
        true,
    ));
}

/// SCVTF/UCVTF from W (every 32-bit integer under the exhaustive switch) and
/// X registers.
#[test]
fn integer_sources() {
    require_clean(run_domain(
        |domain| match domain {
            Domain::Int(width) => Some(int_set(width)),
            _ => None,
        },
        true,
    ));
}

/// Binary16 pairs: every encoding against the edge set (every pair under the
/// exhaustive switch).
#[test]
fn binary16_pairs() {
    require_clean(run_domain(
        |domain| matches!(domain, Domain::Pair(Format::Half)).then(|| pair_set(Format::Half)),
        true,
    ));
}

/// Binary32 and binary64 pairs and every format's fused multiply-add triples.
#[test]
fn wide_pairs_and_fused_triples() {
    require_clean(run_domain(
        |domain| match domain {
            Domain::Pair(Format::Single) => Some(pair_set(Format::Single)),
            Domain::Pair(Format::Double) => Some(pair_set(Format::Double)),
            Domain::Triple(f) => Some(triple_set(f)),
            _ => None,
        },
        true,
    ));
}

/// The differential has teeth: a reference read with the wrong rounding
/// direction, a model with the wrong conversion, and a corrupted word each
/// disagree with the CPU on these sets.
#[test]
fn wrong_references_models_and_words_disagree() {
    require_fp16();
    let forms = all_forms();
    let find = |label: &str| {
        forms
            .iter()
            .position(|f| f.label == label)
            .unwrap_or_else(|| panic!("no form {label}"))
    };
    let page = exec::Page::new(&forms.iter().map(|f| f.word).collect::<Vec<_>>());
    let run = |index: usize, inputs: &[[u64; 3]]| {
        let mut out = vec![[0u64; 4]; inputs.len()];
        page.run(index, inputs, &mut out);
        out
    };
    let halves: Vec<[u64; 3]> = (0..=0xffffu64).map(|a| [a, 0, 0]).collect();
    // 1. FCVTZS read with round-to-nearest instead of toward zero.
    let fcvtzs = find("FCVTZS W,H");
    let out = run(fcvtzs, &halves);
    let wrong_rounding = halves
        .iter()
        .zip(&out)
        .filter(|(inp, o)| {
            let wrong = ieee::to_int(Format::Half, inp[0], RNE, 32, true);
            o[2] != wrong.value as u64 & 0xffff_ffff
        })
        .count();
    assert!(
        wrong_rounding > 1000,
        "RNE-for-RTZ reference agreed: {wrong_rounding}"
    );
    // 2. FRINTM's model swapped for FRINTP's.
    let frintm = find("FRINTM H");
    let out = run(frintm, &halves);
    let wrong_model = sem::encode_frintp(FPSize::Single, leaf("a", Format::Half));
    let mut env = EvalEnv::default();
    env.insert("a".into(), 0);
    let mut model_disagree = 0;
    for (inp, o) in halves.iter().zip(&out) {
        env.set_at(0, inp[0]);
        if let Ok(EvalResult::Float(c)) = wrong_model.try_eval(&env)
            && carrier_bits(Format::Half, c) != Some(o[0])
            && !ieee::is_nan(Format::Half, o[0])
        {
            model_disagree += 1;
        }
    }
    assert!(
        model_disagree > 1000,
        "FRINTP model agreed with FRINTM: {model_disagree}"
    );
    // 3. FADD H's word with the opcode field of FSUB (bit 12) and with a
    // different destination register.
    let fadd = find("FADD H");
    let corrupted = [forms[fadd].word ^ (1 << 12), (forms[fadd].word & !0x1f) | 4];
    let bad_page = exec::Page::new(&corrupted);
    let pairs: Vec<[u64; 3]> = (0..4096u64)
        .map(|i| [0x3c00 + (i & 0x3ff), 0x3800 + ((i * 7) & 0x3ff), 0])
        .collect();
    for index in 0..corrupted.len() {
        let mut out = vec![[0u64; 4]; pairs.len()];
        bad_page.run(index, &pairs, &mut out);
        let disagree = pairs
            .iter()
            .zip(&out)
            .filter(|(inp, o)| {
                check_cpu(
                    Sem::Add(Format::Half),
                    **o,
                    Sem::Add(Format::Half).reference(**inp),
                )
                .is_err()
            })
            .count();
        assert_eq!(
            disagree,
            pairs.len(),
            "corruption {index} agreed on some input"
        );
    }
}

/// The two named boundaries of the single-NaN model are exactly what the
/// differential counts them as: on a signaling operand FMINNM/FMAXNM return
/// the quieted NaN (Invalid Operation) where `encode_fminnm_rr` /
/// `encode_fmaxnm_rr` return the other operand, and on zeros of opposite sign
/// the instruction orders -0 below +0 where the model returns its second
/// operand. Everything else of those forms agrees bit for bit. TrustIR's
/// `FMin`/`FMax` lowering quiets its operands first and admits either zero
/// (`trust-cg-codegen/tests/e2e_aarch64_fp_ieee_lowering.rs`).
#[test]
fn single_nan_model_boundaries_are_the_named_ones() {
    require_fp16();
    let forms = all_forms();
    let page = exec::Page::new(&forms.iter().map(|f| f.word).collect::<Vec<_>>());
    for (label, is_min) in [("FMINNM S", true), ("FMAXNM S", false)] {
        let index = forms.iter().position(|f| f.label == label).expect("form");
        let form = &forms[index];
        let model = form.model.as_ref().expect("model");
        let one = 0x3f80_0000u64;
        let (zero, neg_zero, snan) = (0u64, 0x8000_0000u64, 0x7f80_0001u64);
        let cases = [
            ([snan, one, 0], ModelVerdict::SignalingMinMax),
            ([one, snan, 0], ModelVerdict::SignalingMinMax),
            (
                if is_min {
                    [neg_zero, zero, 0]
                } else {
                    [zero, neg_zero, 0]
                },
                ModelVerdict::SignedZeroMinMax,
            ),
            (
                if is_min {
                    [zero, neg_zero, 0]
                } else {
                    [neg_zero, zero, 0]
                },
                ModelVerdict::Exact,
            ),
            ([0x7fc0_0001, one, 0], ModelVerdict::Exact),
        ];
        let inputs: Vec<[u64; 3]> = cases.iter().map(|(i, _)| *i).collect();
        let mut out = vec![[0u64; 4]; inputs.len()];
        page.run(index, &inputs, &mut out);
        let mut env = EvalEnv::default();
        for name in ["a", "b", "c"] {
            env.insert(name.to_string(), 0);
        }
        for ((input, verdict), cpu) in cases.iter().zip(&out) {
            let want = form.sem.reference(*input);
            check_cpu(form.sem, *cpu, want).unwrap_or_else(|e| panic!("{label} {input:x?}: {e}"));
            for (slot, value) in input.iter().enumerate() {
                env.set_at(slot, *value);
            }
            let result = model.expr.try_eval(&env).expect("evaluates");
            let (got, why) = judge_model(form.sem, *input, model, result, want);
            assert_eq!(got, *verdict, "{label} {input:x?}: {why}");
        }
        let snan_result = form.sem.reference([snan, one, 0]);
        assert_eq!(
            (snan_result.value, snan_result.flags),
            (0x7fc0_0001, Flags::INVALID),
            "{label}: FMINNM/FMAXNM quiet a signaling operand"
        );
    }
}

/// The committed record of the recorded release run
/// (`fixtures/fp_ieee_exhaustive/`, revision and command in its `run.json`)
/// covers every form this target runs, each named form at the strength the
/// coverage gate's evidence note claims for its input space (all 2^16 or 2^32
/// inputs where exhaustive), with no CPU/reference and no model/reference
/// disagreement and the model run on every input of every modeled form.
#[test]
fn recorded_exhaustive_run_covers_every_named_form() {
    let run: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/fp_ieee_exhaustive/run.json"))
            .expect("run.json");
    let revision = run["revision"].as_str().expect("revision");
    assert!(
        revision.len() == 40 && revision.bytes().all(|b| b.is_ascii_hexdigit()),
        "{revision}"
    );
    let lines: Vec<serde_json::Value> =
        include_str!("fixtures/fp_ieee_exhaustive/differential.jsonl")
            .lines()
            .map(|line| serde_json::from_str(line).expect("record line"))
            .collect();
    let forms = all_forms();
    assert_eq!(lines.len(), forms.len(), "one record line per form");
    for line in &lines {
        let form = line["form"].as_str().expect("form");
        assert_eq!(line["cpu_reference_mismatches"], 0, "{form}");
        let verdicts = line["model_verdicts"].as_object().expect("verdicts");
        assert!(!verdicts.contains_key("mismatch"), "{form}: {verdicts:?}");
        let modeled: u64 = verdicts.values().map(|v| v.as_u64().expect("count")).sum();
        let has_model = forms
            .iter()
            .find(|f| f.label == form)
            .unwrap_or_else(|| panic!("record names an unknown form {form}"))
            .model
            .is_some();
        let inputs = line["inputs"].as_u64().expect("inputs");
        assert_eq!(modeled, if has_model { inputs } else { 0 }, "{form}");
    }
    for named in evidence::forms() {
        let line = lines
            .iter()
            .find(|l| l["form"] == named.label.as_str())
            .unwrap_or_else(|| panic!("the record lacks {}", named.label));
        assert_eq!(
            line["strength"],
            named.space.recorded_strength().label(),
            "{}",
            named.label
        );
        if let Some(size) = named.space.exhaustive_size() {
            assert_eq!(line["inputs"], size, "{}", named.label);
        }
    }
}
