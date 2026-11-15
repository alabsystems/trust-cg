// Copyright 2026 Andrew Yates | Apache-2.0
//! Live silicon differential of the in-house NEON semantic models (ledger
//! `L04-P6`).
//!
//! The NEON obligations the coverage gate credits state each emitted
//! instruction's MACHINE side with the `neon_semantics::encode_neon_*` models
//! (and, for the post-index transfers, the word-bound memory-effect parts of
//! `aarch64_memory_effect`). The recorded silicon fixtures
//! (`aarch64_neon_silicon_truth.json`, `aarch64_neon_fp_silicon_truth.json`)
//! cover 24 integer and 14 FP operations; the widening, dot-product, pairwise,
//! permute, lane-move, horizontal and fused/convert models had no hardware
//! differential. This target runs every one of them on the host CPU.
//!
//! For every NEON value opcode the coverage gate audits, every form the live
//! encoder (`trust_cg_codegen::aarch64::encode::encode_instruction`) admits —
//! each arrangement, lane, element size, immediate, shift amount and
//! destination class — is
//!
//! 1. encoded by the real encoder, and the word checked by ENC-5
//!    (`A64DecodeCheck`) to decode to its intent;
//! 2. executed on this CPU inside a small JIT stub that loads `Vn`/`Vm`/`Vd`
//!    and two GPRs from memory, runs the word, and stores every register the
//!    word could write back to memory;
//! 3. compared with the model the verifier uses for that form, evaluated over
//!    the same inputs by `SmtExpr::try_eval` (the evaluator the obligations'
//!    sampling lane uses), built over the same `Var` leaves and lane splits as
//!    the obligations' machine sides.
//!
//! Inputs are exhaustive where the lane is narrow (every byte pair for binary
//! byte-lane forms, every byte for unary ones, every `imm8` for MOVI) and an
//! edge-value grid plus deterministic pseudo-random vectors otherwise. The
//! sources and every register the word must not write are compared too. An FP
//! lane whose model and silicon results are both NaN is counted as a NaN-class
//! match (the model returns the default NaN, the CPU propagates payloads); every
//! other lane must match bit for bit.
//!
//! Encoder-admitted forms that no value model covers are listed, pinned and
//! disclosed (`encoder_only_forms`): no lowering emits them, and they carry no
//! value obligation. The word-bound lane-effect decomposition admits all 29 of
//! them (DUP (element) into a `D` register, REV64 `.8B`), so its parts are run
//! on this CPU for those forms too (`encoder_only_lane_effect_forms_match_silicon`).
//!
//! This is testing evidence about the models on one CPU over finitely many
//! inputs, not a proof, and it credits nothing.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand as Arg, PReg};
use trust_cg_verify::aarch64_neon_lane_effect::{
    NeonLaneEffectDecomposition, NeonLaneEffectPart, check_emitted_neon_lane_effect_word,
    neon_lane_effect,
};
use trust_cg_verify::fp_bitmodel;
use trust_cg_verify::neon_semantics as ns;
use trust_cg_verify::smt::{
    EvalEnv, EvalResult, SmtExpr as E, VectorArrangement as A, lane_extract,
};

// ===========================================================================
// Executable stubs
// ===========================================================================

/// The registers every stub binds: `Vn = v0`, `Vm = v1`, `Vd = v2`, the GPR
/// source `x9` and the GPR destination `x10`.
const VN: u16 = 0;
const VM: u16 = 1;
const VD: u16 = 2;
const XN: u16 = 9;
const XD: u16 = 10;

/// `ldr q0,[x0]; ldr q1,[x0,#16]; ldr q2,[x0,#32]; ldr x9,[x0,#48];
/// ldr x10,[x0,#56]` (words assembled by `clang -target arm64-apple-macos`).
const PROLOGUE: [u32; 5] = [
    0x3dc0_0000,
    0x3dc0_0401,
    0x3dc0_0802,
    0xf940_1809,
    0xf940_1c0a,
];
/// `str q2,[x1]; str x10,[x1,#16]; str x9,[x1,#24]; str q0,[x1,#32];
/// str q1,[x1,#48]; ret`.
const EPILOGUE: [u32; 6] = [
    0x3d80_0022,
    0xf900_082a,
    0xf900_0c29,
    0x3d80_0820,
    0x3d80_0c21,
    0xd65f_03c0,
];
/// Bytes per stub (12 words, padded to a cache-friendly stride).
const STUB_BYTES: usize = 64;

/// One stub's architectural inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Input {
    vn: u128,
    vm: u128,
    vd: u128,
    xn: u64,
    xd: u64,
}

/// What a stub stores back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Output {
    vd: u128,
    xd: u64,
    xn: u64,
    vn: u128,
    vm: u128,
}

mod exec {
    use super::{EPILOGUE, Input, Output, PROLOGUE, STUB_BYTES};

    type Stub = unsafe extern "C" fn(*const u64, *mut u64);

    #[cfg(target_os = "macos")]
    unsafe extern "C" {
        fn pthread_jit_write_protect_np(enabled: libc::c_int);
        fn sys_icache_invalidate(start: *mut libc::c_void, len: libc::size_t);
    }

    /// An executable mapping holding one stub per word.
    pub struct Page {
        base: *mut u8,
        len: usize,
        stubs: usize,
    }

    // SAFETY: the mapping is immutable once published; stubs only read their
    // input block and write their output block.
    unsafe impl Send for Page {}
    unsafe impl Sync for Page {}

    impl Page {
        pub fn new(words: &[u32]) -> Page {
            let mut code = Vec::with_capacity(words.len() * STUB_BYTES);
            for &word in words {
                let start = code.len();
                for w in PROLOGUE.iter().chain([word].iter()).chain(EPILOGUE.iter()) {
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

        /// Run stub `index` once.
        pub fn run(&self, index: usize, input: &Input) -> Output {
            assert!(index < self.stubs);
            let block: [u64; 8] = [
                input.vn as u64,
                (input.vn >> 64) as u64,
                input.vm as u64,
                (input.vm >> 64) as u64,
                input.vd as u64,
                (input.vd >> 64) as u64,
                input.xn,
                input.xd,
            ];
            let mut out = [0u64; 8];
            // SAFETY: the stub reads 64 bytes of `block`, writes 64 bytes of
            // `out`, clobbers only caller-saved v0-v2/x9/x10 and returns; a
            // memory-touching word reads or writes through x9, which the
            // memory tests point at their own buffers.
            unsafe {
                let stub: Stub = std::mem::transmute(self.base.add(index * STUB_BYTES));
                stub(block.as_ptr(), out.as_mut_ptr());
            }
            let wide = |lo: u64, hi: u64| u128::from(lo) | (u128::from(hi) << 64);
            Output {
                vd: wide(out[0], out[1]),
                xd: out[2],
                xn: out[3],
                vn: wide(out[4], out[5]),
                vm: wide(out[6], out[7]),
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

// ===========================================================================
// Operands
// ===========================================================================

fn v(n: u16) -> Arg {
    Arg::PReg(PReg::new(64 + n))
}
fn d(n: u16) -> Arg {
    Arg::PReg(PReg::new(96 + n))
}
fn s(n: u16) -> Arg {
    Arg::PReg(PReg::new(128 + n))
}
fn x(n: u16) -> Arg {
    Arg::PReg(PReg::new(n))
}
fn w(n: u16) -> Arg {
    Arg::PReg(PReg::new(32 + n))
}
fn imm(value: i64) -> Arg {
    Arg::Imm(value)
}

/// The integer arrangement selector every NEON operand list ends with.
fn arrangement(selector: i64) -> Option<A> {
    Some(match selector {
        0 => A::B8,
        1 => A::B16,
        2 => A::H4,
        3 => A::H8,
        4 => A::S2,
        5 => A::S4,
        6 => A::D2,
        _ => return None,
    })
}

/// The FP arrangement selector (`0 = .2S`, `1 = .4S`, `2 = .2D`).
fn fp_arrangement(selector: i64) -> Option<A> {
    Some(match selector {
        0 => A::S2,
        1 => A::S4,
        2 => A::D2,
        _ => return None,
    })
}

/// The 128-bit arrangement of an element size in bytes.
fn element_arrangement(bytes: i64) -> Option<A> {
    Some(match bytes {
        1 => A::B16,
        2 => A::H8,
        4 => A::S4,
        8 => A::D2,
        _ => return None,
    })
}

// ===========================================================================
// Models
// ===========================================================================

/// A vector input leaf, exactly as the obligations name it: a 128-bit view is
/// `Concat(<p>_hi, <p>_lo)`, a 64-bit view is `<p>_lo`.
fn vec_var(prefix: &str, bits: u32) -> E {
    let lo = E::var(format!("{prefix}_lo"), 64);
    if bits <= 64 {
        lo
    } else {
        E::var(format!("{prefix}_hi"), 64).concat(lo)
    }
}

fn xn_var() -> E {
    E::var("xn", 64)
}

/// IEEE parameters of a 32- or 64-bit FP lane.
fn fp_params(lane_bits: u32) -> (u32, u32) {
    if lane_bits == 32 { (8, 24) } else { (11, 53) }
}

/// FP lanes of a vector leaf, the machine-side split of the FP obligations:
/// `bv_bits_to_fp(lane_extract(reg, arr, i))`.
fn fp_lanes(prefix: &str, arr: A) -> Vec<E> {
    let reg = vec_var(prefix, arr.total_bits());
    let (eb, sb) = fp_params(arr.lane_bits());
    (0..arr.lane_count())
        .map(|i| E::bv_bits_to_fp(lane_extract(&reg, arr, i), eb, sb))
        .collect()
}

/// Where a form writes its result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Dest {
    /// `Vd` at `bits` (64: Q=0, the upper half is zeroed).
    Vector(u32),
    /// A scalar SIMD&FP register `Sd`/`Dd` of `bits`; the rest of `Qd` is zeroed.
    Scalar(u32),
    /// `Wd` (zero-extends into `Xd`) or `Xd`.
    Gpr(u32),
}

#[derive(Clone, Debug)]
enum Model {
    /// A bit-vector expression over the input leaves.
    Bits { expr: E, dest: Dest },
    /// Per-lane FP or mask expressions written to `Vd`.
    Lanes {
        lanes: Vec<E>,
        lane_bits: u32,
        total_bits: u32,
        fp_result: bool,
    },
}

/// How a form's inputs are generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Gen {
    /// Every pair of byte values across `Vn`/`Vm` byte lanes (binary byte ops).
    BytePairs(u32),
    /// Every byte pair across adjacent (even, odd) `Vn` byte lanes.
    AdjacentBytePairs,
    /// Every byte value in every `Vn` byte lane.
    Bytes,
    /// Every triple of integer edge values of this lane width.
    Wide(u32),
    /// Every triple of FP edge values of this lane width, then random
    /// near-magnitude FP vectors.
    Fp(u32),
    /// A handful of random vectors (the result does not depend on the inputs).
    Constant,
}

/// One encoder-admitted form.
struct Form {
    op: Op,
    label: String,
    inst: MachInst,
    word: u32,
    model: Model,
    generator: Gen,
}

fn bits(expr: E, dest: Dest) -> Model {
    Model::Bits { expr, dest }
}

fn lanes(lanes: Vec<E>, arr: A, fp_result: bool) -> Model {
    Model::Lanes {
        lanes,
        lane_bits: arr.lane_bits(),
        total_bits: arr.total_bits(),
        fp_result,
    }
}

fn wide_or_bytes(arr: A, binary: bool) -> Gen {
    match (arr.lane_bits(), binary) {
        (8, true) => Gen::BytePairs(arr.lane_count()),
        (8, false) => Gen::Bytes,
        (bits, _) => Gen::Wide(bits),
    }
}

/// The model the verifier uses for `inst`, or `None` when no model covers the
/// form (an encoder-only form).
fn model_for(inst: &MachInst) -> Option<(Model, Gen)> {
    let ops = &inst.operands;
    let last_imm = || match ops.last() {
        Some(Arg::Imm(value)) => Some(*value),
        _ => None,
    };
    let imm_at = |i: usize| match ops.get(i) {
        Some(Arg::Imm(value)) => Some(*value),
        _ => None,
    };
    let lane_vec = |arr: A, prefix: &str| vec_var(prefix, arr.total_bits());
    use Op as O;
    Some(match inst.opcode {
        // ---- lane-wise integer, three registers ----
        O::NeonAddV
        | O::NeonSubV
        | O::NeonMulV
        | O::NeonSmaxV
        | O::NeonSminV
        | O::NeonUmaxV
        | O::NeonUminV
        | O::NeonCmeqV
        | O::NeonCmgtV
        | O::NeonCmgeV
        | O::NeonCmhiV
        | O::NeonCmhsV => {
            let arr = arrangement(last_imm()?)?;
            let (n, m) = (lane_vec(arr, "vn"), lane_vec(arr, "vm"));
            let expr = match inst.opcode {
                O::NeonAddV => ns::encode_neon_add(arr, &n, &m),
                O::NeonSubV => ns::encode_neon_sub(arr, &n, &m),
                O::NeonMulV => ns::encode_neon_mul(arr, &n, &m),
                O::NeonSmaxV => ns::encode_neon_smax(arr, &n, &m),
                O::NeonSminV => ns::encode_neon_smin(arr, &n, &m),
                O::NeonUmaxV => ns::encode_neon_umax(arr, &n, &m),
                O::NeonUminV => ns::encode_neon_umin(arr, &n, &m),
                O::NeonCmeqV => ns::encode_neon_cmeq(arr, &n, &m),
                O::NeonCmgtV => ns::encode_neon_cmgt(arr, &n, &m),
                O::NeonCmgeV => ns::encode_neon_cmge(arr, &n, &m),
                O::NeonCmhiV => ns::encode_neon_cmhi(arr, &n, &m),
                _ => ns::encode_neon_cmhs(arr, &n, &m),
            };
            (
                bits(expr, Dest::Vector(arr.total_bits())),
                wide_or_bytes(arr, true),
            )
        }
        O::NeonMlaV => {
            let arr = arrangement(last_imm()?)?;
            let expr = ns::encode_neon_mla(
                arr,
                &lane_vec(arr, "vd"),
                &lane_vec(arr, "vn"),
                &lane_vec(arr, "vm"),
            );
            (
                bits(expr, Dest::Vector(arr.total_bits())),
                wide_or_bytes(arr, true),
            )
        }
        // ---- whole-register bitwise ----
        O::NeonAndV | O::NeonOrrV | O::NeonEorV | O::NeonBicV | O::NeonBitV | O::NeonNotV => {
            let width = logic_width(inst)?;
            let (n, m, dd) = (
                vec_var("vn", width),
                vec_var("vm", width),
                vec_var("vd", width),
            );
            let expr = match inst.opcode {
                O::NeonAndV => ns::encode_neon_and(&n, &m),
                O::NeonOrrV => ns::encode_neon_orr(&n, &m),
                O::NeonEorV => ns::encode_neon_eor(&n, &m),
                O::NeonBicV => ns::encode_neon_bic(&n, &m),
                O::NeonBitV => ns::encode_neon_bit(&dd, &n, &m),
                _ => ns::encode_neon_not(&n),
            };
            (bits(expr, Dest::Vector(width)), Gen::Wide(64))
        }
        // ---- immediate shifts ----
        O::NeonShlVImm | O::NeonUshrVImm | O::NeonSshrVImm => {
            let arr = arrangement(last_imm()?)?;
            let amount = u32::try_from(imm_at(2)?).ok()?;
            let n = lane_vec(arr, "vn");
            let expr = match inst.opcode {
                O::NeonShlVImm if amount < arr.lane_bits() => ns::encode_neon_shl(arr, &n, amount),
                O::NeonUshrVImm if (1..=arr.lane_bits()).contains(&amount) => {
                    ns::encode_neon_ushr(arr, &n, amount)
                }
                O::NeonSshrVImm if (1..=arr.lane_bits()).contains(&amount) => {
                    ns::encode_neon_sshr(arr, &n, amount)
                }
                _ => return None,
            };
            (
                bits(expr, Dest::Vector(arr.total_bits())),
                wide_or_bytes(arr, false),
            )
        }
        // ---- byte permutes ----
        O::NeonRbitV | O::NeonRev32V | O::NeonRev64V => {
            let arr = arrangement(last_imm()?)?;
            let n = vec_var("vn", 128);
            let expr = match (inst.opcode, arr) {
                (O::NeonRbitV, A::B16) => ns::encode_neon_rbit_16b(&n),
                (O::NeonRbitV, A::B8) => ns::encode_neon_rbit_8b(&n),
                (O::NeonRev32V, A::B16) => ns::encode_neon_rev32_16b(&n),
                (O::NeonRev32V, A::B8) => ns::encode_neon_rev32_8b(&n),
                (O::NeonRev64V, A::B16) => ns::encode_neon_rev64_16b(&n),
                (O::NeonRev64V, A::S4) => ns::encode_neon_rev64_4s(&n),
                _ => return None,
            };
            (bits(expr, Dest::Vector(128)), Gen::Bytes)
        }
        O::NeonCntV => {
            let arr = arrangement(last_imm()?)?;
            if arr.lane_bits() != 8 {
                return None;
            }
            let expr = ns::encode_neon_cnt(arr, &lane_vec(arr, "vn"));
            (bits(expr, Dest::Vector(arr.total_bits())), Gen::Bytes)
        }
        O::NeonUaddlpV | O::NeonSaddlpV => {
            let arr = arrangement(last_imm()?)?;
            if !matches!(arr, A::B16 | A::H8) {
                return None;
            }
            let n = vec_var("vn", 128);
            let expr = if inst.opcode == O::NeonUaddlpV {
                ns::encode_neon_uaddlp(arr, &n)
            } else {
                ns::encode_neon_saddlp(arr, &n)
            };
            let generator = if arr == A::B16 {
                Gen::AdjacentBytePairs
            } else {
                Gen::Wide(arr.lane_bits())
            };
            (bits(expr, Dest::Vector(128)), generator)
        }
        O::NeonAbsV => {
            let arr = arrangement(last_imm()?)?;
            let expr = ns::encode_neon_abs(arr, &lane_vec(arr, "vn"));
            (
                bits(expr, Dest::Vector(arr.total_bits())),
                wide_or_bytes(arr, false),
            )
        }
        // ---- widening, dot and accumulate ----
        O::NeonUdotV => {
            if arrangement(last_imm()?)? != A::B16 {
                return None;
            }
            let expr = ns::encode_neon_udot(
                A::B16,
                &vec_var("vd", 128),
                &vec_var("vn", 128),
                &vec_var("vm", 128),
            );
            (bits(expr, Dest::Vector(128)), Gen::BytePairs(16))
        }
        O::NeonSmlalV | O::NeonSmlal2V | O::NeonUmlalV | O::NeonUmlal2V => {
            if arrangement(last_imm()?)? != A::S4 {
                return None;
            }
            let high = matches!(inst.opcode, O::NeonSmlal2V | O::NeonUmlal2V);
            let signed = matches!(inst.opcode, O::NeonSmlalV | O::NeonSmlal2V);
            let expr = ns::encode_neon_smlal(
                A::S4,
                high,
                signed,
                &vec_var("vd", 128),
                &vec_var("vn", 128),
                &vec_var("vm", 128),
            );
            (bits(expr, Dest::Vector(128)), Gen::Wide(32))
        }
        O::NeonUaddwV | O::NeonUaddw2V | O::NeonSaddwV | O::NeonSaddw2V => {
            if arrangement(last_imm()?)? != A::S4 {
                return None;
            }
            let high = matches!(inst.opcode, O::NeonUaddw2V | O::NeonSaddw2V);
            let (n, m) = (vec_var("vn", 128), vec_var("vm", 128));
            let expr = if matches!(inst.opcode, O::NeonUaddwV | O::NeonUaddw2V) {
                ns::encode_neon_uaddw(A::S4, high, &n, &m)
            } else {
                ns::encode_neon_saddw(A::S4, high, &n, &m)
            };
            (bits(expr, Dest::Vector(128)), Gen::Wide(32))
        }
        O::NeonUadalpV => {
            if arrangement(last_imm()?)? != A::S4 {
                return None;
            }
            let expr = ns::encode_neon_uadalp(A::S4, &vec_var("vd", 128), &vec_var("vn", 128));
            (bits(expr, Dest::Vector(128)), Gen::Wide(32))
        }
        O::NeonExtV => {
            let shift = u32::try_from(last_imm()?).ok()?;
            if !matches!(shift, 1 | 4 | 8 | 12 | 15) {
                return None;
            }
            let expr = ns::encode_neon_ext(shift, &vec_var("vn", 128), &vec_var("vm", 128));
            (bits(expr, Dest::Vector(128)), Gen::Wide(8))
        }
        // ---- horizontal reductions ----
        O::NeonUmaxv => {
            if arrangement(last_imm()?)? != A::S4 {
                return None;
            }
            let expr = ns::encode_neon_umaxv_4s(&vec_var("vn", 128));
            (bits(expr, Dest::Scalar(32)), Gen::Wide(32))
        }
        O::NeonAddpScalar => {
            if arrangement(last_imm()?)? != A::D2 {
                return None;
            }
            let expr = ns::encode_neon_addp_scalar_2d(&vec_var("vn", 128));
            (bits(expr, Dest::Scalar(64)), Gen::Wide(64))
        }
        // ---- lane moves ----
        O::NeonDupScalarD => {
            let lane = u32::try_from(last_imm()?).ok()?;
            if lane > 1 {
                return None;
            }
            let expr = ns::encode_neon_dup_scalar_d(&vec_var("vn", 128), lane);
            (bits(expr, Dest::Scalar(64)), Gen::Wide(64))
        }
        O::NeonDupElem => {
            // The model states the Q=1 (Fpr128 destination) form only.
            if dest_bits(ops.first()?)? != 128 {
                return None;
            }
            let arr = element_arrangement(imm_at(3)?)?;
            let lane = u32::try_from(imm_at(2)?).ok()?;
            if lane >= arr.lane_count() {
                return None;
            }
            let expr = ns::encode_neon_dup_element(&vec_var("vn", 128), arr, lane);
            (bits(expr, Dest::Vector(128)), Gen::Wide(arr.lane_bits()))
        }
        O::NeonDupGen => {
            let bytes = imm_at(2)?;
            let total = dest_bits(ops.first()?)?;
            let full = element_arrangement(bytes)?;
            let arr = if total == 128 {
                full
            } else {
                match full {
                    A::B16 => A::B8,
                    A::H8 => A::H4,
                    A::S4 => A::S2,
                    _ => return None,
                }
            };
            let expr = ns::encode_neon_dup(arr, &xn_var());
            (bits(expr, Dest::Vector(total)), Gen::Wide(64))
        }
        O::NeonInsGen => {
            let arr = element_arrangement(imm_at(3)?)?;
            let lane = u32::try_from(imm_at(2)?).ok()?;
            if lane >= arr.lane_count() {
                return None;
            }
            let expr = ns::encode_neon_ins_general(&vec_var("vd", 128), arr, lane, &xn_var());
            (bits(expr, Dest::Vector(128)), Gen::Wide(64))
        }
        O::NeonUmovGen => {
            let arr = element_arrangement(imm_at(3)?)?;
            let lane = u32::try_from(imm_at(2)?).ok()?;
            if lane >= arr.lane_count() {
                return None;
            }
            let gpr_bits = if arr == A::D2 { 64 } else { 32 };
            let expr = ns::encode_neon_umov_general(&vec_var("vn", 128), arr, lane, gpr_bits);
            (bits(expr, Dest::Gpr(gpr_bits)), Gen::Wide(arr.lane_bits()))
        }
        O::NeonMovi => {
            let total = dest_bits(ops.first()?)?;
            let byte = u8::try_from(imm_at(1)?).ok()?;
            (
                bits(ns::encode_neon_movi(total, byte), Dest::Vector(total)),
                Gen::Constant,
            )
        }
        // ---- FP lane-wise ----
        O::NeonFaddV | O::NeonFsubV | O::NeonFmulV | O::NeonFdivV | O::NeonFcmgtV => {
            let arr = fp_arrangement(last_imm()?)?;
            let (n, m) = (fp_lanes("vn", arr), fp_lanes("vm", arr));
            let (result, fp) = match inst.opcode {
                O::NeonFaddV => (ns::encode_neon_fadd(&n, &m), true),
                O::NeonFsubV => (ns::encode_neon_fsub(&n, &m), true),
                O::NeonFmulV => (ns::encode_neon_fmul(&n, &m), true),
                O::NeonFdivV => (ns::encode_neon_fdiv(&n, &m), true),
                _ => (ns::encode_neon_fcmgt(arr, &n, &m), false),
            };
            (lanes(result, arr, fp), Gen::Fp(arr.lane_bits()))
        }
        O::NeonFmlaV | O::NeonFmlsV => {
            let arr = fp_arrangement(last_imm()?)?;
            let (dd, n, m) = (
                fp_lanes("vd", arr),
                fp_lanes("vn", arr),
                fp_lanes("vm", arr),
            );
            let result = if inst.opcode == O::NeonFmlaV {
                ns::encode_neon_fmla(&dd, &n, &m)
            } else {
                ns::encode_neon_fmls(&dd, &n, &m)
            };
            (lanes(result, arr, true), Gen::Fp(arr.lane_bits()))
        }
        O::NeonFmlaLaneV => {
            let arr = fp_arrangement(last_imm()?)?;
            let selector = usize::try_from(imm_at(3)?).ok()?;
            if arr.total_bits() != 128 || selector >= arr.lane_count() as usize {
                return None;
            }
            let (dd, n, m) = (
                fp_lanes("vd", arr),
                fp_lanes("vn", arr),
                fp_lanes("vm", arr),
            );
            let result = ns::encode_neon_fmla_lane(&dd, &n, &m, selector);
            (lanes(result, arr, true), Gen::Fp(arr.lane_bits()))
        }
        O::NeonUcvtfV | O::NeonScvtfV => {
            let arr = fp_arrangement(last_imm()?)?;
            let reg = vec_var("vn", arr.total_bits());
            let ints: Vec<E> = (0..arr.lane_count())
                .map(|i| lane_extract(&reg, arr, i))
                .collect();
            let (eb, sb) = fp_params(arr.lane_bits());
            let result = if inst.opcode == O::NeonUcvtfV {
                ns::encode_neon_ucvtf_vec(&ints, arr.lane_bits(), eb, sb)
            } else {
                ns::encode_neon_scvtf_vec(&ints, eb, sb)
            };
            (lanes(result, arr, true), Gen::Wide(arr.lane_bits()))
        }
        O::NeonFcvtlV | O::NeonFcvtl2V => {
            let result =
                ns::encode_neon_fcvtl_vec(&vec_var("vn", 128), inst.opcode == O::NeonFcvtl2V);
            (lanes(result, A::D2, true), Gen::Fp(32))
        }
        _ => return None,
    })
}

/// Width of a SIMD&FP destination register class: 128 for `V`, 64 for `D`,
/// 32 for `S`.
fn dest_bits(operand: &Arg) -> Option<u32> {
    match operand {
        Arg::PReg(p) => match p.encoding() {
            64..=95 => Some(128),
            96..=127 => Some(64),
            128..=159 => Some(32),
            _ => None,
        },
        _ => None,
    }
}

/// The register width a bitwise form writes: the trailing arrangement's Q
/// bit, else the destination class (the encoder's `neon_q_bit`).
fn logic_width(inst: &MachInst) -> Option<u32> {
    match inst.operands.last() {
        Some(Arg::Imm(value)) => Some(if arrangement(*value)?.total_bits() == 128 {
            128
        } else {
            64
        }),
        _ => Some(if dest_bits(inst.operands.first()?)? == 128 {
            128
        } else {
            64
        }),
    }
}

// ===========================================================================
// Form enumeration
// ===========================================================================

/// Every NEON value opcode the coverage gate audits (the memory transfers are
/// `aarch64_neon_silicon_differential`'s memory tests).
const VALUE_OPCODES: &[Op] = &[
    Op::NeonAddV,
    Op::NeonSubV,
    Op::NeonMulV,
    Op::NeonSmaxV,
    Op::NeonSminV,
    Op::NeonUmaxV,
    Op::NeonUminV,
    Op::NeonFaddV,
    Op::NeonFsubV,
    Op::NeonFmulV,
    Op::NeonFdivV,
    Op::NeonFcmgtV,
    Op::NeonAndV,
    Op::NeonOrrV,
    Op::NeonEorV,
    Op::NeonBicV,
    Op::NeonNotV,
    Op::NeonRbitV,
    Op::NeonRev32V,
    Op::NeonRev64V,
    Op::NeonCmeqV,
    Op::NeonCmgtV,
    Op::NeonCmgeV,
    Op::NeonCmhiV,
    Op::NeonCmhsV,
    Op::NeonUmaxv,
    Op::NeonAddpScalar,
    Op::NeonDupElem,
    Op::NeonDupGen,
    Op::NeonInsGen,
    Op::NeonUmovGen,
    Op::NeonMovi,
    Op::NeonCntV,
    Op::NeonUaddlpV,
    Op::NeonSaddlpV,
    Op::NeonAbsV,
    Op::NeonBitV,
    Op::NeonUdotV,
    Op::NeonExtV,
    Op::NeonSmlalV,
    Op::NeonSmlal2V,
    Op::NeonUmlalV,
    Op::NeonUmlal2V,
    Op::NeonUaddwV,
    Op::NeonUaddw2V,
    Op::NeonSaddwV,
    Op::NeonSaddw2V,
    Op::NeonMlaV,
    Op::NeonUadalpV,
    Op::NeonFmlaV,
    Op::NeonFmlsV,
    Op::NeonUcvtfV,
    Op::NeonScvtfV,
    Op::NeonFcvtlV,
    Op::NeonFcvtl2V,
    Op::NeonDupScalarD,
    Op::NeonShlVImm,
    Op::NeonUshrVImm,
    Op::NeonSshrVImm,
    Op::NeonFmlaLaneV,
];

/// The NEON memory transfers, checked against the word-bound memory-effect
/// model by the memory tests below.
const MEMORY_OPCODES: &[Op] = &[
    Op::NeonLd1Post,
    Op::NeonSt1Post,
    Op::NeonLdpQPost,
    Op::NeonStpQPost,
];

/// Encoder-admitted forms no model covers, by `(opcode, word)`. No lowering
/// emits them and no obligation names them: REV64 `.8B` (the vectorizer emits
/// REV64 only at `.16B` and `.4S`) and DUP (element) into a 64-bit `D`
/// destination (every emission site allocates a `Q` register; the model states
/// the Q=1 form). Pinned so a new encoder form must be modeled or listed.
fn encoder_only_forms() -> BTreeSet<String> {
    let mut forms = BTreeSet::new();
    forms.insert("NeonRev64V [v2, v0, #0]".to_owned());
    for (bytes, lanes) in [(1, 16), (2, 8), (4, 4)] {
        for lane in 0..lanes {
            forms.insert(format!("NeonDupElem [d2, v0, #{lane}, #{bytes}]"));
        }
    }
    forms
}

/// Every candidate operand list for `op`: each arrangement, lane, element
/// size, immediate, shift and destination class an emitter could name. The
/// encoder decides which are forms.
fn candidates(op: Op) -> Vec<Vec<Arg>> {
    use Op as O;
    let mut out = Vec::new();
    match op {
        O::NeonAddV
        | O::NeonSubV
        | O::NeonMulV
        | O::NeonSmaxV
        | O::NeonSminV
        | O::NeonUmaxV
        | O::NeonUminV
        | O::NeonCmeqV
        | O::NeonCmgtV
        | O::NeonCmgeV
        | O::NeonCmhiV
        | O::NeonCmhsV
        | O::NeonMlaV
        | O::NeonUdotV
        | O::NeonSmlalV
        | O::NeonSmlal2V
        | O::NeonUmlalV
        | O::NeonUmlal2V
        | O::NeonUaddwV
        | O::NeonUaddw2V
        | O::NeonSaddwV
        | O::NeonSaddw2V
        | O::NeonFaddV
        | O::NeonFsubV
        | O::NeonFmulV
        | O::NeonFdivV
        | O::NeonFcmgtV
        | O::NeonFmlaV
        | O::NeonFmlsV => {
            for a in 0..=6 {
                out.push(vec![v(VD), v(VN), v(VM), imm(a)]);
            }
        }
        O::NeonAndV | O::NeonOrrV | O::NeonEorV | O::NeonBicV | O::NeonBitV => {
            for a in 0..=6 {
                out.push(vec![v(VD), v(VN), v(VM), imm(a)]);
            }
            out.push(vec![v(VD), v(VN), v(VM)]);
            out.push(vec![d(VD), d(VN), d(VM)]);
        }
        O::NeonNotV => {
            for a in 0..=6 {
                out.push(vec![v(VD), v(VN), imm(a)]);
            }
            out.push(vec![v(VD), v(VN)]);
            out.push(vec![d(VD), d(VN)]);
        }
        O::NeonRbitV
        | O::NeonRev32V
        | O::NeonRev64V
        | O::NeonCntV
        | O::NeonUaddlpV
        | O::NeonSaddlpV
        | O::NeonAbsV
        | O::NeonUadalpV
        | O::NeonUcvtfV
        | O::NeonScvtfV => {
            for a in 0..=6 {
                out.push(vec![v(VD), v(VN), imm(a)]);
            }
        }
        O::NeonFcvtlV | O::NeonFcvtl2V => out.push(vec![v(VD), v(VN)]),
        O::NeonExtV => {
            for k in 0..=16 {
                out.push(vec![v(VD), v(VN), v(VM), imm(k)]);
            }
        }
        O::NeonShlVImm | O::NeonUshrVImm | O::NeonSshrVImm => {
            for a in 0..=6 {
                for amount in 0..=64 {
                    out.push(vec![v(VD), v(VN), imm(amount), imm(a)]);
                }
            }
        }
        O::NeonFmlaLaneV => {
            for a in 0..=2 {
                for lane in 0..=4 {
                    out.push(vec![v(VD), v(VN), v(VM), imm(lane), imm(a)]);
                }
            }
        }
        O::NeonUmaxv => {
            for a in 0..=6 {
                out.push(vec![s(VD), v(VN), imm(a)]);
            }
        }
        O::NeonAddpScalar => {
            for a in 0..=6 {
                out.push(vec![d(VD), v(VN), imm(a)]);
            }
        }
        O::NeonDupScalarD => {
            for lane in 0..=2 {
                out.push(vec![d(VD), v(VN), imm(lane)]);
            }
        }
        O::NeonDupElem => {
            for dest in [v(VD), d(VD)] {
                for bytes in [1, 2, 4, 8] {
                    for lane in 0..=16 {
                        out.push(vec![dest.clone(), v(VN), imm(lane), imm(bytes)]);
                    }
                }
            }
        }
        O::NeonDupGen => {
            for dest in [v(VD), d(VD)] {
                for bytes in [1, 2, 4, 8] {
                    let source = if bytes == 8 { x(XN) } else { w(XN) };
                    out.push(vec![dest.clone(), source, imm(bytes)]);
                }
            }
        }
        O::NeonInsGen => {
            for bytes in [1, 2, 4, 8] {
                let source = if bytes == 8 { x(XN) } else { w(XN) };
                for lane in 0..=16 {
                    out.push(vec![v(VD), source.clone(), imm(lane), imm(bytes)]);
                }
            }
        }
        O::NeonUmovGen => {
            for bytes in [1, 2, 4, 8] {
                let dest = if bytes == 8 { x(XD) } else { w(XD) };
                for lane in 0..=16 {
                    out.push(vec![dest.clone(), v(VN), imm(lane), imm(bytes)]);
                }
            }
        }
        O::NeonMovi => {
            for dest in [v(VD), d(VD)] {
                for byte in 0..=255 {
                    out.push(vec![dest.clone(), imm(byte)]);
                }
            }
        }
        other => panic!("no candidate shape for {other:?}"),
    }
    out
}

fn render(inst: &MachInst) -> String {
    let operands: Vec<String> = inst
        .operands
        .iter()
        .map(|operand| match operand {
            Arg::PReg(p) => {
                let e = p.encoding();
                match e {
                    0..=31 => format!("x{e}"),
                    32..=63 => format!("w{}", e - 32),
                    64..=95 => format!("v{}", e - 64),
                    96..=127 => format!("d{}", e - 96),
                    128..=159 => format!("s{}", e - 128),
                    _ => format!("p{e}"),
                }
            }
            Arg::Imm(value) => format!("#{value}"),
            other => format!("{other:?}"),
        })
        .collect();
    format!("{:?} [{}]", inst.opcode, operands.join(", "))
}

/// Every encoder-admitted form of `op` (deduplicated by word), and the
/// admitted forms no model covers.
fn forms(op: Op) -> (Vec<Form>, Vec<String>) {
    let mut seen = BTreeSet::new();
    let mut forms = Vec::new();
    let mut unmodeled = Vec::new();
    for operands in candidates(op) {
        let inst = MachInst::new(op, operands);
        let Ok(word) = encode_instruction(&inst) else {
            continue;
        };
        if !seen.insert(word) {
            continue;
        }
        let label = render(&inst);
        match model_for(&inst) {
            Some((model, generator)) => forms.push(Form {
                op,
                label,
                inst,
                word,
                model,
                generator,
            }),
            None => unmodeled.push(label),
        }
    }
    (forms, unmodeled)
}

// ===========================================================================
// Inputs
// ===========================================================================

/// Deterministic xorshift64* stream.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed | 1)
    }
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn wide(&mut self) -> u128 {
        u128::from(self.next()) | (u128::from(self.next()) << 64)
    }
}

/// Integer edge values of a lane width.
fn int_edges(bits: u32) -> Vec<u64> {
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let sign = 1u64 << (bits - 1);
    let mut values = vec![
        0,
        1,
        2,
        3,
        sign - 1,
        sign,
        sign + 1,
        mask,
        mask - 1,
        0x5555_5555_5555_5555 & mask,
        0xaaaa_aaaa_aaaa_aaaa & mask,
        (1u64 << (bits / 2)) & mask,
        ((1u64 << (bits / 2)) - 1) & mask,
    ];
    values.sort_unstable();
    values.dedup();
    values
}

/// FP edge bit patterns of a lane width.
fn fp_edges(bits: u32) -> Vec<u64> {
    if bits == 32 {
        let mut values = vec![
            0x0000_0000,
            0x0000_0001,
            0x007f_ffff,
            0x0080_0000,
            0x3f80_0000,
            0x3fc0_0000,
            0x4049_0fdb,
            0x7f7f_ffff,
            0x7f80_0000,
            0x7fc0_0000,
            0x7fa0_0001,
            0x3380_0000,
            0x4b80_0000,
            0x0f80_0000,
        ];
        let negatives: Vec<u64> = values.iter().map(|v| v | 0x8000_0000).collect();
        values.extend(negatives);
        values
    } else {
        let mut values = vec![
            0x0000_0000_0000_0000,
            0x0000_0000_0000_0001,
            0x000f_ffff_ffff_ffff,
            0x0010_0000_0000_0000,
            0x3ff0_0000_0000_0000,
            0x3ff8_0000_0000_0000,
            0x4009_21fb_5444_2d18,
            0x7fef_ffff_ffff_ffff,
            0x7ff0_0000_0000_0000,
            0x7ff8_0000_0000_0000,
            0x7ff4_0000_0000_0001,
            0x3ca0_0000_0000_0000,
            0x4340_0000_0000_0000,
            0x0010_0000_0000_0001,
        ];
        let negatives: Vec<u64> = values.iter().map(|v| v | (1 << 63)).collect();
        values.extend(negatives);
        values
    }
}

/// The low `bits` bits set (`bits <= 128`).
fn low_bits(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// Pack `values` (lane 0 first) of `bits` each into a 128-bit register.
fn pack(values: &[u64], bits: u32) -> u128 {
    let mask = if bits == 64 {
        u128::from(u64::MAX)
    } else {
        (1u128 << bits) - 1
    };
    values.iter().enumerate().fold(0u128, |acc, (i, value)| {
        acc | ((u128::from(*value) & mask) << (i as u32 * bits))
    })
}

/// Random FP lane bits that favour finite, nearby magnitudes (so FMA and
/// conversions round), mixed with raw patterns.
fn random_fp(rng: &mut Rng, bits: u32) -> u64 {
    let raw = rng.next();
    match raw % 4 {
        0 => raw >> 7,
        _ if bits == 32 => {
            let exponent = 120 + (rng.next() % 16);
            ((raw & 1) << 31) | (exponent << 23) | (rng.next() & 0x7f_ffff)
        }
        _ => {
            let exponent = 1015 + (rng.next() % 16);
            ((raw & 1) << 63) | (exponent << 52) | (rng.next() & 0xf_ffff_ffff_ffff)
        }
    }
}

/// The inputs a form runs over: the generator's structured vectors, then
/// `random` pseudo-random ones.
fn inputs(generator: Gen, seed: u64, random: usize) -> Vec<Input> {
    let mut rng = Rng::new(seed);
    let mut out = Vec::new();
    let fresh = |rng: &mut Rng| Input {
        vn: rng.wide(),
        vm: rng.wide(),
        vd: rng.wide(),
        xn: rng.next(),
        xd: rng.next(),
    };
    match generator {
        Gen::BytePairs(lanes) => {
            // Every (a, b) byte pair once, `lanes` pairs per vector, in the
            // lanes the form reads.
            let lanes = lanes as usize;
            let low = low_bits(8 * lanes as u32);
            for first in (0..65536usize).step_by(lanes) {
                let a: Vec<u64> = (first..first + lanes).map(|p| (p & 0xff) as u64).collect();
                let b: Vec<u64> = (first..first + lanes).map(|p| (p >> 8) as u64).collect();
                let mut input = fresh(&mut rng);
                input.vn = pack(&a, 8) | (input.vn & !low);
                input.vm = pack(&b, 8) | (input.vm & !low);
                out.push(input);
            }
        }
        Gen::AdjacentBytePairs => {
            // Every (a, b) byte pair once in an adjacent (even, odd) byte-lane
            // pair: the operands of every pairwise byte op.
            for first in (0..65536usize).step_by(8) {
                let bytes: Vec<u64> = (first..first + 8)
                    .flat_map(|p| [(p & 0xff) as u64, (p >> 8) as u64])
                    .collect();
                let mut input = fresh(&mut rng);
                input.vn = pack(&bytes, 8);
                out.push(input);
            }
        }
        Gen::Bytes => {
            // Every byte value in every byte lane of both halves.
            for k in 0..256u64 {
                let a: Vec<u64> = (0..16).map(|i| (k + i * 17) & 0xff).collect();
                let mut input = fresh(&mut rng);
                input.vn = pack(&a, 8);
                out.push(input);
            }
        }
        Gen::Wide(bits) | Gen::Fp(bits) => {
            // Every (a, b, c) triple of edge values in every lane of the low
            // half (what a 64-bit form reads) and, offset, of the high half.
            let fp = matches!(generator, Gen::Fp(_));
            let edges = if fp { fp_edges(bits) } else { int_edges(bits) };
            let e = edges.len();
            let total = e * e * e;
            let half = (64 / bits).max(1) as usize;
            let per = (128 / bits) as usize;
            let triple = |t: usize| {
                let t = t % total;
                (edges[t / (e * e)], edges[(t / e) % e], edges[t % e])
            };
            for first in (0..total).step_by(half) {
                let lanes: Vec<(u64, u64, u64)> = (0..per)
                    .map(|i| {
                        if i < half {
                            triple(first + i)
                        } else {
                            triple(first + i + total / 2)
                        }
                    })
                    .collect();
                let mut input = fresh(&mut rng);
                input.vn = pack(&lanes.iter().map(|l| l.0).collect::<Vec<_>>(), bits);
                input.vm = pack(&lanes.iter().map(|l| l.1).collect::<Vec<_>>(), bits);
                input.vd = pack(&lanes.iter().map(|l| l.2).collect::<Vec<_>>(), bits);
                let upper = if bits >= 64 { 0 } else { rng.next() << bits };
                input.xn = lanes[0].0 | upper;
                out.push(input);
            }
            if fp {
                let lanes = |rng: &mut Rng| {
                    let values: Vec<u64> = (0..per).map(|_| random_fp(rng, bits)).collect();
                    pack(&values, bits)
                };
                for _ in 0..random {
                    let mut input = fresh(&mut rng);
                    input.vn = lanes(&mut rng);
                    input.vm = lanes(&mut rng);
                    input.vd = lanes(&mut rng);
                    out.push(input);
                }
                return out;
            }
        }
        Gen::Constant => {
            for _ in 0..4 {
                out.push(fresh(&mut rng));
            }
            return out;
        }
    }
    for _ in 0..random {
        out.push(fresh(&mut rng));
    }
    out
}

// ===========================================================================
// Evaluation and comparison
// ===========================================================================

fn env_of(input: &Input) -> EvalEnv {
    let mut env = EvalEnv::default();
    env.insert("vn_lo".into(), input.vn as u64);
    env.insert("vn_hi".into(), (input.vn >> 64) as u64);
    env.insert("vm_lo".into(), input.vm as u64);
    env.insert("vm_hi".into(), (input.vm >> 64) as u64);
    env.insert("vd_lo".into(), input.vd as u64);
    env.insert("vd_hi".into(), (input.vd >> 64) as u64);
    env.insert("xn".into(), input.xn);
    env
}

fn eval_bits(expr: &E, env: &EvalEnv) -> u128 {
    match expr.try_eval(env).expect("model evaluates") {
        EvalResult::Bv(value) => u128::from(value),
        EvalResult::Bv128(value) => value,
        EvalResult::Bool(value) => u128::from(value),
        other => panic!("model evaluated to {other:?}"),
    }
}

fn eval_lane(expr: &E, env: &EvalEnv, lane_bits: u32, fp_result: bool) -> u64 {
    match expr.try_eval(env).expect("model lane evaluates") {
        EvalResult::Float(f) => {
            if fp_result && lane_bits == 32 {
                fp_bitmodel::fcvt_narrow(f.to_bits())
            } else {
                f.to_bits()
            }
        }
        EvalResult::Bv(value) => value,
        EvalResult::Bv128(value) => value as u64,
        other => panic!("model lane evaluated to {other:?}"),
    }
}

fn is_nan(bits: u64, lane_bits: u32) -> bool {
    if lane_bits == 32 {
        fp_bitmodel::is_nan(fp_bitmodel::F32, bits & 0xffff_ffff)
    } else {
        fp_bitmodel::is_nan(fp_bitmodel::F64, bits)
    }
}

/// Random vectors per opcode, divided among its forms (each form gets at
/// least 256 and at most 8192).
const RANDOM_PER_OPCODE: usize = 65536;

/// Tally of one form's run.
#[derive(Default, Clone, Copy)]
struct Tally {
    vectors: usize,
    nan_class_lanes: usize,
}

/// Compare one silicon output with the model. `Err` names the first
/// disagreement.
fn compare(
    model: &Model,
    input: &Input,
    output: &Output,
    nan_lanes: &mut usize,
) -> Result<(), String> {
    let env = env_of(input);
    if output.vn != input.vn || output.vm != input.vm {
        return Err("a source register changed".into());
    }
    if output.xn != input.xn {
        return Err("x9 changed".into());
    }
    match model {
        Model::Bits { expr, dest } => {
            let value = eval_bits(expr, &env);
            let (want_vd, want_xd) = match *dest {
                Dest::Vector(128) => (value, input.xd),
                Dest::Vector(bits) | Dest::Scalar(bits) => {
                    (value & ((1u128 << bits) - 1), input.xd)
                }
                Dest::Gpr(bits) => {
                    let mask = if bits == 64 {
                        u64::MAX
                    } else {
                        (1u64 << bits) - 1
                    };
                    (input.vd, (value as u64) & mask)
                }
            };
            if output.vd != want_vd || output.xd != want_xd {
                return Err(format!(
                    "model vd={want_vd:#034x} xd={want_xd:#018x}, silicon vd={:#034x} xd={:#018x}",
                    output.vd, output.xd
                ));
            }
        }
        Model::Lanes {
            lanes,
            lane_bits,
            total_bits,
            fp_result,
        } => {
            if output.xd != input.xd {
                return Err("x10 changed".into());
            }
            if *total_bits == 64 && output.vd >> 64 != 0 {
                return Err(format!("upper half not zeroed: {:#034x}", output.vd));
            }
            let mask = if *lane_bits == 64 {
                u64::MAX
            } else {
                (1u64 << lane_bits) - 1
            };
            for (i, lane) in lanes.iter().enumerate() {
                let want = eval_lane(lane, &env, *lane_bits, *fp_result) & mask;
                let got = (output.vd >> (i as u32 * lane_bits)) as u64 & mask;
                if want == got {
                    continue;
                }
                if *fp_result && is_nan(want, *lane_bits) && is_nan(got, *lane_bits) {
                    *nan_lanes += 1;
                    continue;
                }
                return Err(format!(
                    "lane {i}: model {want:#x}, silicon {got:#x} (vd={:#034x})",
                    output.vd
                ));
            }
        }
    }
    Ok(())
}

/// Run every form of `ops` on silicon and compare it with its model. Returns
/// the per-opcode tallies; panics with every failing form named.
fn run_family(ops: &[Op], seed: u64) -> BTreeMap<String, (usize, Tally)> {
    let mut all = Vec::new();
    for &op in ops {
        let (forms, _) = forms(op);
        assert!(!forms.is_empty(), "{op:?} has no modeled encoder form");
        all.extend(forms);
    }
    for form in &all {
        let outcome = A64DecodeCheck.check_one(&form.inst, &form.word.to_le_bytes(), None);
        assert!(
            matches!(outcome, DecodeCheckOutcome::Match),
            "{}: ENC-5 does not decode the encoder's word {:#010x}: {outcome:?}",
            form.label,
            form.word
        );
    }
    // The word-bound lane-effect decomposition of every admitted form carries
    // the encoder's word; its parts are checked against the CPU below.
    let lane_effects: Vec<_> = all
        .iter()
        .map(|form| {
            let decomposition = neon_lane_effect(&form.inst);
            if decomposition.is_some() {
                assert_eq!(
                    check_emitted_neon_lane_effect_word(&form.inst, form.word),
                    Some(Ok(())),
                    "{}: the lane-effect decomposition does not carry the encoder's word",
                    form.label
                );
            }
            decomposition
        })
        .collect();
    let page = exec::Page::new(&all.iter().map(|form| form.word).collect::<Vec<_>>());
    let mut failures = Vec::new();
    let mut tallies: BTreeMap<String, (usize, Tally)> = BTreeMap::new();
    let mut per_opcode: BTreeMap<String, usize> = BTreeMap::new();
    for form in &all {
        *per_opcode.entry(format!("{:?}", form.op)).or_default() += 1;
    }
    for (index, form) in all.iter().enumerate() {
        let mut tally = Tally::default();
        let random = (RANDOM_PER_OPCODE / per_opcode[&format!("{:?}", form.op)]).clamp(256, 8192);
        for input in inputs(form.generator, seed ^ u64::from(form.word), random) {
            let output = page.run(index, &input);
            tally.vectors += 1;
            let lane_check = lane_effects[index]
                .as_ref()
                .map_or(Ok(()), |decomposition| {
                    compare_lane_effect(decomposition, &input, &output)
                });
            if let Err(why) =
                compare(&form.model, &input, &output, &mut tally.nan_class_lanes).and(lane_check)
            {
                failures.push(format!(
                    "{} (word {:#010x}) on vn={:#034x} vm={:#034x} vd={:#034x} xn={:#018x}: {why}",
                    form.label, form.word, input.vn, input.vm, input.vd, input.xn
                ));
                break;
            }
        }
        let entry = tallies.entry(format!("{:?}", form.op)).or_default();
        entry.0 += 1;
        entry.1.vectors += tally.vectors;
        entry.1.nan_class_lanes += tally.nan_class_lanes;
    }
    for (op, (forms, tally)) in &tallies {
        eprintln!(
            "silicon differential: {op}: {forms} form(s), {} input vector(s), {} NaN-class lane(s)",
            tally.vectors, tally.nan_class_lanes
        );
    }
    assert!(
        failures.is_empty(),
        "the NEON model disagrees with this CPU:\n{}",
        failures.join("\n")
    );
    tallies
}

/// Each part of the word-bound lane-effect decomposition, evaluated at the
/// state before the instruction, against what the CPU wrote: `half h` the
/// destination's 64-bit half, `gpr` the general destination, and both sides
/// of every part equal.
fn compare_lane_effect(
    decomposition: &NeonLaneEffectDecomposition,
    input: &Input,
    output: &Output,
) -> Result<(), String> {
    let env = env_of(input);
    for part in &decomposition.parts {
        let machine = eval_bits(&part.obligation.aarch64_expr, &env);
        let intent = eval_bits(&part.obligation.trust_ir_expr, &env);
        let silicon = match part.part {
            NeonLaneEffectPart::Fields => intent,
            NeonLaneEffectPart::Half { half } => {
                u128::from((output.vd >> (64 * u32::from(half))) as u64)
            }
            NeonLaneEffectPart::Gpr => u128::from(output.xd),
        };
        if machine != silicon || intent != machine {
            return Err(format!(
                "lane-effect part `{}`: word side {machine:#x}, operands' side {intent:#x}, \
                 silicon {silicon:#x}",
                part.part
            ));
        }
    }
    Ok(())
}

// ===========================================================================
// The differential, by family
// ===========================================================================

const LANEWISE_INTEGER: &[Op] = &[
    Op::NeonAddV,
    Op::NeonSubV,
    Op::NeonMulV,
    Op::NeonSmaxV,
    Op::NeonSminV,
    Op::NeonUmaxV,
    Op::NeonUminV,
    Op::NeonCmeqV,
    Op::NeonCmgtV,
    Op::NeonCmgeV,
    Op::NeonCmhiV,
    Op::NeonCmhsV,
    Op::NeonMlaV,
    Op::NeonAbsV,
];

const BITWISE_AND_BYTE_PERMUTE: &[Op] = &[
    Op::NeonAndV,
    Op::NeonOrrV,
    Op::NeonEorV,
    Op::NeonBicV,
    Op::NeonBitV,
    Op::NeonNotV,
    Op::NeonRbitV,
    Op::NeonRev32V,
    Op::NeonRev64V,
    Op::NeonCntV,
    Op::NeonExtV,
];

const WIDENING_PAIRWISE_AND_DOT: &[Op] = &[
    Op::NeonUaddlpV,
    Op::NeonSaddlpV,
    Op::NeonUadalpV,
    Op::NeonUdotV,
    Op::NeonSmlalV,
    Op::NeonSmlal2V,
    Op::NeonUmlalV,
    Op::NeonUmlal2V,
    Op::NeonUaddwV,
    Op::NeonUaddw2V,
    Op::NeonSaddwV,
    Op::NeonSaddw2V,
];

const HORIZONTAL_AND_LANE_MOVE: &[Op] = &[
    Op::NeonUmaxv,
    Op::NeonAddpScalar,
    Op::NeonDupElem,
    Op::NeonDupGen,
    Op::NeonInsGen,
    Op::NeonUmovGen,
    Op::NeonDupScalarD,
    Op::NeonMovi,
];

const IMMEDIATE_SHIFT: &[Op] = &[Op::NeonShlVImm, Op::NeonUshrVImm, Op::NeonSshrVImm];

const FP_FUSED_CONVERT_AND_LANEWISE: &[Op] = &[
    Op::NeonFaddV,
    Op::NeonFsubV,
    Op::NeonFmulV,
    Op::NeonFdivV,
    Op::NeonFcmgtV,
    Op::NeonFmlaV,
    Op::NeonFmlsV,
    Op::NeonFmlaLaneV,
    Op::NeonUcvtfV,
    Op::NeonScvtfV,
    Op::NeonFcvtlV,
    Op::NeonFcvtl2V,
];

#[test]
fn lanewise_integer_models_match_silicon() {
    run_family(LANEWISE_INTEGER, 0x1111);
}

#[test]
fn bitwise_and_byte_permute_models_match_silicon() {
    run_family(BITWISE_AND_BYTE_PERMUTE, 0x2222);
}

#[test]
fn widening_pairwise_and_dot_models_match_silicon() {
    run_family(WIDENING_PAIRWISE_AND_DOT, 0x3333);
}

#[test]
fn horizontal_and_lane_move_models_match_silicon() {
    run_family(HORIZONTAL_AND_LANE_MOVE, 0x4444);
}

#[test]
fn immediate_shift_models_match_silicon() {
    run_family(IMMEDIATE_SHIFT, 0x5555);
}

#[test]
fn fp_fused_convert_and_lanewise_models_match_silicon() {
    run_family(FP_FUSED_CONVERT_AND_LANEWISE, 0x6666);
}

// ===========================================================================
// Inventory
// ===========================================================================

/// Every NEON opcode the coverage gate audits is checked here: each value
/// opcode has a modeled encoder form in one family above, each memory transfer
/// is a memory test below, and the encoder-admitted forms no model covers are
/// exactly the pinned list.
#[test]
fn every_audited_neon_opcode_is_differentially_checked() {
    use trust_cg_verify::coverage_gate::{ALL_AARCH64_OPCODES, OpcodeClass, classify_aarch64};
    let audited: BTreeSet<String> = ALL_AARCH64_OPCODES
        .iter()
        .filter(|op| format!("{op:?}").starts_with("Neon"))
        .filter(|op| !matches!(classify_aarch64(**op), OpcodeClass::PseudoOrTrap))
        .map(|op| format!("{op:?}"))
        .collect();
    let checked: BTreeSet<String> = VALUE_OPCODES
        .iter()
        .chain(MEMORY_OPCODES)
        .map(|op| format!("{op:?}"))
        .collect();
    assert_eq!(
        audited, checked,
        "every audited NEON opcode must have a silicon differential"
    );
    let in_families: Vec<String> = [
        LANEWISE_INTEGER,
        BITWISE_AND_BYTE_PERMUTE,
        WIDENING_PAIRWISE_AND_DOT,
        HORIZONTAL_AND_LANE_MOVE,
        IMMEDIATE_SHIFT,
        FP_FUSED_CONVERT_AND_LANEWISE,
    ]
    .concat()
    .iter()
    .map(|op| format!("{op:?}"))
    .collect();
    let families: BTreeSet<String> = in_families.iter().cloned().collect();
    assert_eq!(
        families.len(),
        in_families.len(),
        "an opcode runs in two families"
    );
    let values: BTreeSet<String> = VALUE_OPCODES.iter().map(|op| format!("{op:?}")).collect();
    assert_eq!(families, values, "every value opcode runs in a family");

    let mut unmodeled = BTreeSet::new();
    let mut total = 0usize;
    for &op in VALUE_OPCODES {
        let (forms, missing) = forms(op);
        assert!(!forms.is_empty(), "{op:?} has no modeled encoder form");
        total += forms.len();
        unmodeled.extend(missing);
    }
    eprintln!(
        "silicon differential: {total} modeled encoder forms over {} opcodes",
        values.len()
    );
    assert_eq!(
        unmodeled,
        encoder_only_forms(),
        "encoder-admitted NEON forms without a model changed"
    );
    // Every encoder form of the lane-effect opcodes (the horizontal
    // reductions and permutes) is admitted by the word-bound decomposition,
    // whose parts the families above check against the CPU form by form.
    for &op in trust_cg_verify::aarch64_neon_lane_effect::NEON_LANE_EFFECT_OPCODES {
        let (forms, _) = forms(op);
        let missing: Vec<&str> = forms
            .iter()
            .filter(|form| neon_lane_effect(&form.inst).is_none())
            .map(|form| form.label.as_str())
            .collect();
        assert!(
            missing.is_empty(),
            "{op:?}: encoder forms without a lane-effect decomposition: {missing:?}"
        );
    }
}

/// The encoder-only forms (`encoder_only_forms`) have no value model, but
/// the word-bound lane-effect decomposition admits every one of them (DUP
/// (element) into a `D` register at 8-, 16- and 32-bit lanes, and REV64
/// `.8B`). Each is encoded, ENC-5-checked, bound to the decomposition's word
/// and run on the CPU, and every lane-effect part is compared with what the
/// CPU wrote (both 64-bit halves, so the zeroed upper half of a `D` write
/// too). With the families above, every form the decomposition admits for
/// the lane-effect opcodes has run on silicon.
#[test]
fn encoder_only_lane_effect_forms_match_silicon() {
    let mut checked = Vec::new();
    for &op in trust_cg_verify::aarch64_neon_lane_effect::NEON_LANE_EFFECT_OPCODES {
        let mut seen = BTreeSet::new();
        for operands in candidates(op) {
            let inst = MachInst::new(op, operands);
            let Ok(word) = encode_instruction(&inst) else {
                continue;
            };
            if !seen.insert(word) || model_for(&inst).is_some() {
                continue;
            }
            let label = render(&inst);
            let decomposition = neon_lane_effect(&inst).unwrap_or_else(|| {
                panic!("{label}: an encoder form without a lane-effect decomposition")
            });
            assert_eq!(
                check_emitted_neon_lane_effect_word(&inst, word),
                Some(Ok(())),
                "{label}: the decomposition does not carry the encoder's word"
            );
            let outcome = A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None);
            assert!(
                matches!(outcome, DecodeCheckOutcome::Match),
                "{label}: ENC-5 {outcome:?}"
            );
            let generator = match (op, inst.operands.get(3)) {
                (Op::NeonDupElem, Some(Arg::Imm(bytes))) => {
                    Gen::Wide(8 * u32::try_from(*bytes).expect("element bytes"))
                }
                _ => Gen::Bytes,
            };
            checked.push((label, word, decomposition, generator));
        }
    }
    let labels: BTreeSet<String> = checked.iter().map(|(label, ..)| label.clone()).collect();
    assert_eq!(
        labels,
        encoder_only_forms(),
        "the encoder-only forms changed"
    );
    let page = exec::Page::new(
        &checked
            .iter()
            .map(|(_, word, ..)| *word)
            .collect::<Vec<_>>(),
    );
    let mut failures = Vec::new();
    let mut vectors = 0usize;
    for (index, (label, word, decomposition, generator)) in checked.iter().enumerate() {
        for input in inputs(*generator, 0x8888 ^ u64::from(*word), 2048) {
            vectors += 1;
            if let Err(why) = compare_lane_effect(decomposition, &input, &page.run(index, &input)) {
                failures.push(format!(
                    "{label} (word {word:#010x}) on vn={:#034x} vd={:#034x}: {why}",
                    input.vn, input.vd
                ));
                break;
            }
        }
    }
    eprintln!(
        "silicon differential: {} encoder-only lane-effect form(s), {vectors} input vector(s)",
        checked.len()
    );
    assert!(
        failures.is_empty(),
        "the lane-effect decomposition disagrees with this CPU:\n{}",
        failures.join("\n")
    );
}

// ===========================================================================
// Non-vacuity
// ===========================================================================

/// Run `word` on silicon over `generator`'s inputs and report whether `model`
/// disagrees with it on some input.
fn disagrees(word: u32, model: &Model, generator: Gen) -> bool {
    let page = exec::Page::new(&[word]);
    let mut nan = 0;
    inputs(generator, 0x7777, 1024)
        .iter()
        .any(|input| compare(model, input, &page.run(0, input), &mut nan).is_err())
}

fn word_of(op: Op, operands: Vec<Arg>) -> u32 {
    encode_instruction(&MachInst::new(op, operands)).expect("encodes")
}

/// Plausible mis-models of the newly checked operations disagree with the CPU
/// on the generated inputs: the differential can tell them apart.
#[test]
fn wrong_models_disagree_with_silicon() {
    let n128 = || vec_var("vn", 128);
    let m128 = || vec_var("vm", 128);
    let d128 = || vec_var("vd", 128);
    let cases: Vec<(&str, u32, Model, Gen)> = vec![
        (
            "UADDLP.16B modeled as SADDLP",
            word_of(Op::NeonUaddlpV, vec![v(VD), v(VN), imm(1)]),
            bits(ns::encode_neon_saddlp(A::B16, &n128()), Dest::Vector(128)),
            Gen::Bytes,
        ),
        (
            "UDOT modeled without the accumulator",
            word_of(Op::NeonUdotV, vec![v(VD), v(VN), v(VM), imm(1)]),
            bits(
                ns::encode_neon_udot(
                    A::B16,
                    &E::bv_const(0, 64).concat(E::bv_const(0, 64)),
                    &n128(),
                    &m128(),
                ),
                Dest::Vector(128),
            ),
            Gen::Wide(8),
        ),
        (
            "SMLAL2 modeled as SMLAL (wrong half)",
            word_of(Op::NeonSmlal2V, vec![v(VD), v(VN), v(VM), imm(5)]),
            bits(
                ns::encode_neon_smlal(A::S4, false, true, &d128(), &n128(), &m128()),
                Dest::Vector(128),
            ),
            Gen::Wide(32),
        ),
        (
            "SADDW modeled as UADDW (wrong extension)",
            word_of(Op::NeonSaddwV, vec![v(VD), v(VN), v(VM), imm(5)]),
            bits(
                ns::encode_neon_uaddw(A::S4, false, &n128(), &m128()),
                Dest::Vector(128),
            ),
            Gen::Wide(32),
        ),
        (
            "EXT #4 modeled with its sources swapped",
            word_of(Op::NeonExtV, vec![v(VD), v(VN), v(VM), imm(4)]),
            bits(ns::encode_neon_ext(4, &m128(), &n128()), Dest::Vector(128)),
            Gen::Wide(8),
        ),
        (
            "REV32.16B modeled as REV64.16B",
            word_of(Op::NeonRev32V, vec![v(VD), v(VN), imm(1)]),
            bits(ns::encode_neon_rev64_16b(&n128()), Dest::Vector(128)),
            Gen::Bytes,
        ),
        (
            "ADDP modeled as lane 0",
            word_of(Op::NeonAddpScalar, vec![d(VD), v(VN), imm(6)]),
            bits(lane_extract(&n128(), A::D2, 0), Dest::Scalar(64)),
            Gen::Wide(64),
        ),
        (
            "UMOV.H[3] modeled as sign-extending (SMOV)",
            word_of(Op::NeonUmovGen, vec![w(XD), v(VN), imm(3), imm(2)]),
            bits(lane_extract(&n128(), A::H8, 3).sign_ext(16), Dest::Gpr(32)),
            Gen::Wide(16),
        ),
        (
            "INS.S[1] modeled at lane 2",
            word_of(Op::NeonInsGen, vec![v(VD), w(XN), imm(1), imm(4)]),
            bits(
                ns::encode_neon_ins_general(&d128(), A::S4, 2, &xn_var()),
                Dest::Vector(128),
            ),
            Gen::Wide(32),
        ),
        (
            "CNT.8B modeled without the Q=0 upper-half zeroing",
            word_of(Op::NeonCntV, vec![v(VD), v(VN), imm(0)]),
            bits(ns::encode_neon_cnt(A::B16, &n128()), Dest::Vector(128)),
            Gen::Bytes,
        ),
        (
            "FMLS.2D modeled as FMLA",
            word_of(Op::NeonFmlsV, vec![v(VD), v(VN), v(VM), imm(2)]),
            lanes(
                ns::encode_neon_fmla(
                    &fp_lanes("vd", A::D2),
                    &fp_lanes("vn", A::D2),
                    &fp_lanes("vm", A::D2),
                ),
                A::D2,
                true,
            ),
            Gen::Fp(64),
        ),
        (
            "UCVTF.4S modeled as SCVTF",
            word_of(Op::NeonUcvtfV, vec![v(VD), v(VN), imm(1)]),
            {
                let reg = n128();
                let ints: Vec<E> = (0..4).map(|i| lane_extract(&reg, A::S4, i)).collect();
                lanes(ns::encode_neon_scvtf_vec(&ints, 8, 24), A::S4, true)
            },
            Gen::Wide(32),
        ),
        (
            "FCVTL2 modeled as FCVTL (wrong half)",
            word_of(Op::NeonFcvtl2V, vec![v(VD), v(VN)]),
            lanes(ns::encode_neon_fcvtl_vec(&n128(), false), A::D2, true),
            Gen::Fp(32),
        ),
        (
            "FMLA by element [1] modeled with selector 0",
            word_of(Op::NeonFmlaLaneV, vec![v(VD), v(VN), v(VM), imm(1), imm(1)]),
            lanes(
                ns::encode_neon_fmla_lane(
                    &fp_lanes("vd", A::S4),
                    &fp_lanes("vn", A::S4),
                    &fp_lanes("vm", A::S4),
                    0,
                ),
                A::S4,
                true,
            ),
            Gen::Fp(32),
        ),
    ];
    let mut blind = Vec::new();
    for (name, word, model, generator) in &cases {
        if !disagrees(*word, model, *generator) {
            blind.push(*name);
        }
    }
    assert!(blind.is_empty(), "the differential cannot see: {blind:?}");
}

/// A corrupted word (one field changed) disagrees with the intended form's
/// model: the differential executes the real word, not the mnemonic.
#[test]
fn corrupted_words_disagree_with_the_intended_model() {
    let mut blind = Vec::new();
    for op in [
        Op::NeonUdotV,
        Op::NeonUaddlpV,
        Op::NeonSmlalV,
        Op::NeonExtV,
        Op::NeonAddpScalar,
        Op::NeonUmovGen,
        Op::NeonDupElem,
        Op::NeonFmlaLaneV,
    ] {
        let (forms, _) = forms(op);
        let form = &forms[forms.len() / 2];
        // Flip bit 0 of the Rn field: the same instruction now reads v1 (the
        // stub's Vm) instead of v0. Only a register field is flipped, so the
        // corrupted word is still an allocated encoding of the same class.
        let corrupted = form.word ^ (1 << 5);
        if matches!(
            A64DecodeCheck.check_one(&form.inst, &corrupted.to_le_bytes(), None),
            DecodeCheckOutcome::Match
        ) {
            blind.push(format!("{}: ENC-5 accepts the Rn flip", form.label));
        }
        if !disagrees(corrupted, &form.model, form.generator) {
            blind.push(format!("{}: the Rn flip is not seen", form.label));
        }
    }
    assert!(blind.is_empty(), "{blind:#?}");
}

// ===========================================================================
// Post-index transfers against the word-bound memory-effect model
// ===========================================================================

/// The NEON post-index transfers' decomposition
/// (`aarch64_memory_effect::memory_effect`) agrees with this CPU: for every
/// form, over random buffers, alignments and registers, each part's word side
/// evaluated at the state before the instruction equals what the CPU produced
/// (the written-back base, each loaded register half, each stored 8-byte
/// window), each part's two sides agree, and no byte outside the transfer
/// windows and no other register changes. `LD1`/`ST1` run at every
/// arrangement, `LDP`/`STP` (Q, post-index) at offsets across the `imm7`
/// range.
#[test]
fn post_index_transfers_match_the_word_bound_memory_effect_on_silicon() {
    use trust_cg_verify::aarch64_memory_effect::{
        MemoryEffectPart, check_emitted_memory_effect_word, memory_effect,
    };
    let mut instructions = Vec::new();
    for selector in 0..=6 {
        instructions.push(MachInst::new(
            Op::NeonLd1Post,
            vec![v(VD), x(XN), imm(selector)],
        ));
        instructions.push(MachInst::new(
            Op::NeonSt1Post,
            vec![v(VD), x(XN), imm(selector)],
        ));
    }
    for offset in [-1024, -32, -16, 0, 16, 32, 1008] {
        instructions.push(MachInst::new(
            Op::NeonLdpQPost,
            vec![v(VD), v(VN), x(XN), imm(offset)],
        ));
        instructions.push(MachInst::new(
            Op::NeonStpQPost,
            vec![v(VD), v(VN), x(XN), imm(offset)],
        ));
    }
    let words: Vec<u32> = instructions
        .iter()
        .map(|inst| encode_instruction(inst).expect("encodes"))
        .collect();
    for (inst, word) in instructions.iter().zip(&words) {
        assert!(
            matches!(
                A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None),
                DecodeCheckOutcome::Match
            ),
            "{}: ENC-5",
            render(inst)
        );
        assert_eq!(
            check_emitted_memory_effect_word(inst, *word),
            Some(Ok(())),
            "{}: the decomposition does not carry the emitted word",
            render(inst)
        );
    }
    let page = exec::Page::new(&words);
    let mut rng = Rng::new(0x8888);
    let mut failures = Vec::new();
    let mut checked_parts = 0usize;
    for (index, inst) in instructions.iter().enumerate() {
        let decomposition = memory_effect(inst).expect("admitted");
        let access = decomposition.access;
        for trial in 0..256 {
            let mut buffer = vec![0u8; 128];
            for byte in buffer.iter_mut() {
                *byte = rng.next() as u8;
            }
            let before = buffer.clone();
            let start = 48 + (trial % 16);
            // The stub receives the base as an integer in x9: expose the
            // buffer's provenance, and read it back through the same pointer.
            let memory = buffer.as_mut_ptr();
            let base = memory as u64 + start as u64;
            let input = Input {
                vn: rng.wide(),
                vm: rng.wide(),
                vd: rng.wide(),
                xn: base,
                xd: rng.next(),
            };
            // x9 points `start` bytes into `buffer`; every admitted transfer
            // touches at most 32 bytes from there.
            let output = page.run(index, &input);
            // SAFETY: `memory` is the live 128-byte allocation the stub wrote
            // through; nothing else aliases it here.
            let after = unsafe { std::slice::from_raw_parts(memory, buffer.len()) }.to_vec();
            let window = |memory: &[u8], at: usize| -> u64 {
                u64::from_le_bytes(memory[at..at + 8].try_into().unwrap())
            };
            let lane_at = |lane: usize| start + lane * access.bytes as usize;
            let register = |slot: usize, out: bool| -> u128 {
                match (slot, out) {
                    (0, false) => input.vd,
                    (0, true) => output.vd,
                    (_, false) => input.vn,
                    (_, true) => output.vn,
                }
            };
            let mut env = EvalEnv::default();
            env.insert("base".into(), base);
            for lane in 0..2usize {
                env.insert(format!("w{lane}"), window(&before, lane_at(lane)));
                for half in 0..2usize {
                    env.insert(
                        format!("w{lane}h{half}"),
                        window(&before, lane_at(lane) + 8 * half),
                    );
                    let data = register(lane, false) >> (64 * half);
                    env.insert(format!("d{lane}h{half}"), data as u64);
                }
                env.insert(format!("d{lane}"), register(lane, false) as u64);
            }
            for part in &decomposition.parts {
                let obligation = &part.obligation;
                let machine = eval_bits(&obligation.aarch64_expr, &env);
                let intent = eval_bits(&obligation.trust_ir_expr, &env);
                let silicon = match part.part {
                    MemoryEffectPart::Fields | MemoryEffectPart::Address { .. } => intent,
                    MemoryEffectPart::Writeback => u128::from(output.xn),
                    MemoryEffectPart::Load { lane, half } => u128::from(
                        (register(usize::from(lane), true) >> (64 * u32::from(half))) as u64,
                    ),
                    MemoryEffectPart::Store { lane, half } => u128::from(window(
                        &after,
                        lane_at(usize::from(lane)) + 8 * usize::from(half),
                    )),
                };
                checked_parts += 1;
                if machine != silicon || intent != machine {
                    failures.push(format!(
                        "{} trial {trial} part `{}`: word side {machine:#x}, operands' side \
                         {intent:#x}, silicon {silicon:#x}",
                        render(inst),
                        part.part
                    ));
                }
            }
            // Nothing outside the transfer windows moves, and only the
            // transfer registers change.
            let span = access.lanes() * access.bytes as usize;
            let touched = if access.load {
                0..0
            } else {
                start..start + span
            };
            for (at, (old, new)) in before.iter().zip(&after).enumerate() {
                if !touched.contains(&at) && old != new {
                    failures.push(format!("{} trial {trial}: byte {at} changed", render(inst)));
                }
            }
            let writes_vn = access.load && access.lanes() == 2;
            if (!writes_vn && output.vn != input.vn)
                || output.vm != input.vm
                || output.xd != input.xd
            {
                failures.push(format!(
                    "{} trial {trial}: a bystander register changed",
                    render(inst)
                ));
            }
            if failures.len() > 8 {
                break;
            }
        }
    }
    eprintln!(
        "silicon differential: {} post-index transfer form(s), {checked_parts} part evaluation(s)",
        instructions.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
