// gen_aarch64_neon_fp_silicon_truth.rs — NATIVE NEON-FP BARE-SILICON oracle.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE NEON-FP SILICON-TRUTH GENERATOR — bare-silicon oracle for the
// B-aarch64-neon-fp differential bridge (AArch64 lane-wise FP NEON).
// ===========================================================================
//
// The host IS an Apple M4 (NATIVE AArch64, runs NEON FP DIRECTLY — no Rosetta /
// qemu / Clean-chip-file). For each lane-wise FP NEON op + arrangement, this binary
// loads two 128-bit operands into q-registers, executes the REAL instruction via
// `std::arch::asm!` (`fadd v0.4s, v1.4s, v2.4s`, `fmul v0.2d, ...`, `fminnm`,
// `fcmgt`, ...) with `#[inline(never)]` wrappers, and reads back the 128-bit result
// STRAIGHT off the silicon (`str q0`). Each emitted fact is therefore a
// `:= rfl`-strength HARDWARE theorem — the SAME oracle tier as the AArch64 NEON
// INTEGER bridge, one notch ABOVE the Rosetta/qemu tier the x86/RISC-V FP bridges
// use. This is the FP analog of gen_aarch64_neon_silicon_truth.rs.
//
// otool-confirm the real NEON-FP mnemonics in the built binary:
//   otool -tv <bin> | grep -E 'fadd\.4s|fmul\.2d|fminnm\.|fcmgt\.|fsqrt\.'
// (the macro-generated wrappers each contain exactly one packed NEON-FP instruction.)
//
// GRID (no silent truncation; deterministic): a per-lane FP EDGE alphabet
//   {+0, -0, +Inf, -Inf, qNaN, sNaN, smallest subnormal, largest subnormal,
//    smallest normal, largest normal, +1.0, -1.0, +2.0, a tie-to-even rounding
//    case, two deterministic LCG "random" finite values}
// is packed into the 128-bit operands as every-lane-uniform values + alternating
// A/B mixes over edge pairs + a few fully-random vectors. f32 (.2S/.4S) and f64
// (.2D) have their own alphabets. The grid GUARANTEES per-lane NaN/Inf/zero edges
// AND ordered unequal pairs (so the min/max/compare NaN-vs-number distinctions are
// load-bearing).
//
// AArch64-SPECIFIC FP semantics recorded (modeled AS ARM by the in-house encoders):
//   * FMIN/FMAX are NaN-PROPAGATING (any NaN operand -> NaN result; the selected
//     FPProcessNaN). FMINNM/FMAXNM are IEEE-2008 minNum/maxNum (a lone qNaN -> the
//     NUMBER; sNaN or both-NaN -> NaN). -0 < +0 for all four.
//   * FCMEQ/FCMGT/FCMGE produce per-lane all-ones / all-zero masks (ordered; NaN -> 0).
//
// Regenerate (run ON the M4):
//   rustc -O crates/trust-cg-verify/tests/fixtures/gen_aarch64_neon_fp_silicon_truth.rs \
//       -o /tmp/gen_neon_fp && /tmp/gen_neon_fp \
//       crates/trust-cg-verify/tests/fixtures/aarch64_neon_fp_silicon_truth.json

use std::arch::asm;
use std::collections::BTreeMap;
use std::fmt::Write as _;

// ===========================================================================
// NATIVE NEON-FP wrappers — each runs ONE real packed FP instruction on the M4.
// `str q0` reads back the FULL 128-bit register; for a 64-bit (.2S, D-register)
// arrangement the hardware ZEROES the upper 64 bits.
// ===========================================================================

macro_rules! neon_fp_bin {
    ($name:ident, $mnem:literal) => {
        #[inline(never)]
        fn $name(a: u128, b: u128) -> u128 {
            let mut out: u128 = 0;
            unsafe {
                asm!(
                    "ldr q1, [{a}]",
                    "ldr q2, [{b}]",
                    $mnem,
                    "str q0, [{o}]",
                    a = in(reg) &a, b = in(reg) &b, o = in(reg) &mut out,
                    out("v0") _, out("v1") _, out("v2") _,
                );
            }
            out
        }
    };
}

macro_rules! neon_fp_un {
    ($name:ident, $mnem:literal) => {
        #[inline(never)]
        fn $name(a: u128) -> u128 {
            let mut out: u128 = 0;
            unsafe {
                asm!(
                    "ldr q1, [{a}]",
                    $mnem,
                    "str q0, [{o}]",
                    a = in(reg) &a, o = in(reg) &mut out,
                    out("v0") _, out("v1") _,
                );
            }
            out
        }
    };
}

// ---- FADD / FSUB / FMUL / FDIV (arr3: .2S, .4S, .2D) ----
neon_fp_bin!(fadd_2s, "fadd v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fadd_4s, "fadd v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fadd_2d, "fadd v0.2d, v1.2d, v2.2d");
neon_fp_bin!(fsub_2s, "fsub v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fsub_4s, "fsub v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fsub_2d, "fsub v0.2d, v1.2d, v2.2d");
neon_fp_bin!(fmul_2s, "fmul v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fmul_4s, "fmul v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fmul_2d, "fmul v0.2d, v1.2d, v2.2d");
neon_fp_bin!(fdiv_2s, "fdiv v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fdiv_4s, "fdiv v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fdiv_2d, "fdiv v0.2d, v1.2d, v2.2d");

// ---- FNEG / FABS / FSQRT (unary, arr3) ----
neon_fp_un!(fneg_2s, "fneg v0.2s, v1.2s");
neon_fp_un!(fneg_4s, "fneg v0.4s, v1.4s");
neon_fp_un!(fneg_2d, "fneg v0.2d, v1.2d");
neon_fp_un!(fabs_2s, "fabs v0.2s, v1.2s");
neon_fp_un!(fabs_4s, "fabs v0.4s, v1.4s");
neon_fp_un!(fabs_2d, "fabs v0.2d, v1.2d");
neon_fp_un!(fsqrt_2s, "fsqrt v0.2s, v1.2s");
neon_fp_un!(fsqrt_4s, "fsqrt v0.4s, v1.4s");
neon_fp_un!(fsqrt_2d, "fsqrt v0.2d, v1.2d");

// ---- FCMEQ / FCMGT / FCMGE (compare, arr3) ----
neon_fp_bin!(fcmeq_2s, "fcmeq v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fcmeq_4s, "fcmeq v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fcmeq_2d, "fcmeq v0.2d, v1.2d, v2.2d");
neon_fp_bin!(fcmgt_2s, "fcmgt v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fcmgt_4s, "fcmgt v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fcmgt_2d, "fcmgt v0.2d, v1.2d, v2.2d");
neon_fp_bin!(fcmge_2s, "fcmge v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fcmge_4s, "fcmge v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fcmge_2d, "fcmge v0.2d, v1.2d, v2.2d");

// ---- FMIN / FMAX (NaN-propagating) + FMINNM / FMAXNM (IEEE minNum) (arr3) ----
neon_fp_bin!(fmin_2s, "fmin v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fmin_4s, "fmin v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fmin_2d, "fmin v0.2d, v1.2d, v2.2d");
neon_fp_bin!(fmax_2s, "fmax v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fmax_4s, "fmax v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fmax_2d, "fmax v0.2d, v1.2d, v2.2d");
neon_fp_bin!(fminnm_2s, "fminnm v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fminnm_4s, "fminnm v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fminnm_2d, "fminnm v0.2d, v1.2d, v2.2d");
neon_fp_bin!(fmaxnm_2s, "fmaxnm v0.2s, v1.2s, v2.2s");
neon_fp_bin!(fmaxnm_4s, "fmaxnm v0.4s, v1.4s, v2.4s");
neon_fp_bin!(fmaxnm_2d, "fmaxnm v0.2d, v1.2d, v2.2d");

// ===========================================================================
// GRID generation
// ===========================================================================

/// A small deterministic LCG so the "random" operands are reproducible.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
}

/// Per-lane f32 EDGE alphabet (raw bits, low 32). Guarantees +-0/+-Inf/qNaN/sNaN/
/// subnormals/min-max-normal/+-1/+2/a tie case + 2 deterministic randoms.
fn f32_alphabet(rng: &mut Lcg) -> Vec<u32> {
    vec![
        0x0000_0000,             // +0
        0x8000_0000,             // -0
        0x7f80_0000,             // +Inf
        0xff80_0000,             // -Inf
        0x7fc0_0000,             // qNaN (canonical)
        0x7f80_0001,             // sNaN
        0x0000_0001,             // smallest subnormal
        0x007f_ffff,             // largest subnormal
        0x0080_0000,             // smallest normal
        0x7f7f_ffff,             // largest normal
        0x3f80_0000,             // +1.0
        0xbf80_0000,             // -1.0
        0x4000_0000,             // +2.0
        0x3f80_0001,             // 1.0 + 1ulp (rounding-sensitive)
        (rng.next() as u32) & 0x7fff_ffff | 0x3000_0000, // finite-ish random
        (rng.next() as u32) | 0xb000_0000,               // negative finite-ish random
    ]
}

/// Per-lane f64 EDGE alphabet (raw bits).
fn f64_alphabet(rng: &mut Lcg) -> Vec<u64> {
    vec![
        0x0000_0000_0000_0000,   // +0
        0x8000_0000_0000_0000,   // -0
        0x7ff0_0000_0000_0000,   // +Inf
        0xfff0_0000_0000_0000,   // -Inf
        0x7ff8_0000_0000_0000,   // qNaN (canonical)
        0x7ff0_0000_0000_0001,   // sNaN
        0x0000_0000_0000_0001,   // smallest subnormal
        0x000f_ffff_ffff_ffff,   // largest subnormal
        0x0010_0000_0000_0000,   // smallest normal
        0x7fef_ffff_ffff_ffff,   // largest normal
        0x3ff0_0000_0000_0000,   // +1.0
        0xbff0_0000_0000_0000,   // -1.0
        0x4000_0000_0000_0000,   // +2.0
        0x3ff0_0000_0000_0001,   // 1.0 + 1ulp
        (rng.next() & 0x7fff_ffff_ffff_ffff) | 0x3000_0000_0000_0000, // finite-ish random
        rng.next() | 0xb000_0000_0000_0000,                          // negative finite-ish random
    ]
}

/// Pack `n` lanes of `bits` each (lanes[0] = least-significant) into a u128.
fn pack(lanes: &[u64], bits: u32) -> u128 {
    let mut v: u128 = 0;
    for (i, &lane) in lanes.iter().enumerate() {
        v |= (lane as u128) << (i as u32 * bits);
    }
    v
}

/// Build the deterministic operand grid for an FP arrangement of `n` lanes of
/// `bits` (alphabet given as raw lane bits): every-lane-uniform over the alphabet,
/// alternating A/B over edge pairs, and a handful of mixed-edge vectors.
fn operand_grid(n: u32, bits: u32, alpha: &[u64]) -> Vec<u128> {
    let mut out = Vec::new();
    // 1. every lane = the same alphabet value (covers all per-lane edges uniform).
    for &x in alpha {
        let lanes = vec![x; n as usize];
        out.push(pack(&lanes, bits));
    }
    // 2. alternating x,y,x,y over ordered edge pairs (mixes NaN/Inf/zero with
    //    finite, GUARANTEEING per-vector ordered-unequal + NaN-vs-number lanes).
    let pairs = [
        (10usize, 12usize), // +1.0 / +2.0  (ordered unequal)
        (0, 1),             // +0 / -0      (zero ordering)
        (4, 10),            // qNaN / +1.0  (lone-NaN min/max)
        (5, 10),            // sNaN / +1.0  (sNaN minNum-forces-NaN)
        (2, 11),            // +Inf / -1.0
        (3, 12),            // -Inf / +2.0
        (8, 9),             // smallest/largest normal
        (6, 7),             // subnormals
    ];
    for &(i, j) in &pairs {
        if i < alpha.len() && j < alpha.len() {
            let lanes: Vec<u64> = (0..n).map(|k| if k % 2 == 0 { alpha[i] } else { alpha[j] }).collect();
            out.push(pack(&lanes, bits));
        }
    }
    out
}

#[derive(Clone)]
struct Fact {
    op: String,
    arrangement: String,
    kind: String, // "binary" | "unary" | "compare"
    lane_bits: u32,
    total_bits: u32,
    a: u128,
    b: u128,
    result: u128,
    theorem: String,
}

fn hex128(v: u128) -> String {
    format!("0x{:032x}", v)
}

fn arr_of(name: &str) -> (u32, u32, u32) {
    match name {
        "2s" => (2, 32, 64),
        "4s" => (4, 32, 128),
        "2d" => (2, 64, 128),
        _ => unreachable!(),
    }
}

fn main() {
    let out_path = std::env::args().nth(1).unwrap_or_else(|| {
        "crates/trust-cg-verify/tests/fixtures/aarch64_neon_fp_silicon_truth.json".to_string()
    });

    let mut rng = Lcg(0x0fed_cba9_8765_4321);
    let mut facts: Vec<Fact> = Vec::new();
    let mut per_op: BTreeMap<String, usize> = BTreeMap::new();

    let push = |facts: &mut Vec<Fact>, per_op: &mut BTreeMap<String, usize>, f: Fact| {
        *per_op.entry(f.op.clone()).or_default() += 1;
        facts.push(f);
    };

    // Build per-arrangement operand grids once (deterministic).
    let alpha_f32: Vec<u64> = f32_alphabet(&mut rng).into_iter().map(|x| x as u64).collect();
    let alpha_f64: Vec<u64> = f64_alphabet(&mut rng);
    let grid = |an: &str| -> Vec<u128> {
        let (n, bits, _) = arr_of(an);
        let alpha = if bits == 32 { &alpha_f32 } else { &alpha_f64 };
        operand_grid(n, bits, alpha)
    };

    // ---- binary arithmetic: fadd/fsub/fmul/fdiv over arr3 ----
    let bin: &[(&str, &[(&str, fn(u128, u128) -> u128)])] = &[
        ("fadd", &[("2s", fadd_2s), ("4s", fadd_4s), ("2d", fadd_2d)]),
        ("fsub", &[("2s", fsub_2s), ("4s", fsub_4s), ("2d", fsub_2d)]),
        ("fmul", &[("2s", fmul_2s), ("4s", fmul_4s), ("2d", fmul_2d)]),
        ("fdiv", &[("2s", fdiv_2s), ("4s", fdiv_4s), ("2d", fdiv_2d)]),
    ];
    // ---- compare: fcmeq/fcmgt/fcmge over arr3 ----
    let cmp: &[(&str, &[(&str, fn(u128, u128) -> u128)])] = &[
        ("fcmeq", &[("2s", fcmeq_2s), ("4s", fcmeq_4s), ("2d", fcmeq_2d)]),
        ("fcmgt", &[("2s", fcmgt_2s), ("4s", fcmgt_4s), ("2d", fcmgt_2d)]),
        ("fcmge", &[("2s", fcmge_2s), ("4s", fcmge_4s), ("2d", fcmge_2d)]),
    ];
    // ---- min/max family over arr3 ----
    let mm: &[(&str, &[(&str, fn(u128, u128) -> u128)])] = &[
        ("fmin", &[("2s", fmin_2s), ("4s", fmin_4s), ("2d", fmin_2d)]),
        ("fmax", &[("2s", fmax_2s), ("4s", fmax_4s), ("2d", fmax_2d)]),
        ("fminnm", &[("2s", fminnm_2s), ("4s", fminnm_4s), ("2d", fminnm_2d)]),
        ("fmaxnm", &[("2s", fmaxnm_2s), ("4s", fmaxnm_4s), ("2d", fmaxnm_2d)]),
    ];

    for (kind, group) in [("binary", bin), ("compare", cmp), ("binary", mm)] {
        for (op, variants) in group.iter() {
            for (an, f) in variants.iter() {
                let (_n, bits, total) = arr_of(an);
                let av = grid(an);
                let bv = grid(an);
                let mut i = 0usize;
                for &a in &av {
                    for &b in &bv {
                        let r = f(a, b);
                        push(&mut facts, &mut per_op, Fact {
                            op: op.to_string(), arrangement: an.to_string(), kind: kind.to_string(),
                            lane_bits: bits, total_bits: total, a, b,
                            result: r, theorem: format!("neon_fp_{op}_{an}_{i}"),
                        });
                        i += 1;
                    }
                }
            }
        }
    }

    // ---- unary: fneg/fabs/fsqrt over arr3 ----
    let un: &[(&str, &[(&str, fn(u128) -> u128)])] = &[
        ("fneg", &[("2s", fneg_2s), ("4s", fneg_4s), ("2d", fneg_2d)]),
        ("fabs", &[("2s", fabs_2s), ("4s", fabs_4s), ("2d", fabs_2d)]),
        ("fsqrt", &[("2s", fsqrt_2s), ("4s", fsqrt_4s), ("2d", fsqrt_2d)]),
    ];
    for (op, variants) in un {
        for (an, f) in variants.iter() {
            let (_n, bits, total) = arr_of(an);
            let av = grid(an);
            for (i, &a) in av.iter().enumerate() {
                let r = f(a);
                push(&mut facts, &mut per_op, Fact {
                    op: op.to_string(), arrangement: an.to_string(), kind: "unary".into(),
                    lane_bits: bits, total_bits: total, a, b: 0,
                    result: r, theorem: format!("neon_fp_{op}_{an}_{i}"),
                });
            }
        }
    }

    // ===========================================================================
    // Emit JSON (hand-rolled to avoid any deps; deterministic field order).
    // ===========================================================================
    let total = facts.len();
    let mut s = String::new();
    s.push_str("{\n");
    s.push_str(" \"_header\": {\n");
    s.push_str("  \"purpose\": \"AArch64 lane-wise FP NEON BARE-SILICON ground truth for the B-aarch64-neon-fp differential bridge: each fact is a REAL Apple M4 result, produced by running the actual lane-wise FP NEON instruction natively via std::arch::asm! over q-registers (no Rosetta/qemu/Clean-chip-file). SAME oracle tier as the AArch64 NEON integer bridge; one notch ABOVE the Rosetta/qemu tier the x86/RISC-V FP bridges use.\",\n");
    s.push_str("  \"oracle\": \"m4-silicon-native\",\n");
    s.push_str("  \"oracle_note\": \"Apple M4 (native AArch64). Each (op, arrangement) has an #[inline(never)] wrapper that ldr q1/q2, runs ONE packed FP NEON instruction (fadd v0.4s, ...; fmul v0.2d; fminnm; fcmgt; fsqrt), and str q0 the 128-bit result. otool -tv confirms the real mnemonics. 64-bit (.2S, D-register) arrangements zero the upper 64 bits in hardware.\",\n");
    s.push_str("  \"arm_fp_semantics\": \"FMIN/FMAX = NaN-PROPAGATING (any NaN -> NaN, the FPProcessNaN-selected/quieted input); FMINNM/FMAXNM = IEEE-2008 minNum/maxNum (lone qNaN -> the NUMBER; sNaN or both-NaN -> NaN); -0 < +0 for all four. FCMEQ/FCMGT/FCMGE -> per-lane all-ones/all-zero ordered masks (NaN -> 0). Modeled AS ARM by the in-house encoders, NOT RISC-V minimumNumber, NOT x86 MINSS-second-operand.\",\n");
    s.push_str("  \"determinism\": \"deterministic: a fixed-seed LCG drives the 2 random finite values in each per-lane FP edge alphabet (+-0/+-Inf/qNaN/sNaN/subnormals/min-max-normal/+-1/+2/tie); the grid is every-lane-uniform + alternating edge pairs (incl NaN-vs-number, ordered-unequal, zero-ordering).\",\n");
    s.push_str("  \"regen\": \"rustc -O crates/trust-cg-verify/tests/fixtures/gen_aarch64_neon_fp_silicon_truth.rs -o /tmp/gen_neon_fp && /tmp/gen_neon_fp crates/trust-cg-verify/tests/fixtures/aarch64_neon_fp_silicon_truth.json\",\n");
    s.push_str("  \"operands_encoding\": \"a/b/result are 0x-prefixed 32-hex-digit 128-bit values, lane 0 in the low bits; f32 lanes for .2S/.4S, f64 lanes for .2D. kind discriminates binary/unary/compare.\",\n");
    let _ = write!(s, "  \"included_fact_count\": {total},\n");
    s.push_str("  \"included_per_op\": {\n");
    let n_ops = per_op.len();
    for (k, (op, cnt)) in per_op.iter().enumerate() {
        let comma = if k + 1 < n_ops { "," } else { "" };
        let _ = write!(s, "   \"{op}\": {cnt}{comma}\n");
    }
    s.push_str("  }\n");
    s.push_str(" },\n");
    s.push_str(" \"_accounting\": {\n");
    let _ = write!(s, "  \"total_attempted\": {total},\n");
    let _ = write!(s, "  \"emitted\": {total},\n");
    let _ = write!(s, "  \"value_facts\": {total},\n");
    s.push_str("  \"trap_facts\": 0,\n");
    let _ = write!(s, "  \"op_families\": {n_ops}\n");
    s.push_str(" },\n");
    s.push_str(" \"facts\": [\n");
    for (i, f) in facts.iter().enumerate() {
        let comma = if i + 1 < facts.len() { "," } else { "" };
        let _ = write!(
            s,
            "  {{\"op\": \"{}\", \"arrangement\": \"{}\", \"kind\": \"{}\", \"lane_bits\": {}, \"total_bits\": {}, \"a\": \"{}\", \"b\": \"{}\", \"result\": \"{}\", \"theorem\": \"{}\"}}{}\n",
            f.op, f.arrangement, f.kind, f.lane_bits, f.total_bits,
            hex128(f.a), hex128(f.b), hex128(f.result), f.theorem, comma
        );
    }
    s.push_str(" ]\n}\n");

    std::fs::write(&out_path, s).expect("write fixture");
    eprintln!("emitted {total} NEON-FP silicon facts across {n_ops} op families -> {out_path}");
}
