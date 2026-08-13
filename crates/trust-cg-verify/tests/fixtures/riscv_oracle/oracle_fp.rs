// oracle_fp.rs — THE qemu-system-riscv64 SOFTWARE-GOLDEN-MODEL ORACLE HARNESS
// for the RISC-V F/D SCALAR FLOATING-POINT differential bridge (task #96,
// FRONTIER 2 — the FP analog of oracle.rs which covers RV64 integer ALU).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// What this is
// ===========================================================================
// The RISC-V scalar-FP analog of oracle.rs. It executes each trust-cg RV64
// F/D floating-point op via a REAL RV64 F/D-extension instruction (explicit
// inline assembly over the FLOAT register file — NOT a Rust f32/f64 operator)
// over an IEEE EDGE GRID of bit patterns and records the result the INDEPENDENT
// EXECUTOR (qemu-system-riscv64, a software golden model of the RISC-V ISA)
// produced, AS RAW BITS.
//
// Why this defeats root-cause #2 for RV64 FP: the in-house RISC-V FP encoders
// (riscv_semantics.rs encode_fadd/.../encode_fmin/encode_fcvt_to_int_*) evaluate
// through the silicon-validated INTEGER-ONLY fp_bitmodel. A shared mis-encoding
// in that model — OR a wrong RISC-V-specific decision (modeling FMIN as x86
// MINSD, or FCVT-NaN as 0 instead of INT_MAX) — that qemu does NOT also make is
// CAUGHT by the bridge against these facts.
//
// ===========================================================================
// Enabling FP on the bare-metal `virt` machine
// ===========================================================================
// The FPU starts OFF (mstatus.FS = 0 = Off); any F/D instruction then traps as
// illegal. _start sets mstatus.FS = 1 (Initial) via `csrrsi mstatus, (1<<13)`
// BEFORE any FP instruction runs. With FS != 0 the F/D extension is live.
//
// ===========================================================================
// Honesty: the op MUST be a real RV64 F/D instruction
// ===========================================================================
// Each op is an EXPLICIT RV64 F/D instruction via `core::arch::asm!`. Operands
// are moved GPR<->FPR with fmv.d.x / fmv.w.x (load the bit pattern into a float
// register) and the result read back with fmv.x.d / fmv.x.w (for FP results) or
// straight out a GPR (for FEQ/FLT/FLE and FCVT-to-int). The bit patterns are
// `read_volatile` from a runtime grid in `.data`, so the compiler cannot
// constant-fold the op — the value qemu records is the result of qemu DECODING
// AND EXECUTING the actual F/D instruction word.
//
// f32 single-precision values occupy the LOW 32 bits of a float register;
// NaN-BOXING (RISC-V Section 11.3): a 32-bit value in a 64-bit FPR must have its
// upper 32 bits all-ones, else it reads as a canonical NaN. We construct f32
// operands with fmv.w.x (which NaN-boxes) and read results with fmv.x.w.
//
// ===========================================================================
// Output
// ===========================================================================
// A single JSON document over the UART: a provenance `_header`, a `facts` array
// of {op, theorem, fmt ("s"/"d"), in_bits (hex raw operand patterns), result
// (hex raw bits), result_width}, and an `_accounting` block (total_attempted ==
// emitted). gen_riscv_fp_qemu_truth.sh captures it -> riscv_fp_qemu_truth.json.

#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    unsafe { core::ptr::write_volatile(TEST, 0x3333) }
    loop {}
}

const UART: *mut u8 = 0x1000_0000 as *mut u8;
const TEST: *mut u32 = 0x0010_0000 as *mut u32;

core::arch::global_asm!(
    ".section .text.start",
    ".globl _start",
    "_start:",
    "  la sp, _stack_top",
    // Enable the FPU: set mstatus.FS = 01 (Initial). bit 13 = 0x2000.
    "  li t0, 0x2000",
    "  csrrs zero, mstatus, t0",
    "  call rust_main",
    "1: j 1b",
);

#[inline(always)]
unsafe fn putc(c: u8) {
    core::ptr::write_volatile(UART, c);
}
unsafe fn puts(s: &[u8]) {
    for &c in s {
        putc(c);
    }
}
unsafe fn put_hex_u64(v: u64) {
    putc(b'0');
    putc(b'x');
    for i in (0..16).rev() {
        let nib = ((v >> (i * 4)) & 0xf) as u8;
        putc(if nib < 10 { b'0' + nib } else { b'a' + (nib - 10) });
    }
}
unsafe fn put_dec_u64(mut v: u64) {
    if v == 0 {
        putc(b'0');
        return;
    }
    let mut buf = [0u8; 20];
    let mut n = 0;
    while v > 0 {
        buf[n] = b'0' + (v % 10) as u8;
        v /= 10;
        n += 1;
    }
    while n > 0 {
        n -= 1;
        putc(buf[n]);
    }
}

// ---------------------------------------------------------------------------
// RV64 F/D op primitives — each is a SINGLE real F/D instruction over the FLOAT
// registers, with GPR<->FPR moves to load operands and read the result.
// ---------------------------------------------------------------------------

macro_rules! fd_bin_d {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u64, b: u64) -> u64 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    "fmv.d.x ft0, {a}",
                    "fmv.d.x ft1, {b}",
                    concat!($insn, " ft2, ft0, ft1"),
                    "fmv.x.d {r}, ft2",
                    a = in(reg) a, b = in(reg) b, r = out(reg) r,
                    out("ft0") _, out("ft1") _, out("ft2") _,
                    options(nostack)
                );
            }
            r
        }
    };
}
macro_rules! fd_un_d {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    "fmv.d.x ft0, {a}",
                    concat!($insn, " ft2, ft0"),
                    "fmv.x.d {r}, ft2",
                    a = in(reg) a, r = out(reg) r,
                    out("ft0") _, out("ft2") _,
                    options(nostack)
                );
            }
            r
        }
    };
}
// Double compares write a GPR 0/1.
macro_rules! fd_cmp_d {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u64, b: u64) -> u64 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    "fmv.d.x ft0, {a}",
                    "fmv.d.x ft1, {b}",
                    concat!($insn, " {r}, ft0, ft1"),
                    a = in(reg) a, b = in(reg) b, r = out(reg) r,
                    out("ft0") _, out("ft1") _,
                    options(nostack)
                );
            }
            r
        }
    };
}

// Single (f32): NaN-box on the way in (fmv.w.x), read low-32 (fmv.x.w).
macro_rules! fd_bin_s {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u32, b: u32) -> u32 {
            let r: u64;
            let ax = a as u64;
            let bx = b as u64;
            unsafe {
                core::arch::asm!(
                    "fmv.w.x ft0, {a}",
                    "fmv.w.x ft1, {b}",
                    concat!($insn, " ft2, ft0, ft1"),
                    "fmv.x.w {r}, ft2",
                    a = in(reg) ax, b = in(reg) bx, r = out(reg) r,
                    out("ft0") _, out("ft1") _, out("ft2") _,
                    options(nostack)
                );
            }
            r as u32
        }
    };
}
macro_rules! fd_un_s {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u32) -> u32 {
            let r: u64;
            let ax = a as u64;
            unsafe {
                core::arch::asm!(
                    "fmv.w.x ft0, {a}",
                    concat!($insn, " ft2, ft0"),
                    "fmv.x.w {r}, ft2",
                    a = in(reg) ax, r = out(reg) r,
                    out("ft0") _, out("ft2") _,
                    options(nostack)
                );
            }
            r as u32
        }
    };
}
macro_rules! fd_cmp_s {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u32, b: u32) -> u64 {
            let r: u64;
            let ax = a as u64;
            let bx = b as u64;
            unsafe {
                core::arch::asm!(
                    "fmv.w.x ft0, {a}",
                    "fmv.w.x ft1, {b}",
                    concat!($insn, " {r}, ft0, ft1"),
                    a = in(reg) ax, b = in(reg) bx, r = out(reg) r,
                    out("ft0") _, out("ft1") _,
                    options(nostack)
                );
            }
            r
        }
    };
}

fd_bin_d!(rv_fadd_d, "fadd.d");
fd_bin_d!(rv_fsub_d, "fsub.d");
fd_bin_d!(rv_fmul_d, "fmul.d");
fd_bin_d!(rv_fdiv_d, "fdiv.d");
fd_un_d!(rv_fsqrt_d, "fsqrt.d");
fd_bin_d!(rv_fmin_d, "fmin.d");
fd_bin_d!(rv_fmax_d, "fmax.d");
fd_bin_d!(rv_fsgnj_d, "fsgnj.d");
fd_bin_d!(rv_fsgnjn_d, "fsgnjn.d");
fd_bin_d!(rv_fsgnjx_d, "fsgnjx.d");
fd_cmp_d!(rv_feq_d, "feq.d");
fd_cmp_d!(rv_flt_d, "flt.d");
fd_cmp_d!(rv_fle_d, "fle.d");

fd_bin_s!(rv_fadd_s, "fadd.s");
fd_bin_s!(rv_fsub_s, "fsub.s");
fd_bin_s!(rv_fmul_s, "fmul.s");
fd_bin_s!(rv_fdiv_s, "fdiv.s");
fd_un_s!(rv_fsqrt_s, "fsqrt.s");
fd_bin_s!(rv_fmin_s, "fmin.s");
fd_bin_s!(rv_fmax_s, "fmax.s");
fd_bin_s!(rv_fsgnj_s, "fsgnj.s");
fd_bin_s!(rv_fsgnjn_s, "fsgnjn.s");
fd_bin_s!(rv_fsgnjx_s, "fsgnjx.s");
fd_cmp_s!(rv_feq_s, "feq.s");
fd_cmp_s!(rv_flt_s, "flt.s");
fd_cmp_s!(rv_fle_s, "fle.s");

// FCVT f -> int (read a GPR). RTZ (truncate) form: the trust-cg FcvtToInt
// lowering's mode. `, rtz` is the static rounding-mode field.
macro_rules! fcvt_to_int_d {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    "fmv.d.x ft0, {a}",
                    concat!($insn, " {r}, ft0, rtz"),
                    a = in(reg) a, r = out(reg) r,
                    out("ft0") _,
                    options(nostack)
                );
            }
            r
        }
    };
}
macro_rules! fcvt_to_int_s {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u32) -> u64 {
            let r: u64;
            let ax = a as u64;
            unsafe {
                core::arch::asm!(
                    "fmv.w.x ft0, {a}",
                    concat!($insn, " {r}, ft0, rtz"),
                    a = in(reg) ax, r = out(reg) r,
                    out("ft0") _,
                    options(nostack)
                );
            }
            r
        }
    };
}
fcvt_to_int_d!(rv_fcvt_w_d, "fcvt.w.d"); // f64 -> i32 (sext to 64 in rd)
fcvt_to_int_d!(rv_fcvt_wu_d, "fcvt.wu.d"); // f64 -> u32 (sext to 64)
fcvt_to_int_d!(rv_fcvt_l_d, "fcvt.l.d"); // f64 -> i64
fcvt_to_int_d!(rv_fcvt_lu_d, "fcvt.lu.d"); // f64 -> u64
fcvt_to_int_s!(rv_fcvt_w_s, "fcvt.w.s");
fcvt_to_int_s!(rv_fcvt_wu_s, "fcvt.wu.s");
fcvt_to_int_s!(rv_fcvt_l_s, "fcvt.l.s");
fcvt_to_int_s!(rv_fcvt_lu_s, "fcvt.lu.s");

// FCVT int -> f (move int into a GPR, convert into an FPR, read bits back).
macro_rules! fcvt_from_int_d {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    concat!($insn, " ft2, {a}"),
                    "fmv.x.d {r}, ft2",
                    a = in(reg) a, r = out(reg) r,
                    out("ft2") _,
                    options(nostack)
                );
            }
            r
        }
    };
}
macro_rules! fcvt_from_int_s {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u32 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    concat!($insn, " ft2, {a}"),
                    "fmv.x.w {r}, ft2",
                    a = in(reg) a, r = out(reg) r,
                    out("ft2") _,
                    options(nostack)
                );
            }
            r as u32
        }
    };
}
fcvt_from_int_d!(rv_fcvt_d_w, "fcvt.d.w"); // i32 -> f64
fcvt_from_int_d!(rv_fcvt_d_wu, "fcvt.d.wu"); // u32 -> f64
fcvt_from_int_d!(rv_fcvt_d_l, "fcvt.d.l"); // i64 -> f64
fcvt_from_int_d!(rv_fcvt_d_lu, "fcvt.d.lu"); // u64 -> f64
fcvt_from_int_s!(rv_fcvt_s_w, "fcvt.s.w");
fcvt_from_int_s!(rv_fcvt_s_wu, "fcvt.s.wu");
fcvt_from_int_s!(rv_fcvt_s_l, "fcvt.s.l");
fcvt_from_int_s!(rv_fcvt_s_lu, "fcvt.s.lu");

// FCVT between FP formats.
#[inline(never)]
fn rv_fcvt_s_d(a: u64) -> u32 {
    let r: u64;
    unsafe {
        core::arch::asm!(
            "fmv.d.x ft0, {a}",
            "fcvt.s.d ft2, ft0",
            "fmv.x.w {r}, ft2",
            a = in(reg) a, r = out(reg) r,
            out("ft0") _, out("ft2") _,
            options(nostack)
        );
    }
    r as u32
}
#[inline(never)]
fn rv_fcvt_d_s(a: u32) -> u64 {
    let r: u64;
    let ax = a as u64;
    unsafe {
        core::arch::asm!(
            "fmv.w.x ft0, {a}",
            "fcvt.d.s ft2, ft0",
            "fmv.x.d {r}, ft2",
            a = in(reg) ax, r = out(reg) r,
            out("ft0") _, out("ft2") _,
            options(nostack)
        );
    }
    r
}

// ---------------------------------------------------------------------------
// IEEE edge grids (raw bit patterns), in `.data` (volatile reads, no fold).
// ---------------------------------------------------------------------------
static GD: [u64; 18] = [
    0x0000_0000_0000_0000, // +0
    0x8000_0000_0000_0000, // -0
    0x3FF0_0000_0000_0000, // +1.0
    0xBFF0_0000_0000_0000, // -1.0
    0x4000_0000_0000_0000, // +2.0
    0x3FE0_0000_0000_0000, // +0.5
    0x7FF0_0000_0000_0000, // +Inf
    0xFFF0_0000_0000_0000, // -Inf
    0x7FF8_0000_0000_0000, // qNaN (canonical)
    0x7FF0_0000_0000_0001, // sNaN
    0x0000_0000_0000_0001, // smallest subnormal
    0x000F_FFFF_FFFF_FFFF, // largest subnormal
    0x0010_0000_0000_0000, // smallest normal
    0x7FEF_FFFF_FFFF_FFFF, // largest normal
    0x4009_21FB_5444_2D18, // pi
    0x3FF8_0000_0000_0000, // 1.5
    0x405E_C000_0000_0000, // 123.0
    0xC05E_C000_0000_0000, // -123.0
];
static GS: [u32; 18] = [
    0x0000_0000, // +0
    0x8000_0000, // -0
    0x3F80_0000, // +1.0
    0xBF80_0000, // -1.0
    0x4000_0000, // +2.0
    0x3F00_0000, // +0.5
    0x7F80_0000, // +Inf
    0xFF80_0000, // -Inf
    0x7FC0_0000, // qNaN (canonical)
    0x7F80_0001, // sNaN
    0x0000_0001, // smallest subnormal
    0x007F_FFFF, // largest subnormal
    0x0080_0000, // smallest normal
    0x7F7F_FFFF, // largest normal
    0x4049_0FDB, // pi
    0x3FC0_0000, // 1.5
    0x42F6_0000, // 123.0
    0xC2F6_0000, // -123.0
];
// Integer grid for the int->FP converts (and reused conceptually as the
// expected output domain of FP->int). Covers small, edge, and out-of-range-for-f
// magnitudes.
static GI: [u64; 14] = [
    0x0,
    0x1,
    0xFFFF_FFFF_FFFF_FFFF, // -1 / UINT64_MAX
    0x8000_0000_0000_0000, // INT64_MIN
    0x7FFF_FFFF_FFFF_FFFF, // INT64_MAX
    0x0000_0000_8000_0000, // INT32_MIN as low-32
    0x0000_0000_7FFF_FFFF, // INT32_MAX
    0x0000_0000_FFFF_FFFF, // UINT32_MAX
    0x7B,                  // 123
    0xFFFF_FFFF_FFFF_FF85, // -123
    0x0000_0000_0000_0100, // 256
    0x0000_0010_0000_0000, // 2^36 (not representable exactly in f32)
    0x0000_0000_00FF_FFFF, // 2^24-1
    0x0000_0000_0100_0001, // 2^24+1 (f32 rounding boundary)
];

const NGD: usize = 18;
const NGS: usize = 18;
const NGI: usize = 14;

#[inline(always)]
fn gd(i: usize) -> u64 {
    unsafe { core::ptr::read_volatile(&GD[i]) }
}
#[inline(always)]
fn gs(i: usize) -> u32 {
    unsafe { core::ptr::read_volatile(&GS[i]) }
}
#[inline(always)]
fn gi(i: usize) -> u64 {
    unsafe { core::ptr::read_volatile(&GI[i]) }
}

// ---------------------------------------------------------------------------
// JSON emission with exact accounting.
// ---------------------------------------------------------------------------
static mut TOTAL_ATTEMPTED: u64 = 0;
static mut EMITTED: u64 = 0;
static mut FIRST: bool = true;

unsafe fn emit_fact(op: &[u8], fmt: u8, in_bits: &[u64], result: u64, result_width: u32) {
    TOTAL_ATTEMPTED += 1;
    if !FIRST {
        puts(b",\n");
    }
    FIRST = false;
    puts(b"  {\"op\":\"");
    puts(op);
    puts(b"\",\"theorem\":\"qemu_fp_");
    puts(op);
    putc(b'_');
    put_dec_u64(EMITTED);
    puts(b"\",\"fmt\":\"");
    putc(fmt);
    puts(b"\",\"in_bits\":[");
    for (i, v) in in_bits.iter().enumerate() {
        if i != 0 {
            putc(b',');
        }
        putc(b'"');
        put_hex_u64(*v);
        putc(b'"');
    }
    puts(b"],\"result\":\"");
    put_hex_u64(result);
    puts(b"\",\"result_width\":");
    put_dec_u64(result_width as u64);
    putc(b'}');
    EMITTED += 1;
}

#[no_mangle]
pub extern "C" fn rust_main() -> ! {
    unsafe {
        puts(b"{\n");
        puts(b" \"_header\": {\n");
        puts(b"  \"purpose\": \"RV64 F/D scalar floating-point ground truth for the B-riscv-fp differential bridge: each fact is a result produced by an INDEPENDENT RISC-V executor (qemu-system-riscv64, a software golden model of the ISA) DECODING+EXECUTING a real F/D instruction word over an IEEE edge grid, validating trust-cg's RISC-V FP SmtExpr encoders (riscv_semantics.rs) which route through the silicon-validated integer-only fp_bitmodel.\",\n");
        puts(b"  \"oracle\": \"qemu-system-riscv64\",\n");
        puts(b"  \"oracle_kind\": \"software-golden-model (QEMU TCG machine emulator); independent executor of the real RV64 F/D instruction encodings; one notch below bare silicon. Defeats root-cause #2 for the RV64 scalar-FP ops.\",\n");
        puts(b"  \"machine\": \"virt (RISC-V VirtIO board), -bios none, kernel at 0x80000000, mstatus.FS=Initial\",\n");
        puts(b"  \"code_producer\": \"rustc --target riscv64gc-unknown-none-elf; each op is an explicit single RV64 F/D instruction via core::arch::asm! over volatile runtime bit patterns moved through the float register file (fmv.d.x/fmv.w.x in, fmv.x.d/fmv.x.w or GPR out) -- qemu decodes+executes the actual instruction word.\",\n");
        puts(b"  \"qemu_version\": \"@QEMU_VERSION@\",\n");
        puts(b"  \"recorded_on\": \"@DATE@\",\n");
        puts(b"  \"regen\": \"crates/trust-cg-verify/tests/fixtures/riscv_oracle/gen_riscv_fp_qemu_truth.sh\",\n");
        puts(b"  \"riscv_specific\": \"FMIN/FMAX = IEEE-754-2019 minimumNumber/maximumNumber (lone NaN incl sNaN returns the NUMBER; both NaN -> canonical qNaN 0x7fc0../0x7ff8..; -0 < +0). FCVT-to-int SATURATES with NaN -> max (signed INT_MAX 2^31-1/2^63-1, unsigned UINT_MAX). All NaN-producing ops emit the canonical NaN. fcvt-to-int uses static rtz rounding.\",\n");
        puts(b"  \"inclusion_policy\": \"the RV64 F/D ops trust-cg has an in-house encoder for (riscv_semantics.rs), in single (.s) and double (.d) forms, over an IEEE edge grid (+-0,+-1,2,0.5,+-Inf,qNaN,sNaN,min/max subnormal,min/max normal,pi,1.5,123,-123); FCVT to/from int over an integer edge grid (0,1,-1,INT_MIN/MAX,UINT_MAX,123,-123,2^24+-1,2^36). No FP exceptions are trapped (FS!=0, default exception handling: flags set, no trap), so every fact is a VALUE.\",\n");
        puts(b"  \"result_encoding\": \"result is the RAW result BITS in hex: FP-result ops give the result float's bit pattern (f32 in the low 32, NaN-unboxed via fmv.x.w); FEQ/FLT/FLE give the 0/1 GPR; FCVT-to-int gives the GPR (low result_width bits significant -- W-forms are sign/zero-extended in rd, the bridge compares the low result_width).\"\n");
        puts(b" },\n");
        puts(b" \"facts\": [\n");

        // ===================== binary arithmetic / minmax / sgnj (D) ==========
        let mut two = [0u64; 2];
        let mut one = [0u64; 1];
        let mut i = 0;
        while i < NGD {
            let mut j = 0;
            while j < NGD {
                let a = gd(i);
                let b = gd(j);
                two[0] = a;
                two[1] = b;
                emit_fact(b"fadd.d", b'd', &two, rv_fadd_d(a, b), 64);
                emit_fact(b"fsub.d", b'd', &two, rv_fsub_d(a, b), 64);
                emit_fact(b"fmul.d", b'd', &two, rv_fmul_d(a, b), 64);
                emit_fact(b"fdiv.d", b'd', &two, rv_fdiv_d(a, b), 64);
                emit_fact(b"fmin.d", b'd', &two, rv_fmin_d(a, b), 64);
                emit_fact(b"fmax.d", b'd', &two, rv_fmax_d(a, b), 64);
                emit_fact(b"fsgnj.d", b'd', &two, rv_fsgnj_d(a, b), 64);
                emit_fact(b"fsgnjn.d", b'd', &two, rv_fsgnjn_d(a, b), 64);
                emit_fact(b"fsgnjx.d", b'd', &two, rv_fsgnjx_d(a, b), 64);
                emit_fact(b"feq.d", b'd', &two, rv_feq_d(a, b), 1);
                emit_fact(b"flt.d", b'd', &two, rv_flt_d(a, b), 1);
                emit_fact(b"fle.d", b'd', &two, rv_fle_d(a, b), 1);
                j += 1;
            }
            i += 1;
        }
        // ===================== unary FSQRT (D) ================================
        i = 0;
        while i < NGD {
            let a = gd(i);
            one[0] = a;
            emit_fact(b"fsqrt.d", b'd', &one, rv_fsqrt_d(a), 64);
            i += 1;
        }

        // ===================== binary arithmetic / minmax / sgnj (S) ==========
        i = 0;
        while i < NGS {
            let mut j = 0;
            while j < NGS {
                let a = gs(i);
                let b = gs(j);
                two[0] = a as u64;
                two[1] = b as u64;
                emit_fact(b"fadd.s", b's', &two, rv_fadd_s(a, b) as u64, 32);
                emit_fact(b"fsub.s", b's', &two, rv_fsub_s(a, b) as u64, 32);
                emit_fact(b"fmul.s", b's', &two, rv_fmul_s(a, b) as u64, 32);
                emit_fact(b"fdiv.s", b's', &two, rv_fdiv_s(a, b) as u64, 32);
                emit_fact(b"fmin.s", b's', &two, rv_fmin_s(a, b) as u64, 32);
                emit_fact(b"fmax.s", b's', &two, rv_fmax_s(a, b) as u64, 32);
                emit_fact(b"fsgnj.s", b's', &two, rv_fsgnj_s(a, b) as u64, 32);
                emit_fact(b"fsgnjn.s", b's', &two, rv_fsgnjn_s(a, b) as u64, 32);
                emit_fact(b"fsgnjx.s", b's', &two, rv_fsgnjx_s(a, b) as u64, 32);
                emit_fact(b"feq.s", b's', &two, rv_feq_s(a, b), 1);
                emit_fact(b"flt.s", b's', &two, rv_flt_s(a, b), 1);
                emit_fact(b"fle.s", b's', &two, rv_fle_s(a, b), 1);
                j += 1;
            }
            i += 1;
        }
        i = 0;
        while i < NGS {
            let a = gs(i);
            one[0] = a as u64;
            emit_fact(b"fsqrt.s", b's', &one, rv_fsqrt_s(a) as u64, 32);
            i += 1;
        }

        // ===================== FCVT f -> int (D source) ======================
        i = 0;
        while i < NGD {
            let a = gd(i);
            one[0] = a;
            emit_fact(b"fcvt.w.d", b'd', &one, rv_fcvt_w_d(a), 32);
            emit_fact(b"fcvt.wu.d", b'd', &one, rv_fcvt_wu_d(a), 32);
            emit_fact(b"fcvt.l.d", b'd', &one, rv_fcvt_l_d(a), 64);
            emit_fact(b"fcvt.lu.d", b'd', &one, rv_fcvt_lu_d(a), 64);
            i += 1;
        }
        // ===================== FCVT f -> int (S source) ======================
        i = 0;
        while i < NGS {
            let a = gs(i);
            one[0] = a as u64;
            emit_fact(b"fcvt.w.s", b's', &one, rv_fcvt_w_s(a), 32);
            emit_fact(b"fcvt.wu.s", b's', &one, rv_fcvt_wu_s(a), 32);
            emit_fact(b"fcvt.l.s", b's', &one, rv_fcvt_l_s(a), 64);
            emit_fact(b"fcvt.lu.s", b's', &one, rv_fcvt_lu_s(a), 64);
            i += 1;
        }

        // ===================== FCVT int -> f =================================
        i = 0;
        while i < NGI {
            let a = gi(i);
            one[0] = a;
            emit_fact(b"fcvt.d.w", b'd', &one, rv_fcvt_d_w(a), 64);
            emit_fact(b"fcvt.d.wu", b'd', &one, rv_fcvt_d_wu(a), 64);
            emit_fact(b"fcvt.d.l", b'd', &one, rv_fcvt_d_l(a), 64);
            emit_fact(b"fcvt.d.lu", b'd', &one, rv_fcvt_d_lu(a), 64);
            emit_fact(b"fcvt.s.w", b's', &one, rv_fcvt_s_w(a) as u64, 32);
            emit_fact(b"fcvt.s.wu", b's', &one, rv_fcvt_s_wu(a) as u64, 32);
            emit_fact(b"fcvt.s.l", b's', &one, rv_fcvt_s_l(a) as u64, 32);
            emit_fact(b"fcvt.s.lu", b's', &one, rv_fcvt_s_lu(a) as u64, 32);
            i += 1;
        }

        // ===================== FCVT fp -> fp =================================
        i = 0;
        while i < NGD {
            let a = gd(i);
            one[0] = a;
            emit_fact(b"fcvt.s.d", b'd', &one, rv_fcvt_s_d(a) as u64, 32);
            i += 1;
        }
        i = 0;
        while i < NGS {
            let a = gs(i);
            one[0] = a as u64;
            emit_fact(b"fcvt.d.s", b's', &one, rv_fcvt_d_s(a), 64);
            i += 1;
        }

        // ---- close facts array + accounting trailer ----
        puts(b"\n ],\n");
        puts(b" \"_accounting\": {\n");
        puts(b"  \"total_attempted\": ");
        put_dec_u64(TOTAL_ATTEMPTED);
        puts(b",\n");
        puts(b"  \"emitted\": ");
        put_dec_u64(EMITTED);
        puts(b",\n");
        puts(b"  \"value_facts\": ");
        put_dec_u64(EMITTED);
        puts(b",\n");
        puts(b"  \"trap_facts\": 0,\n");
        puts(b"  \"sampled_grid\": {\"gd\":");
        put_dec_u64(NGD as u64);
        puts(b",\"gs\":");
        put_dec_u64(NGS as u64);
        puts(b",\"gi\":");
        put_dec_u64(NGI as u64);
        puts(b"}\n");
        puts(b" }\n");
        puts(b"}\n");

        if TOTAL_ATTEMPTED == EMITTED {
            puts(b"@@ORACLE_OK ");
            put_dec_u64(EMITTED);
            puts(b"@@\n");
        } else {
            puts(b"@@ORACLE_ACCOUNTING_ERROR@@\n");
        }

        core::ptr::write_volatile(TEST, 0x5555);
    }
    loop {}
}
