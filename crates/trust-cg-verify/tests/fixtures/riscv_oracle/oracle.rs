// oracle.rs — THE qemu-system-riscv64 SOFTWARE-GOLDEN-MODEL ORACLE HARNESS
// (campaign #3, RISC-V — task #93).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// What this is
// ===========================================================================
// The RISC-V analog of the AArch64 on-chip differential harness and the x86
// Rosetta harness (gen_x86_rosetta_truth.c). It executes each trust-cg RV64
// integer ALU/shift/compare op via a REAL RV64 machine instruction (explicit
// inline assembly — NOT a Rust arithmetic operator) over a SAMPLED operand grid
// and records the result the INDEPENDENT EXECUTOR produced.
//
// The "chip" here is `qemu-system-riscv64` — QEMU's independent RISC-V machine
// emulator (TCG), a SOFTWARE GOLDEN MODEL of the RISC-V ISA, NOT a second
// in-house trust-cg model. The facts it emits independently VALIDATE trust-cg's
// RISC-V SmtExpr encoders (riscv_semantics.rs) and DEFEAT root-cause #2 (both
// equivalence sides authored in-house) for the RV64 integer ops — a shared
// mis-encoding in riscv_semantics.rs that this oracle does not also make is
// CAUGHT here. (qemu is a software model, one notch below bare silicon — it does
// not run on a physical RISC-V part — but it is a genuinely INDEPENDENT executor
// of the actual instruction encodings.)
//
// ===========================================================================
// Why bare-metal Rust + qemu-system (not qemu-user)
// ===========================================================================
// On macOS, Homebrew's `qemu` ships only the FULL-MACHINE emulators
// (`qemu-system-*`); the Linux user-mode emulator `qemu-riscv64` is Linux-only
// (it emulates the Linux syscall ABI). So instead of a static Linux RV64 ELF run
// under qemu-user, this is a `#![no_std] #![no_main]` BARE-METAL RV64 program
// that boots directly on QEMU's `virt` machine (entry 0x80000000), executes the
// real RV64 instructions, and reports results by MMIO:
//   * results out the 16550 UART at 0x10000000 (NS16550A on `virt`), and
//   * clean power-off via the SiFive test finisher at 0x100000 (write 0x5555).
// Apple `clang` has NO RISC-V backend, so the RV64 machine code is produced by
// `rustc --target riscv64gc-unknown-none-elf` (the LLVM RISC-V backend bundled
// in rustc) — genuine RV64 codegen, not hand-traced.
//
// ===========================================================================
// Honesty: the op MUST be a real RV64 instruction
// ===========================================================================
// Every op is emitted as an EXPLICIT RV64 instruction via `core::arch::asm!`
// with register operands loaded by `read_volatile` from a runtime operand table
// in `.data`. The compiler cannot constant-fold the op away (the inputs are
// volatile runtime reads and the op is opaque inline asm), so the value qemu
// records is the result of qemu DECODING AND EXECUTING that instruction word —
// the property that makes this an independent oracle and not a Rust-level model.
//
// ===========================================================================
// Output
// ===========================================================================
// Prints, over the UART, a single JSON document: a provenance `_header` (oracle,
// qemu version + machine + date, the rustc target, inclusion policy) plus a
// `facts` array of {op, theorem id, width, operands (decimal-u64), result hex}
// and an `_accounting` block (total_attempted == emitted, no silent truncation).
// gen_riscv_qemu_truth.sh captures that and writes riscv_qemu_truth.json.
//
// W-FORM modeling: a W-form op (e.g. ADDW/SLLW) computes in 32 bits; RV64
// sign-extends the 32-bit result to 64. trust-cg's width-polymorphic encoders,
// when evaluated at width 32, produce the LOW-32 result (no 64-bit extension) —
// matching the AArch64/x86 bridges' "result is the low-32 value" convention. So
// every W-form result is recorded as its LOW 32 bits (maskw). The faithful 32-bit
// computation is identical to the low 32 bits of the architectural sign-extended
// result. W-form shifts mask the amount with &0x1F (5 bits) — exactly what the
// encoders produce at operand-width 32 (mask = width-1 = 31).

#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    // On panic, power off with a non-zero finisher code so the harness run FAILS
    // loudly rather than silently truncating the fact stream.
    unsafe { core::ptr::write_volatile(TEST, 0x3333) }
    loop {}
}

// ---------------------------------------------------------------------------
// MMIO addresses on QEMU's RISC-V `virt` machine.
// ---------------------------------------------------------------------------
const UART: *mut u8 = 0x1000_0000 as *mut u8; // NS16550A serial, THR at +0.
const TEST: *mut u32 = 0x0010_0000 as *mut u32; // SiFive test finisher.

// ---------------------------------------------------------------------------
// Entry: set up a stack, jump to rust_main. Linked at 0x80000000 (virt load).
// ---------------------------------------------------------------------------
core::arch::global_asm!(
    ".section .text.start",
    ".globl _start",
    "_start:",
    "  la sp, _stack_top",
    "  call rust_main",
    "1: j 1b",
);

// ---------------------------------------------------------------------------
// UART output primitives.
// ---------------------------------------------------------------------------
#[inline(always)]
unsafe fn putc(c: u8) {
    core::ptr::write_volatile(UART, c);
}

unsafe fn puts(s: &[u8]) {
    for &c in s {
        putc(c);
    }
}

/// Print `v` as a fixed `0x` + 16-hex-digit lowercase string.
unsafe fn put_hex_u64(v: u64) {
    putc(b'0');
    putc(b'x');
    for i in (0..16).rev() {
        let nib = ((v >> (i * 4)) & 0xf) as u8;
        putc(if nib < 10 { b'0' + nib } else { b'a' + (nib - 10) });
    }
}

/// Print `v` as an unsigned decimal (no leading zeros; "0" for zero).
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
// RV64 op primitives — each is a SINGLE real RV64 instruction in inline asm.
// `in(reg)`/`out(reg)` force the operands into GPRs and the op into the actual
// instruction word qemu decodes. The X (64-bit) and W (32-bit) forms are
// distinct RV64 instructions (ADD vs ADDW, SLL vs SLLW, ...).
// ---------------------------------------------------------------------------

macro_rules! rv_rr {
    ($name:ident, $insn:literal) => {
        #[inline(never)]
        fn $name(a: u64, b: u64) -> u64 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    concat!($insn, " {r}, {a}, {b}"),
                    r = out(reg) r, a = in(reg) a, b = in(reg) b,
                    options(pure, nomem, nostack)
                );
            }
            r
        }
    };
}

// RV64I/M register-register (X, 64-bit).
rv_rr!(rv_add, "add");
rv_rr!(rv_sub, "sub");
rv_rr!(rv_mul, "mul");
rv_rr!(rv_and, "and");
rv_rr!(rv_or, "or");
rv_rr!(rv_xor, "xor");
rv_rr!(rv_sll, "sll");
rv_rr!(rv_srl, "srl");
rv_rr!(rv_sra, "sra");
rv_rr!(rv_slt, "slt");
rv_rr!(rv_sltu, "sltu");

// RV64I register-register W-forms (32-bit op, result sign-extended to 64).
rv_rr!(rv_addw, "addw");
rv_rr!(rv_subw, "subw");
rv_rr!(rv_sllw, "sllw");
rv_rr!(rv_srlw, "srlw");
rv_rr!(rv_sraw, "sraw");
// MULW (low-32 of the 32-bit product, sign-extended).
rv_rr!(rv_mulw, "mulw");
// W-form bitwise are identical to X-form bitwise on the low 32 bits; RISC-V has
// no ANDW/ORW/XORW, so W-form AND/OR/XOR facts are produced by the X-form insn
// with 32-bit operands and the result masked to 32 bits (the encoder at width 32).

// I-type immediate forms. The immediate is a 12-bit signed field encoded in the
// instruction word, so it MUST be a compile-time literal — we sample a fixed set.
macro_rules! rv_ri {
    ($name:ident, $insn:literal, $imm:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    concat!($insn, " {r}, {a}, ", stringify!($imm)),
                    r = out(reg) r, a = in(reg) a,
                    options(pure, nomem, nostack)
                );
            }
            r
        }
    };
}

// ADDI rd, rs1, imm  (sampled imms: 0, 1, -1, 2047 [max+], -2048 [min-]).
rv_ri!(rv_addi_0, "addi", 0);
rv_ri!(rv_addi_1, "addi", 1);
rv_ri!(rv_addi_m1, "addi", -1);
rv_ri!(rv_addi_2047, "addi", 2047);
rv_ri!(rv_addi_m2048, "addi", -2048);

// XORI rd, rs1, imm  (sampled imms: 0, -1 [bitwise NOT], 1 [low-bit flip], 255).
rv_ri!(rv_xori_0, "xori", 0);
rv_ri!(rv_xori_m1, "xori", -1);
rv_ri!(rv_xori_1, "xori", 1);
rv_ri!(rv_xori_255, "xori", 255);

// SLTIU rd, rs1, imm  (sampled imms: 0, 1 [seqz idiom], -1 [sext to all-ones], 100).
rv_ri!(rv_sltiu_0, "sltiu", 0);
rv_ri!(rv_sltiu_1, "sltiu", 1);
rv_ri!(rv_sltiu_m1, "sltiu", -1);
rv_ri!(rv_sltiu_100, "sltiu", 100);

// SLLI / SRLI rd, rs1, shamt (shamt is a 6-bit field 0..63; sampled set).
macro_rules! rv_shamt {
    ($name:ident, $insn:literal, $sh:literal) => {
        #[inline(never)]
        fn $name(a: u64) -> u64 {
            let r: u64;
            unsafe {
                core::arch::asm!(
                    concat!($insn, " {r}, {a}, ", stringify!($sh)),
                    r = out(reg) r, a = in(reg) a,
                    options(pure, nomem, nostack)
                );
            }
            r
        }
    };
}
rv_shamt!(rv_slli_0, "slli", 0);
rv_shamt!(rv_slli_1, "slli", 1);
rv_shamt!(rv_slli_31, "slli", 31);
rv_shamt!(rv_slli_63, "slli", 63);
rv_shamt!(rv_srli_0, "srli", 0);
rv_shamt!(rv_srli_1, "srli", 1);
rv_shamt!(rv_srli_31, "srli", 31);
rv_shamt!(rv_srli_63, "srli", 63);

// ---------------------------------------------------------------------------
// Operand grids, in `.data` (real runtime reads -> the op cannot be folded).
// Edge cases first (0, 1, -1, INT_MIN, INT_MAX, UINT_MAX, powers, random),
// then a couple deterministic "random-ish" values.
// ---------------------------------------------------------------------------
static G64: [u64; 12] = [
    0x0,
    0x1,
    0xFFFF_FFFF_FFFF_FFFF, // -1 / UINT64_MAX
    0x8000_0000_0000_0000, // INT64_MIN
    0x7FFF_FFFF_FFFF_FFFF, // INT64_MAX
    0x2,
    0x100,
    0xFFFF_FFFF, // UINT32_MAX (boundary for W-domain bits)
    0x1_0000_0000,
    0xDEAD_BEEF_CAFE_BABE,
    0x1234_5678_9ABC_DEF0,
    0x8000_0000, // INT32_MIN as a low-32 pattern
];

static G32: [u64; 12] = [
    0x0,
    0x1,
    0xFFFF_FFFF, // -1 / UINT32_MAX
    0x8000_0000, // INT32_MIN
    0x7FFF_FFFF, // INT32_MAX
    0x2,
    0x100,
    0xFFFF,
    0x1_0000,
    0xDEAD_BEEF,
    0x1234_5678,
    0xCAFE_BABE,
];

// Shift-count grid: deliberately includes counts >= width to exercise the
// hardware amount mask (&0x3F at XLEN=64, &0x1F for W-forms) — the #57 contract
// the masked encoders model (count>=width is where masked != SMT clamp-to-0).
static SHIFTC: [u64; 16] = [0, 1, 4, 7, 8, 15, 16, 31, 32, 33, 47, 63, 64, 65, 127, 200];

const NG64: usize = 12;
const NG32: usize = 12;
const NSC: usize = 16;

#[inline(always)]
fn g64(i: usize) -> u64 {
    unsafe { core::ptr::read_volatile(&G64[i]) }
}
#[inline(always)]
fn g32(i: usize) -> u64 {
    unsafe { core::ptr::read_volatile(&G32[i]) }
}
#[inline(always)]
fn sc(i: usize) -> u64 {
    unsafe { core::ptr::read_volatile(&SHIFTC[i]) }
}

#[inline(always)]
fn maskw(v: u64) -> u64 {
    v & 0xFFFF_FFFF
}

// ---------------------------------------------------------------------------
// JSON emission with exact accounting (no silent truncation).
// ---------------------------------------------------------------------------
static mut TOTAL_ATTEMPTED: u64 = 0;
static mut EMITTED: u64 = 0;
static mut FIRST: bool = true;

unsafe fn emit_value(op: &[u8], width: u32, ops: &[u64], result: u64) {
    TOTAL_ATTEMPTED += 1;
    if !FIRST {
        puts(b",\n");
    }
    FIRST = false;
    puts(b"  {\"op\":\"");
    puts(op);
    puts(b"\",\"theorem\":\"qemu_");
    puts(op);
    putc(b'_');
    put_dec_u64(EMITTED);
    puts(b"\",\"width\":");
    put_dec_u64(width as u64);
    puts(b",\"operands\":[");
    for (i, v) in ops.iter().enumerate() {
        if i != 0 {
            putc(b',');
        }
        put_dec_u64(*v);
    }
    puts(b"],\"result\":\"");
    put_hex_u64(result);
    puts(b"\"}");
    EMITTED += 1;
}

#[no_mangle]
pub extern "C" fn rust_main() -> ! {
    unsafe {
        puts(b"{\n");
        puts(b" \"_header\": {\n");
        puts(b"  \"purpose\": \"RV64 integer ALU/shift/compare ground truth for the B-riscv-qemu differential bridge: each fact is a result produced by an INDEPENDENT RISC-V executor (qemu-system-riscv64, a software golden model of the ISA), NOT a second in-house model, validating trust-cg's RISC-V SmtExpr encoders.\",\n");
        puts(b"  \"oracle\": \"qemu-system-riscv64\",\n");
        puts(b"  \"oracle_kind\": \"software-golden-model (QEMU TCG machine emulator); independent executor of the real RV64 instruction encodings; one notch below bare silicon (not a physical RISC-V part). Defeats root-cause #2 (both equivalence sides in-house) for the RV64 integer ops.\",\n");
        puts(b"  \"machine\": \"virt (RISC-V VirtIO board), -bios none, kernel loaded at 0x80000000\",\n");
        puts(b"  \"code_producer\": \"rustc --target riscv64gc-unknown-none-elf (LLVM RISC-V backend); each op is an explicit single RV64 instruction via core::arch::asm! over volatile runtime operands (NOT a Rust operator, NOT constant-folded) -- qemu decodes+executes the actual instruction word.\",\n");
        // qemu_version / recorded_on are spliced in by the regen script (it knows
        // the live `qemu-system-riscv64 --version`); placeholders here are replaced.
        puts(b"  \"qemu_version\": \"@QEMU_VERSION@\",\n");
        puts(b"  \"recorded_on\": \"@DATE@\",\n");
        puts(b"  \"regen\": \"crates/trust-cg-verify/tests/fixtures/riscv_oracle/gen_riscv_qemu_truth.sh\",\n");
        puts(b"  \"inclusion_policy\": \"the RV64 integer ALU/shift/compare ops trust-cg has an in-house encoder for (riscv_semantics.rs), sampled over an edge-case+random grid (0,1,-1,INT_MIN,INT_MAX,UINT_MAX,powers,random) in X(64) and W(32) forms; shift counts include >=width to exercise the &0x3F / &0x1F amount mask (#57). I-type immediates (ADDI/XORI/SLTIU/SLLI/SRLI) sample fixed instruction-literal immediate fields. No traps: RV64 integer ALU does not trap (DIV/REM by zero is defined, and DIV/REM are out of the reconstructable ALU set).\",\n");
        puts(b"  \"operands_encoding\": \"each operand is the low `width` bits as an unsigned decimal u64 (matching the AArch64/x86 fixtures); result is hex (0x..). W-form results are the LOW 32 bits (the width-32 encoder result; equal to the low 32 of the architectural sign-extended W result).\",\n");
        puts(b"  \"comparison_convention\": \"SLT/SLTU/SLTIU results are 0/1 (the boolean bit), matching encode_slt/encode_sltu/encode_sltiu (1-bit). Register shifts use the FAITHFUL amount-masked encoders.\"\n");
        puts(b" },\n");
        puts(b" \"facts\": [\n");

        let mut ops2 = [0u64; 2];
        let mut ops1 = [0u64; 1];

        // ============ binary arith/logic/compare — X (64-bit) ============
        let mut i = 0;
        while i < NG64 {
            let mut j = 0;
            while j < NG64 {
                let a = g64(i);
                let b = g64(j);
                ops2[0] = a;
                ops2[1] = b;
                emit_value(b"add", 64, &ops2, rv_add(a, b));
                emit_value(b"sub", 64, &ops2, rv_sub(a, b));
                emit_value(b"mul", 64, &ops2, rv_mul(a, b));
                emit_value(b"and", 64, &ops2, rv_and(a, b));
                emit_value(b"or", 64, &ops2, rv_or(a, b));
                emit_value(b"xor", 64, &ops2, rv_xor(a, b));
                emit_value(b"slt", 64, &ops2, rv_slt(a, b));
                emit_value(b"sltu", 64, &ops2, rv_sltu(a, b));
                j += 1;
            }
            i += 1;
        }

        // ============ binary arith/logic/compare — W (32-bit) ============
        // ADDW/SUBW/MULW are real W instructions (result masked to low 32).
        // AND/OR/XOR/SLT/SLTU have no W instruction; the width-32 encoder result
        // is the X-form op on the low 32 bits, so we run the X insn and mask.
        i = 0;
        while i < NG32 {
            let mut j = 0;
            while j < NG32 {
                let a = g32(i);
                let b = g32(j);
                ops2[0] = a;
                ops2[1] = b;
                emit_value(b"addw", 32, &ops2, maskw(rv_addw(a, b)));
                emit_value(b"subw", 32, &ops2, maskw(rv_subw(a, b)));
                emit_value(b"mulw", 32, &ops2, maskw(rv_mulw(a, b)));
                emit_value(b"andw", 32, &ops2, maskw(rv_and(a, b)));
                emit_value(b"orw", 32, &ops2, maskw(rv_or(a, b)));
                emit_value(b"xorw", 32, &ops2, maskw(rv_xor(a, b)));
                // SLT/SLTU at width 32: compare the low-32 values as signed/unsigned
                // 32-bit. The X-form slt/sltu compares 64-bit, so the operands must
                // be the SIGN/ZERO-extended low 32 first. We feed the already-32-bit
                // grid values; for signed slt we must sign-extend to 64 to match the
                // width-32 encoder's bvslt. Do that explicitly.
                let sa = ((a as u32) as i32 as i64) as u64;
                let sb = ((b as u32) as i32 as i64) as u64;
                emit_value(b"sltw", 32, &ops2, rv_slt(sa, sb)); // signed 32-bit lt
                let ua = a & 0xFFFF_FFFF;
                let ub = b & 0xFFFF_FFFF;
                emit_value(b"sltuw", 32, &ops2, rv_sltu(ua, ub)); // unsigned 32-bit lt
                j += 1;
            }
            i += 1;
        }

        // ============ register shifts — X (64-bit), masked counts ============
        i = 0;
        while i < NG64 {
            let mut k = 0;
            while k < NSC {
                let a = g64(i);
                let c = sc(k);
                ops2[0] = a;
                ops2[1] = c;
                emit_value(b"sll", 64, &ops2, rv_sll(a, c));
                emit_value(b"srl", 64, &ops2, rv_srl(a, c));
                emit_value(b"sra", 64, &ops2, rv_sra(a, c));
                k += 1;
            }
            i += 1;
        }

        // ============ register shifts — W (32-bit), masked counts (&0x1F) ====
        i = 0;
        while i < NG32 {
            let mut k = 0;
            while k < NSC {
                let a = g32(i);
                let c = sc(k);
                ops2[0] = a;
                ops2[1] = c;
                emit_value(b"sllw", 32, &ops2, maskw(rv_sllw(a, c)));
                emit_value(b"srlw", 32, &ops2, maskw(rv_srlw(a, c)));
                emit_value(b"sraw", 32, &ops2, maskw(rv_sraw(a, c)));
                k += 1;
            }
            i += 1;
        }

        // ============ I-type immediates (X, 64-bit) ============
        // The immediate is a fixed instruction-literal field; we record it as the
        // SIGN-EXTENDED 64-bit value in operands[1] so the bridge can rebuild the
        // encoder with imm as a 64-bit bv_const.
        i = 0;
        while i < NG64 {
            let a = g64(i);
            ops2[0] = a;
            // ADDI
            ops2[1] = 0;
            emit_value(b"addi", 64, &ops2, rv_addi_0(a));
            ops2[1] = 1;
            emit_value(b"addi", 64, &ops2, rv_addi_1(a));
            ops2[1] = (-1i64) as u64;
            emit_value(b"addi", 64, &ops2, rv_addi_m1(a));
            ops2[1] = 2047;
            emit_value(b"addi", 64, &ops2, rv_addi_2047(a));
            ops2[1] = (-2048i64) as u64;
            emit_value(b"addi", 64, &ops2, rv_addi_m2048(a));
            // XORI
            ops2[1] = 0;
            emit_value(b"xori", 64, &ops2, rv_xori_0(a));
            ops2[1] = (-1i64) as u64;
            emit_value(b"xori", 64, &ops2, rv_xori_m1(a));
            ops2[1] = 1;
            emit_value(b"xori", 64, &ops2, rv_xori_1(a));
            ops2[1] = 255;
            emit_value(b"xori", 64, &ops2, rv_xori_255(a));
            // SLTIU (result is the 0/1 boolean bit)
            ops2[1] = 0;
            emit_value(b"sltiu", 64, &ops2, rv_sltiu_0(a));
            ops2[1] = 1;
            emit_value(b"sltiu", 64, &ops2, rv_sltiu_1(a));
            ops2[1] = (-1i64) as u64;
            emit_value(b"sltiu", 64, &ops2, rv_sltiu_m1(a));
            ops2[1] = 100;
            emit_value(b"sltiu", 64, &ops2, rv_sltiu_100(a));
            i += 1;
        }

        // ============ immediate-shift forms SLLI / SRLI (X, 64-bit) ==========
        // shamt is the fixed instruction-literal shift amount in operands[1].
        i = 0;
        while i < NG64 {
            let a = g64(i);
            ops2[0] = a;
            ops2[1] = 0;
            emit_value(b"slli", 64, &ops2, rv_slli_0(a));
            ops2[1] = 1;
            emit_value(b"slli", 64, &ops2, rv_slli_1(a));
            ops2[1] = 31;
            emit_value(b"slli", 64, &ops2, rv_slli_31(a));
            ops2[1] = 63;
            emit_value(b"slli", 64, &ops2, rv_slli_63(a));
            ops2[1] = 0;
            emit_value(b"srli", 64, &ops2, rv_srli_0(a));
            ops2[1] = 1;
            emit_value(b"srli", 64, &ops2, rv_srli_1(a));
            ops2[1] = 31;
            emit_value(b"srli", 64, &ops2, rv_srli_31(a));
            ops2[1] = 63;
            emit_value(b"srli", 64, &ops2, rv_srli_63(a));
            i += 1;
        }
        let _ = &mut ops1;

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
        puts(b"  \"sampled_grid\": {\"g64\":");
        put_dec_u64(NG64 as u64);
        puts(b",\"g32\":");
        put_dec_u64(NG32 as u64);
        puts(b",\"shift_counts\":");
        put_dec_u64(NSC as u64);
        puts(b"}\n");
        puts(b" }\n");
        puts(b"}\n");

        // Sentinel so the regen script can confirm a CLEAN, COMPLETE run (the
        // facts JSON ends BEFORE this line; the script strips it).
        if TOTAL_ATTEMPTED == EMITTED {
            puts(b"@@ORACLE_OK ");
            put_dec_u64(EMITTED);
            puts(b"@@\n");
        } else {
            puts(b"@@ORACLE_ACCOUNTING_ERROR@@\n");
        }

        // Clean power-off (SiFive test finisher: 0x5555 = pass).
        core::ptr::write_volatile(TEST, 0x5555);
    }
    loop {}
}
