#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / bitreverse_intrinsics.rs
//
// Regression coverage for LLVM bitreverse intrinsics imported from clang IR.
// Every program compiles for this host's explicit triple (ELF for
// aarch64-unknown-linux-gnu, Mach-O for aarch64-apple-darwin), is read back
// by that container's disassembler and `nm`, and the linked ones run
// natively. The in-tree readers also check both containers on every host.

mod common;

use std::fs;
use std::process::Command;

use common::{
    HOST_TRIPLE, TARGETS, compile_for, compile_for_host, describe_status, disassemble,
    has_vector_insn, link_with_cc, native_host_or_skip, nm_undefined, object_symbol,
    undefined_symbols, unique_temp_dir,
};
use trust_cg_codegen::pipeline::OptLevel;

const LL_BITREVERSE_INTRINSICS: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

declare i32 @llvm.bitreverse.i32(i32)
declare i64 @llvm.bitreverse.i64(i64)

define i32 @main() {
entry:
  %a = call i32 @llvm.bitreverse.i32(i32 -2147483648)
  %b = call i64 @llvm.bitreverse.i64(i64 -9223372036854775808)
  %bt = trunc i64 %b to i32
  %sum = add i32 %a, %bt
  ret i32 %sum
}
"#;

const LL_HANDWRITTEN_REVERSEBITS: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

define i32 @ReverseBits32(i32 %n) {
entry:
  %slot = alloca i32, align 4
  store i32 %n, ptr %slot, align 4
  %3 = load i32, ptr %slot, align 4
  %4 = lshr i32 %3, 1
  %5 = and i32 %4, 1431655765
  %6 = load i32, ptr %slot, align 4
  %7 = and i32 %6, 1431655765
  %8 = shl i32 %7, 1
  %9 = or i32 %5, %8
  store i32 %9, ptr %slot, align 4
  %10 = load i32, ptr %slot, align 4
  %11 = lshr i32 %10, 2
  %12 = and i32 %11, 858993459
  %13 = load i32, ptr %slot, align 4
  %14 = and i32 %13, 858993459
  %15 = shl i32 %14, 2
  %16 = or i32 %12, %15
  store i32 %16, ptr %slot, align 4
  %17 = load i32, ptr %slot, align 4
  %18 = lshr i32 %17, 4
  %19 = and i32 %18, 252645135
  %20 = load i32, ptr %slot, align 4
  %21 = and i32 %20, 252645135
  %22 = shl i32 %21, 4
  %23 = or i32 %19, %22
  store i32 %23, ptr %slot, align 4
  %24 = load i32, ptr %slot, align 4
  %25 = and i32 %24, -16777216
  %26 = lshr i32 %25, 24
  %27 = load i32, ptr %slot, align 4
  %28 = and i32 %27, 16711680
  %29 = lshr i32 %28, 8
  %30 = or i32 %26, %29
  %31 = load i32, ptr %slot, align 4
  %32 = and i32 %31, 65280
  %33 = shl i32 %32, 8
  %34 = or i32 %30, %33
  %35 = load i32, ptr %slot, align 4
  %36 = and i32 %35, 255
  %37 = shl i32 %36, 24
  %38 = or i32 %34, %37
  ret i32 %38
}

define i64 @ReverseBits64(i64 %n) {
entry:
  %slot = alloca i64, align 8
  store i64 %n, ptr %slot, align 8
  %3 = load i64, ptr %slot, align 8
  %4 = lshr i64 %3, 1
  %5 = and i64 %4, 6148914691236517205
  %6 = load i64, ptr %slot, align 8
  %7 = and i64 %6, 6148914691236517205
  %8 = shl i64 %7, 1
  %9 = or i64 %5, %8
  store i64 %9, ptr %slot, align 8
  %10 = load i64, ptr %slot, align 8
  %11 = lshr i64 %10, 2
  %12 = and i64 %11, 3689348814741910323
  %13 = load i64, ptr %slot, align 8
  %14 = and i64 %13, 3689348814741910323
  %15 = shl i64 %14, 2
  %16 = or i64 %12, %15
  store i64 %16, ptr %slot, align 8
  %17 = load i64, ptr %slot, align 8
  %18 = lshr i64 %17, 4
  %19 = and i64 %18, 1085102592571150095
  %20 = load i64, ptr %slot, align 8
  %21 = and i64 %20, 1085102592571150095
  %22 = shl i64 %21, 4
  %23 = or i64 %19, %22
  store i64 %23, ptr %slot, align 8
  %24 = load i64, ptr %slot, align 8
  %25 = and i64 %24, -72057594037927936
  %26 = lshr i64 %25, 56
  %27 = load i64, ptr %slot, align 8
  %28 = and i64 %27, 71776119061217280
  %29 = lshr i64 %28, 40
  %30 = or i64 %26, %29
  %31 = load i64, ptr %slot, align 8
  %32 = and i64 %31, 280375465082880
  %33 = lshr i64 %32, 24
  %34 = or i64 %30, %33
  %35 = load i64, ptr %slot, align 8
  %36 = and i64 %35, 1095216660480
  %37 = lshr i64 %36, 8
  %38 = or i64 %34, %37
  %39 = load i64, ptr %slot, align 8
  %40 = and i64 %39, 255
  %41 = shl i64 %40, 56
  %42 = or i64 %38, %41
  %43 = load i64, ptr %slot, align 8
  %44 = and i64 %43, 65280
  %45 = shl i64 %44, 40
  %46 = or i64 %42, %45
  %47 = load i64, ptr %slot, align 8
  %48 = and i64 %47, 16711680
  %49 = shl i64 %48, 24
  %50 = or i64 %46, %49
  %51 = load i64, ptr %slot, align 8
  %52 = and i64 %51, 4278190080
  %53 = shl i64 %52, 8
  %54 = or i64 %50, %53
  ret i64 %54
}

define i32 @main() {
entry:
  %a = call i32 @ReverseBits32(i32 -2147483648)
  %b = call i64 @ReverseBits64(i64 -9223372036854775808)
  %bt = trunc i64 %b to i32
  %sum = add i32 %a, %bt
  ret i32 %sum
}
"#;

const LL_REVERTBITS_CLANG_O0: &str = include_str!("fixtures/revertBits_clang_o0.ll");

/// The hand-written 32-bit ladder over `%slot` after its initial store, as in
/// `@ReverseBits32` above: `%38` is the reversed value, and the slot is left
/// holding the state after the three swap steps (each byte bit-reversed).
const LL_LADDER32_AFTER_STORE: &str = r#"  %3 = load i32, ptr %slot, align 4
  %4 = lshr i32 %3, 1
  %5 = and i32 %4, 1431655765
  %6 = load i32, ptr %slot, align 4
  %7 = and i32 %6, 1431655765
  %8 = shl i32 %7, 1
  %9 = or i32 %5, %8
  store i32 %9, ptr %slot, align 4
  %10 = load i32, ptr %slot, align 4
  %11 = lshr i32 %10, 2
  %12 = and i32 %11, 858993459
  %13 = load i32, ptr %slot, align 4
  %14 = and i32 %13, 858993459
  %15 = shl i32 %14, 2
  %16 = or i32 %12, %15
  store i32 %16, ptr %slot, align 4
  %17 = load i32, ptr %slot, align 4
  %18 = lshr i32 %17, 4
  %19 = and i32 %18, 252645135
  %20 = load i32, ptr %slot, align 4
  %21 = and i32 %20, 252645135
  %22 = shl i32 %21, 4
  %23 = or i32 %19, %22
  store i32 %23, ptr %slot, align 4
  %24 = load i32, ptr %slot, align 4
  %25 = and i32 %24, -16777216
  %26 = lshr i32 %25, 24
  %27 = load i32, ptr %slot, align 4
  %28 = and i32 %27, 16711680
  %29 = lshr i32 %28, 8
  %30 = or i32 %26, %29
  %31 = load i32, ptr %slot, align 4
  %32 = and i32 %31, 65280
  %33 = shl i32 %32, 8
  %34 = or i32 %30, %33
  %35 = load i32, ptr %slot, align 4
  %36 = and i32 %35, 255
  %37 = shl i32 %36, 24
  %38 = or i32 %34, %37
"#;

/// The hand-written helpers without their `main`, plus three variants of the
/// 32-bit ladder that selection must not fold, so each keeps its stores: the
/// slot's address escapes to a C function, the slot is read again after the
/// ladder, and an i64 argument enters an 8-byte slot through an i64 store
/// whose low half the 32-bit ladder reads (a width mismatch).
fn reversebits_c_reference_module() -> String {
    let helpers = LL_HANDWRITTEN_REVERSEBITS
        .split("define i32 @main()")
        .next()
        .expect("handwritten helpers");
    let ladder = |name: &str, param: &str, slot_ty: &str, tail: &str| {
        let align = if slot_ty == "i64" { 8 } else { 4 };
        format!(
            "define i32 @{name}({param} %n) {{\nentry:\n  %slot = alloca {slot_ty}, align {align}\n  \
             store {param} %n, ptr %slot, align {align}\n{LL_LADDER32_AFTER_STORE}{tail}}}\n\n"
        )
    };
    let mut module = helpers.to_owned();
    module.push_str("declare void @observe32(ptr)\n\n");
    module.push_str(&ladder(
        "ReverseBits32Escaped",
        "i32",
        "i32",
        "  call void @observe32(ptr %slot)\n  ret i32 %38\n",
    ));
    module.push_str(&ladder(
        "ReverseBits32ReadBack",
        "i32",
        "i32",
        "  %again = load i32, ptr %slot, align 4\n  %mixed = xor i32 %38, %again\n  ret i32 %mixed\n",
    ));
    module.push_str(&ladder(
        "ReverseBits32Wide",
        "i64",
        "i64",
        "  ret i32 %38\n",
    ));
    module
}

/// Checks every helper of [`reversebits_c_reference_module`] against a
/// portable C reference over edge values and a pseudo-random sweep. A
/// dropped store shows up as a wrong `observe32` value, read-back or result.
const C_REFERENCE_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

extern uint32_t ReverseBits32(uint32_t);
extern uint64_t ReverseBits64(uint64_t);
extern uint32_t ReverseBits32Escaped(uint32_t);
extern uint32_t ReverseBits32ReadBack(uint32_t);
extern uint32_t ReverseBits32Wide(uint64_t);

static volatile uint32_t observed;
void observe32(uint32_t *slot) { observed = *slot; }

static uint32_t ref32(uint32_t x) {
    uint32_t r = 0;
    for (int i = 0; i < 32; i++) r |= ((x >> i) & 1u) << (31 - i);
    return r;
}
static uint64_t ref64(uint64_t x) {
    uint64_t r = 0;
    for (int i = 0; i < 64; i++) r |= ((x >> i) & 1u) << (63 - i);
    return r;
}
/* The slot after the three swap steps: each byte bit-reversed in place. */
static uint32_t swapped_bytes32(uint32_t x) {
    uint32_t r = 0;
    for (int i = 0; i < 32; i++) r |= ((x >> i) & 1u) << ((i & ~7) + 7 - (i & 7));
    return r;
}

static int check(uint64_t x) {
    uint32_t w = (uint32_t)x;
    if (ReverseBits32(w) != ref32(w)) return 1;
    if (ReverseBits64(x) != ref64(x)) return 2;
    observed = 0xdeadbeefu;
    if (ReverseBits32Escaped(w) != ref32(w)) return 3;
    if (observed != swapped_bytes32(w)) return 4;
    if (ReverseBits32ReadBack(w) != (ref32(w) ^ swapped_bytes32(w))) return 5;
    if (ReverseBits32Wide(x) != ref32(w)) return 6;
    return 0;
}

int main(void) {
    static const uint64_t edges[] = {
        0, 1, 2, 0x80, 0x80000000u, 0xffffffffu, 0x100000000ull,
        0x8000000000000000ull, 0xffffffffffffffffull, 0x0123456789abcdefull,
    };
    unsigned checked = 0;
    for (unsigned i = 0; i < sizeof edges / sizeof edges[0]; i++, checked++) {
        int failure = check(edges[i]);
        if (failure) { printf("edge %u failed check %d\n", i, failure); return failure; }
    }
    uint64_t state = 0x9e3779b97f4a7c15ull;
    for (int i = 0; i < 4096; i++, checked++) {
        state = state * 6364136223846793005ull + 1442695040888963407ull;
        uint64_t x = state ^ (state >> 29);
        int failure = check(x);
        if (failure) { printf("input %d failed check %d\n", i, failure); return failure; }
    }
    printf("checked %u inputs\n", checked);
    return 0;
}
"#;

fn handwritten_reversebits_with_default_ssp() -> String {
    let mut src = LL_HANDWRITTEN_REVERSEBITS
        .replace(
            "define i32 @ReverseBits32(i32 %n) {",
            "define i32 @ReverseBits32(i32 %n) #0 {",
        )
        .replace(
            "define i64 @ReverseBits64(i64 %n) {",
            "define i64 @ReverseBits64(i64 %n) #0 {",
        )
        .replace("define i32 @main() {", "define i32 @main() #0 {");
    src.push_str(
        r#"
attributes #0 = { noinline nounwind ssp uwtable "stack-protector-buffer-size"="8" }
"#,
    );
    src
}

fn assert_rbit_ret_shape(body: &str, symbol: &str, rbit: &str) {
    assert!(
        body.contains(rbit),
        "{symbol} should emit `{rbit}` directly:\n{body}"
    );
    assert_eq!(
        body.matches("rbit\t").count(),
        1,
        "{symbol} should contain exactly one RBIT:\n{body}"
    );
    assert!(body.contains("ret"), "{symbol} should return:\n{body}");
    for forbidden in [
        "stp\t", "ldp\t", "sub\tsp", "add\tsp", "x29", "x27", "x28", "mov\tw0", "mov\tx0",
    ] {
        assert!(
            !body.contains(forbidden),
            "{symbol} should not contain frame/callee-save/copy pattern `{forbidden}`:\n{body}"
        );
    }
}

/// The in-tree Mach-O/ELF reader sees no undefined symbol of `object` that
/// contains `needle` (spelled for `triple`'s container by the caller).
fn assert_no_undefined_containing(object: &[u8], triple: &str, needle: &str, what: &str) {
    let undefined = undefined_symbols(object);
    assert!(
        undefined.iter().all(|name| !name.contains(needle)),
        "{what} (`{triple}`, in-tree reader): `{needle}` left undefined: {undefined:?}"
    );
}

/// `nm -u` of the host-triple object lists no symbol containing any needle.
fn assert_nm_has_no_undefined(obj_path: &std::path::Path, needles: &[String], what: &str) {
    let undefined = nm_undefined(obj_path);
    for needle in needles {
        assert!(
            !undefined.contains(needle.as_str()),
            "{what} (`{HOST_TRIPLE}`, nm -u): `{needle}` left undefined:\n{undefined}"
        );
    }
}

fn assert_no_stack_guard_undefined_symbols(object: &[u8], obj_path: &std::path::Path) {
    let guards = [
        object_symbol(HOST_TRIPLE, "__stack_chk_guard"),
        object_symbol(HOST_TRIPLE, "__stack_chk_fail"),
    ];
    for guard in &guards {
        assert_no_undefined_containing(
            object,
            HOST_TRIPLE,
            guard,
            "default ssp bitreverse helpers should not emit stack guard symbols",
        );
    }
    assert_nm_has_no_undefined(
        obj_path,
        &guards,
        "default ssp bitreverse helpers should not emit stack guard symbols",
    );
}

#[test]
fn imported_revertbits_clang_o0_vectorizes_mixed_width_sub_loop() {
    const TEST: &str = "imported_revertbits_clang_o0_vectorizes_mixed_width_sub_loop";
    if !native_host_or_skip(TEST) {
        return;
    }

    let object = compile_for_host(LL_REVERTBITS_CLANG_O0, "revertbits_clang_o0", OptLevel::O2);
    let dir = unique_temp_dir("revertbits-clang-o0");
    let obj_path = dir.join("revertbits_clang_o0.o");
    let bin_path = dir.join("revertbits_clang_o0");
    fs::write(&obj_path, object).expect("write object");

    let disasm = disassemble(&obj_path, HOST_TRIPLE);
    let main = disasm.function("main");
    for (mnemonic, arrangement) in [
        ("rev32", "8b"),
        ("rbit", "8b"),
        ("rev64", "16b"),
        ("rbit", "16b"),
    ] {
        assert!(
            has_vector_insn(&main, mnemonic, arrangement),
            "main should contain vectorized mixed-width bitreverse op `{mnemonic}.{arrangement}`:\n{main}"
        );
    }

    link_with_cc(&obj_path, &bin_path);
    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert_eq!(
        output.status.code(),
        Some(0),
        "linked binary should exit cleanly, got {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "0x12345678 -> 0x1e6a2c48\n0x123456789012345 -> 0xa2c48091e6a2c480\n"
    );
}

/// revertBits with an imm12 trip bound. ISel folds `icmp slt i32 %i, 1000`
/// into `cmp w, #1000` (`CmpRI`), the form the vectorizer's trip-count
/// adjustment rewrites; 16777216 does not fit imm12 and stays a `CmpRR` it
/// leaves alone. The vector plan scales the induction step by VF, so dividing
/// that same compare's bound by VF as well would run the second loop over
/// only 0..500 and break the program's `sum == 0` self-check.
#[test]
fn imported_revertbits_imm12_trip_bound_runs_every_iteration_at_o2() {
    const TEST: &str = "imported_revertbits_imm12_trip_bound_runs_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    let source = LL_REVERTBITS_CLANG_O0
        .replace("icmp slt i32 %12, 16777216", "icmp slt i32 %12, 1000")
        .replace("icmp slt i32 %30, 16777216", "icmp slt i32 %30, 1000");
    assert_eq!(
        source.matches("icmp slt i32 %").count(),
        2,
        "fixture should keep exactly two loop trip tests"
    );
    assert_eq!(
        source.matches(", 1000\n").count(),
        2,
        "both revertBits loops should use the imm12 trip bound"
    );

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_for_host(&source, "revertbits_clang_o0_imm12_bound", opt_level);
        let dir = unique_temp_dir("revertbits-clang-o0-imm12-bound");
        let obj_path = dir.join("revertbits_imm12_bound.o");
        let bin_path = dir.join("revertbits_imm12_bound");
        fs::write(&obj_path, object).expect("write object");
        link_with_cc(&obj_path, &bin_path);
        let output = Command::new(&bin_path).output().expect("run linked binary");
        assert_eq!(
            output.status.code(),
            Some(0),
            "{opt_level:?}: both loops must cover 0..1000 so the sums cancel, got {}\n\
             stdout:\n{}\nstderr:\n{}",
            describe_status(output.status),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "0x12345678 -> 0x1e6a2c48\n0x123456789012345 -> 0xa2c48091e6a2c480\n"
        );
    }
}

/// Link and run a revertBits variant at O0 and O2. The program subtracts in
/// its second loop what it added in its first, so it exits 0 only when both
/// loops run exactly the same iterations. At O2 the vectorizer rewrites the
/// second (subtracting) loop with a VF=2 induction whose `CmpRR` trip bound it
/// leaves in place, so any extra or missing vector lane breaks the self-check.
fn assert_revertbits_variant_sums_cancel(source: &str, module: &str, what: &str) {
    assert_revertbits_variant_sums_cancel_at_argc(source, module, what, &[1]);
}

/// [`assert_revertbits_variant_sums_cancel`], running each binary once per
/// `argc` (with `argc - 1` arguments).
fn assert_revertbits_variant_sums_cancel_at_argc(
    source: &str,
    module: &str,
    what: &str,
    argcs: &[usize],
) {
    assert_revertbits_variant_prints_at_argc(source, module, what, argcs, REVERTBITS_STDOUT);
}

/// What the revertBits program prints.
const REVERTBITS_STDOUT: &str =
    "0x12345678 -> 0x1e6a2c48\n0x123456789012345 -> 0xa2c48091e6a2c480\n";

/// Link and run a revertBits variant at O0 and O2, once per `argc`, and
/// expect exit 0 and `stdout`.
fn assert_revertbits_variant_prints_at_argc(
    source: &str,
    module: &str,
    what: &str,
    argcs: &[usize],
    stdout: &str,
) {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_for_host(source, module, opt_level);
        let dir = unique_temp_dir(module);
        let obj_path = dir.join(format!("{module}.o"));
        let bin_path = dir.join(module);
        fs::write(&obj_path, object).expect("write object");
        link_with_cc(&obj_path, &bin_path);
        for &argc in argcs {
            let args: Vec<String> = (1..argc).map(|arg| format!("a{arg}")).collect();
            let output = Command::new(&bin_path)
                .args(&args)
                .output()
                .expect("run linked binary");
            assert_eq!(
                output.status.code(),
                Some(0),
                "{opt_level:?}, argc {argc}: {what}, got {}\nstdout:\n{}\nstderr:\n{}",
                describe_status(output.status),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&output.stdout),
                stdout,
                "{opt_level:?}, argc {argc}: {what}"
            );
        }
    }
}

/// revertBits with the odd bound 16777217 (`movz`+`movk`, a `CmpRR` bound the
/// trip adjustment leaves alone). A VF=2 vector loop stepping `i` by 2 under
/// `i < 16777217` would also run lane 16777217, one past the bound.
#[test]
fn imported_revertbits_odd_trip_bound_runs_exactly_every_iteration_at_o2() {
    const TEST: &str = "imported_revertbits_odd_trip_bound_runs_exactly_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    let source = LL_REVERTBITS_CLANG_O0
        .replace("icmp slt i32 %12, 16777216", "icmp slt i32 %12, 16777217")
        .replace("icmp slt i32 %30, 16777216", "icmp slt i32 %30, 16777217");
    assert_eq!(
        source.matches(", 16777217\n").count(),
        2,
        "both revertBits loops should use the odd trip bound"
    );

    assert_revertbits_variant_sums_cancel(
        &source,
        "revertbits_odd_bound",
        "both loops must cover exactly 0..16777217 so the sums cancel",
    );
}

/// revertBits whose subtracting loop starts at `i = 1`. `rbit(0) == 0`, so the
/// sums still cancel. The trip bound stays 16777216, which VF=2 divides, but
/// the loop now runs 16777215 iterations: a vector loop stepping `i` by 2 from
/// 1 under `i < 16777216` would also run lane 16777216.
#[test]
fn imported_revertbits_nonzero_induction_start_runs_exactly_every_iteration_at_o2() {
    const TEST: &str =
        "imported_revertbits_nonzero_induction_start_runs_exactly_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    let source = LL_REVERTBITS_CLANG_O0.replace("store i32 0, ptr %7", "store i32 1, ptr %7");
    assert_eq!(
        source.matches("store i32 1, ptr %7").count(),
        1,
        "the subtracting loop's induction should start at 1"
    );

    assert_revertbits_variant_sums_cancel(
        &source,
        "revertbits_start_one",
        "the loops must cover 0..16777216 and 1..16777216 so the sums cancel",
    );
}

/// revertBits with a runtime trip bound `argc + 4096` (4097 when run without
/// arguments). No constant bound exists, so a VF=2 vector loop stepping `i`
/// by 2 under `i < n` runs lane `n` whenever `n` is odd.
#[test]
fn imported_revertbits_runtime_trip_bound_runs_exactly_every_iteration_at_o2() {
    const TEST: &str = "imported_revertbits_runtime_trip_bound_runs_exactly_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    let source = LL_REVERTBITS_CLANG_O0
        .replace(
            "define i32 @main() #0 {",
            "define i32 @main(i32 %argc, ptr %argv) #0 {",
        )
        .replace(
            "  %7 = alloca i32, align 4\n",
            "  %7 = alloca i32, align 4\n  %bound = add i32 %argc, 4096\n",
        )
        .replace("icmp slt i32 %12, 16777216", "icmp slt i32 %12, %bound")
        .replace("icmp slt i32 %30, 16777216", "icmp slt i32 %30, %bound");
    assert_eq!(
        source.matches(", %bound\n").count(),
        2,
        "both revertBits loops should use the runtime trip bound"
    );
    assert_eq!(
        source.matches("%bound = add i32 %argc, 4096").count(),
        1,
        "main should compute the runtime bound once"
    );

    assert_revertbits_variant_sums_cancel(
        &source,
        "revertbits_runtime_bound",
        "both loops must cover exactly 0..argc+4096 so the sums cancel",
    );
}

/// revertBits with an inclusive bound, `i <= 16777214`: 16777215 iterations
/// although the bound constant is even. A VF=2 vector loop stepping `i` by 2
/// while `i <= 16777214` would also run lane 16777215.
#[test]
fn imported_revertbits_inclusive_trip_bound_runs_exactly_every_iteration_at_o2() {
    const TEST: &str =
        "imported_revertbits_inclusive_trip_bound_runs_exactly_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    let source = LL_REVERTBITS_CLANG_O0
        .replace("icmp slt i32 %12, 16777216", "icmp sle i32 %12, 16777214")
        .replace("icmp slt i32 %30, 16777216", "icmp sle i32 %30, 16777214");
    assert_eq!(
        source.matches("icmp sle i32 %").count(),
        2,
        "both revertBits loops should use the inclusive trip bound"
    );

    assert_revertbits_variant_sums_cancel(
        &source,
        "revertbits_inclusive_bound",
        "both loops must cover exactly 0..=16777214 so the sums cancel",
    );
}

/// revertBits whose subtracting loop is mid-tested: the header subtracts
/// `rbit(i)` and only then tests `i < 1000000`, so it subtracts for
/// `i = 0..=1000000`, and the adding loop runs `i < 1000001` to match. The
/// coverage clause does not count the exiting header entry as an iteration,
/// and the vectorizer's rewrite counts latch entries only, so the work of that
/// entry escapes both counts, and a VF=2 vector loop also subtracted lane
/// 1000001 (O2 exited 1 until 2026-10-10). The vectorizer refuses work ahead
/// of the header's trip test.
#[test]
fn imported_revertbits_mid_tested_loop_runs_exactly_every_iteration_at_o2() {
    const TEST: &str = "imported_revertbits_mid_tested_loop_runs_exactly_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    const LOOP2: &str = "29:                                               ; preds = %43, %28
  %30 = load i32, ptr %7, align 4
  %31 = icmp slt i32 %30, 16777216
  br i1 %31, label %32, label %46

32:                                               ; preds = %29
  %33 = load i32, ptr %7, align 4
  %34 = call i32 @llvm.bitreverse.i32(i32 %33)
  %35 = zext i32 %34 to i64
  %36 = load i64, ptr %2, align 8
  %37 = sub i64 %36, %35
  store i64 %37, ptr %2, align 8
  %38 = load i32, ptr %7, align 4
  %39 = sext i32 %38 to i64
  %40 = call i64 @llvm.bitreverse.i64(i64 %39)
  %41 = load i64, ptr %3, align 8
  %42 = sub i64 %41, %40
  store i64 %42, ptr %3, align 8
  br label %43

43:                                               ; preds = %32
  %44 = load i32, ptr %7, align 4
  %45 = add nsw i32 %44, 1
  store i32 %45, ptr %7, align 4
  br label %29, !llvm.loop !8
";
    const MID_TESTED_LOOP2: &str =
        "29:                                               ; preds = %42, %28
  %30 = load i32, ptr %7, align 4
  %31 = call i32 @llvm.bitreverse.i32(i32 %30)
  %32 = zext i32 %31 to i64
  %33 = load i64, ptr %2, align 8
  %34 = sub i64 %33, %32
  store i64 %34, ptr %2, align 8
  %35 = load i32, ptr %7, align 4
  %36 = sext i32 %35 to i64
  %37 = call i64 @llvm.bitreverse.i64(i64 %36)
  %38 = load i64, ptr %3, align 8
  %39 = sub i64 %38, %37
  store i64 %39, ptr %3, align 8
  %40 = load i32, ptr %7, align 4
  %41 = icmp slt i32 %40, 1000000
  br i1 %41, label %42, label %46

42:                                               ; preds = %29
  %43 = load i32, ptr %7, align 4
  %44 = add nsw i32 %43, 1
  store i32 %44, ptr %7, align 4
  %45 = load i32, ptr %7, align 4
  br label %29, !llvm.loop !8
";
    assert_eq!(
        LL_REVERTBITS_CLANG_O0.matches(LOOP2).count(),
        1,
        "the fixture's subtracting loop"
    );
    let source = LL_REVERTBITS_CLANG_O0
        .replace(LOOP2, MID_TESTED_LOOP2)
        .replace("icmp slt i32 %12, 16777216", "icmp slt i32 %12, 1000001");
    assert_eq!(
        source.matches("icmp slt i32 %12, 1000001").count(),
        1,
        "the adding loop should run 0..1000001"
    );

    assert_revertbits_variant_sums_cancel(
        &source,
        "revertbits_mid_tested",
        "both loops must cover exactly 0..=1000000 so the sums cancel",
    );
}

/// revertBits whose trip bound, and in a second variant whose subtracting
/// loop's start, depend on `argc` through a value the coverage clause does
/// not sample: `bound = (argc == 6) ? 13 : 2 * argc` in each loop's
/// preheader, and `start = (argc == 6) ? 1 : 0` (`rbit(0) == 0`, so the sums
/// still cancel). The clause decides a run-time trip only at the values it
/// samples, which give an even trip count, so a VF=2 vector loop was
/// published and ran one extra lane at `argc == 6` (O2 exited 1 until
/// 2026-10-10). The vectorizer refuses an induction trip that is not fixed at
/// compile time.
#[test]
fn imported_revertbits_trip_keyed_on_argc_runs_exactly_every_iteration_at_o2() {
    const TEST: &str = "imported_revertbits_trip_keyed_on_argc_runs_exactly_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    let with_argc = LL_REVERTBITS_CLANG_O0.replace(
        "define i32 @main() #0 {",
        "define i32 @main(i32 %argc, ptr %argv) #0 {",
    );
    let keyed_bound = with_argc
        .replace(
            "  store i32 0, ptr %6, align 4\n  br label %11\n",
            "  store i32 0, ptr %6, align 4\n  %b1c = icmp eq i32 %argc, 6\n  \
             %b1m = mul i32 %argc, 2\n  %bound1 = select i1 %b1c, i32 13, i32 %b1m\n  \
             br label %11\n",
        )
        .replace(
            "  store i32 0, ptr %7, align 4\n  br label %29\n",
            "  store i32 0, ptr %7, align 4\n  %b2c = icmp eq i32 %argc, 6\n  \
             %b2s = shl i32 %argc, 1\n  %bound2 = select i1 %b2c, i32 13, i32 %b2s\n  \
             br label %29\n",
        )
        .replace("icmp slt i32 %12, 16777216", "icmp slt i32 %12, %bound1")
        .replace("icmp slt i32 %30, 16777216", "icmp slt i32 %30, %bound2");
    for needle in [
        "%bound1 = select",
        "%bound2 = select",
        "%12, %bound1",
        "%30, %bound2",
    ] {
        assert_eq!(keyed_bound.matches(needle).count(), 1, "{needle}");
    }
    let keyed_start = with_argc.replace(
        "  store i32 0, ptr %7, align 4\n",
        "  %s2c = icmp eq i32 %argc, 6\n  %start2 = select i1 %s2c, i32 1, i32 0\n  \
         store i32 %start2, ptr %7, align 4\n",
    );
    assert_eq!(
        keyed_start.matches("store i32 %start2, ptr %7").count(),
        1,
        "the subtracting loop's start should be keyed on argc"
    );

    for (source, module, what) in [
        (
            &keyed_bound,
            "revertbits_keyed_bound",
            "both loops must cover exactly 0..bound so the sums cancel",
        ),
        (
            &keyed_start,
            "revertbits_keyed_start",
            "the loops must cover 0..16777216 and start..16777216 so the sums cancel",
        ),
    ] {
        assert_revertbits_variant_sums_cancel_at_argc(source, module, what, &[1, 5, 6, 7]);
    }
}

/// Where [`revertbits_storing_the_induction`] puts its store: the body block
/// `%32` or the latch block `%43` of the subtracting loop.
#[derive(Clone, Copy)]
enum StoreBlock {
    Body,
    Latch,
}

/// revertBits whose subtracting loop also stores its induction to a global
/// each iteration, `last = i`, which `main` prints after the sums:
/// `last=16777215`. The store is in the loop block `at`, plain or
/// `volatile`.
fn revertbits_storing_the_induction(at: StoreBlock, volatile: bool) -> String {
    const GLOBALS: &str = "@.str.3 = private unnamed_addr constant [18 x i8] \
                           c\"0x%llx -> 0x%llx\\0A\\00\", align 1\n";
    const BODY_END: &str = "  store i64 %42, ptr %3, align 8\n  br label %43\n";
    const LATCH_START: &str = "43:                                               ; preds = %32\n  \
         %44 = load i32, ptr %7, align 4\n";
    const LAST_PRINT: &str = "  %54 = call i32 (ptr, ...) @printf(ptr noundef @.str.3, \
                              i64 noundef %51, i64 noundef %53)\n";
    for anchor in [GLOBALS, BODY_END, LATCH_START, LAST_PRINT] {
        assert_eq!(
            LL_REVERTBITS_CLANG_O0.matches(anchor).count(),
            1,
            "{anchor}"
        );
    }
    let store = if volatile { "store volatile" } else { "store" };
    let last_store =
        format!("  %last = load i32, ptr %7, align 4\n  {store} i32 %last, ptr @last, align 4\n");
    let source = LL_REVERTBITS_CLANG_O0
        .replace(
            GLOBALS,
            &format!(
                "{GLOBALS}@last = global i32 -1, align 4\n\
                 @.str.last = private unnamed_addr constant [9 x i8] c\"last=%d\\0A\\00\", \
                 align 1\n"
            ),
        )
        .replace(
            LAST_PRINT,
            &format!(
                "{LAST_PRINT}  %lastv = load i32, ptr @last, align 4\n  \
                 %lastp = call i32 (ptr, ...) @printf(ptr noundef @.str.last, i32 noundef %lastv)\n"
            ),
        );
    match at {
        StoreBlock::Body => source.replace(
            BODY_END,
            &format!("  store i64 %42, ptr %3, align 8\n{last_store}  br label %43\n"),
        ),
        StoreBlock::Latch => source.replace(LATCH_START, &{
            let (label, load) = LATCH_START.split_at(LATCH_START.find("  %44").unwrap());
            format!("{label}{last_store}{load}")
        }),
    }
}

/// revertBits whose subtracting loop stores its induction in its latch,
/// `last = i`, and prints it. The store is not part of the vector plan: a
/// VF=2 rewrite that steps `i` by 2 runs it on even `i` only, and O2 printed
/// `last=16777214` with the sum self-check still passing until 2026-10-10.
/// The vectorizer refuses an instruction of the loop its plan does not
/// account for that does more than compute registers.
#[test]
fn imported_revertbits_store_in_the_latch_runs_every_iteration_at_o2() {
    const TEST: &str = "imported_revertbits_store_in_the_latch_runs_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    let source = revertbits_storing_the_induction(StoreBlock::Latch, false);
    assert_eq!(source.matches("store i32 %last, ptr @last").count(), 1);
    assert_revertbits_variant_prints_at_argc(
        &source,
        "revertbits_latch_store",
        "the latch store must run for every i, last = 16777215",
        &[1],
        &format!("{REVERTBITS_STDOUT}last=16777215\n"),
    );
}

/// [`imported_revertbits_store_in_the_latch_runs_every_iteration_at_o2`] with
/// the store in the loop body, plain and `volatile` (O2 printed
/// `last=16777214` for both until 2026-10-10).
#[test]
fn imported_revertbits_store_in_the_body_runs_every_iteration_at_o2() {
    const TEST: &str = "imported_revertbits_store_in_the_body_runs_every_iteration_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    for (volatile, module) in [
        (false, "revertbits_body_store"),
        (true, "revertbits_body_volatile_store"),
    ] {
        let source = revertbits_storing_the_induction(StoreBlock::Body, volatile);
        assert_eq!(source.matches(" i32 %last, ptr @last").count(), 1);
        assert_revertbits_variant_prints_at_argc(
            &source,
            module,
            "the body store must run for every i, last = 16777215",
            &[1],
            &format!("{REVERTBITS_STDOUT}last=16777215\n"),
        );
    }
}

#[test]
fn bitreverse_intrinsics_link_and_run_without_external_symbols() {
    const TEST: &str = "bitreverse_intrinsics_link_and_run_without_external_symbols";
    // The in-tree readers need no host tool: both containers, every host.
    for triple in TARGETS {
        let object = compile_for(
            LL_BITREVERSE_INTRINSICS,
            "bitreverse_intrinsics",
            triple,
            OptLevel::O0,
        );
        assert_no_undefined_containing(
            &object,
            triple,
            "llvm.bitreverse",
            "bitreverse intrinsic was left as an unresolved symbol",
        );
    }
    if !native_host_or_skip(TEST) {
        return;
    }

    let object = compile_for_host(
        LL_BITREVERSE_INTRINSICS,
        "bitreverse_intrinsics",
        OptLevel::O0,
    );
    let dir = unique_temp_dir("bitreverse");
    let obj_path = dir.join("bitreverse.o");
    let bin_path = dir.join("bitreverse");
    fs::write(&obj_path, object).expect("write object");

    // `main` is the object's only function, so both RBIT forms are in it.
    let disasm = disassemble(&obj_path, HOST_TRIPLE);
    assert_eq!(
        disasm.function("main"),
        disasm.text(),
        "main should be the only disassembled function"
    );
    let main = disasm.function("main");
    assert!(
        main.contains("rbit\tw"),
        "i32 bitreverse should select RBIT W-form:\n{main}"
    );
    assert!(
        main.contains("rbit\tx"),
        "i64 bitreverse should select RBIT X-form:\n{main}"
    );

    assert_nm_has_no_undefined(
        &obj_path,
        &["llvm.bitreverse".to_owned()],
        "bitreverse intrinsic was left as an unresolved symbol",
    );

    link_with_cc(&obj_path, &bin_path);
    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert_eq!(
        output.status.code(),
        Some(2),
        "linked binary should return bitreverse32(msb)+bitreverse64(msb)=2, got {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn handwritten_reversebits_helpers_emit_rbit() {
    const TEST: &str = "handwritten_reversebits_helpers_emit_rbit";
    if !native_host_or_skip(TEST) {
        return;
    }

    let object = compile_for_host(
        LL_HANDWRITTEN_REVERSEBITS,
        "handwritten_reversebits",
        OptLevel::O0,
    );
    let dir = unique_temp_dir("handwritten-reversebits");
    let obj_path = dir.join("handwritten_reversebits.o");
    let bin_path = dir.join("handwritten_reversebits");
    fs::write(&obj_path, object).expect("write object");

    let disasm = disassemble(&obj_path, HOST_TRIPLE);
    let reverse32 = disasm.function("ReverseBits32");
    let reverse64 = disasm.function("ReverseBits64");
    assert!(
        reverse32.contains("rbit\tw"),
        "ReverseBits32 should select RBIT W-form:\n{reverse32}"
    );
    assert!(
        reverse64.contains("rbit\tx"),
        "ReverseBits64 should select RBIT X-form:\n{reverse64}"
    );

    link_with_cc(&obj_path, &bin_path);
    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert_eq!(
        output.status.code(),
        Some(2),
        "linked binary should return ReverseBits32(msb)+ReverseBits64(msb)=2, got {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn handwritten_reversebits_helpers_are_frameless_rbit_ret_at_o2() {
    const TEST: &str = "handwritten_reversebits_helpers_are_frameless_rbit_ret_at_o2";
    if !native_host_or_skip(TEST) {
        return;
    }

    let object = compile_for_host(
        LL_HANDWRITTEN_REVERSEBITS,
        "handwritten_reversebits_o2_shape",
        OptLevel::O2,
    );
    let dir = unique_temp_dir("handwritten-reversebits-o2-shape");
    let obj_path = dir.join("handwritten_reversebits_o2_shape.o");
    fs::write(&obj_path, object).expect("write object");

    let disasm = disassemble(&obj_path, HOST_TRIPLE);
    assert_rbit_ret_shape(
        &disasm.function("ReverseBits32"),
        "ReverseBits32",
        "rbit\tw0, w0",
    );
    assert_rbit_ret_shape(
        &disasm.function("ReverseBits64"),
        "ReverseBits64",
        "rbit\tx0, x0",
    );
}

#[test]
fn default_ssp_handwritten_reversebits_helpers_are_frameless_rbit_ret_at_o2() {
    const TEST: &str = "default_ssp_handwritten_reversebits_helpers_are_frameless_rbit_ret_at_o2";
    let src = handwritten_reversebits_with_default_ssp();
    // The in-tree readers need no host tool: both containers, every host.
    for triple in TARGETS {
        let object = compile_for(
            &src,
            "handwritten_reversebits_default_ssp_o2_shape",
            triple,
            OptLevel::O2,
        );
        for guard in ["__stack_chk_guard", "__stack_chk_fail"] {
            assert_no_undefined_containing(
                &object,
                triple,
                &object_symbol(triple, guard),
                "default ssp bitreverse helpers should not emit stack guard symbols",
            );
        }
    }
    if !native_host_or_skip(TEST) {
        return;
    }

    let object = compile_for_host(
        &src,
        "handwritten_reversebits_default_ssp_o2_shape",
        OptLevel::O2,
    );
    let dir = unique_temp_dir("handwritten-reversebits-default-ssp-o2-shape");
    let obj_path = dir.join("handwritten_reversebits_default_ssp_o2_shape.o");
    fs::write(&obj_path, &object).expect("write object");

    assert_no_stack_guard_undefined_symbols(&object, &obj_path);

    let disasm = disassemble(&obj_path, HOST_TRIPLE);
    assert_rbit_ret_shape(
        &disasm.function("ReverseBits32"),
        "ReverseBits32",
        "rbit\tw0, w0",
    );
    assert_rbit_ret_shape(
        &disasm.function("ReverseBits64"),
        "ReverseBits64",
        "rbit\tx0, x0",
    );
}

#[test]
fn handwritten_reversebits_match_c_reference_at_every_opt_level() {
    const TEST: &str = "handwritten_reversebits_match_c_reference_at_every_opt_level";
    if !native_host_or_skip(TEST) {
        return;
    }

    let src = reversebits_c_reference_module();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let name = format!("reversebits_c_reference_{level:?}").to_lowercase();
        let object = compile_for_host(&src, &name, level);
        let dir = unique_temp_dir(&name);
        let obj_path = dir.join(format!("{name}.o"));
        let driver_path = dir.join("driver.c");
        let bin_path = dir.join(&name);
        fs::write(&obj_path, object).expect("write object");
        fs::write(&driver_path, C_REFERENCE_DRIVER).expect("write C driver");

        // The private-slot ladders select RBIT; the escaping slot's ladder
        // keeps a store for the callee to read.
        let disasm = disassemble(&obj_path, HOST_TRIPLE);
        assert!(
            disasm.function("ReverseBits32").contains("rbit\tw"),
            "{level:?}: ReverseBits32 should select RBIT:\n{}",
            disasm.function("ReverseBits32")
        );
        assert!(
            disasm.function("ReverseBits64").contains("rbit\tx"),
            "{level:?}: ReverseBits64 should select RBIT:\n{}",
            disasm.function("ReverseBits64")
        );
        let escaped = disasm.function("ReverseBits32Escaped");
        assert!(
            escaped.contains("str\t") || escaped.contains("stur\t"),
            "{level:?}: the escaping slot must still be stored:\n{escaped}"
        );

        let output = common::native_c_command()
            .arg(&obj_path)
            .arg(&driver_path)
            .arg("-o")
            .arg(&bin_path)
            .output()
            .expect("run cc");
        assert!(
            output.status.success(),
            "{level:?}: cc failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&bin_path).output().expect("run linked binary");
        assert_eq!(
            output.status.code(),
            Some(0),
            "{level:?}: C reference mismatch, got {}\nstdout:\n{}\nstderr:\n{}",
            describe_status(output.status),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "checked 4106 inputs\n",
            "{level:?}"
        );
    }
}
