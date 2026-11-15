#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / libcall_prototypes_e2e.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// L02-P15 (decision record LD-100): the backend read a
// call of `memcpy`, `memmove` or `memset` by the callee's NAME alone and
// lowered it as the bulk-memory operation whatever the declaration said, so
// a module declaring `i64 @memcpy(i64, i64, i64)` (another object of the
// link defines it) copied 8 bytes from address 4 to address 3 and crashed
// where llc's object calls the function and prints `r=348`, and a `memset`
// declared returning its count printed the destination address. LLVM reads
// such a declaration as an ordinary function (its `TargetLibraryInfo`
// checks the prototype) and llc calls it.
//
// * Native (AArch64 Linux GNU or macOS): the L02-P15 re-check's reproducers
//   are imported, compiled at O0 and O2, linked by the host `cc` with the C
//   object that defines the module's `memcpy`/`memmove`/`memset`, and run;
//   stdout must be the program's output as LLVM defines it, which llc
//   22.1.2's builds printed on Linux AArch64 (measured by the differential
//   recorded with the ruling: O0-O3, GNU ld, gold and LLD, static and PIE).
//   Each such object must call the routine. A control declared with C's
//   prototypes keeps the bulk-memory lowering (its 8-byte copy references no
//   `memcpy`) and prints what llc's build prints.
// * Host-neutral: a `fastcc` declaration of one of the three names, which
//   this importer would otherwise read as C, is refused by name.
// * Host-neutral (rule 8, the L02-P15 re-check at `f95ca7609`): the importer
//   never carries the signature or name of one of the three, or of an
//   intrinsic name the backend reads, from anything but the module's own
//   header under that name. An unprototyped `declare ptr @memcpy(...)`
//   called as `ptr (ptr, ptr, i64)` was signed from the call (OD-56) and
//   expanded as C's `memcpy` where llc calls it (the re-check's `u1`, `u3b`,
//   `u6` and `u7`: 0 of 24 configurations equal); so were an unmodeled
//   header (skipped, so declare-by-use signed it), no header at all (LLVM's
//   parser refuses that module) and a Mach-O `\01_memcpy` label (carried as
//   `memcpy`). Each is refused by name; the controls (C's prototype, and the
//   same shapes on another name) import.
// * Host-neutral (rule 9, the third re-check at `f37c48df9`): a direct call
//   whose stated function type, result or parameters, differs from its
//   callee's header. LLVM reads it as a call through a cast, not a call of
//   the declared function (`CallBase::getCalledFunction` is null), so not as
//   the library routine: `%c = call i64 @memcpy(ptr, ptr, i64 8)` against
//   C's `declare ptr @memcpy(ptr, ptr, i64)`, its result unused, was
//   expanded where llc calls the linked `memcpy` (the re-check's
//   `k1_memcpy_cast_call_slot` and `k2_memset_cast_call`, 0 of 24 equal).
//   Every such call is refused by name, whatever its callee: an ordinary
//   callee's result read only through a variadic argument ran otherwise too
//   (`o2_ord_ret_vararg`, 0 of 24 equal, measured with this repair). The
//   controls (calls stating their header's type, K&R signing, `zeroext`
//   edges, a `ptr addrspace(0)` result) import.
// * Host-neutral (rule 10, rule 9's verifier at `2b1a5ee4f`): a call this
//   importer writes in place of an intrinsic was typed by the module's
//   header of the symbol it calls, not by the intrinsic: beside `declare i64
//   @sin(double)`, `@llvm.sin.f64` was called as `sin` and its result read
//   from `x0`, where llc reads `d0` (0 of 24 configurations equal for `sin`,
//   `cos`, `exp`, `log`, `log10` and `pow` with `i64` headers, `sin` with
//   `i32` or `ptr`, `sinf` with `i32`). Such a call is now recorded at the
//   type the intrinsic's lowering calls the symbol at and refused by name
//   when the symbol's final signature is another; so is a libm intrinsic
//   call stating another type than the intrinsic's (llc refuses each), and
//   a `memset_patternN` declared otherwise beside a pattern fill (Darwin).
//   The controls (C's headers, none, a header after the call) import.
// * Native (rule 10's controls): libm intrinsics with C's headers, without
//   headers, through a vector, and with an unprototyped header after the
//   call, compiled at O0 and O2, linked with `-lm` and run, print what llc
//   22.1.2's builds print (measured on Linux AArch64 at O0 and O2).
// * Host-neutral (rule 11, the fifth re-check at `848a8638d`): a module
//   function named like a routine the backend calls on its own, declared
//   with a hidden return buffer (`declare void @memcpy(ptr sret(%S), ptr,
//   i64)`) and called directly, made the selector's own `memcpy` call for
//   an `@llvm.memcpy` in the same function pass its destination in `x8`
//   (the selector keys that fact by name): the import died with signal 11
//   where llc's build copies (0 of 24 configurations equal, 11 probes and
//   the primary). Every such module is refused by name at compile, on
//   both targets, for every listed name; another name compiles.
// * Native (rule 11's controls): a hidden-buffer callee of another name
//   beside the three memory intrinsics, and the reproducer shape with C's
//   prototype, run as llc 22.1.2's Linux AArch64 builds ran.
// * Host-neutral (rule 12, rule 11's verifier and the sixth re-check at
//   `f8e524bc9`): a direct call of an `extern_weak` function is imported as
//   a `CallIndirect` through its address, which keeps the signature and
//   convention but none of the function's attributes. With a hidden return
//   buffer declared (`declare extern_weak void @fill_s(ptr sret(%S), ptr,
//   i64)`) the buffer went in `x0` instead of `x8` and every argument one
//   register later (12 probes, 0 of 24 configurations equal to llc: SIGSEGV
//   or other data), also past rule 11 for a runtime routine's name; and a
//   weak intrinsic the backend lowers by name (`declare extern_weak void
//   @llvm.memcpy.p0.p0.i64(...)`, found by this repair's sweep) became a
//   call of an undefined weak symbol so named (null; SIGSEGV where llc
//   copies). Both are refused by name at import, on both targets; the same
//   modules with strong declarations import.
// * Native (rule 12's control): weak calls whose facts the signature keeps
//   (`zeroext`/`signext` arguments and results, `returned` and other hints,
//   `fastcc`, C's `memcpy`) run as llc 22.1.2's Linux AArch64 builds ran.
//
// Testing evidence about the importer and the backend's call lowering, not a
// proof.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_llvm_import::{Error, import_text_for_target};

use common::{
    APPLE, HOST_TRIPLE, LINUX, LINUX_GNU, TARGETS, compile_for_host, compiler_for, describe_status,
    native_host_or_skip, object_symbol, undefined_symbols, unique_temp_dir,
};

/// `n1_memcpy_ints`: `memcpy` declared with three integers in and one out.
const N1_MEMCPY_INTS: &str = r#"
@fmt = private constant [7 x i8] c"r=%ld\0A\00"

declare i32 @printf(ptr, ...)
declare i64 @memcpy(i64, i64, i64)

define i32 @main() {
  %r = call i64 @memcpy(i64 3, i64 4, i64 8)
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i64 %r)
  ret i32 0
}
"#;

const N1_EXTRA_C: &str = "\
long memcpy(long a, long b, long c) { return a * 100 + b * 10 + c; }
";

/// `n2_memset_ret_count`: `memset` declared returning an `i64`; the linked
/// one fills as C's does and returns the count it wrote.
const N2_MEMSET_RET_COUNT: &str = r#"
@fmt = private constant [15 x i8] c"r=%ld b=%d,%d\0A\00"
@b = global [16 x i8] zeroinitializer

declare i32 @printf(ptr, ...)
declare i64 @memset(ptr, i32, i64)

define i32 @main() {
  %r = call i64 @memset(ptr @b, i32 65, i64 8)
  %p0 = load i8, ptr @b
  %q = getelementptr i8, ptr @b, i64 8
  %p1 = load i8, ptr %q
  %z0 = zext i8 %p0 to i32
  %z1 = zext i8 %p1 to i32
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i64 %r, i32 %z0, i32 %z1)
  ret i32 0
}
"#;

const N2_EXTRA_C: &str = "\
long memset(void *d, int c, unsigned long n) {
    volatile unsigned char *p = d;
    for (unsigned long i = 0; i < n; i++) p[i] = (unsigned char)c;
    return (long)n;
}
";

/// `n3_memmove_ret_i32`: `memmove` declared returning an `i32`, with a
/// run-time count; the linked one moves as C's does and returns the count.
const N3_MEMMOVE_RET_I32: &str = r#"
@fmt = private constant [11 x i8] c"r=%d b=%d\0A\00"
@b = global [16 x i8] c"abcdefghijklmnop"

declare i32 @printf(ptr, ...)
declare i32 @memmove(ptr, ptr, i64)

define i32 @mv(i64 %n) noinline {
  %d = getelementptr i8, ptr @b, i64 1
  %r = call i32 @memmove(ptr %d, ptr @b, i64 %n)
  ret i32 %r
}

define i32 @main() {
  %r = call i32 @mv(i64 6)
  %q = getelementptr i8, ptr @b, i64 6
  %c = load i8, ptr %q
  %z = zext i8 %c to i32
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i32 %r, i32 %z)
  ret i32 0
}
"#;

const N3_EXTRA_C: &str = "\
int memmove(void *d, const void *s, unsigned long n) {
    volatile unsigned char *dd = d;
    const unsigned char *ss = s;
    if ((const unsigned char *)dd < ss) {
        for (unsigned long i = 0; i < n; i++) dd[i] = ss[i];
    } else {
        for (unsigned long i = n; i > 0; i--) dd[i - 1] = ss[i - 1];
    }
    return (int)n;
}
";

/// `memcpy` declared returning nothing, its destination a stack slot read
/// after the call (the shape the backend's SROA reads a `bl memcpy` from);
/// the linked one copies and counts its calls.
const S1_MEMCPY_VOID_SLOT: &str = r#"
@fmt = private constant [22 x i8] c"v=%lx w=%lx hits=%ld\0A\00"
@src = global [40 x i8] c"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmn"
@out = global i64 0
@out2 = global i64 0
@hits = external global i64

declare i32 @printf(ptr, ...)
declare void @memcpy(ptr, ptr, i64)

define void @f8() noinline {
  %s = alloca i64, align 8
  call void @memcpy(ptr %s, ptr @src, i64 8)
  %v = load i64, ptr %s
  store i64 %v, ptr @out
  ret void
}

define void @f40() noinline {
  %s = alloca [40 x i8], align 8
  call void @memcpy(ptr %s, ptr @src, i64 40)
  %v = load i64, ptr %s
  %q = getelementptr i8, ptr %s, i64 32
  %w = load i64, ptr %q
  store i64 %v, ptr @out
  store i64 %w, ptr @out2
  ret void
}

define i32 @main() {
  call void @f8()
  call void @f40()
  %v = load i64, ptr @out
  %w = load i64, ptr @out2
  %h = load i64, ptr @hits
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i64 %v, i64 %w, i64 %h)
  ret i32 0
}
"#;

const S1_EXTRA_C: &str = "\
long hits;
void memcpy(void *d, const void *s, unsigned long n) {
    volatile unsigned char *dd = d;
    const unsigned char *ss = s;
    for (unsigned long i = 0; i < n; i++) dd[i] = ss[i];
    hits++;
}
";

/// The control: `memcpy`, `memmove` and `memset` declared with C's
/// prototypes and called on the C library's own routines.
const C99_CONTROL: &str = r#"
@fmt = private constant [10 x i8] c"%s %d %d\0A\00"
@src = global [16 x i8] c"abcdefghijklmno\00"
@dst = global [16 x i8] zeroinitializer

declare i32 @printf(ptr, ...)
declare ptr @memcpy(ptr, ptr, i64)
declare ptr @memmove(ptr, ptr, i64)
declare ptr @memset(ptr, i32, i64)

define i32 @main() {
  %a = call ptr @memcpy(ptr @dst, ptr @src, i64 8)
  %d1 = getelementptr i8, ptr @dst, i64 1
  %b = call ptr @memmove(ptr %d1, ptr @dst, i64 4)
  %d12 = getelementptr i8, ptr @dst, i64 12
  %c = call ptr @memset(ptr %d12, i32 65, i64 2)
  %same_a = icmp eq ptr %a, @dst
  %same_c = icmp eq ptr %c, %d12
  %za = zext i1 %same_a to i32
  %zc = zext i1 %same_c to i32
  %p = call i32 (ptr, ...) @printf(ptr @fmt, ptr @dst, i32 %za, i32 %zc)
  ret i32 0
}
"#;

/// Compile `extra_c` with the host `cc` (no builtins, so its loops stay the
/// functions they define) into `dir`.
fn compile_extra_c(dir: &Path, stem: &str, extra_c: &str) -> PathBuf {
    let source = dir.join(format!("{stem}.extra.c"));
    fs::write(&source, extra_c).expect("write the C object's source");
    let object = dir.join(format!("{stem}.extra.o"));
    let output = common::native_c_command()
        .args(["-O1", "-fno-builtin", "-c"])
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .output()
        .expect("run cc");
    assert!(
        output.status.success(),
        "cc -c {stem}.extra.c failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    object
}

/// Import and compile `src` for this host at `level`, link it with
/// `extra` (if any) and the libraries `libs` (`-lm`) by the host `cc`, run
/// it, and return its object and stdout. A failing link or a run that does
/// not exit 0 fails the test.
fn build_and_run(
    dir: &Path,
    stem: &str,
    src: &str,
    extra: Option<&Path>,
    libs: &[&str],
    level: OptLevel,
) -> (Vec<u8>, String) {
    let object = compile_for_host(src, stem, level);
    let object_path = dir.join(format!("{stem}.{level:?}.o"));
    fs::write(&object_path, &object).expect("write the object");
    let binary = dir.join(format!("{stem}.{level:?}"));
    let mut link = common::native_c_command();
    link.arg(&object_path);
    if let Some(extra) = extra {
        link.arg(extra);
    }
    let linked = link
        .arg("-o")
        .arg(&binary)
        .args(libs)
        .output()
        .expect("run cc");
    assert!(
        linked.status.success(),
        "{stem} at {level:?}: cc failed: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let run = Command::new(&binary).output().expect("run the program");
    assert!(
        run.status.success(),
        "{stem} at {level:?}: {} (stdout {:?}, stderr {:?})",
        describe_status(run.status),
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    (object, String::from_utf8_lossy(&run.stdout).into_owned())
}

/// Each reproducer declares a library name with another prototype than C's:
/// its object calls the function of that name and the program prints what
/// LLVM's reading of it (an ordinary call) prints, as llc's build did.
#[test]
fn a_memory_routine_declared_otherwise_is_called_and_runs_as_llc_built_it() {
    if !native_host_or_skip(
        "a_memory_routine_declared_otherwise_is_called_and_runs_as_llc_built_it",
    ) {
        return;
    }
    let dir = unique_temp_dir("libcall-prototypes");
    for (stem, src, extra_c, routine, expected) in [
        (
            "n1_memcpy_ints",
            N1_MEMCPY_INTS,
            N1_EXTRA_C,
            "memcpy",
            "r=348\n",
        ),
        (
            "n2_memset_ret_count",
            N2_MEMSET_RET_COUNT,
            N2_EXTRA_C,
            "memset",
            "r=8 b=65,0\n",
        ),
        (
            "n3_memmove_ret_i32",
            N3_MEMMOVE_RET_I32,
            N3_EXTRA_C,
            "memmove",
            "r=6 b=102\n",
        ),
        (
            "s1_memcpy_void_slot",
            S1_MEMCPY_VOID_SLOT,
            S1_EXTRA_C,
            "memcpy",
            "v=4847464544434241 w=6e6d6c6b6a696867 hits=2\n",
        ),
    ] {
        let extra = compile_extra_c(&dir, stem, extra_c);
        for level in [OptLevel::O0, OptLevel::O2] {
            let (object, stdout) = build_and_run(&dir, stem, src, Some(&extra), &[], level);
            assert!(
                undefined_symbols(&object).contains(&object_symbol(HOST_TRIPLE, routine)),
                "{stem} at {level:?}: the object must call `{routine}`"
            );
            assert_eq!(stdout, expected, "{stem} at {level:?}");
        }
    }
}

/// C's prototypes keep the bulk-memory lowering: the 8-byte `memcpy` is
/// expanded (the object references no `memcpy`), and the program prints what
/// llc's build prints.
#[test]
fn c_prototype_memory_calls_keep_their_lowering_and_run_as_llc_built_them() {
    if !native_host_or_skip(
        "c_prototype_memory_calls_keep_their_lowering_and_run_as_llc_built_them",
    ) {
        return;
    }
    let dir = unique_temp_dir("libcall-prototypes-c99");
    for level in [OptLevel::O0, OptLevel::O2] {
        let (object, stdout) = build_and_run(&dir, "c99_control", C99_CONTROL, None, &[], level);
        assert!(
            !undefined_symbols(&object).contains(&object_symbol(HOST_TRIPLE, "memcpy")),
            "at {level:?}: the C prototype's 8-byte memcpy is the bulk-memory operation"
        );
        assert_eq!(stdout, "aabcdfgh 1 1\n", "at {level:?}");
    }
}

/// A `fastcc` declaration of a C library memory routine is refused by name:
/// this importer reads `fastcc` as C, under which the backend would read the
/// call as the routine; LLVM does not, and llc calls it.
#[test]
fn a_fastcc_memory_routine_declaration_is_refused_by_name() {
    for routine in ["memcpy", "memmove", "memset"] {
        let second = if routine == "memset" { "i32" } else { "ptr" };
        let src = format!(
            "@b = global [16 x i8] zeroinitializer\n\
             declare fastcc ptr @{routine}(ptr, {second}, i64)\n\
             define ptr @f({second} %x) {{\n  \
             %r = call fastcc ptr @{routine}(ptr @b, {second} %x, i64 8)\n  \
             ret ptr %r\n}}\n"
        );
        match import_text_for_target(&src, "t", LINUX) {
            Err(Error::Unsupported(reason)) => assert!(
                reason.contains("calling convention `fastcc` on a C library memory routine")
                    && reason.contains(routine),
                "{routine}: {reason}"
            ),
            other => panic!("{routine}: expected a named refusal, got {other:?}"),
        }
        // Control: the same declaration without `fastcc` imports.
        let plain = src.replace("fastcc ", "");
        if let Err(error) = import_text_for_target(&plain, "t", LINUX) {
            panic!("{routine}: the C-convention declaration must import: {error}");
        }
    }
}

/// The L02-P15 re-check's `u1_memcpy_unprototyped` (at `f95ca7609`): an
/// unprototyped `memcpy` called with C's types. llc's build called the
/// linked `memcpy`; the import expanded the copy (0 of 24 equal).
const U1_MEMCPY_UNPROTOTYPED: &str = r#"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"
@buf = global [8192 x i8] zeroinitializer
declare void @show(ptr, i64)
declare void @showp(ptr)
declare void @init()
declare void @report()
declare ptr @memcpy(...)
define i32 @main() {
  call void @init()
  %r = call ptr (ptr, ptr, i64) @memcpy(ptr getelementptr (i8, ptr @buf, i64 40), ptr getelementptr (i8, ptr @buf, i64 3000), i64 8)
  call void @showp(ptr %r)
  call void @show(ptr @buf, i64 8192)
  call void @report()
  ret i32 0
}
"#;

/// The re-check's `u3b_memset_zero_unprototyped`: a 16-byte zero fill.
const U3B_MEMSET_ZERO_UNPROTOTYPED: &str = r#"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"
@buf = global [8192 x i8] zeroinitializer
declare void @show(ptr, i64)
declare void @showp(ptr)
declare void @init()
declare void @report()
declare ptr @memset(...)
define i32 @main() {
  call void @init()
  %r = call ptr (ptr, i32, i64) @memset(ptr getelementptr (i8, ptr @buf, i64 40), i32 0, i64 16)
  call void @showp(ptr %r)
  call void @show(ptr @buf, i64 8192)
  call void @report()
  ret i32 0
}
"#;

/// The re-check's `u6_memcpy32_unprototyped`: a 32-byte copy.
const U6_MEMCPY32_UNPROTOTYPED: &str = r#"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"
@buf = global [8192 x i8] zeroinitializer
declare void @show(ptr, i64)
declare void @showp(ptr)
declare void @init()
declare void @report()
declare ptr @memcpy(...)
define i32 @main() {
  call void @init()
  %r = call ptr (ptr, ptr, i64) @memcpy(ptr getelementptr (i8, ptr @buf, i64 40), ptr getelementptr (i8, ptr @buf, i64 3000), i64 32)
  call void @showp(ptr %r)
  call void @show(ptr @buf, i64 8192)
  call void @report()
  ret i32 0
}
"#;

/// The re-check's `u7_memcpy_unprototyped_slot`: the destination a stack
/// slot read after the call (SROA's fill shape at 40 bytes, an inline
/// expansion at 8).
const U7_MEMCPY_UNPROTOTYPED_SLOT: &str = r#"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"
@fmt = private constant [32 x i8] c"v8=%lx v=%lx w=%lx hits=%ld\0A\00\00\00\00"
@src = global [40 x i8] c"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmn"
@out = global i64 0
@out2 = global i64 0
@hits = external global i64

declare i32 @printf(ptr, ...)
declare ptr @memcpy(...)

define void @f8() noinline {
  %s = alloca i64, align 8
  %c = call ptr (ptr, ptr, i64) @memcpy(ptr %s, ptr @src, i64 8)
  %v = load i64, ptr %s
  store i64 %v, ptr @out
  ret void
}

define void @f40() noinline {
  %s = alloca [40 x i8], align 8
  %c = call ptr (ptr, ptr, i64) @memcpy(ptr %s, ptr @src, i64 40)
  %v = load i64, ptr %s
  %q = getelementptr i8, ptr %s, i64 32
  %w = load i64, ptr %q
  store i64 %v, ptr @out
  store i64 %w, ptr @out2
  ret void
}

define i32 @main() {
  call void @f8()
  %v8 = load i64, ptr @out
  call void @f40()
  %v = load i64, ptr @out
  %w = load i64, ptr @out2
  %h = load i64, ptr @hits
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i64 %v8, i64 %v, i64 %w, i64 %h)
  ret i32 0
}
"#;

/// `src` with `memcpy`'s and `memset`'s unprototyped headers given C's
/// prototype (the controls).
fn with_c_prototypes(src: &str) -> String {
    src.replace("@memcpy(...)", "@memcpy(ptr, ptr, i64)")
        .replace("@memmove(...)", "@memmove(ptr, ptr, i64)")
        .replace("@memset(...)", "@memset(ptr, i32, i64)")
}

/// Import `src` for `triple` and require a refusal naming `routine` and
/// saying `why`.
fn assert_refused(stem: &str, src: &str, triple: &str, routine: &str, why: &str) {
    match import_text_for_target(src, stem, triple) {
        Err(Error::Unsupported(reason)) => assert!(
            reason.contains(why) && reason.contains(routine),
            "{stem}: the refusal must name {routine} and say {why:?}: {reason}"
        ),
        Ok(_) => panic!("{stem}: expected a refusal naming {routine}, the module imported"),
        Err(other) => panic!("{stem}: expected a named refusal, got {other:?}"),
    }
}

/// Import `src` for `triple`, which must succeed.
fn assert_imports(stem: &str, src: &str, triple: &str) {
    if let Err(error) = import_text_for_target(src, stem, triple) {
        panic!("{stem}: must import: {error}");
    }
}

/// An unprototyped `(...)` declaration of a C library memory routine is
/// refused by name, wherever it stands: signed from its calls (OD-56), it
/// would carry C's prototype, which the backend reads as the routine, where
/// LLVM reads a variadic function and llc calls it. With C's prototype the
/// same modules import (they are rule 1's routine then).
#[test]
fn an_unprototyped_declaration_of_a_memory_routine_is_refused_by_name() {
    let after_call = U1_MEMCPY_UNPROTOTYPED.replace("declare ptr @memcpy(...)\n", "")
        + "declare ptr @memcpy(...)\n";
    let memmove = U1_MEMCPY_UNPROTOTYPED.replace("@memcpy", "@memmove");
    let void_memcpy = U1_MEMCPY_UNPROTOTYPED
        .replace("declare ptr @memcpy(...)", "declare void @memcpy(...)")
        .replace("%r = call ptr (ptr, ptr, i64)", "call void (ptr, ptr, i64)")
        .replace("  call void @showp(ptr %r)\n", "");
    let uncalled = "declare ptr @memset(...)\ndefine i32 @f() {\n  ret i32 0\n}\n".to_string();
    for (stem, src, routine) in [
        (
            "u1_memcpy_unprototyped",
            U1_MEMCPY_UNPROTOTYPED.to_string(),
            "memcpy",
        ),
        (
            "u3b_memset_zero_unprototyped",
            U3B_MEMSET_ZERO_UNPROTOTYPED.to_string(),
            "memset",
        ),
        (
            "u6_memcpy32_unprototyped",
            U6_MEMCPY32_UNPROTOTYPED.to_string(),
            "memcpy",
        ),
        (
            "u7_memcpy_unprototyped_slot",
            U7_MEMCPY_UNPROTOTYPED_SLOT.to_string(),
            "memcpy",
        ),
        ("memcpy_declared_after_its_call", after_call, "memcpy"),
        ("memmove_unprototyped", memmove, "memmove"),
        ("void_memcpy_unprototyped", void_memcpy, "memcpy"),
        ("memset_unprototyped_uncalled", uncalled, "memset"),
    ] {
        assert_refused(
            stem,
            &src,
            LINUX,
            &format!("`@{routine}`"),
            "an unprototyped header `(...)`",
        );
        assert_refused(
            stem,
            &src,
            APPLE,
            &format!("`@{routine}`"),
            "an unprototyped header `(...)`",
        );
        assert_imports(
            &format!("{stem}, C's prototype"),
            &with_c_prototypes(&src),
            LINUX,
        );
    }
    // Control: an unprototyped K&R declaration of another name is still
    // signed from its calls (OD-56).
    assert_imports(
        "kr_unprototyped",
        "declare i32 @kr(...)\n\
         define i32 @f() {\n  %r = call i32 (i32, i32) @kr(i32 1, i32 2)\n  ret i32 %r\n}\n",
        LINUX,
    );
}

/// An unprototyped declaration of an LLVM intrinsic name the backend reads
/// is refused by name too (LLVM's verifier refuses a call of one, and llc
/// builds one no call reaches).
#[test]
fn an_unprototyped_declaration_of_an_intrinsic_name_the_backend_reads_is_refused_by_name() {
    for (name, ty) in [
        ("llvm.bitreverse.i32", "i32"),
        ("llvm.bitreverse.i64", "i64"),
        ("llvm.fma.f64", "double"),
        ("llvm.fmuladd.f32", "float"),
        ("llvm.objectsize.i64.p0", "i64"),
        ("llvm.aarch64.crc32w", "i32"),
    ] {
        let src = format!("declare {ty} @{name}(...)\ndefine i32 @f() {{\n  ret i32 0\n}}\n");
        assert_refused(
            name,
            &src,
            LINUX,
            &format!("`@{name}`"),
            "an unprototyped header `(...)`",
        );
    }
}

/// A declaration of a C library memory routine whose signature this reader
/// does not model is refused, not skipped: skipped, a call would sign it
/// (declare-by-use) with C's prototype, where LLVM reads the declaration's
/// own type and llc and opt -O2 call it (`declare fp128 @memcpy(ptr, ptr,
/// i64)` called as `ptr (ptr, ptr, i64)`: 0 of 24 equal at `f95ca7609`).
/// An unmodeled declaration of another name is still skipped.
#[test]
fn an_unmodeled_declaration_of_a_memory_routine_is_refused_by_name() {
    let unmodeled_result = U1_MEMCPY_UNPROTOTYPED.replace(
        "declare ptr @memcpy(...)",
        "declare fp128 @memcpy(ptr, ptr, i64)",
    );
    let unmodeled_parameter = U1_MEMCPY_UNPROTOTYPED.replace(
        "declare ptr @memcpy(...)",
        "declare ptr @memcpy(ptr, ptr, i64, fp128)",
    );
    let vector_memset = U3B_MEMSET_ZERO_UNPROTOTYPED.replace(
        "declare ptr @memset(...)",
        "declare ptr @memset(ptr, <4 x i32>, i64)",
    );
    for (stem, src, routine) in [
        ("q2_memcpy_unmodeled_result", unmodeled_result, "memcpy"),
        (
            "q3_memcpy_unmodeled_parameter",
            unmodeled_parameter,
            "memcpy",
        ),
        ("memset_vector_parameter", vector_memset, "memset"),
    ] {
        assert_refused(
            stem,
            &src,
            LINUX,
            &format!("`@{routine}`"),
            "its signature is not modeled",
        );
    }
    // Control: the same unmodeled header on another name is skipped and its
    // call signs it, as before.
    assert_imports(
        "unmodeled_other_name",
        &U1_MEMCPY_UNPROTOTYPED
            .replace(
                "declare ptr @memcpy(...)",
                "declare fp128 @copy(ptr, ptr, i64)",
            )
            .replace("@memcpy(", "@copy("),
        LINUX,
    );
}

/// A C library memory routine called with no declaration is refused by
/// name: its signature would be the type the call states, C's prototype
/// here. LLVM's parser refuses the module ("use of undefined value"). A call
/// of another undeclared name still declares it by use.
#[test]
fn a_memory_routine_called_without_a_declaration_is_refused_by_name() {
    let undeclared_memcpy = U1_MEMCPY_UNPROTOTYPED.replace("declare ptr @memcpy(...)\n", "");
    let undeclared_memset = U3B_MEMSET_ZERO_UNPROTOTYPED.replace("declare ptr @memset(...)\n", "");
    for (stem, src, routine) in [
        ("q4_memcpy_undeclared", undeclared_memcpy, "memcpy"),
        ("memset_undeclared", undeclared_memset, "memset"),
    ] {
        assert_refused(
            stem,
            &src,
            LINUX,
            &format!("`@{routine}`"),
            "never declared",
        );
    }
    assert_imports(
        "undeclared_other_name",
        &U1_MEMCPY_UNPROTOTYPED
            .replace("declare ptr @memcpy(...)\n", "")
            .replace("@memcpy(", "@copy("),
        LINUX,
    );
}

/// A Mach-O `\01_` asm label naming a C library memory routine is refused
/// by name: LLVM reads `@"\01_memcpy"` as an ordinary function by its IR
/// name (llc 22.1.2 and opt -O2 call `_memcpy` at a count of 8), and this
/// importer carries a label under the name after `\01_`, which the backend
/// would read with C's prototype as the routine (at `f95ca7609` the
/// import's object referenced no `_memcpy`). A label on another name is
/// carried as before.
#[test]
fn a_mach_o_label_naming_a_memory_routine_is_refused_by_name() {
    for routine in ["memcpy", "memmove", "memset"] {
        let second = if routine == "memset" { "i32" } else { "ptr" };
        let src = format!(
            "@b = global [16 x i8] zeroinitializer\n\
             declare ptr @\"\\01_{routine}\"(ptr, {second}, i64)\n\
             define ptr @f({second} %x) {{\n  \
             %r = call ptr @\"\\01_{routine}\"(ptr @b, {second} %x, i64 8)\n  \
             ret ptr %r\n}}\n"
        );
        assert_refused(
            routine,
            &src,
            APPLE,
            &format!("`_{routine}`"),
            "`\\01` asm label",
        );
        let other = src.replace(&format!("\\01_{routine}"), "\\01_copy");
        assert_imports(
            &format!("{routine}, a label on another name"),
            &other,
            APPLE,
        );
    }
}

/// The words every rule-9 refusal carries.
const RULE_9: &str = "LD-100 rule 9";

/// The third re-check's `k1_memcpy_cast_call_slot` (at `f37c48df9`):
/// `memcpy` declared with C's prototype, each call stating `i64 (ptr, ptr,
/// i64)` (a call through a cast of the function, as clang emits it), its
/// result unused. llc and opt call the linked `memcpy`, which copies the
/// program's `src` in reverse and counts; the import expanded the 8-byte
/// copy (`v8` in order, `hits=1` where llc's build printed `hits=2`; 0 of
/// 24 configurations equal).
const K1_MEMCPY_CAST_CALL_SLOT: &str = r#"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"
@fmt = private constant [32 x i8] c"v8=%lx v=%lx w=%lx hits=%ld\0A\00\00\00\00"
@src = global [40 x i8] c"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmn"
@out = global i64 0
@out2 = global i64 0
@hits = external global i64

declare i32 @printf(ptr, ...)
declare ptr @memcpy(ptr noundef, ptr noundef, i64 noundef)

define void @f8() noinline {
  %s = alloca i64, align 8
  %c = call i64 @memcpy(ptr noundef %s, ptr noundef @src, i64 noundef 8)
  %v = load i64, ptr %s
  store i64 %v, ptr @out
  ret void
}

define void @f40() noinline {
  %s = alloca [40 x i8], align 8
  %c = call i64 @memcpy(ptr noundef %s, ptr noundef @src, i64 noundef 40)
  %v = load i64, ptr %s
  %q = getelementptr i8, ptr %s, i64 32
  %w = load i64, ptr %q
  store i64 %v, ptr @out
  store i64 %w, ptr @out2
  ret void
}

define i32 @main() {
  call void @f8()
  %v8 = load i64, ptr @out
  call void @f40()
  %v = load i64, ptr @out
  %w = load i64, ptr @out2
  %h = load i64, ptr @hits
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i64 %v8, i64 %v, i64 %w, i64 %h)
  ret i32 0
}
"#;

/// The re-check's `k2_memset_cast_call`: `memset` declared with C's
/// prototype, the call stating `i32 (ptr, i32, i64)`; llc calls the linked
/// `memset`, the import expanded the zero fill (0 of 24 equal).
const K2_MEMSET_CAST_CALL: &str = r#"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"
@fmt = private constant [16 x i8] c"v=%lx hits=%ld\0A\00"
@dst = global [16 x i8] c"0123456789abcdef"
@hits = external global i64

declare i32 @printf(ptr, ...)
declare ptr @memset(ptr noundef, i32 noundef, i64 noundef)

define i32 @main() {
  %c = call i32 @memset(ptr noundef @dst, i32 noundef 0, i64 noundef 16)
  %v = load i64, ptr @dst
  %h = load i64, ptr @hits
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i64 %v, i64 %h)
  ret i32 0
}
"#;

/// A call of `memcpy`, `memmove` or `memset` that states another function
/// type than the module's C-prototype header is refused by name (rule 9):
/// LLVM reads it as a call through a cast, not the routine, and llc calls
/// the symbol, where the backend read the name and header and expanded it.
/// The re-check's two reproducers and its family (other results, as a call
/// and a tail call; `memset` returning `i64` through its explicit function
/// type; `memmove`; a `void` call; a 32-bit count). The same modules
/// stating the header's type import.
#[test]
fn a_call_stating_another_type_than_a_memory_routines_header_is_refused_by_name() {
    let k1_call = "%c = call i64 @memcpy";
    let mut cases = vec![
        (
            "k1_memcpy_cast_call_slot".to_string(),
            K1_MEMCPY_CAST_CALL_SLOT.to_string(),
            "memcpy",
        ),
        (
            "k2_memset_cast_call".to_string(),
            K2_MEMSET_CAST_CALL.to_string(),
            "memset",
        ),
    ];
    for result in ["i32", "i16", "i8", "i1", "double", "float"] {
        for tail in ["", "tail "] {
            cases.push((
                format!("k1_{tail}{result}_result"),
                K1_MEMCPY_CAST_CALL_SLOT
                    .replace(k1_call, &format!("%c = {tail}call {result} @memcpy")),
                "memcpy",
            ));
        }
    }
    cases.push((
        "k2_memset_i64_result_explicit_type".to_string(),
        K2_MEMSET_CAST_CALL.replace("call i32 @memset", "call i64 (ptr, i32, i64) @memset"),
        "memset",
    ));
    cases.push((
        "k1_memmove".to_string(),
        K1_MEMCPY_CAST_CALL_SLOT.replace("@memcpy", "@memmove"),
        "memmove",
    ));
    cases.push((
        "k1_void_call".to_string(),
        K1_MEMCPY_CAST_CALL_SLOT.replace(k1_call, "call void @memcpy"),
        "memcpy",
    ));
    cases.push((
        "k1_i32_count".to_string(),
        K1_MEMCPY_CAST_CALL_SLOT
            .replace(k1_call, "%c = call ptr @memcpy")
            .replace("i64 noundef 8)", "i32 noundef 8)")
            .replace("i64 noundef 40)", "i32 noundef 40)"),
        "memcpy",
    ));
    for (stem, src, routine) in &cases {
        assert_refused(stem, src, LINUX, &format!("`@{routine}`"), RULE_9);
    }
    // Controls (the re-check's `k1c` and `k2c`): each call states the
    // header's type and imports.
    assert_imports(
        "k1c_memcpy_c_call_slot_control",
        &K1_MEMCPY_CAST_CALL_SLOT.replace(k1_call, "%c = call ptr @memcpy"),
        LINUX,
    );
    assert_imports(
        "k2c_memset_c_call_control",
        &K2_MEMSET_CAST_CALL.replace("call i32 @memset", "call ptr @memset"),
        LINUX,
    );
}

/// A call of an LLVM intrinsic the backend reads by name that states
/// another type than its declaration is refused by name (rule 9); LLVM's
/// verifier refuses each ("Intrinsic called with incompatible signature",
/// llc 22.1.2). An `llvm.mem*` declaration whose fourth parameter is not
/// the `i1 <volatile>` keeps it, so its calls, which state the `i1`, are
/// refused. The same calls at the declared types import.
#[test]
fn a_call_stating_another_type_than_an_intrinsic_declaration_is_refused_by_name() {
    let memcpy = "@b = global [16 x i8] zeroinitializer\n\
         @c = global [16 x i8] zeroinitializer\n\
         declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)\n\
         define void @f() {\n  \
         call void @llvm.memcpy.p0.p0.i64(ptr @b, ptr @c, i64 8, i1 false)\n  \
         ret void\n}\n";
    let fma = "declare double @llvm.fma.f64(double, double, double)\n\
         define double @f(double %a, double %b, double %c) {\n  \
         %r = call double @llvm.fma.f64(double %a, double %b, double %c)\n  \
         ret double %r\n}\n";
    let objectsize = "@b = global [16 x i8] zeroinitializer\n\
         declare i64 @llvm.objectsize.i64.p0(ptr, i1, i1, i1)\n\
         define i64 @f() {\n  \
         %r = call i64 @llvm.objectsize.i64.p0(ptr @b, i1 false, i1 true, i1 false)\n  \
         ret i64 %r\n}\n";
    let cases = [
        (
            "memcpy_intrinsic_with_a_result",
            memcpy.replace("call void @llvm", "%r = call i32 @llvm"),
            "llvm.memcpy.p0.p0.i64",
        ),
        (
            "memcpy_intrinsic_declared_with_an_i32_fourth_parameter",
            memcpy.replace("i64, i1)", "i64, i32)"),
            "llvm.memcpy.p0.p0.i64",
        ),
        (
            "fma_with_float_operands",
            fma.replace(
                "@llvm.fma.f64(double %a, double %b, double %c)",
                "@llvm.fma.f64(float %a, float %b, float %c)",
            )
            .replace(
                "@f(double %a, double %b, double %c)",
                "@f(float %a, float %b, float %c)",
            ),
            "llvm.fma.f64",
        ),
        (
            "objectsize_with_an_i8_flag",
            objectsize.replace("i1 true, i1 false)", "i1 true, i8 0)"),
            "llvm.objectsize.i64.p0",
        ),
    ];
    for (stem, src, name) in &cases {
        assert_refused(stem, src, LINUX, &format!("`@{name}`"), RULE_9);
    }
    // Controls: the same calls at the declared types, and the memory
    // intrinsic called through its explicit type, whose `i1` is dropped as
    // the declaration's is.
    for (stem, src) in [
        ("memcpy_intrinsic", memcpy.to_string()),
        (
            "memcpy_intrinsic_explicit_type",
            memcpy.replace("call void @llvm", "call void (ptr, ptr, i64, i1) @llvm"),
        ),
        ("fma", fma.to_string()),
        ("objectsize", objectsize.to_string()),
    ] {
        assert_imports(stem, &src, LINUX);
    }
}

/// `o2_ord_ret_vararg` (found by this repair): an ordinary `double g(void)`
/// called through a cast as `i64 ()`, its result read only through a
/// variadic argument, which no reader types. Linked with a C `g` that
/// returns 2.5 and leaves `0x1234` in `x0`, llc 22.1.2's build printed
/// `r=1234` (the call's `x0`) and the import at `f37c48df9` another value
/// in each of the re-check harness's 24 configurations (0 of 24 equal).
const O2_ORD_RET_VARARG: &str = r#"
@fmt = private constant [8 x i8] c"r=%lx\0A\00\00"

declare i32 @printf(ptr, ...)
declare double @g()

define i32 @main() {
  %r = call i64 @g()
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i64 %r)
  ret i32 0
}
"#;

/// Rule 9 is not limited to the names the backend reads: a call of any
/// callee whose stated type differs from its signature (the header's, or
/// the first call's under declare-by-use) is refused by name, since
/// trust-ir types the call by the callee's one signature and LLVM by the
/// call's own type. The controls import: calls stating their header's type
/// (also through an explicit non-variadic type), K&R signing (OD-56),
/// `zeroext` edges (the call's `i8` is the edge's unsigned twin), and a
/// `ptr addrspace(0)` result, whose parenthesized address space is no
/// function type.
#[test]
fn a_call_stating_another_type_than_its_callees_signature_is_refused_whatever_the_name() {
    let ordinary = "declare i32 @g(i32)\n\
         define i32 @f() {\n  %r = call i32 @g(i32 1)\n  ret i32 %r\n}\n";
    let cases = [
        ("o2_ord_ret_vararg", O2_ORD_RET_VARARG.to_string()),
        (
            "result_unused",
            ordinary.replace(
                "%r = call i32 @g(i32 1)",
                "%u = call i64 @g(i32 1)\n  %r = add i32 0, 1",
            ),
        ),
        (
            "void_call",
            ordinary.replace(
                "%r = call i32 @g(i32 1)",
                "call void @g(i32 1)\n  %r = add i32 0, 1",
            ),
        ),
        (
            "double_argument",
            ordinary.replace("@g(i32 1)", "@g(double 1.0)"),
        ),
        (
            "extra_argument",
            ordinary.replace("@g(i32 1)", "@g(i32 1, i32 2)"),
        ),
        (
            "second_call_after_declare_by_use",
            "define i32 @f() {\n  %a = call i64 @g(i32 1)\n  %b = call i32 @g(i32 2)\n  \
             ret i32 %b\n}\ndeclare i64 @g(i32)\n"
                .to_string(),
        ),
    ];
    for (stem, src) in &cases {
        assert_refused(stem, src, LINUX, "`@g`", RULE_9);
    }
    for (stem, src) in [
        ("ordinary", ordinary.to_string()),
        (
            "explicit_non_variadic_type",
            ordinary.replace("call i32 @g(i32 1)", "call i32 (i32) @g(i32 1)"),
        ),
        (
            "kr_unprototyped",
            "declare i32 @kr(...)\n\
             define i32 @f() {\n  %r = call i32 @kr(i32 1, i32 2)\n  \
             %s = call i32 @kr(i32 %r, i32 3)\n  ret i32 %s\n}\n"
                .to_string(),
        ),
        (
            "zeroext_edges",
            "declare zeroext i8 @h(i8 zeroext)\n\
             define i8 @f(i8 %x) {\n  %r = call zeroext i8 @h(i8 zeroext %x)\n  ret i8 %r\n}\n"
                .to_string(),
        ),
        (
            "addrspace_zero_result",
            "declare ptr @p()\n\
             define ptr @f() {\n  %r = call ptr addrspace(0) @p()\n  ret ptr %r\n}\n"
                .to_string(),
        ),
        (
            "o2_matching",
            O2_ORD_RET_VARARG.replace("declare double @g()", "declare i64 @g()"),
        ),
    ] {
        assert_imports(stem, &src, LINUX);
    }
}

/// The words every rule-10 refusal carries.
const RULE_10: &str = "LD-100 rule 10";

/// Rule 9's verifier reproducer `q1_sin_i64_header` (2026-10-24):
/// `@llvm.sin.f64`, which this importer calls as `sin`, beside `declare i64
/// @sin(double)`, its result read only through `printf`'s variadic tail.
/// LLVM lowers the intrinsic to a call of `sin` at `double (double)`
/// whatever the module declares `sin` as: llc 22.1.2's build printed
/// `r=0x1.aed548f090ceep-1` (`sin(1.0)`, read from `d0`) and the import at
/// `2b1a5ee4f`, typed by the header, `r=-0x1.12020162c37ep-12` (from `x0`),
/// in each of the verifier's 24 configurations.
const Q1_SIN_I64_HEADER: &str = r#"
@fmt = private constant [11 x i8] c"a=%a r=%a\0A\00"
declare i32 @printf(ptr, ...)
declare i64 @sin(double)
declare double @llvm.sin.f64(double)
define i32 @main() {
  %r = call double @llvm.sin.f64(double 1.0)
  %p = call i32 (ptr, ...) @printf(ptr @fmt, double 2.5e-01, double %r)
  ret i32 0
}
"#;

/// The libm intrinsic families this importer renames to their C symbols,
/// with their operand counts (`llvm.atan2` and `llvm.pow` two).
const LIBM_FAMILIES: [(&str, usize); 16] = [
    ("sin", 1),
    ("cos", 1),
    ("tan", 1),
    ("asin", 1),
    ("acos", 1),
    ("atan", 1),
    ("atan2", 2),
    ("sinh", 1),
    ("cosh", 1),
    ("tanh", 1),
    ("exp", 1),
    ("exp2", 1),
    ("log", 1),
    ("log2", 1),
    ("log10", 1),
    ("pow", 2),
];

/// A program calling the libm intrinsic `intrinsic` with `operands`
/// operands of `ty` (`double` or `float`) beside `header`, its result
/// passed to `printf` as a `double`.
fn libm_program(intrinsic: &str, ty: &str, operands: usize, header: &str) -> String {
    let params = vec![ty; operands].join(", ");
    let args = vec![format!("{ty} 7.5e-01"); operands].join(", ");
    let (widen, printed) = if ty == "double" {
        (String::new(), "%r")
    } else {
        ("  %w = fpext float %r to double\n".to_string(), "%w")
    };
    format!(
        "@fmt = private constant [6 x i8] c\"r=%a\\0A\\00\"\n\
         declare i32 @printf(ptr, ...)\n\
         {header}\n\
         declare {ty} @{intrinsic}({params})\n\
         define i32 @main() {{\n  \
         %r = call {ty} @{intrinsic}({args})\n\
         {widen}  \
         %p = call i32 (ptr, ...) @printf(ptr @fmt, double {printed})\n  \
         ret i32 0\n}}\n"
    )
}

/// A program calling `@llvm.sin.v2f64`, which this importer expands into
/// one `@llvm.sin.f64` call per lane, beside `header`.
fn libm_vector_program(header: &str) -> String {
    format!(
        "@fmt = private constant [9 x i8] c\"v=%a,%a\\0A\\00\"\n\
         declare i32 @printf(ptr, ...)\n\
         {header}\n\
         declare <2 x double> @llvm.sin.v2f64(<2 x double>)\n\
         define i32 @main() {{\n  \
         %v = call <2 x double> @llvm.sin.v2f64(<2 x double> <double 0.5, double 2.0>)\n  \
         %v0 = extractelement <2 x double> %v, i64 0\n  \
         %v1 = extractelement <2 x double> %v, i64 1\n  \
         %p = call i32 (ptr, ...) @printf(ptr @fmt, double %v0, double %v1)\n  \
         ret i32 0\n}}\n"
    )
}

/// Rule 10: the call this importer writes for a libm intrinsic is a call of
/// the C symbol at the intrinsic's type, so a module whose final signature
/// of that symbol is another (another result, parameter, count, a variadic
/// or an unprototyped header) is refused by name, for every family at both
/// widths and through the vector expander's lane calls; with C's header,
/// none, or an unprototyped header after the call (which keeps the call's
/// signature, OD-56) the same programs import.
#[test]
fn a_libm_intrinsic_beside_another_signature_of_its_symbol_is_refused_by_name() {
    let mut cases = vec![(
        "q1_sin_i64_header".to_string(),
        Q1_SIN_I64_HEADER.to_string(),
        "llvm.sin.f64".to_string(),
    )];
    for (stem, header) in [
        ("sin_i32_header", "declare i32 @sin(double)"),
        ("sin_ptr_header", "declare ptr @sin(double)"),
        ("sin_float_result_header", "declare float @sin(double)"),
        ("sin_void_header", "declare void @sin(double)"),
        ("sin_float_parameter_header", "declare double @sin(float)"),
        (
            "sin_two_parameter_header",
            "declare double @sin(double, double)",
        ),
        ("sin_variadic_header", "declare double @sin(double, ...)"),
        ("sin_unprototyped_header", "declare double @sin(...)"),
    ] {
        cases.push((
            stem.to_string(),
            Q1_SIN_I64_HEADER.replace("declare i64 @sin(double)", header),
            "llvm.sin.f64".to_string(),
        ));
    }
    for (family, operands) in LIBM_FAMILIES {
        for (ty, symbol, wrong) in [
            ("double", family.to_string(), "i64"),
            ("float", format!("{family}f"), "i32"),
        ] {
            let suffix = if ty == "double" { "f64" } else { "f32" };
            let intrinsic = format!("llvm.{family}.{suffix}");
            let params = vec![ty; operands].join(", ");
            cases.push((
                format!("{intrinsic}_{wrong}_header"),
                libm_program(
                    &intrinsic,
                    ty,
                    operands,
                    &format!("declare {wrong} @{symbol}({params})"),
                ),
                intrinsic.clone(),
            ));
        }
    }
    cases.push((
        "sin_vector_lanes_i64_header".to_string(),
        libm_vector_program("declare i64 @sin(double)"),
        "llvm.sin.f64".to_string(),
    ));
    for (stem, src, intrinsic) in &cases {
        assert_refused(stem, src, LINUX, &format!("`@{intrinsic}`"), RULE_10);
    }
    // Controls: C's header, none, and an unprototyped header after the call.
    let mut controls = vec![
        (
            "q1_c_header".to_string(),
            Q1_SIN_I64_HEADER.replace("declare i64 @sin(double)", "declare double @sin(double)"),
        ),
        (
            "q1_no_header".to_string(),
            Q1_SIN_I64_HEADER.replace("declare i64 @sin(double)\n", ""),
        ),
        (
            "q1_unprototyped_header_after_the_call".to_string(),
            format!(
                "{}declare double @sin(...)\n",
                Q1_SIN_I64_HEADER.replace("declare i64 @sin(double)\n", "")
            ),
        ),
        (
            "q1_explicit_call_type".to_string(),
            Q1_SIN_I64_HEADER
                .replace("declare i64 @sin(double)", "declare double @sin(double)")
                .replace("call double @llvm", "call double (double) @llvm"),
        ),
        (
            "sin_vector_lanes_c_header".to_string(),
            libm_vector_program("declare double @sin(double)"),
        ),
    ];
    for (family, operands) in LIBM_FAMILIES {
        for (ty, symbol) in [
            ("double", family.to_string()),
            ("float", format!("{family}f")),
        ] {
            let suffix = if ty == "double" { "f64" } else { "f32" };
            let intrinsic = format!("llvm.{family}.{suffix}");
            let params = vec![ty; operands].join(", ");
            controls.push((
                format!("{intrinsic}_c_header"),
                libm_program(
                    &intrinsic,
                    ty,
                    operands,
                    &format!("declare {ty} @{symbol}({params})"),
                ),
            ));
        }
    }
    for (stem, src) in &controls {
        assert_imports(stem, src, LINUX);
    }
}

/// Rule 10: a libm intrinsic call stating another type than the
/// intrinsic's (an operand of another type, another count, a variadic
/// call type) is refused by name; llc 22.1.2 refuses each ("Invalid user of
/// intrinsic instruction!", "Intrinsic has incorrect argument type!",
/// "Callsite was not defined with variable arguments!", "invalid intrinsic
/// signature"), and this importer would call the C symbol at the call's
/// type. The call is checked against a declaration of the intrinsic too, as
/// any call is against its callee's (rule 9). An uncalled declaration of the
/// intrinsic at another type imports, as llc builds it.
#[test]
fn a_libm_intrinsic_call_stating_another_type_than_the_intrinsics_is_refused_by_name() {
    let sin = libm_program("llvm.sin.f64", "double", 1, "declare double @sin(double)");
    let pow = libm_program(
        "llvm.pow.f64",
        "double",
        2,
        "declare double @pow(double, double)",
    );
    let sin_call = "call double @llvm.sin.f64(double 7.5e-01)";
    for (stem, src, intrinsic) in [
        (
            "float_operand_no_declarations",
            sin.replace(sin_call, "call double @llvm.sin.f64(float 7.5e-01)")
                .replace("declare double @llvm.sin.f64(double)\n", "")
                .replace("declare double @sin(double)\n", ""),
            "llvm.sin.f64",
        ),
        (
            "float_operand",
            sin.replace(sin_call, "call double @llvm.sin.f64(float 7.5e-01)"),
            "llvm.sin.f64",
        ),
        (
            "float_operand_undeclared",
            sin.replace(sin_call, "call double @llvm.sin.f64(float 7.5e-01)")
                .replace("declare double @llvm.sin.f64(double)\n", ""),
            "llvm.sin.f64",
        ),
        (
            "two_operands",
            sin.replace(
                sin_call,
                "call double @llvm.sin.f64(double 7.5e-01, double 1.0)",
            ),
            "llvm.sin.f64",
        ),
        (
            "variadic_call_type",
            sin.replace(
                sin_call,
                "call double (double, ...) @llvm.sin.f64(double 7.5e-01)",
            ),
            "llvm.sin.f64",
        ),
        (
            "pow_one_operand",
            pow.replace(
                "@llvm.pow.f64(double 7.5e-01, double 7.5e-01)",
                "@llvm.pow.f64(double 7.5e-01)",
            ),
            "llvm.pow.f64",
        ),
    ] {
        assert_refused(stem, &src, LINUX, &format!("`@{intrinsic}`"), RULE_10);
    }
    // The call at the intrinsic's type against a declaration of the
    // intrinsic at another: refused as a call stating another type than its
    // callee's (rule 9), and an unprototyped one by its split.
    assert_refused(
        "intrinsic_declared_with_a_float_operand",
        &sin.replace(
            "declare double @llvm.sin.f64(double)",
            "declare double @llvm.sin.f64(float)",
        ),
        LINUX,
        "`@llvm.sin.f64`",
        RULE_9,
    );
    assert_refused(
        "intrinsic_declared_unprototyped",
        &sin.replace(
            "declare double @llvm.sin.f64(double)",
            "declare double @llvm.sin.f64(...)",
        ),
        LINUX,
        "`@llvm.sin.f64`",
        "has no faithful spelling",
    );
    for (stem, src) in [
        ("sin", sin.clone()),
        (
            "explicit_call_type",
            sin.replace(
                sin_call,
                "call double (double) @llvm.sin.f64(double 7.5e-01)",
            ),
        ),
        ("pow", pow.clone()),
        (
            "uncalled_intrinsic_declared_otherwise",
            format!("{sin}declare double @llvm.cos.f64(float)\n"),
        ),
    ] {
        assert_imports(stem, &src, LINUX);
    }
}

/// A Darwin pattern fill of 16-byte elements, which this importer lowers
/// to a call of libSystem's `memset_pattern16` at `void (ptr, ptr, i64)`.
const MSP16_FILL: &str = "declare void @llvm.experimental.memset.pattern.p0.i128.i64(ptr, i128, i64, i1)\n\
     define void @f(ptr %d) {\n  \
     call void @llvm.experimental.memset.pattern.p0.i128.i64(ptr %d, i128 5, i64 4, i1 false)\n  \
     ret void\n}\n";

/// Rule 10 for the other call this importer writes in place of an
/// intrinsic: beside a `memset_patternN` declared otherwise than
/// libSystem's `void (ptr, ptr, i64)` (another result, count type, a
/// variadic or unprototyped header, a hidden return buffer), the pattern
/// fill was called by the module's header (llc 22.1.2's Darwin object calls
/// no `memset_pattern16` for the first four); refused by name now, in either
/// order. With libSystem's header, before or after the fill, or none, it
/// imports.
#[test]
fn a_memset_pattern_routine_declared_otherwise_is_refused_by_name() {
    let msp4_fill = MSP16_FILL
        .replace("p0.i128.i64", "p0.i32.i64")
        .replace("i128", "i32");
    for (stem, src, routine, why) in [
        (
            "msp16_i32_result",
            format!("declare i32 @memset_pattern16(ptr, ptr, i64)\n{MSP16_FILL}"),
            "memset_pattern16",
            RULE_10,
        ),
        (
            "msp16_i32_count",
            format!("declare void @memset_pattern16(ptr, ptr, i32)\n{MSP16_FILL}"),
            "memset_pattern16",
            RULE_10,
        ),
        (
            "msp16_variadic",
            format!("declare void @memset_pattern16(ptr, ptr, i64, ...)\n{MSP16_FILL}"),
            "memset_pattern16",
            RULE_10,
        ),
        (
            "msp16_unprototyped",
            format!("declare void @memset_pattern16(...)\n{MSP16_FILL}"),
            "memset_pattern16",
            RULE_10,
        ),
        (
            "msp16_hidden_return_buffer",
            format!("declare void @memset_pattern16(ptr sret(i8), ptr, i64)\n{MSP16_FILL}"),
            "memset_pattern16",
            "hidden return-buffer",
        ),
        (
            "msp4_i64_result",
            format!("declare i64 @memset_pattern4(ptr, ptr, i64)\n{msp4_fill}"),
            "memset_pattern4",
            RULE_10,
        ),
        (
            "msp16_i32_result_after_the_fill",
            format!("{MSP16_FILL}declare i32 @memset_pattern16(ptr, ptr, i64)\n"),
            "memset_pattern16",
            "conflicting signatures",
        ),
    ] {
        assert_refused(stem, &src, APPLE, &format!("`@{routine}`"), why);
    }
    for (stem, src) in [
        ("msp16_no_header", MSP16_FILL.to_string()),
        (
            "msp16_libsystem_header",
            format!("declare void @memset_pattern16(ptr, ptr, i64)\n{MSP16_FILL}"),
        ),
        (
            "msp16_libsystem_header_after_the_fill",
            format!("{MSP16_FILL}declare void @memset_pattern16(ptr, ptr, i64)\n"),
        ),
        ("msp4_no_header", msp4_fill.clone()),
    ] {
        assert_imports(stem, &src, APPLE);
    }
}

/// Rule 10's runnable controls: libm intrinsics with C's headers.
const M1_LIBM_C_HEADERS: &str = r#"
@fmt = private constant [46 x i8] c"sin=%a cos=%a pow=%a atan2=%a\0Aexp=%a sinf=%a\0A\00"

declare i32 @printf(ptr, ...)
declare double @sin(double)
declare double @cos(double)
declare double @pow(double, double)
declare double @atan2(double, double)
declare double @exp(double)
declare float @sinf(float)

define i32 @main() {
  %s = call double @llvm.sin.f64(double 1.0)
  %c = call double @llvm.cos.f64(double 1.0)
  %p = call double @llvm.pow.f64(double 2.0, double 0.5)
  %a = call double @llvm.atan2.f64(double 1.0, double 2.0)
  %e = call double @llvm.exp.f64(double 0.75)
  %f = call float @llvm.sin.f32(float 1.0)
  %fd = fpext float %f to double
  %r = call i32 (ptr, ...) @printf(ptr @fmt, double %s, double %c, double %p, double %a, double %e, double %fd)
  ret i32 0
}

declare double @llvm.sin.f64(double)
declare double @llvm.cos.f64(double)
declare double @llvm.pow.f64(double, double)
declare double @llvm.atan2.f64(double, double)
declare double @llvm.exp.f64(double)
declare float @llvm.sin.f32(float)
"#;

/// Rule 10's runnable controls: libm intrinsics without headers, one
/// through the vector expander's lane calls.
const M2_LIBM_NO_HEADERS: &str = r#"
@fmt = private constant [33 x i8] c"sin=%a log10=%a v=%a,%a sinf=%a\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %s = call double @llvm.sin.f64(double 1.0)
  %l = call double @llvm.log10.f64(double 0.75)
  %v = call <2 x double> @llvm.sin.v2f64(<2 x double> <double 0.5, double 2.0>)
  %v0 = extractelement <2 x double> %v, i64 0
  %v1 = extractelement <2 x double> %v, i64 1
  %f = call float @llvm.sin.f32(float 1.0)
  %fd = fpext float %f to double
  %r = call i32 (ptr, ...) @printf(ptr @fmt, double %s, double %l, double %v0, double %v1, double %fd)
  ret i32 0
}

declare double @llvm.sin.f64(double)
declare double @llvm.log10.f64(double)
declare <2 x double> @llvm.sin.v2f64(<2 x double>)
declare float @llvm.sin.f32(float)
"#;

/// Rule 10's runnable controls: an unprototyped `sin` header after the
/// call (it keeps the call's signature) and a call through the explicit
/// non-variadic type.
const M3_LIBM_HEADER_AFTER_CALL: &str = r#"
@fmt = private constant [16 x i8] c"sin=%a tanh=%a\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
  %s = call double @llvm.sin.f64(double 1.0)
  %t = call double (double) @llvm.tanh.f64(double 0.5)
  %r = call i32 (ptr, ...) @printf(ptr @fmt, double %s, double %t)
  ret i32 0
}

declare double @llvm.sin.f64(double)
declare double @llvm.tanh.f64(double)
declare double @sin(...)
declare double @tanh(double)
"#;

/// Rule 10's controls run: each object calls `sin` and prints what llc
/// 22.1.2's Linux AArch64 builds of the same module printed at O0 and O2
/// (glibc's libm; measured, the expected text below). Before and after
/// rule 10 alike.
#[test]
fn libm_intrinsics_with_c_headers_or_none_run_as_llc_built_them() {
    let test = "libm_intrinsics_with_c_headers_or_none_run_as_llc_built_them";
    if !native_host_or_skip(test) {
        return;
    }
    if !LINUX_GNU {
        eprintln!(
            "SKIP {test}: the expected text is llc's Linux AArch64 builds' output, read from \
             glibc's libm"
        );
        return;
    }
    let dir = unique_temp_dir("libcall-prototypes-libm");
    for (stem, src, expected) in [
        (
            "m1_libm_c_headers",
            M1_LIBM_C_HEADERS,
            "sin=0x1.aed548f090ceep-1 cos=0x1.14a280fb5068cp-1 pow=0x1.6a09e667f3bcdp+0 \
             atan2=0x1.dac670561bb4fp-2\nexp=0x1.0ef9db467dcf8p+1 sinf=0x1.aed548p-1\n",
        ),
        (
            "m2_libm_no_headers",
            M2_LIBM_NO_HEADERS,
            "sin=0x1.aed548f090ceep-1 log10=-0x1.ffbfc2bbc7802p-4 \
             v=0x1.eaee8744b05fp-2,0x1.d18f6ead1b446p-1 sinf=0x1.aed548p-1\n",
        ),
        (
            "m3_libm_header_after_call",
            M3_LIBM_HEADER_AFTER_CALL,
            "sin=0x1.aed548f090ceep-1 tanh=0x1.d9353d7568af3p-2\n",
        ),
    ] {
        for level in [OptLevel::O0, OptLevel::O2] {
            let (object, stdout) = build_and_run(&dir, stem, src, None, &["-lm"], level);
            assert!(
                undefined_symbols(&object).contains(&object_symbol(HOST_TRIPLE, "sin")),
                "{stem} at {level:?}: the object must call `sin`"
            );
            assert_eq!(stdout, expected, "{stem} at {level:?}");
        }
    }
}

const RULE_11: &str = "LD-100 rule 11";

/// The fifth L02-P15 re-check's shape (`s1_memcpy_sret_decl_intrinsic`, at
/// `848a8638d`): a module function named `routine` declared with a hidden
/// return buffer, `void (ptr sret(%S), second, i64)`, called directly in a
/// branch never taken at run time, beside `@llvm.<routine>` with the count
/// `count` (`%c`, a run-time 21, or a literal). The selector keyed the
/// hidden-buffer fact by the symbol's name, so its own call of `routine`
/// for the intrinsic passed the destination in `x8`, the source in `x0` and
/// the count in `x1`: the import died with signal 11 in 24 of 24
/// configurations where llc's build, which calls the routine at C's
/// convention whatever the module declares, printed the copy (the
/// re-check's 11 probes: `memcpy` at a run-time count, 40 and 64 bytes;
/// `memmove` and `memset` at a run-time count, 8, 40 and 64; a `memcpy` of
/// 8 bytes is expanded inline and ran alike). `header` `"sret"` declares
/// that; any other value declares C's prototype instead (the control).
fn hidden_buffer_routine_program(routine: &str, header: &str, count: &str) -> String {
    let (second, second_arg, intrinsic, source) = match routine {
        "memset" => ("i32", "i32 65", "@llvm.memset.p0.i64", "i8 66"),
        "memmove" => ("ptr", "ptr @src", "@llvm.memmove.p0.p0.i64", "ptr @src"),
        _ => ("ptr", "ptr @src", "@llvm.memcpy.p0.p0.i64", "ptr @src"),
    };
    let intrinsic_params = if routine == "memset" {
        "ptr, i8, i64, i1"
    } else {
        "ptr, ptr, i64, i1"
    };
    let (header, call) = match header {
        "sret" => (
            format!("declare void @{routine}(ptr sret(%S), {second}, i64)"),
            format!("call void @{routine}(ptr sret(%S) %buf, {second_arg}, i64 8)"),
        ),
        _ => (
            format!("declare ptr @{routine}(ptr, {second}, i64)"),
            format!("%r = call ptr @{routine}(ptr %buf, {second_arg}, i64 8)"),
        ),
    };
    format!(
        "%S = type {{ [4 x i64] }}\n\
         @src = global [64 x i8] c\"abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ!?\"\n\
         @dst = global [64 x i8] zeroinitializer\n\
         @n = global i64 21\n\
         @flag = global i32 0\n\
         @fs = private constant [6 x i8] c\"[%s]\\0A\\00\"\n\
         declare i32 @printf(ptr, ...)\n\
         {header}\n\
         declare void {intrinsic}({intrinsic_params})\n\
         define i32 @main() {{\n\
         entry:\n  \
         %buf = alloca %S\n  \
         %f = load volatile i32, ptr @flag\n  \
         %never = icmp eq i32 %f, 12345\n  \
         br i1 %never, label %odd, label %go\n\
         odd:\n  \
         {call}\n  \
         br label %go\n\
         go:\n  \
         %c = load volatile i64, ptr @n\n  \
         call void {intrinsic}(ptr @dst, {source}, i64 {count}, i1 false)\n  \
         %p = call i32 (ptr, ...) @printf(ptr @fs, ptr @dst)\n  \
         ret i32 0\n\
         }}\n"
    )
}

/// Compile `src` (imported for `triple`) at O0 and O2 and require a refusal
/// naming `routine` and saying `why` (rule 11's, or trust-ir's for a pinned
/// RC-runtime entry).
fn assert_compile_refused(stem: &str, src: &str, triple: &str, routine: &str, why: &[&str]) {
    let module = import_text_for_target(src, stem, triple)
        .unwrap_or_else(|error| panic!("{stem} for {triple}: must import: {error}"));
    for level in [OptLevel::O0, OptLevel::O2] {
        match compiler_for(triple, level).compile(&module) {
            Err(error) => {
                let reason = error.to_string();
                assert!(
                    why.iter().all(|needle| reason.contains(needle))
                        && reason.contains(&format!("`{routine}`")),
                    "{stem} for {triple} at {level:?}: the refusal must name `{routine}` and say \
                     {why:?}: {reason}"
                );
            }
            Ok(_) => panic!("{stem} for {triple} at {level:?}: compiled; it must be refused"),
        }
    }
}

/// Rule 11's refusal, naming `routine`.
const RULE_11_REFUSAL: [&str; 2] = ["[TCG-SRET-ABI]", RULE_11];

/// LD-100 rule 11. A module function named like a routine this backend
/// calls on its own (`trust_cg_lower::RuntimeSymbol`), declared with a
/// hidden return buffer and called directly, is refused by name: the
/// selector keys that fact by the symbol's name, which the backend's own
/// call of the routine shares. Every reproducer shape, and every listed
/// name, on both targets. The Clean RC entries are refused before, by
/// trust-ir's validation, which pins their declaration, parameter
/// attributes included (`RcEntryPointSignatureMismatch`).
#[test]
fn a_runtime_routine_name_declared_with_a_hidden_buffer_is_refused_by_name() {
    for routine in ["memcpy", "memmove", "memset"] {
        for count in ["%c", "8", "40", "64"] {
            let src = hidden_buffer_routine_program(routine, "sret", count);
            for triple in TARGETS {
                assert_compile_refused(
                    &format!("{routine}_sret_beside_the_intrinsic_{count}"),
                    &src,
                    triple,
                    routine,
                    &RULE_11_REFUSAL,
                );
            }
        }
    }
    for symbol in trust_cg_lower::RuntimeSymbol::ALL {
        let name = symbol.name();
        let why: &[&str] = if name.starts_with("clean_") {
            &["RcEntryPointSignatureMismatch"]
        } else {
            &RULE_11_REFUSAL
        };
        let src = format!(
            "%S = type {{ [4 x i64] }}\n\
             @src = global [8 x i8] zeroinitializer\n\
             declare void @{name}(ptr sret(%S), ptr, i64)\n\
             define void @f() {{\n  \
             %buf = alloca %S\n  \
             call void @{name}(ptr sret(%S) %buf, ptr @src, i64 8)\n  \
             ret void\n}}\n"
        );
        for triple in TARGETS {
            assert_compile_refused(&format!("{name}_sret"), &src, triple, name, why);
        }
    }
    // Control: the same shape under another name compiles.
    let src = "%S = type { [4 x i64] }\n\
               @src = global [8 x i8] zeroinitializer\n\
               declare void @fill_s(ptr sret(%S), ptr, i64)\n\
               define void @f() {\n  \
               %buf = alloca %S\n  \
               call void @fill_s(ptr sret(%S) %buf, ptr @src, i64 8)\n  \
               ret void\n}\n";
    for triple in TARGETS {
        let module = import_text_for_target(src, "fill_s_sret", triple)
            .unwrap_or_else(|error| panic!("fill_s_sret for {triple}: must import: {error}"));
        for level in [OptLevel::O0, OptLevel::O2] {
            if let Err(error) = compiler_for(triple, level).compile(&module) {
                panic!("fill_s_sret for {triple} at {level:?}: must compile: {error}");
            }
        }
    }
}

/// Rule 11's controls run: a hidden-buffer callee of another name keeps
/// `x8` beside the backend's own `memcpy`, `memmove` and `memset` calls in
/// the same function (the C object defines it as `struct S fill_s(const
/// char *, long)`), and the reproducer shape with C's prototype for the
/// routine copies. Each prints what llc 22.1.2's Linux AArch64 build of the
/// same module printed (measured; before and after rule 11 alike).
#[test]
fn hidden_buffer_calls_of_other_names_and_c_prototypes_run_as_llc_built_them() {
    let test = "hidden_buffer_calls_of_other_names_and_c_prototypes_run_as_llc_built_them";
    if !native_host_or_skip(test) {
        return;
    }
    let dir = unique_temp_dir("libcall-prototypes-hidden-buffer");
    let extra = compile_extra_c(&dir, "fill_s", FILL_S_EXTRA_C);
    for level in [OptLevel::O0, OptLevel::O2] {
        let (object, stdout) = build_and_run(
            &dir,
            "c1_sret_other_name_beside_mem_intrinsics",
            C1_SRET_OTHER_NAME,
            Some(&extra),
            &[],
            level,
        );
        let undefined = undefined_symbols(&object);
        for routine in ["fill_s", "memcpy", "memmove", "memset"] {
            assert!(
                undefined.contains(&object_symbol(HOST_TRIPLE, routine)),
                "c1 at {level:?}: the object must call `{routine}`"
            );
        }
        assert_eq!(
            stdout,
            "[abcdefghijklmnopqrstu] [abcdefghijklmnopqrstu] [BBBBBBBBBBBBBBBBBBBBB] \
             6867666564636261 8\n",
            "c1 at {level:?}"
        );
    }
    for (routine, expected) in [
        ("memcpy", "[abcdefghijklmnopqrstu]\n"),
        ("memmove", "[abcdefghijklmnopqrstu]\n"),
        ("memset", "[BBBBBBBBBBBBBBBBBBBBB]\n"),
    ] {
        let stem = format!("{routine}_c_prototype_beside_the_intrinsic");
        let src = hidden_buffer_routine_program(routine, "c", "%c");
        for level in [OptLevel::O0, OptLevel::O2] {
            let (_, stdout) = build_and_run(&dir, &stem, &src, None, &[], level);
            assert_eq!(stdout, expected, "{stem} at {level:?}");
        }
    }
}

/// Rule 11's control `c1`: `fill_s`, declared with a hidden return buffer
/// and not named like a runtime routine, called directly beside the three
/// memory intrinsics at a run-time count.
const C1_SRET_OTHER_NAME: &str = r#"
%S = type { [4 x i64] }

@src = global [32 x i8] c"abcdefghijklmnopqrstuvwxyz012345"
@d1 = global [32 x i8] zeroinitializer
@d2 = global [32 x i8] zeroinitializer
@d3 = global [32 x i8] zeroinitializer
@n = global i64 21
@fmt = private constant [26 x i8] c"[%s] [%s] [%s] %llx %lld\0A\00"

declare i32 @printf(ptr, ...)
declare void @fill_s(ptr sret(%S), ptr, i64)
declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)
declare void @llvm.memmove.p0.p0.i64(ptr, ptr, i64, i1)
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)

define i32 @main() {
entry:
  %buf = alloca %S
  call void @fill_s(ptr sret(%S) %buf, ptr @src, i64 8)
  %c = load volatile i64, ptr @n
  call void @llvm.memcpy.p0.p0.i64(ptr @d1, ptr @src, i64 %c, i1 false)
  call void @llvm.memmove.p0.p0.i64(ptr @d2, ptr @src, i64 %c, i1 false)
  call void @llvm.memset.p0.i64(ptr @d3, i8 66, i64 %c, i1 false)
  %w0 = load i64, ptr %buf
  %f3 = getelementptr i8, ptr %buf, i64 24
  %w3 = load i64, ptr %f3
  %p = call i32 (ptr, ...) @printf(ptr @fmt, ptr @d1, ptr @d2, ptr @d3, i64 %w0, i64 %w3)
  ret i32 0
}
"#;

/// `fill_s`: a 32-byte result (returned through `x8` on AArch64) holding the
/// first `n` (at most 16) bytes of `p` and, in its last word, `n`.
const FILL_S_EXTRA_C: &str = "\
struct S {
    long long v[4];
};

struct S fill_s(const char *p, long n) {
    struct S s;
    s.v[0] = 0;
    s.v[1] = 0;
    s.v[2] = 0;
    for (long i = 0; i < n && i < 16; i++) {
        ((char *)s.v)[i] = p[i];
    }
    s.v[3] = n;
    return s;
}
";

/// The words every rule-12 refusal carries.
const RULE_12: &str = "LD-100 rule 12";

/// The sixth re-check's shape: `@{callee}` declared (`linkage`, `header`
/// the rest of the declaration) and called by `call` (on `%buf`, a 32-byte
/// stack slot, and `%c`, a run-time count), the slot's four words printed.
/// `guard` wraps the call in clang's null test of the address, and `after`
/// prints the declaration after the call, as clang does.
fn weak_call_program(
    linkage: &str,
    header: &str,
    call: &str,
    callee: &str,
    guard: bool,
    after: bool,
) -> String {
    let declaration = format!("declare {linkage} {header}\n");
    let (open, close) = if guard {
        (
            format!(
                "  %nz = icmp ne ptr @{callee}, null\n  br i1 %nz, label %call, label %skip\n\
                 call:\n"
            ),
            "  br label %skip\nskip:\n".to_string(),
        )
    } else {
        (String::new(), String::new())
    };
    format!(
        "%S = type {{ [4 x i64] }}\n\
         @src = global [32 x i8] c\"abcdefghijklmnopqrstuvwxyz012345\"\n\
         @n = global i64 21\n\
         @f4 = private constant [21 x i8] c\"%llx %llx %llx %llx\\0A\\00\"\n\
         declare i32 @printf(ptr, ...)\n\
         {before}\
         define i32 @main() {{\n\
         entry:\n  \
         %buf = alloca %S\n  \
         %c = load volatile i64, ptr @n\n\
         {open}  \
         {call}\n\
         {close}  \
         %w0 = load i64, ptr %buf\n  \
         %g1 = getelementptr i8, ptr %buf, i64 8\n  \
         %w1 = load i64, ptr %g1\n  \
         %g2 = getelementptr i8, ptr %buf, i64 16\n  \
         %w2 = load i64, ptr %g2\n  \
         %g3 = getelementptr i8, ptr %buf, i64 24\n  \
         %w3 = load i64, ptr %g3\n  \
         %p = call i32 (ptr, ...) @printf(ptr @f4, i64 %w0, i64 %w1, i64 %w2, i64 %w3)\n  \
         ret i32 0\n\
         }}\n\
         {later}",
        before = if after { "" } else { declaration.as_str() },
        later = if after { declaration.as_str() } else { "" },
    )
}

/// LD-100 rule 12. A direct call of an `extern_weak` function whose
/// declaration has a hidden return buffer (`sret`) is refused by name at
/// import, on both targets: the call must go through the function's
/// address, and the backend's indirect call carries no `sret` (it passed
/// the buffer in `x0` and shifted every argument, where llc passes it in
/// `x8`; the sixth re-check's 12 probes, 0 of 24 configurations equal).
/// The re-check's shapes: one, two and nine arguments, the buffer second, a
/// null-guarded call, the declaration after the call, `fastcc`, a `tail` and
/// a `notail` call, beside a strong hidden-buffer call, and the routine
/// names rule 11 refuses (`memcpy`, `memset`, `fmod`), which this path let
/// past it.
/// So is a weak intrinsic the backend lowers by name: through its address
/// the call reached an undefined weak symbol named after the intrinsic
/// (SIGSEGV where llc lowers the intrinsic; found by this repair's sweep).
/// Each module with its declaration strong imports.
#[test]
fn a_weak_call_the_indirect_lowering_would_change_is_refused_by_name() {
    let sret: [(&str, &str, &str); 11] = [
        (
            "mk1",
            "void @mk1(ptr sret(%S), i64)",
            "call void @mk1(ptr sret(%S) %buf, i64 %c)",
        ),
        (
            "fill_s",
            "void @fill_s(ptr sret(%S), ptr, i64)",
            "call void @fill_s(ptr sret(%S) %buf, ptr @src, i64 8)",
        ),
        (
            "mk9",
            "void @mk9(ptr sret(%S), i64, i64, i64, i64, i64, i64, i64, i64, i64)",
            "call void @mk9(ptr sret(%S) %buf, i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, \
             i64 7, i64 8, i64 %c)",
        ),
        (
            "mk2",
            "void @mk2(i64, ptr sret(%S))",
            "call void @mk2(i64 %c, ptr sret(%S) %buf)",
        ),
        (
            "mkf",
            "fastcc void @mkf(ptr sret(%S), double, i64, double)",
            "call fastcc void @mkf(ptr sret(%S) %buf, double 1.5, i64 %c, double 2.5)",
        ),
        (
            "mk1",
            "void @mk1(ptr sret(%S), i64)",
            "tail call void @mk1(ptr sret(%S) %buf, i64 %c)",
        ),
        (
            "mk1",
            "void @mk1(ptr sret(%S), i64)",
            "notail call void @mk1(ptr sret(%S) %buf, i64 %c)",
        ),
        (
            "mk1",
            "void @mk1(ptr sret(%S), i64)\ndeclare void @mk2(ptr sret(%S), i64)",
            "call void @mk2(ptr sret(%S) %buf, i64 3)\n  \
             call void @mk1(ptr sret(%S) %buf, i64 %c)",
        ),
        (
            "memcpy",
            "void @memcpy(ptr sret(%S), ptr, i64)",
            "call void @memcpy(ptr sret(%S) %buf, ptr @src, i64 8)",
        ),
        (
            "fmod",
            "void @fmod(ptr sret(%S), i64)",
            "call void @fmod(ptr sret(%S) %buf, i64 %c)",
        ),
        (
            "memset",
            "void @memset(ptr sret(%S), i32, i64)",
            "call void @memset(ptr sret(%S) %buf, i32 65, i64 %c)",
        ),
    ];
    for (index, (callee, header, call)) in sret.iter().enumerate() {
        for (guard, after) in [(false, false), (true, false), (false, true)] {
            let stem = format!("weak_sret_{index}_{callee}_{guard}_{after}");
            let weak = weak_call_program("extern_weak", header, call, callee, guard, after);
            let strong = weak_call_program("", header, call, callee, guard, after);
            for triple in TARGETS {
                assert_refused(&stem, &weak, triple, &format!("`@{callee}`"), RULE_12);
                assert_refused(
                    &stem,
                    &weak,
                    triple,
                    "hidden return buffer (`sret`)",
                    RULE_12,
                );
                assert_imports(&format!("{stem}_strong"), &strong, triple);
            }
        }
    }
    let intrinsics: [(&str, &str, &str); 7] = [
        (
            "llvm.memcpy.p0.p0.i64",
            "void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)",
            "call void @llvm.memcpy.p0.p0.i64(ptr %buf, ptr @src, i64 %c, i1 false)",
        ),
        (
            "llvm.memmove.p0.p0.i64",
            "void @llvm.memmove.p0.p0.i64(ptr, ptr, i64, i1)",
            "call void @llvm.memmove.p0.p0.i64(ptr %buf, ptr @src, i64 %c, i1 false)",
        ),
        (
            "llvm.memset.p0.i64",
            "void @llvm.memset.p0.i64(ptr, i8, i64, i1)",
            "call void @llvm.memset.p0.i64(ptr %buf, i8 65, i64 %c, i1 false)",
        ),
        (
            "llvm.bitreverse.i64",
            "i64 @llvm.bitreverse.i64(i64)",
            "%r = call i64 @llvm.bitreverse.i64(i64 %c)\n  store i64 %r, ptr %buf",
        ),
        (
            "llvm.objectsize.i64.p0",
            "i64 @llvm.objectsize.i64.p0(ptr, i1, i1, i1)",
            "%r = call i64 @llvm.objectsize.i64.p0(ptr @src, i1 false, i1 false, i1 false)\n  \
             store i64 %r, ptr %buf",
        ),
        (
            "llvm.fma.f64",
            "double @llvm.fma.f64(double, double, double)",
            "%r = call double @llvm.fma.f64(double 1.5, double 2.0, double 0.25)\n  \
             store double %r, ptr %buf",
        ),
        (
            "llvm.fmuladd.f64",
            "double @llvm.fmuladd.f64(double, double, double)",
            "%r = call double @llvm.fmuladd.f64(double 1.5, double 2.0, double 0.25)\n  \
             store double %r, ptr %buf",
        ),
    ];
    for (intrinsic, header, call) in intrinsics {
        for after in [false, true] {
            let stem = format!("weak_{intrinsic}_{after}");
            let weak = weak_call_program("extern_weak", header, call, intrinsic, false, after);
            let strong = weak_call_program("", header, call, intrinsic, false, after);
            for triple in TARGETS {
                assert_refused(&stem, &weak, triple, &format!("`@{intrinsic}`"), RULE_12);
                assert_refused(&stem, &weak, triple, "no library defines", RULE_12);
                assert_imports(&format!("{stem}_strong"), &strong, triple);
            }
        }
    }
}

/// Rule 12's control: weak calls whose facts the signature keeps go through
/// the function's address and run as llc 22.1.2's Linux AArch64 build of
/// the same module ran (measured: O0-O3, GNU ld, gold and LLD, static and
/// PIE, before and after rule 12). The C object reads or writes each narrow
/// value in a full 32-bit register, so an unextended `zeroext` or `signext`
/// argument, or a result extended otherwise, would print otherwise; `pid`
/// returns its `returned` argument; `fc` is `fastcc`; `memcpy` is C's,
/// called through its address. Linux only: Mach-O weak references are
/// refused by the backend.
#[test]
fn weak_calls_whose_facts_the_signature_keeps_run_as_llc_built_them() {
    let test = "weak_calls_whose_facts_the_signature_keeps_run_as_llc_built_them";
    if !native_host_or_skip(test) {
        return;
    }
    if !LINUX_GNU {
        eprintln!(
            "SKIP {test}: the backend refuses a Mach-O weak reference, and the expected text is \
             llc's Linux AArch64 builds' output"
        );
        return;
    }
    let dir = unique_temp_dir("libcall-prototypes-weak-calls");
    let extra = compile_extra_c(&dir, "k12", K12_EXTRA_C);
    for level in [OptLevel::O0, OptLevel::O2] {
        let (object, stdout) = build_and_run(
            &dir,
            "k12_weak_kept_facts_control",
            K12_WEAK_KEPT_FACTS,
            Some(&extra),
            &[],
            level,
        );
        let undefined = undefined_symbols(&object);
        for callee in ["zx8", "sx8", "zr16", "sr16", "pid", "fc", "memcpy"] {
            assert!(
                undefined.contains(callee),
                "k12 at {level:?}: the object must reference `{callee}`: {undefined:?}"
            );
        }
        assert_eq!(
            stdout, "89 ffffff89 acf1 2b3c abcdef0123453dd3 451 [abcdefghijklmnopqrstu]\n",
            "k12 at {level:?}"
        );
    }
}

/// Rule 12's control `k12_weak_kept_facts_control`.
const K12_WEAK_KEPT_FACTS: &str = r#"
@src = global [32 x i8] c"abcdefghijklmnopqrstuvwxyz012345"
@dst = global [32 x i8] zeroinitializer
@big = global i64 -6066930334832433271
@n = global i64 21
@fmt = private constant [26 x i8] c"%x %x %x %x %llx %d [%s]\0A\00"

declare i32 @printf(ptr, ...)
declare extern_weak i32 @zx8(i8 zeroext)
declare extern_weak i32 @sx8(i8 signext)
declare extern_weak zeroext i16 @zr16(i64)
declare extern_weak signext i16 @sr16(i64)
declare extern_weak ptr @pid(ptr noundef nonnull returned)
declare extern_weak fastcc i32 @fc(i32, i32)
declare extern_weak ptr @memcpy(ptr, ptr, i64)

define i32 @main() {
entry:
  %v = load volatile i64, ptr @big
  %t = trunc i64 %v to i8
  %a = call i32 @zx8(i8 zeroext %t)
  %b = call i32 @sx8(i8 signext %t)
  %c = call zeroext i16 @zr16(i64 %v)
  %cz = zext i16 %c to i32
  %d = call signext i16 @sr16(i64 %v)
  %ds = sext i16 %d to i32
  %p = call ptr @pid(ptr @big)
  %pv = load i64, ptr %p
  %e = tail call fastcc i32 @fc(i32 %a, i32 40)
  %k = load volatile i64, ptr @n
  %r = call ptr @memcpy(ptr @dst, ptr @src, i64 %k)
  %o = call i32 (ptr, ...) @printf(ptr @fmt, i32 %a, i32 %b, i32 %cz, i32 %ds, i64 %pv, i32 %e, ptr %r)
  ret i32 0
}
"#;

/// The C object rule 12's control links: each narrow value is read or
/// written in a full 32-bit register.
const K12_EXTRA_C: &str = "\
unsigned zx8(unsigned x) { return x; }
int sx8(int x) { return x; }
unsigned short zr16(long v) { return (unsigned short)(v >> 3); }
short sr16(long v) { return (short)(v >> 5); }
long *pid(long *p) { *p ^= 0x5a5a; return p; }
int fc(int a, int b) { return a * 3 + b; }
";
