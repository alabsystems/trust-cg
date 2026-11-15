// trust-cg-llvm-import / tests/library_name_refusals.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// L02-P15 (decision record LD-86): a module that
// defines a function or global under a name llc 22.1.2's code generator
// calls or replaces on its own is refused by name, whatever the
// definition's linkage, and a vector intrinsic declaration is read only
// under the name LLVM gives its declared types. The reproducers are the
// closure audit's of 2026-10-16 (each ran otherwise under llc at O1-O3
// than in the import); every test here uses the public API only, so it
// runs against an importer without the rules.

use trust_cg_llvm_import::{Error, import_text, import_text_for_target};

const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";

fn refusal(src: &str, target: &str) -> String {
    match import_text_for_target(src, "t", target) {
        Err(Error::Unsupported(reason)) => reason,
        other => panic!("expected a named refusal for {target}\n{src}\ngot {other:?}"),
    }
}

fn library_meaning(name: &str) -> String {
    format!("gives `{name}` library meaning on its own")
}

fn runtime_libcall(name: &str) -> String {
    format!("LLVM 22.1.2 lists `{name}` as a runtime library call for AArch64")
}

/// The audit's `chk_strcpy`: the module's own `__strcpy_chk`, called with
/// object size -1, wrote `X` (88) in the import at O0-O3, where llc at
/// O1-O3 called `strcpy` (97).
const CHK_STRCPY: &str = "\
target triple = \"aarch64-unknown-linux-gnu\"
@buf = global [16 x i8] zeroinitializer
@src = constant [4 x i8] c\"abc\\00\"
define ptr @__strcpy_chk(ptr %d, ptr %s, i64 %n) {
entry:
  store i8 88, ptr %d
  %p1 = getelementptr i8, ptr %d, i64 1
  store i8 0, ptr %p1
  ret ptr %d
}
define i32 @main() {
entry:
  %r = call ptr @__strcpy_chk(ptr @buf, ptr @src, i64 -1)
  %c = load i8, ptr @buf
  %z = zext i8 %c to i32
  ret i32 %z
}
";

/// The audit's `chk_memcpy`: an internal `__memcpy_chk` gave 7 in the
/// import, 42 (`memcpy`) in llc's build at O1-O3.
const CHK_MEMCPY_INTERNAL: &str = "\
target triple = \"aarch64-unknown-linux-gnu\"
@dst = global [8 x i8] zeroinitializer
@src = global [8 x i8] c\"*bcdefg\\00\"
define internal ptr @__memcpy_chk(ptr %d, ptr %s, i64 %n, i64 %sz) {
entry:
  store i8 7, ptr %d
  ret ptr %d
}
define i32 @main() {
entry:
  %r = call ptr @__memcpy_chk(ptr @dst, ptr @src, i64 8, i64 -1)
  %c = load i8, ptr @dst
  %z = zext i8 %c to i32
  ret i32 %z
}
";

/// Every fortified function of LLVM 22.1.2's `TargetLibraryInfo.td`.
const FORTIFIED: [&str; 18] = [
    "__memccpy_chk",
    "__memcpy_chk",
    "__memmove_chk",
    "__mempcpy_chk",
    "__memset_chk",
    "__snprintf_chk",
    "__sprintf_chk",
    "__stpcpy_chk",
    "__stpncpy_chk",
    "__strcat_chk",
    "__strcpy_chk",
    "__strlcat_chk",
    "__strlcpy_chk",
    "__strlen_chk",
    "__strncat_chk",
    "__strncpy_chk",
    "__vsnprintf_chk",
    "__vsprintf_chk",
];

#[test]
fn fortified_definitions_are_refused_whatever_their_linkage() {
    assert!(refusal(CHK_STRCPY, LINUX).contains(&library_meaning("__strcpy_chk")));
    assert!(refusal(CHK_MEMCPY_INTERNAL, LINUX).contains(&library_meaning("__memcpy_chk")));
    for name in FORTIFIED {
        for linkage in ["", "internal", "private", "weak", "linkonce_odr"] {
            for target in [LINUX, DARWIN] {
                let src = format!(
                    "define {linkage} ptr @{name}(ptr %d, ptr %s, i64 %n, i64 %m) {{\n  \
                     ret ptr %d\n}}\n"
                );
                let reason = refusal(&src, target);
                assert!(reason.contains(&library_meaning(name)), "{src}: {reason}");
                assert!(reason.contains("object size is unknown"), "{src}: {reason}");
            }
        }
    }
}

/// The audit's `ldexp_sve`: the module's own `ldexp` (42), called
/// `memory(none)` from a `+sve` function, ran in the import at O0-O3,
/// where llc at O1-O3 computed 1.5 * 2^3 with an SVE `fscale` (12).
const LDEXP_SVE: &str = "\
target triple = \"aarch64-unknown-linux-gnu\"
define double @ldexp(double %x, i32 %n) {
entry:
  ret double 4.200000e+01
}
define i32 @main() #0 {
entry:
  %v = call double @ldexp(double 1.500000e+00, i32 3) #1
  %i = fptosi double %v to i32
  ret i32 %i
}
attributes #0 = { \"target-features\"=\"+sve\" }
attributes #1 = { memory(none) }
";

/// The second skeptic's `ldexpf_cpu`: `"target-cpu"="neoverse-v2"` alone
/// gives SVE.
const LDEXPF_CPU: &str = "\
target triple = \"aarch64-unknown-linux-gnu\"
define float @ldexpf(float %x, i32 %e) #0 {
entry:
  ret float 42.0
}
define i32 @main() #1 {
entry:
  %r = call float @ldexpf(float 1.5, i32 3) #2
  %i = fptosi float %r to i32
  ret i32 %i
}
attributes #0 = { noinline nounwind }
attributes #1 = { nounwind \"target-cpu\"=\"neoverse-v2\" }
attributes #2 = { memory(none) nounwind }
";

#[test]
fn ldexp_definitions_are_refused_on_every_target() {
    assert!(refusal(LDEXP_SVE, LINUX).contains(&library_meaning("ldexp")));
    assert!(refusal(LDEXPF_CPU, LINUX).contains(&library_meaning("ldexpf")));
    // Without SVE llc calls the module's `ldexp` as the import does; the
    // features are not read, so the definition is refused all the same.
    for name in ["ldexp", "ldexpf", "ldexpl"] {
        for linkage in ["", "internal", "weak"] {
            for target in [LINUX, DARWIN] {
                let src = format!(
                    "define {linkage} double @{name}(double %x, i32 %n) {{\n  ret double %x\n}}\n"
                );
                let reason = refusal(&src, target);
                assert!(reason.contains(&library_meaning(name)), "{src}: {reason}");
                assert!(reason.contains("an SVE `fscale`"), "{src}: {reason}");
            }
        }
    }
}

/// The audit's `exp10_darwin`: llc's Darwin object at O1-O3 called
/// libSystem's `___exp10` for a `memory(none)` call of the module's own
/// `exp10`, which the import ran (object level; no Darwin host).
const EXP10_DARWIN: &str = "\
target triple = \"arm64-apple-macosx14.0.0\"
define double @exp10(double %x) {
entry:
  ret double 4.200000e+01
}
define i32 @main() {
entry:
  %v = call double @exp10(double 2.000000e+00) #1
  %i = fptosi double %v to i32
  ret i32 %i
}
attributes #1 = { memory(none) }
";

/// The second skeptic's `def___exp10_darwin`: llc's call of `__exp10`
/// for libSystem's `exp10` reached the module's own `__exp10`.
const DEF_UNDERSCORE_EXP10_DARWIN: &str = "\
target triple = \"arm64-apple-macosx14.0.0\"
declare double @exp10(double)
define double @__exp10(double %x) #0 {
entry:
  ret double 42.0
}
define i32 @main() {
entry:
  %r = call double @exp10(double 2.0) #1
  %i = fptosi double %r to i32
  ret i32 %i
}
attributes #0 = { noinline nounwind }
attributes #1 = { memory(none) nounwind }
";

#[test]
fn exp10_definitions_are_refused_on_every_target() {
    assert!(refusal(EXP10_DARWIN, DARWIN).contains(&library_meaning("exp10")));
    assert!(refusal(DEF_UNDERSCORE_EXP10_DARWIN, DARWIN).contains(&runtime_libcall("__exp10")));
    // Off Darwin llc calls `exp10` as the import does; the OS is not read.
    for name in ["exp10", "exp10f", "exp10l"] {
        for linkage in ["", "internal", "weak"] {
            for target in [LINUX, DARWIN] {
                let src =
                    format!("define {linkage} double @{name}(double %x) {{\n  ret double %x\n}}\n");
                let reason = refusal(&src, target);
                assert!(reason.contains(&library_meaning(name)), "{src}: {reason}");
                assert!(reason.contains("`__exp10`"), "{src}: {reason}");
            }
        }
    }
    for name in ["__exp10", "__exp10f"] {
        for target in [LINUX, DARWIN] {
            let src = format!("define double @{name}(double %x) {{\n  ret double %x\n}}\n");
            assert!(
                refusal(&src, target).contains(&runtime_libcall(name)),
                "{src}"
            );
        }
    }
}

/// The audit's `udivti3_const`: with the module's own `__udivti3` (42),
/// `udiv i128 100, 3` gave 42 in the import at O0-O3, 33 in llc's build at
/// O1-O3, which divides by a constant inline.
const UDIVTI3_CONST: &str = "\
target triple = \"aarch64-unknown-linux-gnu\"
@a = global i128 100
define i128 @__udivti3(i128 %x, i128 %y) {
entry:
  ret i128 42
}
define i32 @main() {
entry:
  %a = load i128, ptr @a
  %q = udiv i128 %a, 3
  %i = trunc i128 %q to i32
  ret i32 %i
}
";

/// The audit's `floattidf`: with the module's own `__floattidf` (70.0),
/// the `i128` 100 converted to `double` and back gave 70 in the import,
/// 100 in llc's build at O1-O3.
const FLOATTIDF: &str = "\
target triple = \"aarch64-unknown-linux-gnu\"
@a = global i128 100
define double @__floattidf(i128 %x) {
entry:
  ret double 7.000000e+01
}
define i32 @main() {
entry:
  %a = load i128, ptr @a
  %d = sitofp i128 %a to double
  %i = fptosi double %d to i32
  ret i32 %i
}
";

#[test]
fn runtime_libcall_definitions_are_refused_whatever_their_linkage() {
    assert!(refusal(UDIVTI3_CONST, LINUX).contains(&runtime_libcall("__udivti3")));
    assert!(refusal(FLOATTIDF, LINUX).contains(&runtime_libcall("__floattidf")));
    for name in [
        "__udivti3",
        "__divti3",
        "__umodti3",
        "__multi3",
        "__floattidf",
        "__fixdfti",
        "__addtf3",
        "__aarch64_cas4_acq",
        "fmod",
        "fmodf",
        "floor",
        "pow",
        "memset_pattern8",
        "malloc",
        "_Unwind_Resume",
    ] {
        for linkage in ["", "internal", "private", "weak"] {
            for target in [LINUX, DARWIN] {
                let src = format!("define {linkage} i64 @{name}(i64 %x) {{\n  ret i64 42\n}}\n");
                assert!(
                    refusal(&src, target).contains(&runtime_libcall(name)),
                    "{src}"
                );
            }
        }
        let src = format!("@{name} = global i64 1\n");
        assert!(
            refusal(&src, LINUX).contains(&runtime_libcall(name)),
            "{src}"
        );
    }
}

/// The first skeptic's `vsin_decl_wrong_call_ok`: a declaration whose type
/// contradicts its name, beside a call under the name its own type gives,
/// was admitted and ran (94, sin(1.25) * 100), where llc 22.1.2 renames the
/// declaration `@llvm.sin.v4f32` and rejects the call ("Intrinsic called
/// with incompatible signature").
const VSIN_DECL_WRONG: &str = "\
target triple = \"aarch64-unknown-linux-gnu\"
@x = global double 1.25
@y = global double 2.25
declare <4 x float> @llvm.sin.v2f64(<4 x float>)
define i32 @main() {
  %x = load double, ptr @x
  %y = load double, ptr @y
  %w0 = insertelement <2 x double> poison, double %x, i32 0
  %v = insertelement <2 x double> %w0, double %y, i32 1
  %r = call <2 x double> @llvm.sin.v2f64(<2 x double> %v)
  %e = extractelement <2 x double> %r, i32 0
  %m = fmul double %e, 1.0e2
  %i = fptosi double %m to i32
  ret i32 %i
}
";

#[test]
fn vector_intrinsic_declarations_are_read_only_under_their_types_name() {
    let reason = refusal(VSIN_DECL_WRONG, LINUX);
    assert!(
        reason.contains("declaration of `@llvm.sin.v2f64`")
            && reason.contains("names this one `@llvm.sin.v4f32`"),
        "{reason}"
    );
    for (src, needle) in [
        // A vector declaration under a scalar name, beside a scalar call
        // (llc rejects the call).
        (
            "declare <2 x double> @llvm.sin.f64(<2 x double>)\n\
             define double @f(double %x) {\n  %r = call double @llvm.sin.f64(double %x)\n  \
             ret double %r\n}\n",
            "names this one `@llvm.sin.v2f64`",
        ),
        (
            "declare <4 x i32> @llvm.abs.i32(<4 x i32>, i1)\n",
            "names this one `@llvm.abs.v4i32`",
        ),
        (
            "declare <4 x float> @llvm.fmuladd.v2f64(<4 x float>, <4 x float>, <4 x float>)\n",
            "names this one `@llvm.fmuladd.v4f32`",
        ),
        (
            "declare <2 x i64> @llvm.ctpop.v2i32(<2 x i64>)\n",
            "names this one `@llvm.ctpop.v2i64`",
        ),
        // A reduction is named by its vector operand.
        (
            "declare i32 @llvm.vector.reduce.add.v8i32(<4 x i32>)\n",
            "names this one `@llvm.vector.reduce.add.v4i32`",
        ),
        (
            "declare float @llvm.vector.reduce.fadd.v2f32(float, <4 x float>)\n",
            "names this one `@llvm.vector.reduce.fadd.v4f32`",
        ),
        // A declaration that agrees with its name, and a call whose type
        // does not (llc rejects the call).
        (
            "declare i32 @llvm.vector.reduce.add.v4i32(<4 x i32>)\n\
             define i32 @f() {\n  \
             %r = call i32 @llvm.vector.reduce.add.v4i32(<8 x i32> <i32 1, i32 2, i32 3, i32 4, \
             i32 5, i32 6, i32 7, i32 8>)\n  ret i32 %r\n}\n",
            "names this reduction `llvm.vector.reduce.add.v8i32`",
        ),
    ] {
        let reason = refusal(src, LINUX);
        assert!(reason.contains(needle), "{src}: {reason}");
    }
}

/// Declarations of every refused name, and definitions under names LLVM
/// lists in no library table llc reads (`strcmp`, `puts`, `abs`, ...),
/// are admitted, as are vector intrinsic declarations under the name LLVM
/// gives their types.
#[test]
fn ordinary_definitions_and_library_declarations_are_admitted() {
    for src in [
        "define i64 @strcmp(ptr %a, ptr %b) {\n  ret i64 0\n}\n",
        "define i32 @puts(ptr %s) {\n  ret i32 0\n}\n",
        "define i32 @abs(i32 %x) {\n  ret i32 %x\n}\n",
        "define internal i64 @my_udivti3(i64 %x) {\n  ret i64 %x\n}\n",
        "declare ptr @__strcpy_chk(ptr, ptr, i64)\n\
         define ptr @f(ptr %d, ptr %s) {\n  \
         %r = call ptr @__strcpy_chk(ptr %d, ptr %s, i64 -1)\n  ret ptr %r\n}\n",
        "declare double @ldexp(double, i32)\n\
         define double @f(double %x) {\n  %r = call double @ldexp(double %x, i32 3)\n  \
         ret double %r\n}\n",
        "declare double @exp10(double)\n\
         define double @f(double %x) {\n  %r = call double @exp10(double %x)\n  \
         ret double %r\n}\n",
        "@a = global i128 100\n\
         define i128 @f() {\n  %a = load i128, ptr @a\n  %q = udiv i128 %a, 3\n  \
         ret i128 %q\n}\n",
        "declare <2 x double> @llvm.sin.v2f64(<2 x double>)\n\
         define double @f(double %x, double %y) {\n  \
         %w = insertelement <2 x double> poison, double %x, i32 0\n  \
         %v = insertelement <2 x double> %w, double %y, i32 1\n  \
         %r = call <2 x double> @llvm.sin.v2f64(<2 x double> %v)\n  \
         %e = extractelement <2 x double> %r, i32 0\n  ret double %e\n}\n",
        "declare <4 x float> @llvm.fmuladd.v4f32(<4 x float>, <4 x float>, <4 x float>)\n",
        "declare i32 @llvm.vector.reduce.add.v4i32(<4 x i32>)\n\
         define i32 @f() {\n  \
         %r = call i32 @llvm.vector.reduce.add.v4i32(<4 x i32> <i32 1, i32 2, i32 3, i32 4>)\n  \
         ret i32 %r\n}\n",
        "declare float @llvm.vector.reduce.fadd.v4f32(float, <4 x float>)\n",
    ] {
        for target in [LINUX, DARWIN] {
            import_text_for_target(src, "t", target)
                .unwrap_or_else(|error| panic!("{target}\n{src}: {error}"));
        }
        import_text(src, "t").unwrap_or_else(|error| panic!("{src}: {error}"));
    }
}
