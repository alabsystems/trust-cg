// trust-cg-llvm-import / tests/target_cpu_names.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// L02-P15 (decision record LD-95, which corrects
// LD-04's premise): a `"target-cpu"` or `"tune-cpu"` is read only when it
// names a processor LLVM 22 defines for the compile target's architecture.
// llc 22 looks the name up exactly, and for a name it does not define it
// sets none of a processor's features: on AArch64 it then builds the
// function without `fp-armv8` or `neon`, with the soft-float calling
// convention (a `double` passed in `x0`), where the import builds the
// hard-float one. The second closure audit of L02-P15 (2026-10-23) found
// every name but `thunderx3t110` admitted. Every test here uses the public
// API only, so it runs against an importer without the rule. The llc
// differential over named processors is `symbol_linkage_elf`'s
// `imported_named_processors_run_like_llc`.

use std::collections::BTreeSet;

use serde_json::Value;
use trust_cg_llvm_import::{Error, import_text, import_text_for_target};

const LINUX: &str = "aarch64-unknown-linux-gnu";

/// The refusal of `thunderx3t110`, whose tuning implies `strict-align`
/// (LD-04), which comes before the name is looked up.
const MODE: &str = "processor implies the target feature `strict-align`";
const DARWIN: &str = "aarch64-apple-darwin";

/// The processor tables of LLVM 22.1.2 (`llvm-tblgen --dump-json`, written
/// by `scripts/extract_llvm_subtarget_features.py`).
const LLVM22_TABLES: &str = include_str!("fixtures/llvm22_subtarget_features.json");

/// The refusal of `src` compiled for `target` (`None`: imported with no
/// compile target, so the module's own `target triple` is read).
fn refusal(src: &str, target: Option<&str>) -> String {
    let result = match target {
        Some(target) => import_text_for_target(src, "t", target),
        None => import_text(src, "t"),
    };
    match result {
        Err(Error::Unsupported(reason)) => reason,
        other => panic!("expected a named refusal for {target:?}\n{src}\ngot {other:?}"),
    }
}

fn admitted(src: &str, target: Option<&str>) {
    let result = match target {
        Some(target) => import_text_for_target(src, "t", target),
        None => import_text(src, "t"),
    };
    if let Err(error) = result {
        panic!("expected {target:?} to admit\n{src}\ngot {error}");
    }
}

/// The processor and alias names of LLVM 22.1.2's `target` table.
fn llvm_names(target: &str) -> BTreeSet<String> {
    let tables: Value = serde_json::from_str(LLVM22_TABLES).expect("the extract");
    let target = &tables["targets"][target];
    ["processors", "aliases"]
        .iter()
        .flat_map(|section| target[section].as_object().expect(section).keys().cloned())
        .collect()
}

/// The attribute `"key"="value"` (`value` as spelled in LLVM text) where a
/// function attribute is read: a definition's own, a group a definition
/// uses, a declaration's own and a group a call uses; each with the subject
/// its refusal names.
fn placements(key: &str, value: &str) -> [(String, &'static str); 4] {
    [
        (
            format!("define i64 @f() \"{key}\"=\"{value}\" {{\n  ret i64 5\n}}\n"),
            "`@f`: attribute",
        ),
        (
            format!(
                "define i64 @f() #0 {{\n  ret i64 5\n}}\n\
                 attributes #0 = {{ nounwind \"{key}\"=\"{value}\" }}\n"
            ),
            "`@f`: attribute group `#0`",
        ),
        (
            format!("declare i64 @g() \"{key}\"=\"{value}\"\n"),
            "`@g`: attribute",
        ),
        (
            format!(
                "declare i64 @g()\ndefine i64 @f() {{\n  %r = call i64 @g() #1\n  \
                 ret i64 %r\n}}\nattributes #1 = {{ \"{key}\"=\"{value}\" }}\n"
            ),
            "call to `@g`: attribute group `#1`",
        ),
    ]
}

/// The audit's spellings of names LLVM 22 does not define for AArch64, as
/// written in LLVM text: llc 22.1.2 built each one soft-float. `\00` and
/// `\09` are LLVM's escapes of NUL and tab.
const UNDEFINED_ON_AARCH64: [&str; 20] = [
    "native",
    "armv8-a",
    "Cortex-A57",
    "CORTEX-A72",
    "Generic",
    "GENERIC",
    "generic ",
    " generic",
    "generic\\00",
    "generic\\09",
    "apple-m1 ",
    "cortex-a72x",
    "neoverse_v2",
    "help",
    "nosuchcpu",
    "x86-64",
    "znver4",
    "sifive-u74",
    "generic-rv64",
    "\\00",
];

/// A name LLVM 22 does not define for AArch64 is refused by name, as
/// either key, wherever a function attribute is read, for AArch64 Linux and
/// Apple. The importer used to read every name but `thunderx3t110`.
#[test]
fn undefined_processor_names_are_refused_by_name() {
    let needle = "is not one LLVM 22 defines for the compile target's architecture, AArch64";
    for value in UNDEFINED_ON_AARCH64 {
        for key in ["target-cpu", "tune-cpu"] {
            for (src, subject) in placements(key, value) {
                for target in [LINUX, DARWIN] {
                    let reason = refusal(&src, Some(target));
                    assert!(
                        reason.contains(needle) && reason.contains(subject),
                        "{target} {src}: {reason}"
                    );
                }
            }
        }
    }
}

/// The closure audit's reproducers: `main` prints a `double` through
/// `printf` under `"target-cpu"="nosuchcpu"` (llc passed it in `x0`,
/// printf read `d0`), and a `double` argument of an internal function under
/// `"target-cpu"="native"` (llc's callee read `x0`).
#[test]
fn the_closure_audit_reproducers_are_refused() {
    let printf = "target triple = \"aarch64-unknown-linux-gnu\"\n\
        @fmt = private unnamed_addr constant [6 x i8] c\"%.3f\\0A\\00\", align 1\n\
        @g = global double 2.5, align 8\n\
        declare i32 @printf(ptr, ...)\n\
        define i32 @main() #0 {\n\
        entry:\n  %v = load volatile double, ptr @g, align 8\n\
        \x20 %r = call i32 (ptr, ...) @printf(ptr @fmt, double %v)\n  ret i32 0\n}\n\
        attributes #0 = { nounwind \"target-cpu\"=\"nosuchcpu\" }\n";
    let native = "target triple = \"aarch64-unknown-linux-gnu\"\n\
        @.fmt = private unnamed_addr constant [6 x i8] c\"%lld\\0A\\00\"\n\
        declare i32 @printf(ptr, ...)\n\
        define internal i64 @callee(double %x, i64 %k) #0 {\n\
        \x20 %b = bitcast double %x to i64\n  %r = add i64 %b, %k\n  ret i64 %r\n}\n\
        define i32 @main() {\n  %v = call i64 @callee(double 2.5, i64 7)\n\
        \x20 %pr = call i32 (ptr, ...) @printf(ptr @.fmt, i64 %v)\n  ret i32 0\n}\n\
        attributes #0 = { noinline \"target-cpu\"=\"native\" }\n";
    for (src, name, subject) in [
        (printf, "\"nosuchcpu\"", "`@main`: attribute group `#0`"),
        (native, "\"native\"", "`@callee`: attribute group `#0`"),
    ] {
        for target in [None, Some(LINUX), Some(DARWIN)] {
            let reason = refusal(src, target);
            assert!(
                reason.contains(&format!("processor {name} is not one LLVM 22 defines"))
                    && reason.contains(subject),
                "{target:?}: {reason}"
            );
        }
        // The same module under a name LLVM 22 defines is admitted.
        let named = src.replace(name, "\"cortex-a72\"");
        for target in [None, Some(LINUX)] {
            admitted(&named, target);
        }
    }
}

/// Every name LLVM 22.1.2's AArch64 table defines (its 82 processors and
/// 17 aliases) is read as either key for AArch64 Linux and Apple, inline
/// and through a group, but `thunderx3t110`, whose tuning implies
/// `strict-align` (LD-04). So are the empty name (`generic` to llc) and a
/// key without a value, and a name spelled with LLVM's escapes
/// (`cortex\2Da72` is `cortex-a72`).
#[test]
fn every_llvm22_aarch64_processor_name_is_read() {
    let names = llvm_names("AArch64");
    assert_eq!(names.len(), 99);
    let mut refused = Vec::new();
    for name in &names {
        for key in ["target-cpu", "tune-cpu"] {
            for (src, subject) in placements(key, name) {
                for target in [LINUX, DARWIN] {
                    if name == "thunderx3t110" {
                        let reason = refusal(&src, Some(target));
                        assert!(
                            reason.contains(MODE) && reason.contains(subject),
                            "{target} {src}: {reason}"
                        );
                        refused.push(name.as_str());
                    } else {
                        admitted(&src, Some(target));
                    }
                }
            }
        }
    }
    refused.dedup();
    assert_eq!(refused, ["thunderx3t110"]);
    for value in ["", "cortex\\2Da72", "apple\\2Dm1"] {
        for key in ["target-cpu", "tune-cpu"] {
            for (src, _) in placements(key, value) {
                admitted(&src, Some(LINUX));
            }
        }
    }
    admitted(
        "define i64 @f() \"target-cpu\" {\n  ret i64 5\n}\n",
        Some(LINUX),
    );
    // The module's own AArch64 triple is read as the compile target.
    for triple in ["arm64-apple-macosx15.0.0", "aarch64-unknown-linux-gnu"] {
        admitted(
            &format!(
                "target triple = \"{triple}\"\n\
                 define i64 @f() \"target-cpu\"=\"apple-m1\" {{\n  ret i64 5\n}}\n"
            ),
            None,
        );
    }
}

/// A name is read against the compile target's architecture: RISC-V's and
/// x86's names on those targets (not AArch64's), with no target known only
/// a name all three define (`generic`), and on any other architecture none
/// (`arm64e`, `aarch64_be` and `aarch64_32` among them, which this
/// importer does not read as AArch64). The caller's target takes the place
/// of the module's `target triple`, as llc's `-mtriple` does.
#[test]
fn processor_names_are_read_for_the_compile_targets_architecture() {
    let aarch64 = llvm_names("AArch64");
    let riscv = llvm_names("RISCV");
    let x86 = llvm_names("X86");
    let every: BTreeSet<&String> = aarch64.iter().chain(&riscv).chain(&x86).collect();
    let define = |key: &str, name: &str| {
        format!("define i64 @f() \"{key}\"=\"{name}\" {{\n  ret i64 5\n}}\n")
    };
    for (target, defined, architecture) in [
        ("riscv64-unknown-linux-gnu", &riscv, "RISC-V"),
        ("x86_64-unknown-linux-gnu", &x86, "x86"),
    ] {
        for name in &every {
            for key in ["target-cpu", "tune-cpu"] {
                let src = define(key, name);
                if defined.contains(*name) {
                    admitted(&src, Some(target));
                } else {
                    let reason = refusal(&src, Some(target));
                    let why = if name.as_str() == "thunderx3t110" {
                        MODE.to_string()
                    } else {
                        format!("defines for the compile target's architecture, {architecture}")
                    };
                    assert!(reason.contains(&why), "{target} {src}: {reason}");
                }
            }
        }
    }
    for name in &every {
        for key in ["target-cpu", "tune-cpu"] {
            let src = define(key, name);
            if name.as_str() == "generic" {
                admitted(&src, None);
            } else {
                let reason = refusal(&src, None);
                let why = if name.as_str() == "thunderx3t110" {
                    MODE
                } else {
                    "a module with no known target may be compiled for"
                };
                assert!(reason.contains(why), "{src}: {reason}");
            }
        }
    }
    for target in [
        "arm64e-apple-ios",
        "aarch64_be-unknown-linux-gnu",
        "aarch64_32-unknown-linux-gnu",
        "wasm32-unknown-unknown",
    ] {
        for name in ["generic", "", "cortex-a72"] {
            let reason = refusal(&define("target-cpu", name), Some(target));
            assert!(
                reason.contains("whose processor table this importer does not read"),
                "{target} {name:?}: {reason}"
            );
        }
    }
    let x86_module = "target triple = \"x86_64-unknown-linux-gnu\"\n\
        define i64 @f() \"target-cpu\"=\"x86-64\" {\n  ret i64 5\n}\n";
    admitted(x86_module, None);
    let reason = refusal(x86_module, Some(LINUX));
    assert!(reason.contains("AArch64"), "{reason}");
}
