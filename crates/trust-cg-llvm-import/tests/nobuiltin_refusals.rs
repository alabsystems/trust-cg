// trust-cg-llvm-import / tests/nobuiltin_refusals.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// L02-P15 (decision record LD-97): the keyword
// attribute `nobuiltin` and the string attributes "no-builtins" and
// "no-builtin-<name>" are refused by name wherever the importer reads a
// function attribute (a definition's or declaration's own, a call's own, and
// a group one of them uses). llc 22 keeps such a call as a call of the named
// function; this importer's backend reads a call of a declared `memcpy`,
// `memmove` or `memset` with a constant count by its name and may expand it
// inline, so a freestanding module's own `memcpy` or `memset` was not
// called where llc's object calls it. The third closure audit of L02-P15 (2026-10-23, at 9a237122b)
// ran the reproducers below otherwise than llc in 24 of 24 configurations.
// The same file pins the refusal of an instruction that follows a
// terminator without a label (LLVM starts an implicitly numbered block
// there), which the importer used to merge into the block before it and
// leave to the IR validator. Every test here uses the public API only, so
// it runs against an importer without the rules.

use trust_cg_llvm_import::{Error, import_text, import_text_for_target};

const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";

/// The words every refusal of the builtin restrictions carries.
const NOBUILTIN: &str = "this importer's backend reads a call of a library function by its name";

/// The words the refusal of an unlabelled block carries.
const UNLABELLED: &str = "follows its block's terminator without a label";

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

/// The audit's `r1_nobuiltin_memcpy`: `main` (under "no-builtins") copies 8
/// bytes with `memcpy` and 4 with `memmove`, each call `nobuiltin`, and
/// prints how often the program's own `memcpy` and `memmove` (another
/// object of the link) ran. llc's build printed `memcpy=1`, the import's
/// `memcpy=0` at O0-O3 through GNU ld, gold and LLD, static and PIE.
const R1_NOBUILTIN_MEMCPY: &str = "\
target datalayout = \"e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32\"
target triple = \"aarch64-unknown-linux-gnu\"

@fmt = private constant [25 x i8] c\"memcpy=%d memmove=%d %s\\0A\\00\"
@src = global [16 x i8] c\"abcdefghijklmno\\00\"
@dst = global [16 x i8] zeroinitializer
@hits_memcpy = external global i32
@hits_memmove = external global i32

declare i32 @printf(ptr, ...)
declare ptr @memcpy(ptr, ptr, i64)
declare ptr @memmove(ptr, ptr, i64)

define i32 @main() #0 {
  %a = call ptr @memcpy(ptr @dst, ptr @src, i64 8) #1
  %b = call ptr @memmove(ptr @dst, ptr @src, i64 4) #1
  %h1 = load i32, ptr @hits_memcpy
  %h2 = load i32, ptr @hits_memmove
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i32 %h1, i32 %h2, ptr @dst)
  ret i32 0
}

attributes #0 = { \"no-builtins\" }
attributes #1 = { nobuiltin }
";

/// The audit's `r5_memset`: a 16-byte zero fill under `nobuiltin` and
/// "no-builtin-memset"; llc's build printed `memset=1`, the import's
/// `memset=0`.
const R5_MEMSET: &str = "\
target datalayout = \"e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32\"
target triple = \"aarch64-unknown-linux-gnu\"

@fmt = private constant [12 x i8] c\"memset=%d \\0A\\00\"
@dst = global [16 x i8] c\"abcdefghijklmno\\00\"
@hits_memset = external global i32

declare i32 @printf(ptr, ...)
declare ptr @memset(ptr, i32, i64)

define i32 @main() \"no-builtin-memset\" {
  %a = call ptr @memset(ptr @dst, i32 0, i64 16) nobuiltin
  %h = load i32, ptr @hits_memset
  %p = call i32 (ptr, ...) @printf(ptr @fmt, i32 %h)
  ret i32 0
}
";

/// The audit's `r2_variants`, one restriction per function: (a) a
/// `nobuiltin` call, (b) "no-builtins" on the caller, (c)
/// "no-builtin-memcpy" on the caller, (d) a `nobuiltin` `memmove`.
fn r2_variant(caller_attributes: &str, call_attributes: &str, callee: &str) -> String {
    format!(
        "target triple = \"aarch64-unknown-linux-gnu\"\n\
         @src = global [16 x i8] c\"abcdefghijklmno\\00\"\n\
         @dst = global [16 x i8] zeroinitializer\n\
         declare ptr @{callee}(ptr, ptr, i64)\n\
         define void @a() noinline {caller_attributes} {{\n  \
         %r = call ptr @{callee}(ptr @dst, ptr @src, i64 8) {call_attributes}\n  \
         ret void\n}}\n\
         define i32 @main() {{\n  call void @a()\n  ret i32 0\n}}\n"
    )
}

/// The three restrictions as LLVM text spells them, LLVM's escapes
/// included (`\2D` is `-`, `\6D` is `m`).
const SPELLINGS: [&str; 9] = [
    "nobuiltin",
    "\"no-builtins\"",
    "\"no-builtins\"=\"true\"",
    "\"no-builtins\"=\"false\"",
    "\"no-builtin-memcpy\"",
    "\"no-builtin-memset\"",
    "\"no-builtin-printf\"",
    "\"no\\2Dbuiltins\"",
    "\"no-builtin-\\6Demcpy\"",
];

/// `attribute` where a function attribute is read: a definition's own, a
/// group a definition uses, a declaration's own, a group a declaration
/// uses, a call's own and a group a call uses; each with the subject its
/// refusal names.
fn placements(attribute: &str) -> [(String, &'static str); 6] {
    let call = |attributes: &str, group: &str| {
        format!(
            "declare ptr @memcpy(ptr, ptr, i64)\n\
             define void @f(ptr %d, ptr %s) {{\n  \
             %r = call ptr @memcpy(ptr %d, ptr %s, i64 8) {attributes}\n  ret void\n}}\n{group}"
        )
    };
    [
        (
            format!("define i64 @f() {attribute} {{\n  ret i64 5\n}}\n"),
            "`@f`: attribute",
        ),
        (
            format!(
                "define i64 @f() #0 {{\n  ret i64 5\n}}\n\
                 attributes #0 = {{ nounwind {attribute} }}\n"
            ),
            "`@f`: attribute group `#0`",
        ),
        (
            format!("declare ptr @memcpy(ptr, ptr, i64) {attribute}\n"),
            "`@memcpy`: attribute",
        ),
        (
            format!(
                "declare ptr @memcpy(ptr, ptr, i64) #0\n\
                 attributes #0 = {{ {attribute} }}\n"
            ),
            "`@memcpy`: attribute group `#0`",
        ),
        (call(attribute, ""), "call to `@memcpy`: attribute"),
        (
            call("#1", &format!("attributes #1 = {{ {attribute} }}\n")),
            "call to `@memcpy`: attribute group `#1`",
        ),
    ]
}

/// The closure audit's reproducers are refused by name, with the module's
/// own triple and for AArch64 Linux.
#[test]
fn the_closure_audit_reproducers_are_refused() {
    let variants = [
        r2_variant("", "nobuiltin", "memcpy"),
        r2_variant("\"no-builtins\"", "", "memcpy"),
        r2_variant("\"no-builtin-memcpy\"", "", "memcpy"),
        r2_variant("", "nobuiltin", "memmove"),
    ];
    let sources = [R1_NOBUILTIN_MEMCPY, R5_MEMSET]
        .into_iter()
        .chain(variants.iter().map(String::as_str));
    for src in sources {
        for target in [None, Some(LINUX)] {
            let reason = refusal(src, target);
            assert!(reason.contains(NOBUILTIN), "{target:?}\n{src}\n{reason}");
        }
    }
}

/// Each spelling is refused by name in every placement, for AArch64 Linux
/// and Apple, and with no compile target.
#[test]
fn every_builtin_restriction_is_refused_wherever_an_attribute_is_read() {
    for attribute in SPELLINGS {
        for (src, subject) in placements(attribute) {
            for target in [None, Some(LINUX), Some(DARWIN)] {
                let reason = refusal(&src, target);
                assert!(
                    reason.contains(NOBUILTIN) && reason.contains(subject),
                    "{target:?} {attribute}\n{src}\n{reason}"
                );
            }
        }
    }
}

/// The same programs without the restrictions are admitted: a plain call
/// of a declared `memcpy`, `memmove` or `memset` (LLVM's LangRef lets it be
/// read as the C library function), the `builtin` keyword, and a string
/// attribute that only starts like one (`"no-builtinsx"` is refused as an
/// attribute the importer does not read, not as a restriction).
#[test]
fn the_programs_without_the_restrictions_are_admitted() {
    let r1 = R1_NOBUILTIN_MEMCPY
        .replace(
            "attributes #0 = { \"no-builtins\" }",
            "attributes #0 = { nounwind }",
        )
        .replace(
            "attributes #1 = { nobuiltin }",
            "attributes #1 = { builtin }",
        );
    let r5 = R5_MEMSET
        .replace(" \"no-builtin-memset\"", "")
        .replace(" nobuiltin", "");
    for src in [r1.as_str(), r5.as_str(), &r2_variant("", "", "memcpy")] {
        for target in [None, Some(LINUX)] {
            admitted(src, target);
        }
    }
    let reason = refusal(
        "define i64 @f() \"no-builtinsx\" {\n  ret i64 5\n}\n",
        Some(LINUX),
    );
    assert!(
        reason.contains("not a string attribute this importer reads")
            && !reason.contains(NOBUILTIN),
        "{reason}"
    );
}

/// LLVM starts a new basic block at an instruction that follows a
/// terminator, numbered like an unnamed value when it has no label (here
/// `%0` is the entry block and `%1` the block after `br`). The importer
/// read blocks only from their labels and merged such an instruction into
/// the block before it, where the IR validator refused the module for an
/// instruction after a terminator; it is now refused by name. A labelled
/// block in the same place is read.
#[test]
fn an_unlabelled_block_after_a_terminator_is_refused_by_name() {
    for (src, line) in [
        (
            "define i64 @f() {\n  ret i64 1\n  ret i64 2\n}\n",
            "`ret i64 2`",
        ),
        (
            "define i64 @f() {\n  br label %1\n  ret i64 2\n}\n",
            "`ret i64 2`",
        ),
        (
            "define i64 @f(i64 %x) {\nentry:\n  br label %next\n  %y = add i64 %x, 1\n  \
             ret i64 %y\nnext:\n  ret i64 %x\n}\n",
            "`%y = add i64 %x, 1`",
        ),
        (
            "define i64 @f(i64 %x) {\nentry:\n  ret i64 %x\n  switch i64 %x, label %d [\n    \
             i64 0, label %d\n  ]\nd:\n  ret i64 0\n}\n",
            "`switch i64 %x, label %d [",
        ),
    ] {
        for target in [None, Some(LINUX)] {
            let reason = refusal(src, target);
            assert!(
                reason.contains("`@f`") && reason.contains(UNLABELLED) && reason.contains(line),
                "{target:?}\n{src}\n{reason}"
            );
        }
    }
    admitted(
        "define i64 @f(i64 %x) {\nentry:\n  br label %next\nmid:\n  %y = add i64 %x, 1\n  \
         ret i64 %y\nnext:\n  ret i64 %x\n}\n",
        Some(LINUX),
    );
    // A `uselistorder` directive, which LLVM reads after the last block,
    // starts no block: it keeps the refusal its own reader gives.
    let reason = refusal(
        "define i64 @f(i64 %x) {\n  %a = add i64 %x, 2\n  %b = add i64 %a, 1\n  \
         %c = add i64 %a, 2\n  %d = add i64 %b, %c\n  ret i64 %d\n  \
         uselistorder i64 %a, { 1, 0 }\n}\n",
        Some(LINUX),
    );
    assert!(
        reason.contains("opcode `uselistorder`") && !reason.contains(UNLABELLED),
        "{reason}"
    );
}
