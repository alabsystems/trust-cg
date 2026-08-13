#![cfg(feature = "driver")]

// Integration tests for `switch` import, covering the full path from
// a real clang -O0-shaped `.ll` file through the codegen pipeline to
// AArch64 Mach-O bytes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Part of #439 (WS2). Pins the importer's switch support end to end.
//
// These tests intentionally exercise three properties in isolation:
//
//  1. `switch_dispatch_import_to_trust_ir`: textual `switch` in the shape
//     clang -O0 emits (multi-line, `[` on the header line, `]` on its
//     own line) imports cleanly and the resulting trust_ir function has all
//     expected blocks terminated.
//
//  2. `switch_dispatch_full_pipeline_aarch64_o0`: the same IR compiles
//     all the way through `trust-cg-codegen` to a non-empty Mach-O object.
//     That's the "end-to-end" claim from issue #439's acceptance
//     criteria for WS2: programs Trust Codegen did not write itself flow
//     through the pipeline.
//
//  3. `switch_narrow_widths_round_trip`: i8/i16/i32/i64 selector widths
//     all import. The importer must not assume i32.

use std::fs;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_llvm_import::import_module;

/// A `switch`-centric program in the shape clang -O0 emits. `dispatch`
/// has four cases plus a default; every arm returns a distinct value
/// so nothing can be accidentally constant-folded by a clever front
/// end. The bodies are kept to `ret` because the importer's switch
/// support is the feature under test, not call/alloca.
///
/// NOTE: The multi-line `[ ... ]` layout (case list on its own lines,
/// `]` on a separate physical line) is exactly what clang emits — the
/// parser must handle that, not just the LangRef single-line form.
const DISPATCH_LL: &str = "\
target triple = \"arm64-apple-macosx14.0.0\"

define i32 @dispatch(i32 %sel) {
entry:
  switch i32 %sel, label %def [
    i32 0, label %c0
    i32 1, label %c1
    i32 2, label %c2
    i32 3, label %c3
  ]
c0:
  ret i32 10
c1:
  ret i32 11
c2:
  ret i32 12
c3:
  ret i32 13
def:
  ret i32 99
}
";

fn write_ll(contents: &str, name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("trust-cg-switch-e2e-{}", std::process::id()));
    fs::create_dir_all(&dir).expect("create tmp dir");
    let path = dir.join(format!("{name}.ll"));
    fs::write(&path, contents).expect("write .ll");
    path
}

#[test]
fn switch_dispatch_import_to_trust_ir() {
    let path = write_ll(DISPATCH_LL, "dispatch");
    let module = import_module(&path).expect("dispatch.ll imports");

    let func = module
        .functions
        .iter()
        .find(|f| f.name == "dispatch")
        .expect("dispatch function exists");

    // entry + c0 + c1 + c2 + c3 + def = 6 blocks. Importer may insert
    // additional synthetic blocks (e.g. for ABI lowering) but must not
    // drop any of the user-visible ones.
    assert!(
        func.blocks.len() >= 6,
        "expected >= 6 blocks, got {}",
        func.blocks.len()
    );

    // Every block must be terminated. The importer must not emit a
    // block whose last instruction is not a terminator — that would
    // be a silent bug that only manifests downstream.
    for b in &func.blocks {
        assert!(!b.body.is_empty(), "block has no instructions at all");
        let last = b.body.last().unwrap();
        let is_term = matches!(
            last.inst,
            trust_ir::inst::Inst::Return { .. }
                | trust_ir::inst::Inst::Br { .. }
                | trust_ir::inst::Inst::CondBr { .. }
                | trust_ir::inst::Inst::Switch { .. }
                | trust_ir::inst::Inst::Unreachable
        );
        assert!(
            is_term,
            "block terminator is not a terminator inst: {:?}",
            last.inst
        );
    }

    // Exactly one Inst::Switch, and it has 4 cases.
    let switches: Vec<_> = func
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .filter_map(|i| match &i.inst {
            trust_ir::inst::Inst::Switch { cases, .. } => Some(cases.len()),
            _ => None,
        })
        .collect();
    assert_eq!(
        switches,
        vec![4],
        "expected one switch with 4 cases, got {:?}",
        switches
    );
}

#[test]
fn switch_dispatch_full_pipeline_aarch64_o0() {
    let path = write_ll(DISPATCH_LL, "dispatch-pipeline");
    let module = import_module(&path).expect("dispatch.ll imports");

    let cfg = CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::Aarch64,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        panic_unwind: false,
    };
    let compiler = Compiler::new(cfg);
    let result = compiler.compile(&module).expect("codegen succeeds");

    // A non-trivial Mach-O object must come out. The exact byte count
    // varies with linker versions and section alignment; we just want
    // to assert "not empty" and "has a plausible object-sized payload"
    // so a silent regression that emits 0 bytes is caught.
    assert!(
        result.object_code.len() > 64,
        "object is suspiciously small: {} bytes",
        result.object_code.len()
    );
}

/// A `switch` that routes two case values to the SAME target label, whose
/// target carries a phi. This is the richards_benchmark shape: LLVM lists one
/// phi entry per parallel edge (`[ ptr null, %entry ], [ ptr null, %entry ]`),
/// which must be collapsed to one branch-arg per case. Before the dedup fix the
/// adapter rejected this with "branch-arg count (2) does not match target
/// params (1)"; this test locks in that the whole pipeline now accepts it.
const DUP_EDGE_LL: &str = "\
target triple = \"arm64-apple-macosx14.0.0\"

define i32 @dup(i32 %sel, i32 %a) {
entry:
  switch i32 %sel, label %def [
    i32 0, label %merge
    i32 1, label %merge
    i32 2, label %merge
  ]
merge:
  %v = phi i32 [ %a, %entry ], [ %a, %entry ], [ %a, %entry ]
  ret i32 %v
def:
  ret i32 99
}
";

#[test]
fn switch_parallel_edges_to_phi_target_full_pipeline_aarch64() {
    let path = write_ll(DUP_EDGE_LL, "dup-edge-pipeline");
    let module = import_module(&path).expect("dup-edge switch/phi imports");

    let cfg = CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::Aarch64,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        panic_unwind: false,
    };
    let compiler = Compiler::new(cfg);
    let result = compiler
        .compile(&module)
        .expect("parallel-edge switch/phi lowers through the adapter to codegen");
    assert!(
        result.object_code.len() > 64,
        "object is suspiciously small: {} bytes",
        result.object_code.len()
    );
}

#[test]
fn switch_narrow_widths_round_trip() {
    // Every legal selector width must import. Bodies are trivial so
    // only the switch parse path is under test. Using i64 and i8 in
    // addition to i32 catches any accidental hard-coded width.
    let cases = [
        ("i1", "i1", "1"),
        ("i8", "i8", "7"),
        ("i16", "i16", "300"),
        ("i32", "i32", "42"),
        ("i64", "i64", "9999999999"),
    ];
    for (ty, case_ty, case_val) in cases {
        let ll = format!(
            "target triple = \"arm64-apple-macosx14.0.0\"\n\
             define {ty} @f({ty} %s) {{\n\
             entry:\n  switch {ty} %s, label %d [ {case_ty} {case_val}, label %c ]\n\
             c:\n  ret {ty} 1\n\
             d:\n  ret {ty} 0\n\
             }}\n"
        );
        let path = write_ll(&ll, &format!("narrow-{ty}"));
        import_module(&path).unwrap_or_else(|e| {
            panic!("selector width {ty} / case {case_ty} {case_val} failed: {e:?}")
        });
    }
}
