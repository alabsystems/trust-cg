// End-to-end coverage for the OPT-4 shared trust-ir-level inliner at the
// `translate_module_for_arch` seam inside `Compiler::compile`.
//
// The inliner's LIR-level transform is unit-tested in
// `trust_cg_opt::ir_inline`; this test drives a genuine MULTI-FUNCTION trust_ir
// module through the REAL `Compiler::compile` x86-64 path and asserts:
//   * at O2 the seam inlines both call sites of a pure scalar leaf callee
//     (`sq`) into the caller (`entry`) — observed via the compile trace — and
//     the inlined LIR passes every downstream x86 gate (ISel, carrier-hygiene,
//     regalloc validator) so `compile` returns Ok;
//   * at O0 the pass is skipped (0 sites), matching the gate.
//
// NOTE ON THE RUSTC BRIDGE: rustc partitions each function into its own codegen
// unit, so the bridge feeds `Compiler::compile` one function per module and this
// cross-function inliner stays dormant (but safe) there. This test exercises the
// whole-module path the inliner actually pays (aarch64/riscv direct pipelines +
// any whole-module frontend), which is why it builds the module directly.

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_codegen::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_ir::{FuncId, Ty};
use trust_ir_build::ModuleBuilder;

/// Build `sq(x) = x*x` (FuncId 0, a pure single-block scalar leaf) and
/// `entry(x) = sq(x) + sq(x)` (FuncId 1, two call sites).
fn two_function_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("ir_inline_seam");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);

    // sq(x) = x * x
    {
        let mut fb = mb.function("sq", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let r = fb.mul(Ty::I64, x, x);
        fb.ret(vec![r]);
        fb.build();
    }
    // entry(x) = sq(x) + sq(x)
    {
        let mut fb = mb.function("entry", ft);
        let blk = fb.create_block();
        let x = fb.add_block_param(blk, Ty::I64);
        fb.switch_to_block(blk);
        let a = fb.call(FuncId::new(0), vec![x]);
        let b = fb.call(FuncId::new(0), vec![x]);
        let s = fb.add(Ty::I64, a, b);
        fb.ret(vec![s]);
        fb.build();
    }
    mb.build()
}

fn compile_x86(opt_level: OptLevel) -> trust_cg_codegen::CompilationResult {
    let config = CompilerConfig {
        opt_level,
        target: Target::X86_64,
        trace_level: CompilerTraceLevel::Full,
        parallel: false,
        ..Default::default()
    };
    let compiler = Compiler::new(config);
    compiler
        .compile(&two_function_module())
        .expect("multi-function x86-64 compile should succeed")
}

/// Extract the "N" from the `ir_inline` trace entry's `"N sites / M rounds"`
/// detail, or `None` if the pass did not run / left no entry.
fn inlined_sites(result: &trust_cg_codegen::CompilationResult) -> Option<usize> {
    let trace = result.trace.as_ref()?;
    let entry = trace.entries.iter().find(|e| e.phase == "ir_inline")?;
    let detail = entry.detail.as_ref()?;
    detail
        .split_whitespace()
        .next()
        .and_then(|n| n.parse::<usize>().ok())
}

#[test]
fn seam_inlines_pure_scalar_leaf_at_o2() {
    let result = compile_x86(OptLevel::O2);
    // Both `sq(x)` call sites in `entry` are inlined by the shared seam, and the
    // resulting LIR passes the full x86 gate stack (compile returned Ok above).
    assert_eq!(
        inlined_sites(&result),
        Some(2),
        "the O2 seam must inline both call sites of the pure scalar leaf `sq`"
    );
    // The object must be a valid container in the HOST-NATIVE format (the
    // inlined code lowered + encoded). `Target::X86_64` with the default
    // target spec is OS-aware: ELF on Linux/BSD hosts, Mach-O on macOS, COFF
    // on Windows — asserting Mach-O magic unconditionally was macOS-assumption
    // test debt (2026-07-31 x86-Linux battery).
    let obj = &result.object_code;
    assert!(
        obj.len() >= 4,
        "inlined module object too small for a magic: {} bytes",
        obj.len()
    );
    match std::env::consts::OS {
        "linux" | "android" | "freebsd" | "netbsd" | "openbsd" | "dragonfly" => {
            assert_eq!(
                &obj[0..4],
                b"\x7FELF",
                "inlined module must still produce a valid ELF object on this host"
            );
        }
        "macos" => {
            assert_eq!(
                obj[0..4],
                0xFEED_FACFu32.to_le_bytes(),
                "inlined module must still produce a valid Mach-O object on macOS"
            );
        }
        other => panic!("no host-native x86-64 object-format expectation wired for OS {other}"),
    }
}

#[test]
fn seam_skips_inlining_at_o0() {
    let result = compile_x86(OptLevel::O0);
    // At O0 the pass is gated off, so either no `ir_inline` trace entry exists or
    // it reports zero sites.
    assert!(
        matches!(inlined_sites(&result), None | Some(0)),
        "the O0 gate must skip inlining"
    );
}
