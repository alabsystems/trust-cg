// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! OD-225: a compile that claims proofs runs neither shared pre-ISel LIR pass.
//!
//! At O1 and above two target-independent LIR passes run between the
//! adapter and instruction selection: the module inliner
//! (`trust_cg_opt::ir_inline`) and unsigned-range simplification
//! (`trust_cg_opt::lir_unsigned_range`). Every per-function proof (the x86-64
//! source-bound body theorem, the per-instruction lowering proofs, the JIT
//! certificates) takes the LIR handed to instruction selection as its source,
//! and neither pass is validated: the inliner has a structural self-check
//! (opcode multiset, CFG shape, fresh values) that a swapped argument mapping
//! passes, and the range pass deletes `Assert`s and folds branches from its
//! own interval facts with no check at all. So a compile that claims proofs
//! (`emit_proofs` on the AOT seam; `emit_proofs` or a verifying validation
//! mode on the JIT step; `InlineOnlyAdmission::Withhold` on a raw lane's
//! step) runs neither: its proofs' source is exactly the adapter's LIR. A
//! compile that claims nothing keeps both passes.
//!
//! The fixtures are the two rewrites the ruling names: a call of a pure leaf
//! the inliner splices, and an `Assume` (an LIR `Assert`) of `(x & 63) < 64`
//! the range pass deletes. Each case is a before/after pair: under a proof
//! claim the LIR keeps the call and the `Assert`; without one both passes
//! still rewrite it.
//!
//! The AOT and JIT compiles below need an independently checked proof to
//! promote. Where the replay tools are absent their proof-claiming leg can
//! only be refused, and it says so; the raw-lane step is checked on every
//! host.

use std::collections::HashMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_codegen::{
    CompilationResult, CompileError, Compiler, CompilerConfig, CompilerTraceLevel,
    InlineOnlyAdmission, JitExternBindings, prepare_jit_lir_module,
};
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{
    CodegenLicensePolicy, Function, GuardCarrierArch, ProofContext, TlsDialect,
    prepare_module_for_lir,
};
use trust_ir::{BinOp, FuncId, ICmpOp, Module, OverflowOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEAF: &str = "tcg_od225_mask";
const ENTRY: &str = "tcg_od225_entry";
const X86_TRIPLE: &str = "x86_64-apple-darwin";
const AARCH64_TRIPLE: &str = "aarch64-apple-darwin";

/// `mask(x) = x & 63`, a pure one-block scalar leaf (the inliner's
/// straight-line tier), and `entry(x) = { m = mask(x); assume(m < 64); m + 1 }`.
/// Inlining exposes `m`'s interval `[0, 63]`, after which the range pass folds
/// the compare and deletes the `Assert` the `assume` lowers to.
fn inline_and_assert_module() -> Module {
    let mut mb = ModuleBuilder::new("od225_inline_and_assert");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    {
        let mut fb = mb.function(LEAF, ft);
        let block = fb.create_block();
        let x = fb.add_block_param(block, Ty::I64);
        fb.switch_to_block(block);
        let mask = fb.iconst(Ty::I64, 63);
        let m = fb.binop(BinOp::And, Ty::I64, x, mask);
        fb.ret(vec![m]);
        fb.build();
    }
    {
        let mut fb = mb.function(ENTRY, ft);
        let block = fb.create_block();
        let x = fb.add_block_param(block, Ty::I64);
        fb.switch_to_block(block);
        let m = fb.call(FuncId::new(0), vec![x]);
        let bound = fb.iconst(Ty::I64, 64);
        let in_range = fb.icmp(ICmpOp::Ult, Ty::I64, m, bound);
        fb.assume(in_range);
        let one = fb.iconst(Ty::I64, 1);
        let r = fb.add(Ty::I64, m, one);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `sq(x) = x * x` and `entry(x) = sq(x) + sq(x)`: two calls of a pure leaf
/// and nothing the range pass rewrites (the inliner's AOT seam fixture,
/// `x86_64_ir_inline_seam.rs`).
fn inline_only_module() -> Module {
    let mut mb = ModuleBuilder::new("od225_inline");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    {
        let mut fb = mb.function(LEAF, ft);
        let block = fb.create_block();
        let x = fb.add_block_param(block, Ty::I64);
        fb.switch_to_block(block);
        let r = fb.mul(Ty::I64, x, x);
        fb.ret(vec![r]);
        fb.build();
    }
    {
        let mut fb = mb.function(ENTRY, ft);
        let block = fb.create_block();
        let x = fb.add_block_param(block, Ty::I64);
        fb.switch_to_block(block);
        let a = fb.call(FuncId::new(0), vec![x]);
        let b = fb.call(FuncId::new(0), vec![x]);
        let s = fb.add(Ty::I64, a, b);
        fb.ret(vec![s]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `bounded(x) = { m = x & 63; assume(m < 64); m }`: one function, nothing to
/// inline, an `Assert` the AOT seam's whole-module range pass deletes.
fn assert_only_module() -> Module {
    let mut mb = ModuleBuilder::new("od225_assert");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, ft);
    let block = fb.create_block();
    let x = fb.add_block_param(block, Ty::I64);
    fb.switch_to_block(block);
    let mask = fb.iconst(Ty::I64, 63);
    let m = fb.binop(BinOp::And, Ty::I64, x, mask);
    let bound = fb.iconst(Ty::I64, 64);
    let in_range = fb.icmp(ICmpOp::Ult, Ty::I64, m, bound);
    fb.assume(in_range);
    fb.ret(vec![m]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `checked(a, b) = { (s, o) = (a & 0xffff) +ovf (b & 0xffff); if o { trap }
/// else { s } }`: a checked add whose operands' intervals exclude overflow, so
/// the range pass rewrites it to a plain add and folds the trap branch away.
/// Both forms are inside the x86-64 body theorem's lane (slices 6 and 10).
fn checked_add_module() -> Module {
    let mut mb = ModuleBuilder::new("od225_checked_add");
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ft);
    let block = fb.create_block();
    let trap = fb.create_block();
    let done = fb.create_block();
    let a = fb.add_block_param(block, Ty::U64);
    let b = fb.add_block_param(block, Ty::U64);
    fb.switch_to_block(block);
    let mask = fb.iconst(Ty::U64, 0xffff);
    let ma = fb.binop(BinOp::And, Ty::U64, a, mask);
    let mb_ = fb.binop(BinOp::And, Ty::U64, b, mask);
    let (sum, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, ma, mb_);
    fb.condbr(overflowed, trap, vec![], done, vec![]);
    fb.switch_to_block(trap);
    fb.unreachable();
    fb.switch_to_block(done);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// What `entry` of [`inline_and_assert_module`] answers.
fn reference(x: i64) -> i64 {
    (x & 63) + 1
}

type Lir = Vec<(Function, ProofContext)>;

fn translate(module: &Module) -> (Lir, trust_cg_lower::PreparedModuleForLir<'_>) {
    let prepared = prepare_module_for_lir(module, GuardCarrierArch::X86_64).expect("prepare");
    let (functions, validation) = prepared
        .translate_with_tls_and_validation_with_license(TlsDialect::default(), &permit_unlicensed())
        .expect("translate");
    validation
        .replay_exact_module_bindings(&functions)
        .expect("replay");
    drop(validation);
    (functions, prepared)
}

/// `(calls of the leaf, Asserts)` in `entry`'s LIR.
fn entry_shape(functions: &[(Function, ProofContext)]) -> (usize, usize) {
    let (entry, _) = functions
        .iter()
        .find(|(function, _)| function.name == ENTRY)
        .expect("entry in the LIR");
    let instructions = || entry.blocks.values().flat_map(|block| &block.instructions);
    let calls = instructions()
        .filter(|i| matches!(&i.opcode, Opcode::Call { name, .. } if name == LEAF))
        .count();
    let asserts = instructions()
        .filter(|i| matches!(i.opcode, Opcode::Assert))
        .count();
    (calls, asserts)
}

fn identities(functions: &[(Function, ProofContext)]) -> Vec<Option<String>> {
    functions
        .iter()
        .map(|(function, _)| function.canonical_body_identity())
        .collect()
}

/// The raw-lane step (`prepare_jit_lir_module`, the JIT step every raw lane
/// and `Compiler::compile_module_to_jit` run): under the proof-claim admission
/// the LIR leaves the step exactly as the adapter produced it, the call and
/// the `Assert` kept; without a proof claim the inliner splices the leaf and
/// the range pass deletes the `Assert`. O0 runs nothing either way.
#[test]
fn the_shared_step_rewrites_the_lir_only_without_a_proof_claim() {
    let module = inline_and_assert_module();
    let no_bindings: HashMap<String, *const u8> = HashMap::new();
    for (opt_level, makes_claim) in [
        (OptLevel::O2, false),
        (OptLevel::O2, true),
        (OptLevel::O1, true),
        (OptLevel::O3, true),
        (OptLevel::O0, false),
        (OptLevel::O0, true),
    ] {
        let (mut functions, prepared) = translate(&module);
        assert_eq!(entry_shape(&functions), (1, 1), "the adapter's LIR");
        let adapter_lir = identities(&functions);
        let preparation = prepare_jit_lir_module(
            &mut functions,
            prepared.module(),
            GuardCarrierArch::X86_64,
            TlsDialect::default(),
            opt_level,
            InlineOnlyAdmission::for_proof_claim(makes_claim),
            &permit_unlicensed(),
            JitExternBindings::Map(&no_bindings),
        )
        .expect("prepare");
        let label = format!("{opt_level:?}, proof claim {makes_claim}");
        assert_eq!(
            preparation.skipped_for_proof_claim,
            makes_claim && opt_level != OptLevel::O0,
            "{label}"
        );
        if makes_claim || opt_level == OptLevel::O0 {
            assert!(!preparation.ran, "{label}: the step ran");
            assert_eq!(preparation.inline.sites, 0, "{label}");
            assert_eq!(preparation.range.asserts_removed, 0, "{label}");
            assert_eq!(
                entry_shape(&functions),
                (1, 1),
                "{label}: the call and the Assert are kept"
            );
            assert_eq!(
                identities(&functions),
                adapter_lir,
                "{label}: the LIR is the adapter's, byte for byte"
            );
        } else {
            assert!(preparation.ran, "{label}");
            assert_eq!(preparation.inline.sites, 1, "{label}");
            assert_eq!(preparation.range.asserts_removed, 1, "{label}");
            assert_eq!(
                entry_shape(&functions),
                (0, 0),
                "{label}: the leaf is spliced and the Assert deleted"
            );
        }
    }
}

fn trace_detail(result: &CompilationResult, phase: &str) -> Option<String> {
    result
        .trace
        .as_ref()?
        .entries
        .iter()
        .find(|entry| entry.phase == phase)
        .and_then(|entry| entry.detail.clone())
}

#[allow(clippy::result_large_err)] // Returns the compiler's own error type unchanged.
fn compile_aot(
    module: &Module,
    triple: &'static str,
    opt_level: OptLevel,
    emit_proofs: bool,
) -> Result<CompilationResult, CompileError> {
    let module = module.clone();
    let environment = trust_cg_codegen::env_lock::EnvOverrideSnapshot::capture_current_thread();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            environment.run(|| {
                let target = if triple.starts_with("x86_64") {
                    Target::X86_64
                } else {
                    Target::Aarch64
                };
                Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level,
                        target,
                        emit_proofs,
                        parallel: false,
                        trace_level: CompilerTraceLevel::Full,
                        ..CompilerConfig::default()
                    },
                    TargetSpec::parse(triple).expect("triple"),
                )
                .with_codegen_license(permit_unlicensed())
                .compile(&module)
            })
        })
        .expect("spawn compile thread")
        .join()
        .expect("compile thread")
}

/// Why the replay tools a promoting x86-64 compile binds are unavailable, or
/// `None` when the identity-admitted AY and a capable checker are present
/// (`x86_source_bound_body.rs`'s rule).
fn replay_tools_unavailable() -> Option<String> {
    if std::env::var_os("TCG_REFINE_SOLVER").is_some_and(|value| value == "0") {
        return Some("TCG_REFINE_SOLVER=0 refuses live replay".into());
    }
    if trust_cg_verify::ay_bridge::admitted_proof_solver().is_none() {
        return Some(
            trust_cg_verify::ay_bridge::proof_toolchain_unavailable_reason()
                .unwrap_or_else(|| "no admitted AY with a capable checker".into()),
        );
    }
    None
}

/// The fixtures the AOT tests compile, by name.
fn aot_fixtures() -> [(&'static str, Module); 3] {
    [
        ("inline", inline_only_module()),
        ("assert", assert_only_module()),
        ("checked", checked_add_module()),
    ]
}

/// The non-proof control of the AOT seam: both passes run at O1+, on x86-64
/// and on AArch64 (the seam precedes target dispatch).
#[test]
fn an_aot_compile_without_a_proof_claim_runs_both_passes() {
    for triple in [X86_TRIPLE, AARCH64_TRIPLE] {
        for opt_level in [OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            for (fixture, module) in aot_fixtures() {
                let label = format!("{triple} {opt_level:?} {fixture}");
                let result = compile_aot(&module, triple, opt_level, false)
                    .unwrap_or_else(|error| panic!("{label}: {error}"));
                let inline = trace_detail(&result, "ir_inline");
                let range = trace_detail(&result, "lir_unsigned_range")
                    .unwrap_or_else(|| panic!("{label}: no range phase"));
                eprintln!(
                    "{label}: no proof claim, {} instructions, {} bytes; ir_inline {inline:?}; \
                     lir_unsigned_range {range:?}",
                    result.metrics.instruction_count, result.metrics.code_size_bytes
                );
                assert_eq!(trace_detail(&result, "lir_passes_skipped"), None, "{label}");
                match fixture {
                    "inline" => assert!(
                        inline.as_deref().is_some_and(|d| d.starts_with("2 sites")),
                        "{label}: {inline:?}"
                    ),
                    "assert" => assert!(range.contains("1 assert"), "{label}: {range}"),
                    _ => assert!(
                        range.starts_with("1 uadd") && range.ends_with("1 branch"),
                        "{label}: {range}"
                    ),
                }
            }
        }
    }
}

/// A proof-claiming AOT compile at O1+ runs neither pass: no `ir_inline` or
/// `lir_unsigned_range` phase. With the replay tools present the x86-64
/// inliner fixture must promote (two calls of a module function are inside
/// the body theorem's lane), so the claim is checked on its trace; the kept
/// `Assert` is outside the x86-64 theorem, so that fixture may be refused,
/// never for a reason the passes would have hidden.
#[test]
fn a_proof_claiming_aot_compile_runs_neither_pass() {
    let tools = replay_tools_unavailable();
    if let Some(reason) = &tools {
        eprintln!("NOTE: replay tools unavailable ({reason}); a refusal is the only outcome");
    }
    let mut failures = Vec::new();
    for triple in [X86_TRIPLE, AARCH64_TRIPLE] {
        for opt_level in [OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            for (fixture, module) in aot_fixtures() {
                let label = format!("{triple} {opt_level:?} {fixture}");
                match compile_aot(&module, triple, opt_level, true) {
                    Ok(result) => {
                        let inline = trace_detail(&result, "ir_inline");
                        let range = trace_detail(&result, "lir_unsigned_range");
                        eprintln!(
                            "{label}: proof claim promoted, {} instructions, {} bytes; \
                             ir_inline {inline:?}; lir_unsigned_range {range:?}",
                            result.metrics.instruction_count, result.metrics.code_size_bytes
                        );
                        if inline.is_some() || range.is_some() {
                            failures.push(format!("{label}: a pass ran under a proof claim"));
                        }
                        if trace_detail(&result, "lir_passes_skipped").is_none() {
                            failures.push(format!("{label}: the skip is not traced"));
                        }
                    }
                    Err(CompileError::IrInline { detail }) => failures.push(format!(
                        "{label}: the inliner ran under a proof claim: {detail}"
                    )),
                    Err(error) => {
                        eprintln!("{label}: proof claim refused: {error}");
                        if tools.is_none()
                            && triple == X86_TRIPLE
                            && fixture == "inline"
                            && opt_level == OptLevel::O2
                        {
                            failures.push(format!(
                                "{label}: with the replay tools present this fixture must \
                                 promote: {error}"
                            ));
                        }
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The JIT seam (`Compiler::compile_module_to_jit`): a verifying validation
/// mode claims proofs (x86-64's default `CachedVerified`, and `AlwaysVerify`),
/// so it runs neither pass; `Unchecked` claims nothing and runs both. Only an
/// x86-64 or AArch64 host has an in-process JIT.
#[test]
fn a_verifying_jit_compile_runs_neither_pass() {
    use trust_cg_codegen::compiler::JitValidationMode;
    let Some(host) = Target::try_host() else {
        eprintln!("SKIP a_verifying_jit_compile_runs_neither_pass: no in-process JIT host");
        return;
    };
    let compile = |mode: JitValidationMode| {
        let mut config = CompilerConfig::jit_fast(host);
        config.opt_level = OptLevel::O2;
        config.trace_level = CompilerTraceLevel::Full;
        config.jit_validation_mode_override = Some(mode);
        Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&inline_and_assert_module(), &HashMap::new())
            .map_err(Box::new)
    };
    let phase = |trace: Option<&trust_cg_codegen::CompilerTrace>, name: &str| {
        trace.and_then(|trace| {
            trace
                .entries
                .iter()
                .find(|entry| entry.phase == name)
                .and_then(|entry| entry.detail.clone())
        })
    };
    let run = |result: &trust_cg_codegen::JitCompilationResult| -> Vec<i64> {
        let entry: extern "C" fn(i64) -> i64 = unsafe {
            result
                .buffer
                .get_fn_bound(ENTRY)
                .expect("entry symbol")
                .into_inner()
        };
        [-1, 0, 5, 63, 64, 200].iter().map(|x| entry(*x)).collect()
    };
    let expected: Vec<i64> = [-1, 0, 5, 63, 64, 200]
        .iter()
        .map(|x| reference(*x))
        .collect();

    let unchecked = compile(JitValidationMode::Unchecked).expect("an Unchecked JIT compiles");
    let inline = phase(unchecked.trace.as_ref(), "ir_inline").expect("ir_inline ran");
    assert!(inline.starts_with("1 sites"), "{inline}");
    let range = phase(unchecked.trace.as_ref(), "lir_unsigned_range").expect("range ran");
    assert!(range.contains("1 assert"), "{range}");
    assert_eq!(run(&unchecked), expected);

    let instructions = |result: &trust_cg_codegen::JitCompilationResult| -> Vec<(String, usize)> {
        result
            .per_function_metrics
            .iter()
            .map(|metrics| (metrics.name.clone(), metrics.instruction_count))
            .collect()
    };
    eprintln!(
        "Unchecked: per-function instructions {:?}",
        instructions(&unchecked)
    );

    let mut failures = Vec::new();
    for mode in [
        JitValidationMode::CachedVerified,
        JitValidationMode::AlwaysVerify,
    ] {
        match compile(mode) {
            Ok(result) => {
                let inline = phase(result.trace.as_ref(), "ir_inline");
                let range = phase(result.trace.as_ref(), "lir_unsigned_range");
                eprintln!(
                    "{mode:?}: compiled; per-function instructions {:?}; ir_inline {inline:?}; \
                     lir_unsigned_range {range:?}",
                    instructions(&result)
                );
                if inline.is_some() || range.is_some() {
                    failures.push(format!("{mode:?}: a pass ran under a proof claim"));
                }
                if run(&result) != expected {
                    failures.push(format!("{mode:?}: wrong answers"));
                }
            }
            Err(error) => match *error {
                CompileError::IrInline { detail } => failures.push(format!(
                    "{mode:?}: the inliner ran under a proof claim: {detail}"
                )),
                error => eprintln!("{mode:?}: refused: {error}"),
            },
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
