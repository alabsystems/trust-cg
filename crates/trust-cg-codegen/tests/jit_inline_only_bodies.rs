// JIT-path LIR inlining and inline-only (trust-ir `AvailableExternally`)
// runtime bodies, end to end through `Compiler::compile_module_to_jit`.
//
// The fixture is the shape a frontend with a runtime ships: ONE definition of
// a helper (`tcg_test_read_lit`, the host function bound through the extern
// map) plus an inline-only body of its fast path (a bounds check and a load),
// whose out-of-range case calls the runtime's out-of-line remainder
// (`tcg_test_read_lit_slow`). At O1+ the JIT splices the fast path into the
// caller, so the definition is never called and only out-of-range reads reach
// the slow path; at O0, under `TCG_NO_JIT_LIR_PREPARE`, and when a
// proof-producing compile withholds the body, every read calls the
// definition. Every arm answers every read identically.

use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_codegen::{
    Compiler, CompilerConfig, CompilerTraceLevel, InlineOnlyAdmission, JIT_LIR_PREPARE_KILL_SWITCH,
    JitCompilationResult, JitExternBindings, prepare_jit_lir_module,
};
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{CodegenLicensePolicy, GuardCarrierArch, TlsDialect, prepare_module_for_lir};
use trust_ir::{ICmpOp, Linkage, Module, Ty};
use trust_ir_build::ModuleBuilder;

const DEFINITION: &str = "tcg_test_read_lit";
const SLOW: &str = "tcg_test_read_lit_slow";

static DEFINITION_CALLS: AtomicUsize = AtomicUsize::new(0);
static SLOW_CALLS: AtomicUsize = AtomicUsize::new(0);
/// The counters are process-global: tests that read them run one at a time.
static COUNTERS: Mutex<()> = Mutex::new(());

/// The runtime's out-of-line remainder.
extern "C" fn host_read_lit_slow(_table: *const i64, index: i64) -> i64 {
    SLOW_CALLS.fetch_add(1, Ordering::SeqCst);
    -1000 - index
}

/// The runtime's definition of the helper: the fast path, else the remainder.
extern "C" fn host_read_lit(table: *const i64, index: i64) -> i64 {
    DEFINITION_CALLS.fetch_add(1, Ordering::SeqCst);
    // SAFETY: the tests pass a table whose word 0 is its length.
    let len = unsafe { *table };
    if (index as u64) < (len as u64) {
        // SAFETY: bounds-checked above.
        unsafe { *table.add(1 + index as usize) }
    } else {
        host_read_lit_slow(table, index)
    }
}

fn externs() -> HashMap<String, *const u8> {
    HashMap::from([
        (DEFINITION.to_string(), host_read_lit as *const u8),
        (SLOW.to_string(), host_read_lit_slow as *const u8),
    ])
}

/// `entry(table, i) = tcg_test_read_lit(table, i) + tcg_test_read_lit(table, i + 1)`
/// with an inline-only body of `tcg_test_read_lit` (when `inline_only`), or a
/// plain declaration of it.
fn read_module(inline_only: bool) -> Module {
    let mut mb = ModuleBuilder::new("jit_inline_only_bodies");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let slow = mb.declare_function(SLOW, ft);
    let read = if inline_only {
        let mut fb = mb.function(DEFINITION, ft);
        fb.set_linkage(Linkage::AvailableExternally);
        let entry = fb.create_block();
        let table = fb.add_block_param(entry, Ty::Ptr);
        let index = fb.add_block_param(entry, Ty::I64);
        let fast = fb.create_block();
        let slow_block = fb.create_block();
        fb.switch_to_block(entry);
        let len = fb.load(Ty::I64, table);
        let in_range = fb.icmp(ICmpOp::Ult, Ty::I64, index, len);
        fb.condbr(in_range, fast, vec![], slow_block, vec![]);
        fb.switch_to_block(fast);
        let one = fb.iconst(Ty::I64, 1);
        let slot = fb.add(Ty::I64, index, one);
        let element = fb.gep(Ty::I64, table, vec![slot]);
        let value = fb.load(Ty::I64, element);
        fb.ret(vec![value]);
        fb.switch_to_block(slow_block);
        let rest = fb.call(slow, vec![table, index]);
        fb.ret(vec![rest]);
        fb.build()
    } else {
        mb.declare_function(DEFINITION, ft)
    };
    {
        let mut fb = mb.function("entry", ft);
        let entry = fb.create_block();
        let table = fb.add_block_param(entry, Ty::Ptr);
        let index = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let first = fb.call(read, vec![table, index]);
        let one = fb.iconst(Ty::I64, 1);
        let next = fb.add(Ty::I64, index, one);
        let second = fb.call(read, vec![table, next]);
        let sum = fb.add(Ty::I64, first, second);
        fb.ret(vec![sum]);
        fb.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // The bodyless declarations are FFI boundaries, so the module pins the
    // host target it is JIT-compiled for: every ingestion entry refuses what
    // trust-ir's validator refuses (`TargetInfoRequired`, WS7.3).
    module.target_info = Some(
        trust_cg_codegen::CoreHostJitTarget::detect()
            .expect("supported JIT host")
            .trust_ir_target_info()
            .clone(),
    );
    module
}

fn host_target() -> Target {
    Target::try_host().expect("an in-process JIT host")
}

/// The host JIT configuration of a compile that claims no proof: an explicit
/// `Unchecked` mode, the AArch64 default. x86-64's default, `CachedVerified`,
/// claims proofs, and a compile that claims proofs runs no LIR inliner
/// (ruling OD-225; `a_verifying_jit_validation_mode_splices_no_inline_only_body`
/// below), so without the override these inliner tests would test nothing on
/// an x86-64 host.
fn no_claim_jit_config() -> CompilerConfig {
    let mut config = CompilerConfig::jit_fast(host_target());
    config.jit_validation_mode_override =
        Some(trust_cg_codegen::compiler::JitValidationMode::Unchecked);
    config
}

fn compile(module: &Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = no_claim_jit_config();
    config.opt_level = opt_level;
    config.trace_level = CompilerTraceLevel::Full;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &externs())
        .expect("compile_module_to_jit")
}

const TABLE: [i64; 5] = [4, 10, 20, 30, 40];
const INDICES: [i64; 7] = [-1, 0, 1, 2, 3, 4, 9];

/// What `entry` must answer, from the definition's own semantics.
fn reference(index: i64) -> i64 {
    let read = |i: i64| {
        if (i as u64) < (TABLE[0] as u64) {
            TABLE[1 + i as usize]
        } else {
            -1000 - i
        }
    };
    read(index) + read(index + 1)
}

/// Out-of-range reads among every `entry(INDICES[k])` (two reads each).
fn out_of_range_reads() -> usize {
    INDICES
        .iter()
        .flat_map(|i| [*i, i + 1])
        .filter(|i| (*i as u64) >= (TABLE[0] as u64))
        .count()
}

/// Run `entry` over every index; returns (answers, definition calls, slow calls).
fn run(result: &JitCompilationResult) -> (Vec<i64>, usize, usize) {
    let entry: extern "C" fn(*const i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("entry")
            .expect("entry symbol")
            .into_inner()
    };
    DEFINITION_CALLS.store(0, Ordering::SeqCst);
    SLOW_CALLS.store(0, Ordering::SeqCst);
    let answers = INDICES
        .iter()
        .map(|index| entry(TABLE.as_ptr(), *index))
        .collect();
    (
        answers,
        DEFINITION_CALLS.load(Ordering::SeqCst),
        SLOW_CALLS.load(Ordering::SeqCst),
    )
}

fn trace_detail(result: &JitCompilationResult, phase: &str) -> Option<String> {
    result
        .trace
        .as_ref()?
        .entries
        .iter()
        .find(|entry| entry.phase == phase)
        .and_then(|entry| entry.detail.clone())
}

#[test]
fn inlined_and_called_fast_paths_answer_identically_at_every_opt_level() {
    let _serial = COUNTERS.lock().unwrap_or_else(|e| e.into_inner());
    let expected: Vec<i64> = INDICES.iter().map(|i| reference(*i)).collect();
    let reads = INDICES.len() * 2;
    let module = read_module(true);
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let result = compile(&module, opt_level);
        let (answers, definition_calls, slow_calls) = run(&result);
        assert_eq!(answers, expected, "{opt_level:?}");
        assert_eq!(slow_calls, out_of_range_reads(), "{opt_level:?}");
        if opt_level == OptLevel::O0 {
            assert_eq!(
                definition_calls, reads,
                "O0 calls the definition for every read"
            );
            assert!(result.inline_only_bodies.spliced.is_empty());
            assert!(
                trace_detail(&result, "ir_inline").is_none(),
                "no step at O0"
            );
        } else {
            assert_eq!(
                definition_calls, 0,
                "{opt_level:?}: the fast path replaced every call to the definition"
            );
            let spliced: Vec<_> = result
                .inline_only_bodies
                .spliced
                .iter()
                .map(|u| (u.name.as_str(), u.sites))
                .collect();
            assert_eq!(spliced, vec![(DEFINITION, 2)], "{opt_level:?}");
            assert!(result.inline_only_bodies.withheld.is_empty());
            let premises = result.inline_only_bodies.premises();
            assert_eq!(premises.len(), 1);
            assert!(premises[0].contains("one-definition rule"), "{premises:?}");
            let detail = trace_detail(&result, "ir_inline").expect("ir_inline trace entry");
            assert!(
                detail.contains("2 inline-only site(s) from 1 body(ies)"),
                "{detail}"
            );
            assert!(trace_detail(&result, "lir_unsigned_range").is_some());
        }
    }
}

#[test]
fn a_declaration_without_a_body_stays_a_call_at_every_opt_level() {
    let _serial = COUNTERS.lock().unwrap_or_else(|e| e.into_inner());
    let expected: Vec<i64> = INDICES.iter().map(|i| reference(*i)).collect();
    let module = read_module(false);
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let result = compile(&module, opt_level);
        let (answers, definition_calls, _) = run(&result);
        assert_eq!(answers, expected, "{opt_level:?}");
        assert_eq!(definition_calls, INDICES.len() * 2, "{opt_level:?}");
        assert_eq!(result.inline_only_bodies, Default::default());
    }
}

#[test]
fn the_kill_switch_keeps_every_call() {
    let _serial = COUNTERS.lock().unwrap_or_else(|e| e.into_inner());
    let expected: Vec<i64> = INDICES.iter().map(|i| reference(*i)).collect();
    let module = read_module(true);
    trust_cg_codegen::env_lock::with_env_overrides(&[(JIT_LIR_PREPARE_KILL_SWITCH, "1")], || {
        let result = compile(&module, OptLevel::O2);
        let (answers, definition_calls, _) = run(&result);
        assert_eq!(answers, expected);
        assert_eq!(definition_calls, INDICES.len() * 2);
        assert_eq!(result.inline_only_bodies, Default::default());
        assert!(trace_detail(&result, "ir_inline").is_none());
    });
}

#[test]
fn the_killed_step_emits_the_same_bytes_as_a_module_with_no_inline_only_body() {
    // With the step off, the module with an inline-only body and the module
    // that only DECLARES the helper are the same codegen input: the body is
    // never emitted and every call routes to the symbol.
    let digest = |module: &Module| {
        let result = compile(module, OptLevel::O2);
        let function = |name: &str| {
            result
                .validation
                .as_ref()
                .and_then(|v| v.functions.iter().find(|f| f.function == name))
                .map(|f| f.bytes_sha256.clone())
        };
        function("entry")
    };
    trust_cg_codegen::env_lock::with_env_overrides(&[(JIT_LIR_PREPARE_KILL_SWITCH, "1")], || {
        let with_body = digest(&read_module(true));
        let without_body = digest(&read_module(false));
        assert!(with_body.is_some());
        assert_eq!(with_body, without_body);
    });
}

#[test]
fn a_withheld_body_leaves_the_call_and_names_why() {
    let module = read_module(true);
    let prepared = prepare_module_for_lir(&module, GuardCarrierArch::AArch64).expect("prepare");
    let translate = || {
        let (functions, validation) = prepared
            .translate_with_tls_and_validation_with_license(
                TlsDialect::default(),
                &permit_unlicensed(),
            )
            .expect("translate");
        validation
            .replay_exact_module_bindings(&functions)
            .expect("replay");
        functions
    };
    let calls_to_definition =
        |functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)]| {
            functions
                .iter()
                .flat_map(|(f, _)| f.blocks.values())
                .flat_map(|b| &b.instructions)
                .filter(|i| matches!(&i.opcode, Opcode::Call { name, .. } if name == DEFINITION))
                .count()
        };

    let mut withheld = translate();
    let before = calls_to_definition(&withheld);
    assert_eq!(before, 2);
    let preparation = prepare_jit_lir_module(
        &mut withheld,
        prepared.module(),
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        OptLevel::O2,
        InlineOnlyAdmission::Withhold,
        &permit_unlicensed(),
        JitExternBindings::Any,
    )
    .expect("prepare");
    // OD-225: the proof-claim admission runs neither pass of the step, so the
    // LIR is the adapter's; the body is still listed as withheld.
    assert!(!preparation.ran);
    assert!(preparation.skipped_for_proof_claim);
    assert_eq!(
        calls_to_definition(&withheld),
        2,
        "a withheld body leaves the calls"
    );
    assert!(preparation.inline_only.spliced.is_empty());
    assert_eq!(preparation.inline_only.withheld.len(), 1);
    assert_eq!(preparation.inline_only.withheld[0].name, DEFINITION);
    assert!(
        preparation.inline_only.withheld[0]
            .reason
            .contains("proof-producing compile"),
        "{:?}",
        preparation.inline_only.withheld
    );

    let mut disclosed = translate();
    let preparation = prepare_jit_lir_module(
        &mut disclosed,
        prepared.module(),
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        OptLevel::O2,
        InlineOnlyAdmission::DisclosedPremise,
        &permit_unlicensed(),
        JitExternBindings::Any,
    )
    .expect("prepare");
    assert_eq!(calls_to_definition(&disclosed), 0);
    assert_eq!(preparation.inline_only.spliced.len(), 1);
    assert_eq!(preparation.inline_only.spliced[0].sites, 2);
}

/// A module-local helper reached through the JIT's exact module edge: the JIT
/// now inlines it (OPT-4 was AOT-only), with the same answers at every level.
fn exact_edge_module() -> Module {
    let mut mb = ModuleBuilder::new("jit_exact_edge_inline");
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let square = {
        let mut fb = mb.function("square_plus_one", ft);
        fb.set_linkage(Linkage::Internal);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let sq = fb.mul(Ty::I64, x, x);
        let one = fb.iconst(Ty::I64, 1);
        let r = fb.add(Ty::I64, sq, one);
        fb.ret(vec![r]);
        fb.build()
    };
    {
        let mut fb = mb.function("entry", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let a = fb.call(square, vec![x]);
        let b = fb.call(square, vec![a]);
        fb.ret(vec![b]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn the_jit_inlines_a_module_local_helper_through_its_exact_edge() {
    let module = exact_edge_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = no_claim_jit_config();
        config.opt_level = opt_level;
        config.trace_level = CompilerTraceLevel::Full;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("compile_module_to_jit");
        let entry: extern "C" fn(i64) -> i64 = unsafe {
            result
                .buffer
                .get_fn_bound("entry")
                .expect("entry symbol")
                .into_inner()
        };
        for x in [-3_i64, 0, 2, 7] {
            let a = x.wrapping_mul(x).wrapping_add(1);
            assert_eq!(
                entry(x),
                a.wrapping_mul(a).wrapping_add(1),
                "{opt_level:?} x={x}"
            );
        }
        let detail = trace_detail(&result, "ir_inline");
        if opt_level == OptLevel::O0 {
            assert!(detail.is_none());
        } else {
            let detail = detail.expect("ir_inline trace entry");
            assert!(detail.starts_with("2 sites"), "{opt_level:?}: {detail}");
        }
    }
}

extern "C" fn host_square_plus_one_override(x: i64) -> i64 {
    x.wrapping_sub(1000)
}

#[test]
fn an_explicit_extern_binding_keeps_a_non_local_definition_a_call() {
    // `square_plus_one` with External linkage: an explicit extern binding of
    // its name interposes on it in the JIT link, so it must never be spliced;
    // without the binding it is the module's own definition and is spliced.
    let mut module = exact_edge_module();
    for function in &mut module.functions {
        if function.name == "square_plus_one" {
            function.linkage = Linkage::External;
        }
    }
    for with_binding in [false, true] {
        let externs = if with_binding {
            HashMap::from([(
                "square_plus_one".to_string(),
                host_square_plus_one_override as *const u8,
            )])
        } else {
            HashMap::new()
        };
        let mut config = no_claim_jit_config();
        config.opt_level = OptLevel::O2;
        config.trace_level = CompilerTraceLevel::Full;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &externs)
            .expect("compile_module_to_jit");
        let entry: extern "C" fn(i64) -> i64 = unsafe {
            result
                .buffer
                .get_fn_bound("entry")
                .expect("entry symbol")
                .into_inner()
        };
        let detail = trace_detail(&result, "ir_inline").expect("ir_inline trace entry");
        for x in [-3_i64, 0, 2, 7] {
            let expected = if with_binding {
                x.wrapping_sub(1000).wrapping_sub(1000)
            } else {
                let a = x.wrapping_mul(x).wrapping_add(1);
                a.wrapping_mul(a).wrapping_add(1)
            };
            assert_eq!(entry(x), expected, "binding={with_binding} x={x}");
        }
        if with_binding {
            assert!(detail.starts_with("0 sites"), "{detail}");
        } else {
            assert!(detail.starts_with("2 sites"), "{detail}");
        }
    }
}

#[test]
fn the_inline_only_kill_switch_withholds_the_body_and_keeps_module_inlining() {
    let _serial = COUNTERS.lock().unwrap_or_else(|e| e.into_inner());
    let expected: Vec<i64> = INDICES.iter().map(|i| reference(*i)).collect();
    trust_cg_codegen::env_lock::with_env_overrides(
        &[(trust_cg_codegen::INLINE_ONLY_BODIES_KILL_SWITCH, "1")],
        || {
            let result = compile(&read_module(true), OptLevel::O2);
            let (answers, definition_calls, _) = run(&result);
            assert_eq!(answers, expected);
            assert_eq!(definition_calls, INDICES.len() * 2);
            assert!(result.inline_only_bodies.spliced.is_empty());
            assert_eq!(result.inline_only_bodies.withheld.len(), 1);
            assert!(
                result.inline_only_bodies.withheld[0]
                    .reason
                    .contains(trust_cg_codegen::INLINE_ONLY_BODIES_KILL_SWITCH),
                "{:?}",
                result.inline_only_bodies.withheld
            );
            // The step itself still ran: module definitions are still inlined.
            let exact = Compiler::new({
                let mut config = no_claim_jit_config();
                config.opt_level = OptLevel::O2;
                config.trace_level = CompilerTraceLevel::Full;
                config
            })
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&exact_edge_module(), &HashMap::new())
            .expect("compile_module_to_jit");
            let detail = trace_detail(&exact, "ir_inline").expect("ir_inline trace entry");
            assert!(detail.starts_with("2 sites"), "{detail}");
        },
    );
}

#[test]
fn a_verifying_jit_validation_mode_splices_no_inline_only_body() {
    // `CachedVerified` (x86-64's default) and `AlwaysVerify` require
    // proof-grade evidence for every published function: such a compile
    // makes a proof claim, so it withholds every inline-only body. It may also
    // refuse the module for an unrelated proof gap on this host; it never
    // splices a body.
    use trust_cg_codegen::compiler::JitValidationMode;
    let _serial = COUNTERS.lock().unwrap_or_else(|e| e.into_inner());
    for mode in [
        JitValidationMode::CachedVerified,
        JitValidationMode::AlwaysVerify,
    ] {
        let mut config = CompilerConfig::jit_fast(host_target());
        config.opt_level = OptLevel::O2;
        config.jit_validation_mode_override = Some(mode);
        match Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&read_module(true), &externs())
        {
            Ok(result) => {
                eprintln!("{mode:?}: compiled, every inline-only body withheld");
                assert!(result.inline_only_bodies.spliced.is_empty(), "{mode:?}");
                assert_eq!(result.inline_only_bodies.withheld.len(), 1, "{mode:?}");
                let expected: Vec<i64> = INDICES.iter().map(|i| reference(*i)).collect();
                let (answers, definition_calls, _) = run(&result);
                assert_eq!(answers, expected, "{mode:?}");
                assert_eq!(definition_calls, INDICES.len() * 2, "{mode:?}");
            }
            Err(error) => {
                eprintln!("{mode:?}: refused: {error}");
                assert!(
                    !matches!(error, trust_cg_codegen::CompileError::IrInline { .. }),
                    "{mode:?}: {error}"
                );
            }
        }
    }
    assert_eq!(
        InlineOnlyAdmission::for_proof_claim(true),
        InlineOnlyAdmission::Withhold
    );
    assert_eq!(
        InlineOnlyAdmission::for_proof_claim(false),
        InlineOnlyAdmission::DisclosedPremise
    );
}

const FIELD: &str = "tcg_test_ctor_field";
static FIELD_CALLS: AtomicUsize = AtomicUsize::new(0);

/// The runtime's definition of a constructor-field read: `obj[1 + index]`.
extern "C" fn host_ctor_field(obj: *const i64, index: i64) -> i64 {
    FIELD_CALLS.fetch_add(1, Ordering::SeqCst);
    // SAFETY: the test passes an object with the fields it reads.
    unsafe { *obj.add(1 + index as usize) }
}

/// `entry(obj, i) = tcg_test_ctor_field(obj, i) + tcg_test_ctor_field(obj, i + 1)`
/// with a ONE-block inline-only body of the field read (a load, no branch).
fn field_module() -> Module {
    let mut mb = ModuleBuilder::new("jit_inline_only_field_read");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let field = {
        let mut fb = mb.function(FIELD, ft);
        fb.set_linkage(Linkage::AvailableExternally);
        let entry = fb.create_block();
        let obj = fb.add_block_param(entry, Ty::Ptr);
        let index = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let slot = fb.add(Ty::I64, index, one);
        let element = fb.gep(Ty::I64, obj, vec![slot]);
        let value = fb.load(Ty::I64, element);
        fb.ret(vec![value]);
        fb.build()
    };
    {
        let mut fb = mb.function("entry", ft);
        let entry = fb.create_block();
        let obj = fb.add_block_param(entry, Ty::Ptr);
        let index = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let first = fb.call(field, vec![obj, index]);
        let one = fb.iconst(Ty::I64, 1);
        let next = fb.add(Ty::I64, index, one);
        let second = fb.call(field, vec![obj, next]);
        let sum = fb.add(Ty::I64, first, second);
        fb.ret(vec![sum]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_one_block_field_read_is_spliced_and_answers_as_the_definition() {
    let _serial = COUNTERS.lock().unwrap_or_else(|e| e.into_inner());
    let object: [i64; 6] = [0xc0, 11, 22, 33, 44, 55];
    let externs = HashMap::from([(FIELD.to_string(), host_ctor_field as *const u8)]);
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut config = no_claim_jit_config();
        config.opt_level = opt_level;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&field_module(), &externs)
            .expect("compile_module_to_jit");
        let entry: extern "C" fn(*const i64, i64) -> i64 = unsafe {
            result
                .buffer
                .get_fn_bound("entry")
                .expect("entry symbol")
                .into_inner()
        };
        FIELD_CALLS.store(0, Ordering::SeqCst);
        for index in 0..4_i64 {
            assert_eq!(
                entry(object.as_ptr(), index),
                object[1 + index as usize] + object[2 + index as usize],
                "{opt_level:?} index={index}"
            );
        }
        let spliced: Vec<_> = result
            .inline_only_bodies
            .spliced
            .iter()
            .map(|u| (u.name.as_str(), u.sites))
            .collect();
        if opt_level == OptLevel::O0 {
            assert!(spliced.is_empty());
            assert_eq!(FIELD_CALLS.load(Ordering::SeqCst), 8);
        } else {
            assert_eq!(spliced, vec![(FIELD, 2)], "{opt_level:?}");
            assert_eq!(FIELD_CALLS.load(Ordering::SeqCst), 0, "{opt_level:?}");
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
