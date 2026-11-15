// trust-cg-codegen/tests/e2e_aarch64_composed_transition.rs
//
// The composed transition record (ledger L09-P3) through the public
// `Pipeline` and `Compiler` on the host's AArch64 triple:
//
// * Every kernel of an affine corpus (one block or one diamond of
//   I32/I64 values: wrapping add/sub, constants including MOVZ/MOVK
//   expansions, comparisons, flat selects) composes at O0-O3 under a
//   proof-grade preparation: legalization (TrustIR -> LIR), selection
//   (LIR -> raw MachIR), every interface-changing optimizer run, the
//   post-allocation comparison and the proof-grade encoding, each adjacent
//   pair sharing one interface, starting at the exact module-owned TrustIR
//   function and ending at exactly the bytes the object and the JIT buffer
//   publish for the function.
// * Recording never changes an emitted byte.
// * Functions outside the legalization check's domain are named, not
//   composed, and not required.
// * Corruption controls on real records: each link dropped, each internal
//   interface swapped, an unvalidated rewrite inserted (AOT profile
//   instrumentation between the optimizer and allocation; a pass that
//   rewrites a constant and one that does so silently, run through a pass
//   manager and mapped to links by the pipeline's own `pass_run_link`), and
//   every byte of the published function flipped after the last link: each
//   is refused by name.
// * The proof-required routes (`--emit-proofs` objects, the proof-required
//   JIT) require the composition right after preparation, before proof
//   promotion: real AOT instrumentation is refused by composition on both
//   routes on any host, and an untouched composing function is never
//   refused by composition. (The byte binding after publication and an
//   unvalidated optimizer run inside a real preparation are driven by the
//   crate's unit tests, which can arm the pipeline's test hooks.)
// * Native: the proof-grade objects agree with a C reference on an input
//   grid.
// * Census: the whole-body owner's family corpus classified by record.
//
// Evidence strength: each link is decided exactly over its own model by
// trusted Rust (the affine check, the pass validators, the post-allocation
// comparison, ENC-5 and the layout cross-check); the composition is that
// chain, not a proof. The native rows are a bounded differential.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(all(target_arch = "aarch64", feature = "verify"))]

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use trust_cg_codegen::composed_transition::{
    ComposedTransitionPolicy, pass_run_link, require_composition, require_object_publication,
};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, PreparationMetrics};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachOperand};
use trust_cg_opt::{MachinePass, PassManager, PassValidationConfig};
use trust_cg_verify::composed_transition::{
    CompositionRefusal, EvidenceStrength, LinkStage, TransitionRecord, bytes_interface,
    mach_function_interface, mach_function_interface_digest, trust_ir_function_interface,
};

#[path = "common/source_bound_body_cases.rs"]
mod body_cases;
#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/native_host.rs"]
mod native_host;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// One kernel: its symbol stem, trust-ir function type and body, and its C
/// parameter and result types and reference expression over `a` and `b`.
struct Kernel {
    name: &'static str,
    functy: &'static str,
    body: &'static str,
    c_param: &'static str,
    c_result: &'static str,
    c_reference: &'static str,
}

const ADD: Kernel = Kernel {
    name: "ct_add",
    functy: "(i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64):\n    %2 = add i64 %0, %1\n    ret %2\n",
    c_param: "int64_t",
    c_result: "int64_t",
    c_reference: "(int64_t)((uint64_t)a + (uint64_t)b)",
};

const SUB32: Kernel = Kernel {
    name: "ct_sub32",
    functy: "(i32, i32) -> (i32)",
    body: "bb0(%0: i32, %1: i32):\n    %2 = sub i32 %0, %1\n    ret %2\n",
    c_param: "int32_t",
    c_result: "int32_t",
    c_reference: "(int32_t)((uint32_t)a - (uint32_t)b)",
};

/// `(a + 5 - b) + a - 0x1234_5678_9abc`: a dead-code-eliminated temporary
/// at O1+ and a MOVZ/MOVK constant.
const AFFINE: Kernel = Kernel {
    name: "ct_affine",
    functy: "(i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64):\n    %2 = const i64 5\n    %3 = add i64 %0, %2\n    \
           %4 = sub i64 %3, %1\n    %5 = add i64 %4, %0\n    %6 = const i64 20015998343868\n    \
           %7 = sub i64 %5, %6\n    ret %7\n",
    c_param: "int64_t",
    c_result: "int64_t",
    c_reference: "(int64_t)((uint64_t)a + 5 - (uint64_t)b + (uint64_t)a - 20015998343868ull)",
};

/// A recomputed sum (CSE and the declarative rewrites at O2+).
const DUP: Kernel = Kernel {
    name: "ct_dup",
    functy: "(i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64):\n    %2 = add i64 %0, %1\n    %3 = add i64 %0, %1\n    \
           %4 = sub i64 %2, %3\n    %5 = add i64 %4, %1\n    ret %5\n",
    c_param: "int64_t",
    c_result: "int64_t",
    c_reference: "b",
};

const MIN: Kernel = Kernel {
    name: "ct_min",
    functy: "(i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64):\n    %2 = icmp slt i64 %0, %1\n    \
           %3 = select i64 %2, %0, %1\n    ret %3\n",
    c_param: "int64_t",
    c_result: "int64_t",
    c_reference: "a < b ? a : b",
};

const ULT32: Kernel = Kernel {
    name: "ct_ult32",
    functy: "(i32, i32) -> (bool)",
    body: "bb0(%0: i32, %1: i32):\n    %2 = icmp ult i32 %0, %1\n    ret %2\n",
    c_param: "int32_t",
    c_result: "_Bool",
    c_reference: "(uint32_t)a < (uint32_t)b",
};

const SGE_SELECT: Kernel = Kernel {
    name: "ct_sge_select",
    functy: "(i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64):\n    %2 = icmp sge i64 %0, %1\n    %3 = const i64 7\n    \
           %4 = sub i64 %0, %1\n    %5 = select i64 %2, %4, %3\n    ret %5\n",
    c_param: "int64_t",
    c_result: "int64_t",
    c_reference: "a >= b ? (int64_t)((uint64_t)a - (uint64_t)b) : 7",
};

/// One arithmetic diamond.
const DIAMOND: Kernel = Kernel {
    name: "ct_diamond",
    functy: "(i64, i64) -> (i64)",
    body: "bb0(%0: i64, %1: i64):\n    %2 = icmp slt i64 %0, %1\n    condbr %2, bb1, bb2\n\
           bb1:\n    %3 = const i64 3\n    %4 = add i64 %0, %3\n    br bb3(%4)\n\
           bb2:\n    %5 = sub i64 %1, %0\n    br bb3(%5)\n\
           bb3(%6: i64):\n    ret %6\n",
    c_param: "int64_t",
    c_result: "int64_t",
    c_reference: "a < b ? (int64_t)((uint64_t)a + 3) : (int64_t)((uint64_t)b - (uint64_t)a)",
};

const KERNELS: [&Kernel; 8] = [
    &ADD,
    &SUB32,
    &AFFINE,
    &DUP,
    &MIN,
    &ULT32,
    &SGE_SELECT,
    &DIAMOND,
];

/// Functions outside the legalization check's domain, and the reason prefix
/// their records give.
const OUT_OF_DOMAIN: [(&str, &str, &str); 3] = [
    (
        "ct_mul",
        "(i64, i64) -> (i64)",
        "bb0(%0: i64, %1: i64):\n    %2 = mul i64 %0, %1\n    ret %2\n",
    ),
    (
        "ct_load",
        "(ptr) -> (i64)",
        "bb0(%0: ptr):\n    %1 = load i64, ptr %0\n    ret %1\n",
    ),
    (
        "ct_loop",
        "(i64) -> (i64)",
        "bb0(%0: i64):\n    %1 = const i64 0\n    %2 = const i64 1\n    br bb1(%1, %1)\n\
         bb1(%3: i64, %4: i64):\n    %5 = icmp ult i64 %3, %0\n    condbr %5, bb2, bb3\n\
         bb2:\n    %6 = add i64 %4, %3\n    %7 = add i64 %3, %2\n    br bb1(%7, %6)\n\
         bb3:\n    ret %4\n",
    ),
];

fn level_tag(level: OptLevel) -> &'static str {
    match level {
        OptLevel::O0 => "o0",
        OptLevel::O1 => "o1",
        OptLevel::O2 => "o2",
        OptLevel::O3 => "o3",
    }
}

fn module(symbol: &str, functy: &str, body: &str) -> trust_ir::Module {
    let text = format!(
        "; TrustIr text format v1\nmodule \"ct\"\ntarget \"{}\" 8 little abi=\"aapcs64\"\n\
         functy.0 = {functy}\nfn @{symbol}(functy.0) {{\n{body}}}\n",
        native_host::TRIPLE
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("{symbol}: trust-ir parse: {error:?}\n{text}"))
}

/// The license these hand-built fixtures compile under: they carry no codegen
/// license (`body_gate: None`), which trust-cg refuses by default (WS7.5,
/// decision gate DG-73), so every compile states `Permit` explicitly.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

fn lir(module: &trust_ir::Module) -> trust_cg_lower::Function {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("adapter: {error}"))
    .0
}

fn proof_pipeline(level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: level,
        target_triple: native_host::TRIPLE.into(),
        ..PipelineConfig::default()
    })
    .with_proof_grade_aarch64_publication()
}

fn prepare(
    pipeline: &Pipeline,
    module: &trust_ir::Module,
    lir: &trust_cg_lower::Function,
) -> (MachFunction, PreparationMetrics) {
    pipeline
        .prepare_function_with_metrics_and_trust_ir_module(lir, None, module, &module.functions[0])
        .unwrap_or_else(|error| panic!("{}: preparation: {error}", lir.name))
}

/// One kernel at one level, prepared at proof grade.
struct Built {
    symbol: String,
    module: trust_ir::Module,
    lir: trust_cg_lower::Function,
    function: MachFunction,
    record: TransitionRecord,
    object: Vec<u8>,
}

fn build(kernel: &Kernel, level: OptLevel) -> Built {
    let symbol = format!("{}_{}", kernel.name, level_tag(level));
    let module = module(&symbol, kernel.functy, kernel.body);
    let lir = lir(&module);
    let pipeline = proof_pipeline(level);
    let (function, metrics) = prepare(&pipeline, &module, &lir);
    let record = metrics
        .composed_transition
        .unwrap_or_else(|| panic!("{symbol}: a proof-grade preparation builds a record"));
    let object = pipeline
        .compile_module_with_globals(std::slice::from_ref(&function), &[])
        .unwrap_or_else(|error| panic!("{symbol}: object: {error}"));
    native_host::assert_native_object(&object);
    Built {
        symbol,
        module,
        lir,
        function,
        record,
        object,
    }
}

fn corpus() -> Vec<Built> {
    let mut built = Vec::new();
    for kernel in KERNELS {
        for level in LEVELS {
            built.push(build(kernel, level));
        }
    }
    built
}

/// Every affine kernel composes at every level, from its TrustIR source to
/// the bytes its object carries, and every link names its relation.
#[test]
fn every_affine_kernel_composes_from_its_source_to_its_published_bytes() {
    let mut pass_runs: BTreeMap<String, usize> = BTreeMap::new();
    for built in corpus() {
        let composed = built
            .record
            .compose()
            .unwrap_or_else(|refusal| panic!("{}: {refusal}\n{:#?}", built.symbol, built.record));
        assert_eq!(composed.strength, EvidenceStrength::ExactlyDecided);
        let origin = trust_ir_function_interface(&built.module, 0).expect("module-owned");
        composed
            .check_origin(&origin)
            .expect("the chain starts at the source");
        // The selection link ends at the raw selection the public API
        // reproduces.
        let raw = proof_pipeline(OptLevel::O0)
            .select_ir_function(&built.lir)
            .expect("selection");
        assert_eq!(built.record.links[1].to, mach_function_interface(&raw));
        // The post-allocation link ends at the final function.
        let post = built
            .record
            .links
            .iter()
            .rfind(|link| link.stage == LinkStage::PostAllocation)
            .expect("a post-allocation link");
        assert_eq!(post.to, mach_function_interface(&built.function));
        // The object carries exactly the terminal bytes.
        let records = [(built.symbol.as_str(), Some(&built.record))];
        assert_eq!(
            require_object_publication(&built.object, &records),
            Ok(1),
            "{}",
            built.symbol
        );
        for link in &built.record.links {
            assert!(link.verdict.is_established(), "{}: {link:?}", built.symbol);
            assert!(
                !link.relation.is_empty() && !link.check.is_empty() && !link.model.is_empty(),
                "{}: {}",
                built.symbol,
                link.name
            );
            if link.stage == LinkStage::PassRun {
                *pass_runs.entry(link.name.clone()).or_default() += 1;
            }
        }
        eprintln!(
            "COMPOSED_TRANSITION {} links={} pass_runs={} strength={}",
            built.symbol,
            composed.links,
            composed.pass_runs,
            composed.strength.as_str()
        );
    }
    eprintln!("validated optimizer runs in the chains: {pass_runs:?}");
    assert!(
        pass_runs.values().sum::<usize>() >= 4,
        "the corpus must put optimizer runs into chains: {pass_runs:?}"
    );
}

/// Recording a chain observes; it never changes an emitted byte.
#[test]
fn recording_never_changes_the_emitted_object() {
    let mut sources: Vec<(String, String, String)> = KERNELS
        .iter()
        .map(|k| (k.name.to_string(), k.functy.to_string(), k.body.to_string()))
        .collect();
    sources.extend(
        OUT_OF_DOMAIN
            .iter()
            .map(|(n, f, b)| (n.to_string(), f.to_string(), b.to_string())),
    );
    for (name, functy, body) in &sources {
        for level in LEVELS {
            let symbol = format!("{name}_{}", level_tag(level));
            let module = module(&symbol, functy, body);
            let lir = lir(&module);
            let object = |policy| {
                let pipeline = Pipeline::new(PipelineConfig {
                    opt_level: level,
                    target_triple: native_host::TRIPLE.into(),
                    ..PipelineConfig::default()
                })
                .with_composed_transitions(policy);
                let (function, metrics) = prepare(&pipeline, &module, &lir);
                assert_eq!(
                    metrics.composed_transition.is_some(),
                    policy == ComposedTransitionPolicy::Record
                );
                pipeline
                    .compile_module_with_globals(std::slice::from_ref(&function), &[])
                    .expect("object")
            };
            assert_eq!(
                object(ComposedTransitionPolicy::Off),
                object(ComposedTransitionPolicy::Record),
                "{symbol}: recording changed the object"
            );
        }
    }
}

/// Outside the legalization check's domain a record says why, links
/// nothing and is not required by a proof-required route.
#[test]
fn functions_outside_the_domain_are_named_and_not_required() {
    for (name, functy, body) in OUT_OF_DOMAIN {
        for level in LEVELS {
            let module = module(name, functy, body);
            let lir = lir(&module);
            let (_, metrics) = prepare(&proof_pipeline(level), &module, &lir);
            let record = metrics.composed_transition.expect("a record");
            assert!(!record.in_legalization_domain(), "{name} {level:?}");
            assert!(record.links.is_empty(), "{name}: no link is paid for");
            let why = record.not_composed.as_ref().expect("a reason");
            assert_eq!(why.stage, LinkStage::Legalization);
            assert!(
                why.reason.starts_with("unsupported affine TrustIR"),
                "{name}: {}",
                why.reason
            );
            assert_eq!(require_composition(name, Some(&record)), Ok(None));
        }
    }
    // A preparation without a TrustIR source has nothing to start from.
    let module = module(ADD.name, ADD.functy, ADD.body);
    let (_, metrics) = proof_pipeline(OptLevel::O2)
        .prepare_function_with_metrics(&lir(&module), None)
        .expect("preparation");
    let record = metrics.composed_transition.expect("a record");
    assert!(
        record
            .not_composed
            .as_ref()
            .is_some_and(|why| why.reason.contains("no TrustIR source"))
    );
}

fn assert_refused(record: &TransitionRecord, class: &str, what: &str) -> CompositionRefusal {
    let refusal = record
        .compose()
        .expect_err(&format!("{what}: the composition must refuse"));
    assert_eq!(refusal.class(), class, "{what}: {refusal}");
    assert!(
        refusal.to_string().starts_with("[TCG-COMPOSED-TRANSITION]"),
        "{refusal}"
    );
    refusal
}

/// Real records corrupted after the fact: each dropped link, each swapped
/// internal interface and each flipped published byte is refused by name.
#[test]
fn corruption_controls_on_real_records_are_refused_by_name() {
    let mut controls = 0usize;
    for built in corpus() {
        let links = built.record.links.len();
        for index in 0..links {
            let mut dropped = built.record.clone();
            let link = dropped.links.remove(index);
            let what = format!("{} without link {index} `{}`", built.symbol, link.name);
            let refusal = dropped.compose().expect_err(&what);
            match link.stage {
                LinkStage::PassRun => assert_eq!(refusal.class(), "interface-mismatch", "{what}"),
                stage => assert!(
                    matches!(&refusal, CompositionRefusal::MissingLink { stage: missing, .. } if *missing == stage)
                        || refusal.class() == "interface-mismatch",
                    "{what}: {refusal}"
                ),
            }
            controls += 1;
        }
        for index in 0..links - 1 {
            for end in ["to", "from"] {
                let mut swapped = built.record.clone();
                let link = if end == "to" {
                    &mut swapped.links[index].to
                } else {
                    &mut swapped.links[index + 1].from
                };
                link.digest[31] ^= 0x01;
                let refusal = assert_refused(
                    &swapped,
                    "interface-mismatch",
                    &format!("{} boundary {index} {end}", built.symbol),
                );
                assert!(
                    matches!(refusal, CompositionRefusal::InterfaceMismatch { index: at, .. } if at == index)
                );
                controls += 1;
            }
        }
        // A byte of the published function changed after the last link.
        let composed = built.record.compose().expect("composes");
        let len = composed.terminal_len.expect("an encoding length") as usize;
        let published = trust_cg_codegen::composed_transition::object_function_bytes(
            &built.object,
            &built.symbol,
            len as u64,
        )
        .expect("the object's bytes");
        assert_eq!(bytes_interface(&published), composed.terminal);
        let start = built
            .object
            .windows(len)
            .position(|window| window == published.as_slice())
            .expect("the object holds the function's bytes");
        for offset in 0..len {
            let mut object = built.object.clone();
            object[start + offset] ^= 0x04;
            let records = [(built.symbol.as_str(), Some(&built.record))];
            let refusal = require_object_publication(&object, &records)
                .expect_err("a flipped byte after the last link");
            assert_eq!(
                refusal.class(),
                "published-bytes-mismatch",
                "{}",
                built.symbol
            );
            controls += 1;
        }
    }
    eprintln!("corruption controls refused: {controls}");
    assert!(controls > 500, "{controls}");
}

/// Rewrites the immediate of the first `ADD #imm` (the returned value's
/// `a + 5`): a change of the function's result.
struct BumpAddend {
    report: bool,
}

impl MachinePass for BumpAddend {
    fn name(&self) -> &str {
        if self.report {
            "evil-addend-bump"
        } else {
            "silent-addend-bump"
        }
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        for inst in &mut func.insts {
            if inst.opcode == AArch64Opcode::AddRI
                && let Some(MachOperand::Imm(value)) = inst.operands.get_mut(2)
            {
                *value += 1;
                return self.report;
            }
        }
        panic!("the fixture adds an immediate");
    }
}

/// An unvalidated rewrite between two links breaks the chain by name:
/// real AOT profile instrumentation, and passes that change the returned
/// value (reported and silent) on the real raw selection.
#[test]
fn corruption_an_unvalidated_rewrite_is_refused_by_name() {
    let kernel = &AFFINE;
    for level in LEVELS {
        let symbol = format!("{}_{}", kernel.name, level_tag(level));
        let module = module(&symbol, kernel.functy, kernel.body);
        let lir = lir(&module);
        // Instrumentation runs between the optimizer and allocation, and no
        // validator covers it.
        let sink = Arc::new(Mutex::new(trust_cg_opt::pgo::CounterMap::new()));
        let instrumented = proof_pipeline(level).with_profile_generate_sink(sink);
        let (_, metrics) = prepare(&instrumented, &module, &lir);
        let record = metrics.composed_transition.expect("a record");
        let refusal = assert_refused(&record, "interface-mismatch", &symbol);
        assert!(
            matches!(&refusal, CompositionRefusal::InterfaceMismatch { right_name, .. } if right_name == "post-ra-value-flow"),
            "{symbol}: {refusal}"
        );

        // A pass that rewrites the returned value's addend, run through a
        // pass manager on the real raw selection after the real legalization
        // and selection.
        let (_, metrics) = prepare(&proof_pipeline(level), &module, &lir);
        let real = metrics.composed_transition.expect("a record");
        for report in [true, false] {
            let mut raw = proof_pipeline(OptLevel::O0)
                .select_ir_function(&lir)
                .expect("selection");
            assert_eq!(real.links[1].to, mach_function_interface(&raw));
            let mut manager = PassManager::new()
                .with_pass(Box::new(BumpAddend { report }))
                .with_pass_validation(PassValidationConfig::enforce());
            manager.set_transition_digest(Some(mach_function_interface_digest));
            let stats = manager.run_once_with_stats(&mut raw);
            let mut record = TransitionRecord::new(&symbol);
            record.links.extend(real.links[..2].iter().cloned());
            // The production mapping from a transition to its link.
            record.links.extend(
                stats
                    .pass_validation
                    .transitions
                    .into_iter()
                    .map(pass_run_link),
            );
            record.links.extend(real.links[2..].iter().cloned());
            let refusal = assert_refused(&record, "link-not-established", &symbol);
            let expected = BumpAddend { report }.name().to_string();
            assert!(
                matches!(&refusal, CompositionRefusal::LinkNotEstablished { index: 2, name, stage: LinkStage::PassRun, outcome, .. }
                    if *name == expected && outcome == if report { "unproved" } else { "refuted" }),
                "{symbol} report={report}: {refusal}"
            );
        }
    }
}

/// The JIT publishes exactly the composed bytes of a composing function.
#[test]
fn the_jit_publishes_exactly_the_composed_bytes() {
    use trust_cg_codegen::jit::{JitCompiler, JitConfig};
    for built in corpus() {
        let composed = built.record.compose().expect("composes");
        let jit = JitCompiler::new(JitConfig {
            opt_level: OptLevel::O2,
            verify: false,
            ..JitConfig::default()
        });
        let buffer = jit
            .compile_raw(std::slice::from_ref(&built.function), &Default::default())
            .unwrap_or_else(|error| panic!("{}: JIT: {error}", built.symbol));
        let (_, range) = buffer
            .function_ranges()
            .iter()
            .find(|(name, _)| *name == built.function.name)
            .cloned()
            .expect("a range");
        let published = &buffer.code_slice()[range.start as usize..range.end as usize];
        composed
            .check_published(published)
            .unwrap_or_else(|refusal| panic!("{}: {refusal}", built.symbol));
        let mut mutated = published.to_vec();
        mutated[0] ^= 0x01;
        assert!(composed.check_published(&mutated).is_err());
    }
}

/// The proof-required routes (`--emit-proofs` objects through
/// `Compiler::compile`, the proof-required JIT through
/// `Compiler::compile_module_to_jit`) require an in-domain function's
/// composition right after preparation, before any certificate is generated
/// or promoted, so this row is decided on every host:
///
/// * AOT profile instrumentation (real, between the optimizer and
///   allocation, no validator) is refused by composition on both routes;
/// * untouched, neither route refuses by composition: it publishes with a
///   composing record and counts one composed publication, or proof
///   promotion refuses it afterwards (this host's proof tools refuse the
///   frame's opcodes), never anything else.
///
/// The byte binding after publication is driven through the routes by the
/// crate's unit test `proof_required_routes_bind_compositions_to_their_publications`.
#[test]
// The big `Err` is the compiler's own public error type.
#[allow(clippy::result_large_err)]
fn proof_required_routes_require_the_composition_before_promotion() {
    use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
    let kernel = &ADD;
    let module = module(kernel.name, kernel.functy, kernel.body);
    let compiler = || {
        Compiler::new(CompilerConfig {
            opt_level: OptLevel::O2,
            emit_proofs: true,
            parallel: false,
            ..CompilerConfig::default()
        })
        .with_codegen_license(permit_unlicensed())
    };
    let route = |compiler: Compiler, jit: bool| {
        if jit {
            compiler
                .compile_module_to_jit(&module, &Default::default())
                .map(|result| {
                    (
                        result.metrics.composed_transitions,
                        result.metrics.composed_publications,
                    )
                })
        } else {
            compiler.compile(&module).map(|result| {
                (
                    result.metrics.composed_transitions,
                    result.metrics.composed_publications,
                )
            })
        }
    };
    for jit in [false, true] {
        let sink = Arc::new(Mutex::new(trust_cg_opt::pgo::CounterMap::new()));
        match route(compiler().with_profile_generate(sink), jit) {
            Err(CompileError::ComposedTransitionRefused { refusal, .. }) => assert!(
                matches!(&*refusal, CompositionRefusal::InterfaceMismatch { right_name, .. } if right_name == "post-ra-value-flow"),
                "jit={jit}: {refusal}"
            ),
            other => panic!("jit={jit}: instrumentation must be refused by composition: {other:?}"),
        }
        match route(compiler(), jit) {
            Ok((records, publications)) => {
                assert_eq!(records.len(), 1, "jit={jit}");
                records[0].compose().expect("a published function composes");
                assert_eq!(publications, 1, "jit={jit}: the binding ran");
                eprintln!("route jit={jit}: published with a composing record");
            }
            Err(CompileError::ComposedTransitionRefused { refusal, .. }) => {
                panic!("jit={jit}: a composing function was refused by composition: {refusal}")
            }
            Err(error @ CompileError::ProofPromotionRejected { .. }) => {
                eprintln!("route jit={jit}: composed, then refused at proof promotion: {error}")
            }
            Err(other) => panic!("jit={jit}: unexpected refusal: {other}"),
        }
    }
}

const DRIVER_HEAD: &str = r#"
#include <stdint.h>
#include <stdio.h>
static int bad = 0;
static uint64_t word(uint64_t* s) {
  *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17;
  switch (*s % 9) {
    case 0: return 0; case 1: return ~0ull; case 2: return 1ull << 63;
    case 3: return (1ull << 63) - 1; case 4: return 0x80000000ull; case 5: return 0x7fffffffull;
    default: return *s;
  }
}
"#;

/// The proof-grade objects agree with the C references natively.
#[test]
fn proof_grade_objects_match_the_c_reference_natively() {
    use std::fmt::Write as _;
    use std::process::Command;
    let built = corpus();
    let dir = fresh_dir::create("trust_cg_ct_");
    let mut objects = Vec::new();
    for b in &built {
        let path = dir.join(format!("{}.o", b.symbol));
        std::fs::write(&path, &b.object).expect("write object");
        objects.push(path);
    }
    let mut c = String::from(DRIVER_HEAD);
    for kernel in KERNELS {
        let (t, r) = (kernel.c_param, kernel.c_result);
        let _ = writeln!(
            c,
            "static {r} r_{n}({t} a, {t} b) {{ return {e}; }}",
            n = kernel.name,
            e = kernel.c_reference
        );
        for level in LEVELS {
            let _ = writeln!(c, "{r} {}_{}({t}, {t});", kernel.name, level_tag(level));
        }
    }
    c.push_str("int main(void) {\n  uint64_t s = 0x9e3779b97f4a7c15ull;\n  long calls = 0;\n");
    c.push_str("  for (int round = 0; round < 4096; round++) {\n");
    c.push_str("    uint64_t x = word(&s), y = word(&s);\n");
    c.push_str("    if (round % 5 == 0) y = x;\n");
    for kernel in KERNELS {
        let t = kernel.c_param;
        for level in LEVELS {
            let _ = writeln!(
                c,
                "    if ((uint64_t){n}_{l}(({t})x, ({t})y) != (uint64_t)r_{n}(({t})x, ({t})y)) {{ printf(\"MISMATCH {n}_{l} %llx %llx\\n\", (unsigned long long)x, (unsigned long long)y); bad = 1; }} calls++;",
                n = kernel.name,
                l = level_tag(level)
            );
        }
    }
    c.push_str("  }\n  printf(\"composed-transition native rows: %s (%ld calls)\\n\", bad ? \"MISMATCH\" : \"all equal\", calls);\n  return bad;\n}\n");
    let driver = dir.join("driver.c");
    let binary = dir.join("composed_transition_rows");
    std::fs::write(&driver, &c).expect("write driver");
    let link = Command::new(native_host::C_COMPILER)
        .arg("-O1")
        .arg(&driver)
        .args(&objects)
        .args(native_host::link_hardening_args())
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run the linker");
    assert!(
        link.status.success(),
        "link:\n{}\n{c}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&binary).output().expect("run the rows");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "native rows failed:\n{stdout}");
    assert!(stdout.contains("all equal"), "{stdout}");
    eprintln!("{} objects on {}: {stdout}", built.len(), native_host::HOST);
}

/// Census of the whole-body owner's family corpus under a proof-grade
/// preparation at O0-O3: each function's record is classified, and every
/// function in the legalization domain must compose, so the proof-required
/// routes' requirement refuses none of them. (Measured 2026-10-14: none of
/// the 88 compiles is in the domain; their sources use U64/Boolean
/// connectives, shifts and nested selects the affine check does not admit,
/// so no TrustIR-to-bytes claim exists for them.)
#[test]
fn census_of_the_whole_body_families() {
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for case in body_cases::CASES {
        let module = body_cases::module(case);
        let lir = body_cases::lir(&module);
        for level in LEVELS {
            let (_, metrics) = prepare(&proof_pipeline(level), &module, &lir);
            let record = metrics.composed_transition.expect("a record");
            let key = match require_composition(&lir.name, Some(&record)) {
                Ok(Some(_)) => "composed".to_string(),
                Ok(None) => format!(
                    "not-covered: {}",
                    record
                        .not_composed
                        .as_ref()
                        .map(|why| why.reason.chars().take(60).collect::<String>())
                        .unwrap_or_default()
                ),
                Err(refusal) => panic!(
                    "{} {level:?}: an in-domain function does not compose: {refusal}",
                    lir.name
                ),
            };
            *counts.entry(key).or_default() += 1;
        }
    }
    for (key, count) in &counts {
        eprintln!("COMPOSED_TRANSITION_CENSUS whole-body-families {key}: {count}");
    }
    let total: usize = counts.values().sum();
    assert_eq!(total, body_cases::CASES.len() * LEVELS.len());
}
