// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Census of the proof-required AArch64 JIT (ledger L11-P11).
//!
//! Every shape of the corpora this repository maintains for the verifying
//! JIT goes through the public proof-required route
//! (`CompilerConfig { emit_proofs: true, .. }`, which resolves to
//! `JitValidationMode::AlwaysVerify`) on the host's own triple, at O0 to O3:
//!
//! * `a64-body`: the 22 families of the frameless whole-body owner
//!   (`tests/common/source_bound_body_cases.rs`, L09-P6);
//! * `arith`: the 160-row source-bound arithmetic matrix of
//!   `jit_source_bound_arithmetic` (ten shapes, four integer types);
//! * `fixture`: the identity, ADD and constant leaves of the fail-closed
//!   policy and custody campaigns;
//! * `memory`: the ten load/store leaves of `aarch64_memory_source_binding`
//!   (L07-P2);
//! * `trap`: division, remainder, shift and overflow bodies whose guards
//!   lower to trap carriers (L04-P12);
//! * `call`: calling frames (an internal call, an external call through a
//!   veneer, a value live across a call, two calls);
//! * `beat-llvm`: every leaf function (no call, no global address) of the
//!   18 beat-llvm programs' committed TrustIR modules.
//!
//! Each compile either publishes or is refused. A refusal is named by its
//! class: the reason of the FIRST uncovered row of the emitted opcode
//! inventory (statistical evidence, an instruction-derived obligation, an
//! unreplayed source-bound theorem, an uncredited memory or trap row, an
//! E0.2 copy/constant, ...), or the error variant for a refusal before the
//! inventory. Every publication must carry a verified certificate for every
//! function and the installed-artifact replay (L11-P2) of every function,
//! and, where the shape has a reference, execute correctly over its input
//! grid. The per-family outcome is pinned exactly for the two proof tool
//! pairs this host measured (`measured_tools`); any other pair is held to the
//! invariants only. Lines `JIT_PROOF_CENSUS` give each compile and
//! `JIT_PROOF_CENSUS_SUMMARY` each family; `TCG_JIT_PROOF_CENSUS_OUT=<dir>`
//! also writes them as JSON lines, and `TCG_TRACE_OPCODE_INVENTORY=1` prints
//! every blocking row of every refused function. The census runs only when
//! `TCG_JIT_PROOF_CENSUS=1` is set (see [`on_big_stack`]); the record is
//! `reports/2026-10-12-jit-proof-coverage-census`. Execution here is
//! testing, not proof.
#![cfg(all(target_arch = "aarch64", feature = "verify"))]
// Test fixture: the big `Err` is the compiler's own public error type.
#![allow(clippy::result_large_err)]

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;

use trust_cg_codegen::compiler::{
    CompileError, Compiler, CompilerConfig, JitCompilationResult, JitValidationMode,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::inst::BinOp;
use trust_ir::{Inst, ProofAnnotation, Ty};
use trust_ir_build::ModuleBuilder;

#[path = "common/source_bound_body_cases.rs"]
mod cases;
#[path = "common/source_bound_proof_tools.rs"]
mod source_bound_proof_tools;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// The two tool pairs whose census this file pins.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tools {
    /// The installed Trust package 9192's AY (0.26.0 build 9624) with the
    /// managed Clean 0.9.0 (package 8606) discovery falls back to.
    Package9192,
    /// The overlay of AY `2657db47c` (build 10123) and Clean `ed21fee39`.
    Overlay,
}

const PACKAGE_9192_AY: &str = "40e852cc7fa3a3289f17a47b5a8d6d1a5218177b4a95087538ff2c3d702ac7a8";
const MANAGED_CLEAN_8606: &str = "9c594e838ff7e73815977c2d675238828f82417e77986abfe38d75b8ab060e16";
const OVERLAY_AY: &str = "b37fa549fa0712cc6283f0675d029f2a802641d1c61c0a6a329ed69faae3a9a8";
const OVERLAY_CLEAN: &str = "ad10bed671a8bf8110b3abefd4f72d6b13380ddba308aa1c58181867a03fac96";

fn measured_tools() -> Option<Tools> {
    let ay = trust_cg_verify::ay_identity::resolve_for_process().ok()?;
    let (_, clean) = trust_cg_verify::obligation_cert_store::resolve_proof_checker().ok()?;
    match (ay.sha256(), clean.as_str()) {
        (PACKAGE_9192_AY, MANAGED_CLEAN_8606) => Some(Tools::Package9192),
        (OVERLAY_AY, OVERLAY_CLEAN) => Some(Tools::Overlay),
        _ => None,
    }
}

/// What one compile did.
#[derive(Clone, Debug)]
enum Outcome {
    /// Published; `calls` native calls agreed with the reference (0 when the
    /// shape has none); the installed-artifact replay checked
    /// `replayed_words` installed words.
    Published { calls: usize, replayed_words: usize },
    /// Refused, by `class`; `first` is the first uncovered row's opcode and
    /// `listed` every uncovered opcode (empty outside the inventory).
    Refused {
        class: String,
        first: String,
        listed: Vec<String>,
    },
}

#[derive(Clone, Debug)]
struct Row {
    family: &'static str,
    shape: String,
    level: OptLevel,
    outcome: Outcome,
}

/// The refusal classes, named by the stable reason each uncovered row
/// carries (the constants the verifier owns), in priority order.
fn row_class(reason: &str) -> &'static str {
    use trust_cg_verify::function_verifier as fv;
    let classes: [(&str, &'static str); 13] = [
        (
            trust_cg_verify::source_bound_a64_body::A64_BODY_NEEDS_REPLAY,
            "body-theorem-unreplayed",
        ),
        (
            "source-bound frame needs independently replayed proof",
            "frame-theorem-unreplayed",
        ),
        (
            "source-bound arithmetic needs independently replayed proof",
            "alu-theorem-unreplayed",
        ),
        (
            trust_cg_verify::aarch64_memory_source_binding::SOURCE_BOUND_MEMORY_NOT_CREDITED,
            "memory-row-uncredited",
        ),
        (
            trust_cg_verify::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT,
            "trap-row-uncredited",
        ),
        (fv::MEMORY_EFFECT_IS_NOT_CREDIT, "memory-effect-only"),
        (fv::NEON_LANE_EFFECT_IS_NOT_CREDIT, "neon-lane-effect-only"),
        (
            fv::INSTRUCTION_DERIVED_IS_NOT_CREDIT,
            "instruction-derived-only",
        ),
        (fv::REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT, "registry-name-only"),
        (fv::STATISTICAL_EVIDENCE_IS_NOT_CREDIT, "statistical-only"),
        ("no proof mapping for opcode", "no-proof-mapping"),
        ("Unknown:", "solver-unknown"),
        ("Failed", "refuted"),
    ];
    classes
        .iter()
        .find(|(needle, _)| reason.contains(needle))
        .map_or("other-row", |(_, class)| class)
}

/// The E0.2 copy/constant opcodes (no credit route outside their owners).
fn is_copy_or_constant(opcode: &str) -> bool {
    matches!(
        opcode,
        "AArch64::Movz"
            | "AArch64::Movn"
            | "AArch64::Movk"
            | "AArch64::MovI"
            | "AArch64::MovR"
            | "AArch64::MOVWrr"
            | "AArch64::MOVXrr"
    )
}

/// Name a refusal: `(class, first opcode, listed opcodes)`.
fn classify(error: &CompileError) -> (String, String, Vec<String>) {
    match error {
        CompileError::ProofPromotionRejected { reason, .. } => {
            let reason = trust_cg_verify::ay_bridge::without_solver_refusal_note(reason);
            let listed: Vec<String> = reason
                .split_once("distinct opcode(s) [")
                .and_then(|(_, rest)| rest.split_once(']'))
                .map(|(list, _)| list.split(", ").map(str::to_owned).collect())
                .unwrap_or_default();
            if listed.is_empty() {
                let class = if reason.contains("has no non-vacuous proof-grade machine-IR") {
                    "certificate-gate"
                } else if reason.contains("exception") || reason.contains("unwind") {
                    "exception-tables"
                } else {
                    "promotion-other"
                };
                return (class.to_owned(), String::new(), listed);
            }
            let first_part = reason
                .split_once("; first in ")
                .map_or("", |(_, rest)| rest);
            let first = first_part
                .split_once(" is ")
                .and_then(|(_, rest)| rest.split(' ').next())
                .unwrap_or("")
                .to_owned();
            let function = first_part
                .split_once('[')
                .map_or("", |(function, _)| function);
            let first = format!("{function}:{first}");
            let class = if listed.iter().all(|opcode| is_copy_or_constant(opcode)) {
                "e02-copy-constant".to_owned()
            } else {
                row_class(first_part).to_owned()
            };
            (class, first, listed)
        }
        CompileError::Jit(inner) => {
            let debug = format!("{inner:?}");
            let name: String = debug
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            (format!("jit:{name}"), String::new(), Vec::new())
        }
        other => {
            let debug = format!("{other:?}");
            let name: String = debug
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            (format!("compile:{name}"), String::new(), Vec::new())
        }
    }
}

fn compiler(level: OptLevel) -> Compiler {
    Compiler::new(CompilerConfig {
        opt_level: level,
        emit_proofs: true,
        parallel: false,
        ..CompilerConfig::jit_fast(Target::Aarch64)
    })
}

/// Publication invariants: the proof-required mode, every function's
/// certificate verified, and the installed-artifact replay (L11-P2) of every
/// published function over the image the seal hashed. Returns the installed
/// words the replay compared.
fn check_publication(label: &str, result: &JitCompilationResult) -> usize {
    let validation = result
        .validation
        .as_ref()
        .unwrap_or_else(|| panic!("{label}: a proof-required JIT records its validation"));
    assert_eq!(validation.mode, JitValidationMode::AlwaysVerify, "{label}");
    assert!(validation.every_function_semantics_verified(), "{label}");
    for (name, _) in result.buffer.function_ranges() {
        let certificate = result
            .buffer
            .certificate(name)
            .unwrap_or_else(|| panic!("{label}: `{name}` has no certificate"));
        assert!(certificate.is_verified(), "{label}: `{name}` unverified");
    }
    let replay = result.buffer.installed_replay().unwrap_or_else(|| {
        panic!("{label}: a proof-required publication carries its installed-artifact replay")
    });
    assert!(
        replay.covers_exactly(
            result
                .buffer
                .function_ranges()
                .iter()
                .map(|(name, _)| name.as_str())
        ),
        "{label}: the replay covers every published function"
    );
    assert_eq!(
        replay.installed_image_sha256(),
        result.buffer.published_image_sha256(),
        "{label}"
    );
    replay.words_compared() + replay.branch_sites()
}

/// Compile one module and record the outcome; `run` executes a publication
/// and returns its number of checked native calls.
fn census_one(
    rows: &mut Vec<Row>,
    family: &'static str,
    shape: &str,
    level: OptLevel,
    module: &trust_ir::Module,
    externs: &HashMap<String, *const u8>,
    run: impl FnOnce(&JitCompilationResult) -> usize,
) {
    let label = format!("{family}/{shape}/{level:?}");
    let outcome = match compiler(level)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, externs)
    {
        Ok(result) => {
            let replayed_words = check_publication(&label, &result);
            Outcome::Published {
                calls: run(&result),
                replayed_words,
            }
        }
        Err(error) => {
            let (class, first, listed) = classify(&error);
            Outcome::Refused {
                class,
                first,
                listed,
            }
        }
    };
    let line = match &outcome {
        Outcome::Published {
            calls,
            replayed_words,
        } => format!("outcome=publish calls={calls} replayed_words={replayed_words}"),
        Outcome::Refused {
            class,
            first,
            listed,
        } => format!(
            "outcome=refuse class={class} first={first} listed=[{}]",
            listed.join(",")
        ),
    };
    println!("JIT_PROOF_CENSUS family={family} shape={shape} level={level:?} {line}");
    rows.push(Row {
        family,
        shape: shape.to_owned(),
        level,
        outcome,
    });
}

/// Per-family totals: `(compiles, published, refusals by class)`.
struct Summary {
    compiles: usize,
    published: usize,
    calls: usize,
    replayed_words: usize,
    by_class: BTreeMap<String, usize>,
}

fn summarize(family: &str, rows: &[Row]) -> Summary {
    let mut summary = Summary {
        compiles: 0,
        published: 0,
        calls: 0,
        replayed_words: 0,
        by_class: BTreeMap::new(),
    };
    for row in rows.iter().filter(|row| row.family == family) {
        summary.compiles += 1;
        match &row.outcome {
            Outcome::Published {
                calls,
                replayed_words,
            } => {
                summary.published += 1;
                summary.calls += calls;
                summary.replayed_words += replayed_words;
            }
            Outcome::Refused { class, .. } => {
                *summary.by_class.entry(class.clone()).or_default() += 1;
            }
        }
    }
    let mut classes = String::new();
    for (class, count) in &summary.by_class {
        let _ = write!(classes, "{class}:{count},");
    }
    println!(
        "JIT_PROOF_CENSUS_SUMMARY family={family} compiles={} published={} refused={} calls={} \
         replayed_words={} classes=[{}] tools={}",
        summary.compiles,
        summary.published,
        summary.compiles - summary.published,
        summary.calls,
        summary.replayed_words,
        classes.trim_end_matches(','),
        source_bound_proof_tools::resolved_proof_tools()
    );
    write_json(family, rows);
    summary
}

fn write_json(family: &str, rows: &[Row]) {
    let Some(dir) = std::env::var_os("TCG_JIT_PROOF_CENSUS_OUT") else {
        return;
    };
    let mut text = String::new();
    for row in rows.iter().filter(|row| row.family == family) {
        let (outcome, class, first, listed, calls) = match &row.outcome {
            Outcome::Published { calls, .. } => ("publish", "", "", Vec::new(), *calls),
            Outcome::Refused {
                class,
                first,
                listed,
            } => ("refuse", class.as_str(), first.as_str(), listed.clone(), 0),
        };
        let listed: Vec<String> = listed.iter().map(|op| format!("\"{op}\"")).collect();
        let _ = writeln!(
            text,
            "{{\"family\":\"{}\",\"shape\":\"{}\",\"level\":\"{:?}\",\"outcome\":\"{outcome}\",\
             \"class\":\"{class}\",\"first\":\"{first}\",\"listed\":[{}],\"calls\":{calls}}}",
            row.family,
            row.shape,
            row.level,
            listed.join(",")
        );
    }
    let path = std::path::Path::new(&dir).join(format!("{family}.jsonl"));
    std::fs::write(&path, text).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
}

/// Run one census family on a large stack, only when requested
/// (`TCG_JIT_PROOF_CENSUS=1`): with the installed package's AY every framed
/// shape waits for its `unknown` frame answer, so the full census takes
/// hours there. Unrequested, it prints SKIP and supplies no evidence; it is
/// a measurement, not a floor target.
fn on_big_stack(f: impl FnOnce() + Send + 'static) {
    if std::env::var_os("TCG_JIT_PROOF_CENSUS").is_none() {
        println!("SKIP JIT_PROOF_CENSUS (set TCG_JIT_PROOF_CENSUS=1 to measure)");
        return;
    }
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .expect("spawn census thread")
        .join()
        .expect("census thread panicked");
}

// ---------------------------------------------------------------------------
// a64-body
// ---------------------------------------------------------------------------

#[test]
fn census_whole_body_families() {
    on_big_stack(|| {
        let mut rows = Vec::new();
        for case in cases::CASES {
            let module = cases::module(case);
            let name = cases::symbol(case);
            for level in LEVELS {
                census_one(
                    &mut rows,
                    "a64-body",
                    case.name,
                    level,
                    &module,
                    &HashMap::new(),
                    |result| {
                        let mut calls = 0;
                        for input in cases::grid(case.sig) {
                            let expected = (case.reference)(&input);
                            let got = cases::call(&result.buffer, &name, case.sig, &input);
                            if let Some(expected) = expected {
                                assert_eq!(got, expected, "{} {level:?} {input:?}", case.name);
                                calls += 1;
                            }
                        }
                        calls
                    },
                );
            }
        }
        let summary = summarize("a64-body", &rows);
        assert_eq!(summary.compiles, cases::CASES.len() * LEVELS.len());
        pin("a64-body", &summary);
    });
}

// ---------------------------------------------------------------------------
// arith
// ---------------------------------------------------------------------------

const ARITH_SHAPES: [&str; 10] = [
    "add",
    "sub",
    "add_small",
    "add_shifted",
    "sub_small",
    "sub_shifted",
    "add_negative",
    "sub_negative",
    "chain",
    "double",
];

fn arith_module(ty: Ty, shape: &str) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("source_bound_arithmetic");
    let signature = builder.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
    let mut f = builder.function("calculate", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, ty.clone());
    let b = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    let constant = |value: i128| match ty {
        Ty::U32 => value as u32 as i128,
        Ty::U64 => value as u64 as i128,
        _ => value,
    };
    let result = match shape {
        "add" => f.add(ty.clone(), a, b),
        "sub" => f.sub(ty.clone(), a, b),
        "double" => f.add(ty.clone(), a, a),
        "chain" => {
            let c = f.iconst(ty.clone(), 4096);
            let d = f.iconst(ty.clone(), constant(-3));
            let v = f.add(ty.clone(), a, c);
            let v = f.sub(ty.clone(), v, b);
            f.add(ty.clone(), v, d)
        }
        _ => {
            let value = if shape.ends_with("small") {
                4095
            } else if shape.ends_with("shifted") {
                4096
            } else {
                -1
            };
            let c = f.iconst(ty.clone(), constant(value));
            if shape.starts_with("add") {
                f.add(ty.clone(), a, c)
            } else {
                f.sub(ty.clone(), a, c)
            }
        }
    };
    f.ret(vec![result]);
    f.build();
    builder.build().expect("census module builds")
}

fn arith_expected(shape: &str, a: u64, b: u64) -> u64 {
    match shape {
        "add" => a.wrapping_add(b),
        "sub" => a.wrapping_sub(b),
        "double" => a.wrapping_add(a),
        "add_small" => a.wrapping_add(4095),
        "sub_small" => a.wrapping_sub(4095),
        "add_shifted" => a.wrapping_add(4096),
        "sub_shifted" => a.wrapping_sub(4096),
        "add_negative" => a.wrapping_sub(1),
        "sub_negative" => a.wrapping_add(1),
        "chain" => a.wrapping_add(4096).wrapping_sub(b).wrapping_sub(3),
        _ => unreachable!("closed source corpus"),
    }
}

#[test]
fn census_arithmetic_matrix() {
    on_big_stack(|| {
        let inputs = [
            0,
            1,
            4095,
            4096,
            u32::MAX as u64,
            1 << 32,
            i64::MAX as u64,
            u64::MAX,
        ];
        let mut rows = Vec::new();
        for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
            let narrow = matches!(ty, Ty::I32 | Ty::U32);
            for shape in ARITH_SHAPES {
                let module = arith_module(ty.clone(), shape);
                for level in LEVELS {
                    census_one(
                        &mut rows,
                        "arith",
                        &format!("{ty:?}/{shape}"),
                        level,
                        &module,
                        &HashMap::new(),
                        |result| {
                            let mut calls = 0;
                            for a in inputs {
                                for b in inputs {
                                    // SAFETY: the exact source ABI of
                                    // `calculate`; the buffer is live.
                                    let got = unsafe {
                                        if narrow {
                                            u64::from((result
                                                .buffer
                                                .get_fn_bound::<extern "C" fn(u32, u32) -> u32>(
                                                    "calculate",
                                                )
                                                .unwrap()
                                                .as_ref())(
                                                a as u32, b as u32
                                            ))
                                        } else {
                                            (result
                                                .buffer
                                                .get_fn_bound::<extern "C" fn(u64, u64) -> u64>(
                                                    "calculate",
                                                )
                                                .unwrap()
                                                .as_ref())(
                                                a, b
                                            )
                                        }
                                    };
                                    let mut want = arith_expected(shape, a, b);
                                    if narrow {
                                        want = u64::from(arith_expected(
                                            shape,
                                            u64::from(a as u32),
                                            u64::from(b as u32),
                                        )
                                            as u32);
                                    }
                                    assert_eq!(got, want, "{ty:?}/{shape}/{level:?} {a} {b}");
                                    calls += 1;
                                }
                            }
                            calls
                        },
                    );
                }
            }
        }
        let summary = summarize("arith", &rows);
        assert_eq!(summary.compiles, 160);
        pin("arith", &summary);
    });
}

// ---------------------------------------------------------------------------
// fixture
// ---------------------------------------------------------------------------

fn unary_module(
    name: &str,
    body: impl FnOnce(&mut trust_ir_build::FunctionBuilder<'_>, trust_ir::ValueId),
) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("census_fixture");
    let signature = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut f = builder.function(name, signature);
    let entry = f.create_block();
    let value = f.add_block_param(entry, Ty::I64);
    f.switch_to_block(entry);
    body(&mut f, value);
    f.build();
    builder.build().expect("census module builds")
}

fn call_i64(result: &JitCompilationResult, name: &str, value: i64) -> i64 {
    // SAFETY: every fixture here has the `(i64) -> i64` C ABI and the buffer
    // is live for the call.
    unsafe {
        (result
            .buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>(name)
            .unwrap()
            .as_ref())(value)
    }
}

const I64_GRID: [i64; 8] = [i64::MIN, i64::MIN + 1, -42, -1, 0, 1, 42, i64::MAX];

#[test]
fn census_fixtures() {
    on_big_stack(|| {
        let mut rows = Vec::new();
        let identity = unary_module("identity_fn", |f, v| f.ret(vec![v]));
        let answer = unary_module("answer", |f, _| {
            let c = f.iconst(Ty::I64, 42);
            f.ret(vec![c]);
        });
        let add = {
            let mut builder = ModuleBuilder::new("census_fixture");
            let signature = builder.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
            let mut f = builder.function("proof_required_add", signature);
            let entry = f.create_block();
            let a = f.add_block_param(entry, Ty::I64);
            let b = f.add_block_param(entry, Ty::I64);
            f.switch_to_block(entry);
            let sum = f.add(Ty::I64, a, b);
            f.ret(vec![sum]);
            f.build();
            builder.build().expect("census module builds")
        };
        for level in LEVELS {
            census_one(
                &mut rows,
                "fixture",
                "identity",
                level,
                &identity,
                &HashMap::new(),
                |r| {
                    for v in I64_GRID {
                        assert_eq!(call_i64(r, "identity_fn", v), v);
                    }
                    I64_GRID.len()
                },
            );
            census_one(
                &mut rows,
                "fixture",
                "answer",
                level,
                &answer,
                &HashMap::new(),
                |r| {
                    for v in I64_GRID {
                        assert_eq!(call_i64(r, "answer", v), 42);
                    }
                    I64_GRID.len()
                },
            );
            census_one(
                &mut rows,
                "fixture",
                "add",
                level,
                &add,
                &HashMap::new(),
                |r| {
                    let mut calls = 0;
                    for a in I64_GRID {
                        for b in I64_GRID {
                            // SAFETY: `(i64, i64) -> i64` C ABI; live buffer.
                            let got = unsafe {
                                (r.buffer
                                    .get_fn_bound::<extern "C" fn(i64, i64) -> i64>(
                                        "proof_required_add",
                                    )
                                    .unwrap()
                                    .as_ref())(a, b)
                            };
                            assert_eq!(got, a.wrapping_add(b));
                            calls += 1;
                        }
                    }
                    calls
                },
            );
        }
        let summary = summarize("fixture", &rows);
        assert_eq!(summary.compiles, 12);
        pin("fixture", &summary);
    });
}

// ---------------------------------------------------------------------------
// memory
// ---------------------------------------------------------------------------

const MEMORY_SHAPES: [&str; 10] = [
    "load64",
    "load32",
    "load16",
    "load8",
    "load64_offset",
    "chase",
    "store64",
    "store8",
    "copy64",
    "swap64",
];

fn memory_module(shape: &str) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("memory_leaf");
    let (params, returns) = match shape {
        "load64" | "load64_offset" | "chase" => (vec![Ty::Ptr], vec![Ty::U64]),
        "load32" => (vec![Ty::Ptr], vec![Ty::U32]),
        "load16" => (vec![Ty::Ptr], vec![Ty::U16]),
        "load8" => (vec![Ty::Ptr], vec![Ty::U8]),
        "store64" => (vec![Ty::Ptr, Ty::U64], vec![]),
        "store8" => (vec![Ty::Ptr, Ty::U8], vec![]),
        "copy64" | "swap64" => (vec![Ty::Ptr, Ty::Ptr], vec![]),
        _ => unreachable!("closed shape set"),
    };
    let signature = builder.add_func_type(params.clone(), returns);
    let mut f = builder.function("leaf", signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        "load64" | "load32" | "load16" | "load8" => {
            let ty = match shape {
                "load64" => Ty::U64,
                "load32" => Ty::U32,
                "load16" => Ty::U16,
                _ => Ty::U8,
            };
            let v = f.load(ty, args[0]);
            f.ret(vec![v]);
        }
        "load64_offset" => {
            let p = f.gep_byte_offset(args[0], 16);
            let v = f.load(Ty::U64, p);
            f.ret(vec![v]);
        }
        "chase" => {
            let p = f.load(Ty::Ptr, args[0]);
            let q = f.gep_byte_offset(p, 8);
            let v = f.load(Ty::U64, q);
            f.ret(vec![v]);
        }
        "store64" => {
            f.store(Ty::U64, args[0], args[1]);
            f.ret(vec![]);
        }
        "store8" => {
            f.store(Ty::U8, args[0], args[1]);
            f.ret(vec![]);
        }
        "copy64" => {
            let v = f.load(Ty::U64, args[1]);
            f.store(Ty::U64, args[0], v);
            f.ret(vec![]);
        }
        _ => {
            let a = f.load(Ty::U64, args[0]);
            let b = f.load(Ty::U64, args[1]);
            f.store(Ty::U64, args[0], b);
            f.store(Ty::U64, args[1], a);
            f.ret(vec![]);
        }
    }
    f.build();
    builder.build().expect("census module builds")
}

/// Run a published memory leaf on live host memory; returns the calls made.
fn run_memory(shape: &str, result: &JitCompilationResult) -> usize {
    let buffer = &result.buffer;
    let cells: [u64; 4] = [
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
        0x8000_0000_0000_0001,
        42,
    ];
    // SAFETY: each arm uses the leaf's exact C ABI, the verifying JIT
    // published it, `buffer` is live and every pointer names live, aligned
    // host memory of at least the accessed width.
    unsafe {
        match shape {
            "load64" | "load32" | "load16" | "load8" => {
                let f = buffer
                    .get_fn_bound::<extern "C" fn(*const u64) -> u64>("leaf")
                    .unwrap();
                let mask = match shape {
                    "load64" => u64::MAX,
                    "load32" => u64::from(u32::MAX),
                    "load16" => u64::from(u16::MAX),
                    _ => u64::from(u8::MAX),
                };
                for cell in cells {
                    assert_eq!(f.as_ref()(&cell) & mask, cell & mask, "{shape}");
                }
                cells.len()
            }
            "load64_offset" => {
                let f = buffer
                    .get_fn_bound::<extern "C" fn(*const u64) -> u64>("leaf")
                    .unwrap();
                assert_eq!(f.as_ref()(cells.as_ptr()), cells[2]);
                1
            }
            "chase" => {
                let inner = [11u64, 42u64];
                let outer: *const u64 = inner.as_ptr();
                let f = buffer
                    .get_fn_bound::<extern "C" fn(*const *const u64) -> u64>("leaf")
                    .unwrap();
                assert_eq!(f.as_ref()(&outer), 42);
                1
            }
            "store64" | "store8" => {
                let f = buffer
                    .get_fn_bound::<extern "C" fn(*mut u64, u64)>("leaf")
                    .unwrap();
                let mut cell = u64::MAX;
                f.as_ref()(&mut cell, 0xfeed_beef_0bad_f00d);
                let want = if shape == "store64" {
                    0xfeed_beef_0bad_f00d
                } else {
                    // The low byte replaced, the other seven kept.
                    !0xff_u64 | 0x0d
                };
                assert_eq!(cell, want, "{shape}");
                1
            }
            "copy64" => {
                let (mut dst, src) = (0u64, u64::MAX - 7);
                let f = buffer
                    .get_fn_bound::<extern "C" fn(*mut u64, *const u64)>("leaf")
                    .unwrap();
                f.as_ref()(&mut dst, &src);
                assert_eq!(dst, u64::MAX - 7);
                1
            }
            _ => {
                let (mut a, mut b) = (1u64 << 63, 5u64);
                let f = buffer
                    .get_fn_bound::<extern "C" fn(*mut u64, *mut u64)>("leaf")
                    .unwrap();
                f.as_ref()(&mut a, &mut b);
                assert_eq!((a, b), (5, 1 << 63));
                1
            }
        }
    }
}

#[test]
fn census_memory_leaves() {
    on_big_stack(|| {
        let mut rows = Vec::new();
        for shape in MEMORY_SHAPES {
            let module = memory_module(shape);
            for level in LEVELS {
                census_one(
                    &mut rows,
                    "memory",
                    shape,
                    level,
                    &module,
                    &HashMap::new(),
                    |r| run_memory(shape, r),
                );
            }
        }
        let summary = summarize("memory", &rows);
        assert_eq!(summary.compiles, 40);
        pin("memory", &summary);
    });
}

// ---------------------------------------------------------------------------
// trap
// ---------------------------------------------------------------------------

const TRAP_SHAPES: [&str; 8] = [
    "udiv64",
    "sdiv64",
    "urem32",
    "udiv64_proven",
    "shl64",
    "shl64_proven",
    "sadd64_proven",
    "uadd32_proven",
];

fn trap_module(shape: &str) -> trust_ir::Module {
    let narrow = shape.ends_with("32") || shape.contains("32_");
    let ty = if narrow { Ty::U32 } else { Ty::U64 };
    let ty = if shape.starts_with('s') { Ty::I64 } else { ty };
    let mut builder = ModuleBuilder::new("census_trap");
    let signature = builder.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
    let mut f = builder.function("guarded", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, ty.clone());
    let b = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    let proven = |annotation: ProofAnnotation| {
        if shape.ends_with("_proven") {
            vec![annotation]
        } else {
            Vec::new()
        }
    };
    let (op, annotation) = match shape {
        s if s.starts_with("udiv") => (BinOp::UDiv, ProofAnnotation::DivNonZero),
        s if s.starts_with("sdiv") => (BinOp::SDiv, ProofAnnotation::DivNonZero),
        s if s.starts_with("urem") => (BinOp::URem, ProofAnnotation::DivNonZero),
        s if s.starts_with("shl") => (BinOp::Shl, ProofAnnotation::ShiftInRange),
        _ => (BinOp::Add, ProofAnnotation::NoOverflow),
    };
    let value = f.binop_proven(op, ty.clone(), a, b, proven(annotation));
    f.ret(vec![value]);
    f.build();
    builder.build().expect("census module builds")
}

/// Inputs inside every guard and the expected result.
fn trap_grid(shape: &str) -> Vec<(u64, u64, u64)> {
    match shape {
        "udiv64" | "udiv64_proven" => vec![(100, 7, 14), (u64::MAX, 1, u64::MAX), (5, u64::MAX, 0)],
        "sdiv64" => vec![
            (100, 7, 14),
            ((-100i64) as u64, 7, (-14i64) as u64),
            (i64::MIN as u64, 2, (i64::MIN / 2) as u64),
        ],
        "urem32" => vec![(100, 7, 2), (u64::from(u32::MAX), 10, 5)],
        "shl64" | "shl64_proven" => vec![(1, 63, 1 << 63), (3, 0, 3), (5, 2, 20)],
        "sadd64_proven" => vec![(1, 2, 3), ((-5i64) as u64, 3, (-2i64) as u64)],
        _ => vec![(1, 2, 3), (100, 200, 300)],
    }
}

#[test]
fn census_trap_bodies() {
    on_big_stack(|| {
        let mut rows = Vec::new();
        for shape in TRAP_SHAPES {
            let module = trap_module(shape);
            let narrow = shape.contains("32");
            for level in LEVELS {
                census_one(
                    &mut rows,
                    "trap",
                    shape,
                    level,
                    &module,
                    &HashMap::new(),
                    |r| {
                        let grid = trap_grid(shape);
                        for (a, b, want) in &grid {
                            // SAFETY: the exact `(T, T) -> T` C ABI of
                            // `guarded`; inputs stay inside every guard; live
                            // buffer.
                            let got = unsafe {
                                if narrow {
                                    u64::from((r
                                        .buffer
                                        .get_fn_bound::<extern "C" fn(u32, u32) -> u32>("guarded")
                                        .unwrap()
                                        .as_ref())(
                                        *a as u32, *b as u32
                                    ))
                                } else {
                                    (r.buffer
                                        .get_fn_bound::<extern "C" fn(u64, u64) -> u64>("guarded")
                                        .unwrap()
                                        .as_ref())(*a, *b)
                                }
                            };
                            assert_eq!(got, *want, "{shape}/{level:?} {a} {b}");
                        }
                        grid.len()
                    },
                );
            }
        }
        let summary = summarize("trap", &rows);
        assert_eq!(summary.compiles, TRAP_SHAPES.len() * LEVELS.len());
        pin("trap", &summary);
    });
}

// ---------------------------------------------------------------------------
// call
// ---------------------------------------------------------------------------

extern "C" fn census_external_twice(value: i64) -> i64 {
    value.wrapping_mul(2)
}

extern "C" fn census_external_identity(value: i64) -> i64 {
    value
}

const CALL_SHAPES: [&str; 4] = [
    "call_then_add",
    "call_external",
    "live_across_call",
    "two_calls",
];

/// One calling frame, `caller`, alone in its module: every callee is an
/// external host function bound through the extern table, so the census
/// measures the calling frame itself (a defined callee would be compiled
/// first and name its own refusal).
fn call_module(shape: &str) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("census_call");
    let unary = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let binary = builder.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let callee = if shape == "call_external" {
        builder.declare_function("census_external_twice", unary)
    } else {
        builder.declare_function("census_external_identity", unary)
    };
    let mut f = builder.function("caller", binary);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::I64);
    let b = f.add_block_param(entry, Ty::I64);
    f.switch_to_block(entry);
    let result = match shape {
        "call_then_add" | "call_external" => {
            let called = f.call(callee, vec![a]);
            f.add(Ty::I64, called, b)
        }
        "live_across_call" => {
            let sum = f.add(Ty::I64, a, b);
            let called = f.call(callee, vec![a]);
            f.add(Ty::I64, called, sum)
        }
        _ => {
            let first = f.call(callee, vec![a]);
            let second = f.call(callee, vec![b]);
            f.add(Ty::I64, first, second)
        }
    };
    f.ret(vec![result]);
    f.build();
    builder.build().expect("census module builds")
}

fn call_expected(shape: &str, a: i64, b: i64) -> i64 {
    match shape {
        "call_then_add" => a.wrapping_add(b),
        "call_external" => a.wrapping_mul(2).wrapping_add(b),
        "live_across_call" => a.wrapping_add(a.wrapping_add(b)),
        _ => a.wrapping_add(b),
    }
}

#[test]
fn census_calling_frames() {
    on_big_stack(|| {
        let mut rows = Vec::new();
        let mut externs: HashMap<String, *const u8> = HashMap::new();
        externs.insert(
            "census_external_twice".to_owned(),
            census_external_twice as *const u8,
        );
        externs.insert(
            "census_external_identity".to_owned(),
            census_external_identity as *const u8,
        );
        for shape in CALL_SHAPES {
            let module = call_module(shape);
            for level in LEVELS {
                census_one(&mut rows, "call", shape, level, &module, &externs, |r| {
                    let mut calls = 0;
                    for a in I64_GRID {
                        for b in I64_GRID {
                            // SAFETY: `(i64, i64) -> i64` C ABI; live buffer.
                            let got = unsafe {
                                (r.buffer
                                    .get_fn_bound::<extern "C" fn(i64, i64) -> i64>("caller")
                                    .unwrap()
                                    .as_ref())(a, b)
                            };
                            assert_eq!(got, call_expected(shape, a, b));
                            calls += 1;
                        }
                    }
                    calls
                });
            }
        }
        let summary = summarize("call", &rows);
        assert_eq!(summary.compiles, CALL_SHAPES.len() * LEVELS.len());
        // No source-bound owner credits a call: every calling frame is
        // refused, whatever the proof tools, and the BL is named.
        assert_eq!(summary.published, 0, "a calling frame published");
        for row in &rows {
            let Outcome::Refused { listed, .. } = &row.outcome else {
                unreachable!("checked above");
            };
            assert!(
                listed.iter().any(|opcode| opcode == "AArch64::Bl"),
                "{}/{:?}: the call row is not named: {listed:?}",
                row.shape,
                row.level
            );
        }
        pin("call", &summary);
    });
}

// ---------------------------------------------------------------------------
// beat-llvm
// ---------------------------------------------------------------------------

/// Whether a function is a leaf this census can compile alone: a body, no
/// call of any kind, no global address, no exception edge.
fn is_census_leaf(function: &trust_ir::Function) -> bool {
    !function.blocks.is_empty()
        && function.blocks.iter().all(|block| {
            block.body.iter().all(|node| {
                !matches!(
                    node.inst,
                    Inst::Call { .. }
                        | Inst::CallIndirect { .. }
                        | Inst::CallCannotUnwind { .. }
                        | Inst::CallIndirectCannotUnwind { .. }
                        | Inst::GlobalAddr { .. }
                        | Inst::Invoke { .. }
                        | Inst::InvokeIndirect { .. }
                        | Inst::DropInvoke { .. }
                        | Inst::AssertInvoke { .. }
                        | Inst::LandingPad { .. }
                        | Inst::Resume { .. }
                )
            })
        })
}

/// Every distinct leaf of the committed beat-llvm modules, alone in a
/// module of its own: `(program, function, module)`.
fn beat_llvm_leaves() -> Vec<(String, String, trust_ir::Module)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/compile-corpus/modules/bridge");
    let mut dirs: Vec<_> = std::fs::read_dir(&root)
        .unwrap_or_else(|error| panic!("{}: {error}", root.display()))
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("beat-llvm--"))
        })
        .collect();
    dirs.sort();
    assert_eq!(dirs.len(), 18, "the 18 beat-llvm programs");
    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for dir in dirs {
        let program = dir
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or_default()
            .trim_start_matches("beat-llvm--")
            .to_owned();
        let mut files: Vec<_> = std::fs::read_dir(&dir)
            .unwrap_or_else(|error| panic!("{}: {error}", dir.display()))
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
            .collect();
        files.sort();
        for file in files {
            let bytes = std::fs::read(&file).expect("read module");
            let module = trust_cg_codegen::pipeline::load_module_from_bytes(&bytes)
                .unwrap_or_else(|error| panic!("{}: {error}", file.display()));
            for function in &module.functions {
                if !is_census_leaf(function) || !seen.insert(function.name.clone()) {
                    continue;
                }
                let mut alone = module.clone();
                let mut leaf = function.clone();
                leaf.id = trust_ir::FuncId::new(0);
                leaf.linkage = trust_ir::Linkage::External;
                alone.functions = vec![leaf];
                alone.globals.clear();
                out.push((program.clone(), function.name.clone(), alone));
            }
        }
    }
    out
}

#[test]
fn census_beat_llvm_leaves() {
    on_big_stack(|| {
        let leaves = beat_llvm_leaves();
        let mut rows = Vec::new();
        for (program, function, module) in &leaves {
            for level in [OptLevel::O0, OptLevel::O2] {
                census_one(
                    &mut rows,
                    "beat-llvm",
                    &format!("{program}::{function}"),
                    level,
                    module,
                    &HashMap::new(),
                    |_| 0,
                );
            }
        }
        let summary = summarize("beat-llvm", &rows);
        assert_eq!(summary.compiles, leaves.len() * 2);
        pin("beat-llvm", &summary);
    });
}

// ---------------------------------------------------------------------------
// pins
// ---------------------------------------------------------------------------

/// The measured outcome of each family for each pinned tool pair:
/// `(family, tools, published, refusals by class)`
/// (`reports/2026-10-12-jit-proof-coverage-census`). The package pins are
/// this tree's measurement, not a property of the package: the same AY
/// certified 11 whole-body theorems in the 2026-10-01 record and none here,
/// and the record does not separate a changed theorem text from AY's strict
/// self-check nondeterminism. A package pin that moves needs that question
/// answered before it is read as a credit change.
type Pin = (&'static str, Tools, usize, &'static [(&'static str, usize)]);

const PINS: &[Pin] = &[
    (
        "a64-body",
        Tools::Overlay,
        67,
        &[("body-theorem-unreplayed", 4), ("e02-copy-constant", 17)],
    ),
    ("arith", Tools::Overlay, 160, &[]),
    ("fixture", Tools::Overlay, 12, &[]),
    (
        "memory",
        Tools::Overlay,
        21,
        &[
            ("e02-copy-constant", 15),
            ("instruction-derived-only", 2),
            ("statistical-only", 2),
        ],
    ),
    (
        "trap",
        Tools::Overlay,
        12,
        &[("instruction-derived-only", 1), ("statistical-only", 19)],
    ),
    ("call", Tools::Overlay, 0, &[("statistical-only", 16)]),
    (
        "beat-llvm",
        Tools::Overlay,
        1,
        &[
            ("certificate-gate", 2),
            ("e02-copy-constant", 3),
            ("instruction-derived-only", 4),
            ("statistical-only", 40),
        ],
    ),
    (
        "a64-body",
        Tools::Package9192,
        0,
        &[
            ("body-theorem-unreplayed", 79),
            ("instruction-derived-only", 9),
        ],
    ),
    (
        "arith",
        Tools::Package9192,
        0,
        &[("frame-theorem-unreplayed", 160)],
    ),
    (
        "fixture",
        Tools::Package9192,
        0,
        &[("frame-theorem-unreplayed", 12)],
    ),
    (
        "memory",
        Tools::Package9192,
        21,
        &[
            ("e02-copy-constant", 15),
            ("instruction-derived-only", 2),
            ("statistical-only", 2),
        ],
    ),
    (
        "trap",
        Tools::Package9192,
        0,
        &[
            ("body-theorem-unreplayed", 4),
            ("frame-theorem-unreplayed", 8),
            ("instruction-derived-only", 1),
            ("statistical-only", 19),
        ],
    ),
    ("call", Tools::Package9192, 0, &[("statistical-only", 16)]),
    (
        "beat-llvm",
        Tools::Package9192,
        0,
        &[
            ("body-theorem-unreplayed", 2),
            ("certificate-gate", 2),
            ("e02-copy-constant", 2),
            ("instruction-derived-only", 4),
            ("statistical-only", 40),
        ],
    ),
];

fn pin(family: &str, summary: &Summary) {
    let Some(tools) = measured_tools() else {
        println!("JIT_PROOF_CENSUS_UNPINNED family={family}: not a measured tool pair");
        return;
    };
    let Some((_, _, published, classes)) = PINS
        .iter()
        .find(|(name, pinned, _, _)| *name == family && *pinned == tools)
    else {
        println!("JIT_PROOF_CENSUS_UNPINNED family={family} tools={tools:?}");
        return;
    };
    assert_eq!(summary.published, *published, "{family} under {tools:?}");
    let expected: BTreeMap<String, usize> = classes
        .iter()
        .map(|(class, count)| ((*class).to_owned(), *count))
        .collect();
    assert_eq!(summary.by_class, expected, "{family} under {tools:?}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes, and no refusal is the license's, by accident.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
