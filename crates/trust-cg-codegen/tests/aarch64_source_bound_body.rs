// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The AArch64 whole-body owner (`trust_cg_verify::source_bound_a64_body`)
//! on the real pipeline's output, on this host.
//!
//! * Every family (Boolean parameters and connectives, integer bitwise rows,
//!   negation, register, immediate and shifted-register shifts under
//!   trust-ir's shift-amount rule, wide constants, nested selects with
//!   arithmetic on selected values and the conditional increment, invert and
//!   negate idioms, compares against immediates, extension idioms, diamonds
//!   with computed arms and block arguments, bit-test branches, multi-block
//!   DAGs) binds at O0-O3 in both preparations the routes publish: the AOT
//!   route's (default register allocator) and the JIT's (`jit_fast`'s fast
//!   register allocator), each at proof grade for the host triple. The JIT
//!   preparation's bytes are the bytes the JIT publishes.
//! * Corruptions of those real bodies (wrong or inverted condition codes,
//!   swapped select arms, CBZ/CBNZ and TBZ/TBNZ exchanged, the wrong shift
//!   kind or amount, a changed mask, a different logic row, a dropped block
//!   argument) are refused by name, and the verifier under Enforce rejects
//!   them with the named precondition failure.
//! * The owner's machine model of every admitted row agrees with this CPU:
//!   hand-built probe bodies (`common/source_bound_body_probes.rs`) run
//!   through the JIT and their outputs equal the model's evaluation of the
//!   body theorem's machine term; each probe's decoys (a mis-model of its
//!   row) disagree with the CPU on some input.
//! * The compiled code runs natively: through the JIT (MAP_JIT publication on
//!   Apple silicon) against Rust references, and as an AOT object (Mach-O on
//!   macOS, ELF on Linux GNU) linked by the host C compiler with a driver that
//!   compares it, call by call, against C references the same compiler builds
//!   at -O2 (`/usr/bin/clang` on Darwin).
//! * Without an independently replayed proof every covered row stays
//!   unverified and a proof-required report is not promotable.
//!
//! Nothing here is Formal evidence. The opt-in qualification target
//! `aarch64_source_bound_body_qualification` (`TCG_A64_BODY_QUALIFY=1`, needs
//! the identity-admitted AY and a Clean with carcara-verify) puts every
//! theorem and every corruption's theorem to the solver lane and runs the
//! proof-required JIT (`reports/2026-10-01-aarch64-source-bound-body`).
#![cfg(all(target_arch = "aarch64", feature = "verify"))]

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_cg_ir::{AArch64Opcode as M, InstId};
use trust_cg_verify::source_bound_a64_body::{
    A64_BODY_NEEDS_REPLAY, A64BodyRefusal, admits_machine_opcode, source_bound_a64_body,
};

#[path = "common/source_bound_body_cases.rs"]
mod cases;
use cases::{
    CASES, LEVELS, PREPS, Prep, Sig, call, grid, lir, module, mutants, on_big_stack, prepare_as,
    symbol,
};

#[path = "common/source_bound_body_probes.rs"]
mod probes;

#[path = "common/native_host.rs"]
mod native_host;
#[path = "common/rosetta.rs"]
mod process;

/// Every family member binds at every level, frameless; the bound rows are
/// admitted opcodes; the slice's copies and constants are kept apart from
/// the computing rows (both are credited by a replayed theorem, OD-35 route C).
#[test]
fn every_family_binds_at_every_level() {
    on_big_stack(|| {
        let mut census = BTreeMap::new();
        for case in CASES {
            let module = module(case);
            let lir = lir(&module);
            assert!(
                !trust_cg_verify::source_bound_frame::source_admits_frame_owner(&lir),
                "{}: the frame owner must not judge this source",
                case.name
            );
            assert!(trust_cg_verify::source_bound_a64_body::source_admits_a64_body_owner(&lir));
            for (level, prep) in LEVELS
                .into_iter()
                .flat_map(|level| PREPS.map(|prep| (level, prep)))
            {
                let machine = prepare_as(prep, &lir, level);
                let owner = source_bound_a64_body(&lir, &machine).unwrap_or_else(|refusal| {
                    panic!("{}/{level:?}/{prep:?}: {refusal}\n{machine:#?}", case.name)
                });
                assert!(
                    !machine
                        .insts
                        .iter()
                        .any(|inst| inst.opcode == M::StpPreIndex),
                    "{}/{level:?}: a frameless body",
                    case.name
                );
                for id in owner.covered() {
                    let opcode = machine.insts[id.0 as usize].opcode;
                    assert!(admits_machine_opcode(opcode), "{opcode:?}");
                    assert!(!matches!(
                        opcode,
                        M::MOVXrr
                            | M::MOVWrr
                            | M::MovR
                            | M::Movz
                            | M::Movn
                            | M::Movk
                            | M::MovI
                            | M::Ret
                    ));
                }
                for id in owner.copies_and_constants() {
                    let opcode = machine.insts[id.0 as usize].opcode;
                    assert!(
                        matches!(
                            opcode,
                            M::MOVXrr | M::MOVWrr | M::MovR | M::Movz | M::Movn | M::Movk | M::MovI
                        ),
                        "{opcode:?}"
                    );
                }
                let obligation = owner.obligation();
                assert!(!obligation.is_degenerate());
                assert!(obligation.fp_inputs.is_empty());
                let mut opcodes: Vec<String> = owner
                    .covered()
                    .iter()
                    .map(|id| format!("{:?}", machine.insts[id.0 as usize].opcode))
                    .collect();
                opcodes.sort();
                opcodes.dedup();
                census.insert(
                    format!("{}/{level:?}/{prep:?}", case.name),
                    format!(
                        "covered={} copies_and_constants={} opcodes={}",
                        owner.covered().len(),
                        owner.copies_and_constants().len(),
                        opcodes.join(",")
                    ),
                );
            }
        }
        for (key, line) in &census {
            println!("A64_BODY_BIND {key} {line}");
        }
        assert_eq!(census.len(), CASES.len() * LEVELS.len() * PREPS.len());
        let differ = CASES
            .iter()
            .flat_map(|case| LEVELS.map(|level| (case, level)))
            .filter(|(case, level)| {
                let lir = lir(&module(case));
                let rows = |prep| {
                    let machine = prepare_as(prep, &lir, *level);
                    machine
                        .block_order
                        .iter()
                        .flat_map(|block| machine.blocks[block.0 as usize].insts.clone())
                        .map(|id| {
                            let inst = &machine.insts[id.0 as usize];
                            format!("{:?} {:?}", inst.opcode, inst.operands)
                        })
                        .collect::<Vec<_>>()
                };
                rows(Prep::Aot) != rows(Prep::Jit)
            })
            .count();
        println!(
            "A64_BODY_BIND_SUMMARY families={} bodies={} jit_preparation_differs={differ}",
            CASES.len(),
            census.len()
        );
    });
}

/// Corruptions of the real bodies are refused by name: the concrete
/// evaluation of both gated DAGs finds an input on which they differ.
#[test]
fn corruptions_of_real_bodies_are_refused_by_name() {
    on_big_stack(|| {
        let mut classes: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
        let mut unrefuted = Vec::new();
        for case in CASES {
            let module = module(case);
            let lir = lir(&module);
            for level in [OptLevel::O0, OptLevel::O2] {
                for prep in PREPS {
                    let machine = prepare_as(prep, &lir, level);
                    let owner = source_bound_a64_body(&lir, &machine).unwrap();
                    for (class, mutant) in mutants(&machine, owner.covered()) {
                        let entry = classes.entry(class).or_default();
                        entry.0 += 1;
                        match source_bound_a64_body(&lir, &mutant) {
                            Err(A64BodyRefusal::Mismatch(_)) => entry.1 += 1,
                            Err(other) => unrefuted.push(format!(
                                "{}/{level:?}/{prep:?} {class}: refused without a mismatch: \
                                 {other}",
                                case.name
                            )),
                            Ok(_) => unrefuted.push(format!(
                                "{}/{level:?}/{prep:?} {class}: bound\n{mutant:#?}",
                                case.name
                            )),
                        }
                    }
                }
            }
        }
        for (class, (applied, refuted)) in &classes {
            println!("A64_BODY_MUTANTS class={class:?} refuted={refuted}/{applied}");
        }
        assert!(unrefuted.is_empty(), "{}", unrefuted.join("\n"));
        for class in [
            "inverted condition",
            "wrong condition",
            "swapped arms",
            "wrong shift kind",
            "wrong shift amount",
            "changed mask",
            "different logic row",
            "dropped block argument",
            "cbz/cbnz exchanged",
            "tbz/tbnz exchanged",
        ] {
            assert!(
                classes.get(class).is_some_and(|(applied, _)| *applied > 0),
                "no {class} mutant was applicable"
            );
        }
    });
}

/// Native JIT execution of every family at every level against the Rust
/// references (inputs on which the source is undefined are not called).
#[test]
fn native_jit_executes_every_family() {
    on_big_stack(|| {
        let mut calls = 0usize;
        for case in CASES {
            let module = module(case);
            for level in LEVELS {
                let compiler = Compiler::new(CompilerConfig {
                    opt_level: level,
                    parallel: false,
                    ..CompilerConfig::jit_fast(Target::Aarch64)
                })
                .with_codegen_license(permit_unlicensed());
                let result = compiler
                    .compile_module_to_jit(&module, &HashMap::new())
                    .unwrap_or_else(|error| panic!("{}/{level:?}: {error}", case.name));
                let protection = result.buffer.executable_memory_protection();
                assert!(
                    protection.published_rx
                        && protection.map_jit == cfg!(target_os = "macos")
                        && protection.write_protect_supported == cfg!(target_os = "macos"),
                    "{}/{level:?}: {protection:?}",
                    case.name
                );
                for row in grid(case.sig) {
                    let Some(expected) = (case.reference)(&row) else {
                        continue;
                    };
                    let mask = if case.sig == Sig::Ww {
                        u64::from(u32::MAX)
                    } else {
                        u64::MAX
                    };
                    let actual = call(&result.buffer, &symbol(case), case.sig, &row);
                    assert_eq!(
                        actual,
                        expected & mask,
                        "{}/{level:?} at {row:x?}",
                        case.name
                    );
                    calls += 1;
                }
            }
        }
        println!(
            "A64_BODY_NATIVE_JIT host={} functions={} calls={calls}",
            trust_cg_codegen::target::TargetSpec::host_for_architecture(Target::Aarch64).triple(),
            CASES.len() * LEVELS.len()
        );
    });
}

fn c_driver(level: OptLevel) -> String {
    let mut out = String::from(
        "#include <stdint.h>\n#include <stdio.h>\n#include <inttypes.h>\n\
         static unsigned long long calls, failures;\n",
    );
    for case in CASES {
        let (ret, params) = case.sig.c_types();
        let formals: Vec<String> = params
            .iter()
            .enumerate()
            .map(|(i, ty)| format!("{ty} a{i}"))
            .collect();
        let types = params.join(", ");
        writeln!(out, "extern {ret} {}({types});", symbol(case)).unwrap();
        writeln!(
            out,
            "static {ret} ref_{}({}) {{ {} }}",
            case.name,
            formals.join(", "),
            case.c_body
        )
        .unwrap();
    }
    for case in CASES {
        let (_, params) = case.sig.c_types();
        let mut body = String::new();
        let mut close = String::new();
        for (i, ty) in params.iter().enumerate() {
            let values: Vec<String> = case
                .sig
                .domain(i)
                .iter()
                .map(|v| format!("UINT64_C({v:#x})"))
                .collect();
            writeln!(
                body,
                "static const uint64_t d{i}[] = {{{}}}; \
                 for (unsigned i{i} = 0; i{i} < sizeof d{i} / sizeof d{i}[0]; ++i{i}) {{ \
                 {ty} a{i} = ({ty})d{i}[i{i}];",
                values.join(", ")
            )
            .unwrap();
            close.push('}');
        }
        let args: Vec<String> = (0..params.len()).map(|i| format!("a{i}")).collect();
        // Braced: the driver is one line per case, and GCC's
        // -Wmisleading-indentation (in -Wall, an error under -Werror) rejects
        // an unbraced `if` followed by another statement on the same line.
        let guard = if case.name == "shl_bare64" {
            "if (a1 >= 64) { continue; } "
        } else {
            ""
        };
        writeln!(
            out,
            "static void run_{name}(void) {{ {body} {guard}++calls; \
             if ((uint64_t){sym}({args}) != (uint64_t)ref_{name}({args})) {{ \
             if (failures++ < 8) fprintf(stderr, \"FAIL {name} {level:?}\\n\"); }} {close} }}",
            name = case.name,
            sym = symbol(case),
            args = args.join(", "),
        )
        .unwrap();
    }
    out.push_str("int main(void) {\n");
    for case in CASES {
        writeln!(out, "  run_{}();", case.name).unwrap();
    }
    out.push_str(
        "  printf(\"CALLS %llu FAILURES %llu\\n\", calls, failures);\n  return failures != 0;\n}\n",
    );
    out
}

/// AOT: each level's functions in one native object, linked by the host
/// C compiler (`native_host::C_COMPILER`: `/usr/bin/clang` on Darwin, `cc`
/// on Linux) with a driver whose references the same compiler builds at -O2;
/// every call is compared against that reference (a native differential).
#[test]
fn native_aot_objects_match_c_compiled_references() {
    on_big_stack(|| {
        let directory = tempfile::Builder::new()
            .prefix("trust-cg-a64-body-aot-")
            .tempdir()
            .unwrap();
        let mut total = 0u64;
        for level in LEVELS {
            let pipeline = Pipeline::new(PipelineConfig {
                opt_level: level,
                target_triple: native_host::TRIPLE.into(),
                verify: false,
                ..Default::default()
            })
            .with_proof_grade_aarch64_publication();
            let mut functions = Vec::new();
            for case in CASES {
                let module = module(case);
                let lir = lir(&module);
                let machine = pipeline.prepare_function(&lir).unwrap();
                source_bound_a64_body(&lir, &machine)
                    .unwrap_or_else(|refusal| panic!("{}/{level:?}: {refusal}", case.name));
                functions.push(machine);
            }
            let object = pipeline.compile_module(&functions).unwrap();
            native_host::assert_native_object(&object);
            let tier = directory.path().join(format!("{level:?}"));
            std::fs::create_dir(&tier).unwrap();
            std::fs::write(tier.join("bodies.o"), &object).unwrap();
            std::fs::write(tier.join("driver.c"), c_driver(level)).unwrap();
            let binary = tier.join("run");
            let mut link = std::process::Command::new(native_host::C_COMPILER);
            link.args(["-O2", "-std=c11", "-Wall", "-Wextra", "-Werror"])
                .args(native_host::link_hardening_args())
                .arg(tier.join("driver.c"))
                .arg(tier.join("bodies.o"))
                .arg("-o")
                .arg(&binary);
            let linked =
                process::command_output_with_timeout(&mut link, process::codegen_link_timeout())
                    .unwrap();
            assert!(
                !linked.timed_out && linked.output.status.success(),
                "{level:?}: {}",
                String::from_utf8_lossy(&linked.output.stderr)
            );
            let mut command = std::process::Command::new(&binary);
            let run =
                process::command_output_with_timeout(&mut command, process::codegen_run_timeout())
                    .unwrap();
            let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
            assert!(
                !run.timed_out && run.output.status.success(),
                "{level:?}: {stdout} {}",
                String::from_utf8_lossy(&run.output.stderr)
            );
            let calls: u64 = stdout
                .split_whitespace()
                .nth(1)
                .and_then(|n| n.parse().ok())
                .unwrap_or_else(|| panic!("{level:?}: {stdout}"));
            assert!(stdout.contains("FAILURES 0"), "{level:?}: {stdout}");
            assert!(calls > 0);
            total += calls;
        }
        println!(
            "A64_BODY_NATIVE_AOT host={} objects={} calls={total}",
            native_host::HOST,
            LEVELS.len()
        );
    });
}

/// Without an independently replayed proof (the replay lane refused here)
/// every covered row stays unverified, naming the body theorem's need, and
/// the proof-required report is not promotable.
#[test]
fn covered_rows_stay_unverified_without_replay() {
    use trust_cg_verify::function_verifier::InstructionVerificationResult as R;
    use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
    use trust_cg_verify::{FunctionVerifier, VerificationConfig};
    on_big_stack(|| {
        trust_cg_verify::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
            for case in CASES {
                let module = module(case);
                let lir = lir(&module);
                for (level, prep) in [OptLevel::O1, OptLevel::O3]
                    .into_iter()
                    .flat_map(|level| PREPS.map(|prep| (level, prep)))
                {
                    let machine = prepare_as(prep, &lir, level);
                    let owner = source_bound_a64_body(&lir, &machine).unwrap();
                    let verifier =
                        FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
                    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                    let (captured, exported) =
                        verifier.verify_with_request_for_export(&machine, Some(&lir), &request);
                    let report = captured.report();
                    assert!(report.precondition_failure.is_none(), "{report:?}");
                    assert!(exported.is_empty());
                    for row in &report.instructions {
                        if !owner.covers(InstId(row.inst_index as u32)) {
                            continue;
                        }
                        match &row.result {
                            R::Unverified { reason } => assert!(
                                reason.starts_with(A64_BODY_NEEDS_REPLAY),
                                "{}/{level:?}/{prep:?}: {reason}",
                                case.name
                            ),
                            other => panic!("{}/{level:?}/{prep:?}: {other:?}", case.name),
                        }
                    }
                    assert!(!report.emitted_opcode_inventory().is_promotable());
                }
            }
        });
    });
}

/// The LIR opcode census: how many of the LIR `Opcode` variants a
/// source-bound AArch64 owner admits, before this owner (the frame owner's
/// affine domain and its chain/diamond control) and with it.
#[test]
fn lir_opcode_census_before_and_after() {
    let source = include_str!("../../trust-cg-lower/src/instructions.rs");
    let start = source
        .find("pub enum Opcode {")
        .expect("the LIR Opcode enum");
    let body = &source[start..];
    let end = body.find("\n}\n").expect("the end of the enum");
    let mut variants = Vec::new();
    let mut depth = 0i32;
    for line in body[..end].lines().skip(1) {
        let trimmed = line.trim();
        if depth == 0
            && let Some(first) = trimmed.chars().next()
            && first.is_ascii_uppercase()
        {
            let name: String = trimmed
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                variants.push(name);
            }
        }
        depth += line.matches('{').count() as i32 + line.matches('(').count() as i32;
        depth -= line.matches('}').count() as i32 + line.matches(')').count() as i32;
    }
    variants.sort();
    variants.dedup();
    let before = [
        "Iconst", "Copy", "Iadd", "Isub", "Icmp", "Select", "Return", "Jump", "Brif",
    ];
    let after: Vec<&str> = trust_cg_verify::source_bound_a64_body::ADMITTED_LIR_OPCODES.to_vec();
    for name in before.iter().chain(&after) {
        assert!(variants.iter().any(|v| v == name), "{name} is a LIR opcode");
    }
    let mut union: Vec<&str> = before
        .iter()
        .copied()
        .chain(after.iter().copied())
        .collect();
    union.sort();
    union.dedup();
    println!(
        "A64_LIR_OPCODE_CENSUS variants={} before={} after={} added={}",
        variants.len(),
        before.len(),
        union.len(),
        union
            .iter()
            .filter(|name| !before.contains(name))
            .copied()
            .collect::<Vec<_>>()
            .join(",")
    );
    assert_eq!(union.len(), 20);
    // The admitted opcodes the families and captured leaf's real sources
    // (through the TrustIR adapter) contain; the rest are bound by the unit fixtures only.
    let mut exercised: Vec<String> = CASES
        .iter()
        .flat_map(|case| {
            let lir = lir(&module(case));
            lir.blocks
                .values()
                .flat_map(|block| {
                    block
                        .instructions
                        .iter()
                        .map(|inst| format!("{:?}", inst.opcode))
                })
                .collect::<Vec<_>>()
        })
        .map(|name| {
            name.split([' ', '{', '('])
                .next()
                .unwrap_or_default()
                .to_owned()
        })
        .filter(|name| after.contains(&name.as_str()))
        .collect();
    for block in cases::captured_narrow_leaf().blocks.values() {
        for inst in &block.instructions {
            let name = format!("{:?}", inst.opcode);
            let name = name.split([' ', '{', '(']).next().unwrap();
            if after.contains(&name) {
                exercised.push(name.to_owned());
            }
        }
    }
    exercised.sort();
    exercised.dedup();
    let unexercised: Vec<&str> = after
        .iter()
        .copied()
        .filter(|name| !exercised.iter().any(|seen| seen == name))
        .collect();
    println!(
        "A64_LIR_OPCODE_FAMILIES exercised={} ({}) unit_fixtures_only={}",
        exercised.len(),
        exercised.join(","),
        unexercised.join(",")
    );
    // trust-ir has no and-not/or-not operation, so the adapter never emits
    // these two; `source_bound_a64_body::tests::rows` binds them.
    assert_eq!(unexercised, ["BandNot", "BorNot"]);
}

/// The JIT preparation the floor binds is the code the JIT publishes: for
/// every family and level, the bytes of `prepare_as(Prep::Jit, ..)` linked by
/// the raw JIT equal the bytes `CompilerConfig::jit_fast` publishes for the
/// same symbol.
#[test]
fn jit_preparation_is_the_published_jit_code() {
    use trust_cg_codegen::jit::{JitCompiler, JitConfig};
    let bytes = |buffer: &trust_cg_codegen::jit::ExecutableBuffer, name: &str| -> Vec<u8> {
        let (_, range) = buffer
            .function_ranges()
            .iter()
            .find(|(symbol, _)| symbol == name || symbol.strip_prefix('_') == Some(name))
            .unwrap_or_else(|| panic!("{name}: {:?}", buffer.function_ranges()));
        buffer.code_slice()[range.start as usize..range.end as usize].to_vec()
    };
    on_big_stack(move || {
        let mut compared = 0usize;
        for case in CASES {
            let module = module(case);
            let lir = lir(&module);
            for level in LEVELS {
                let published = Compiler::new(CompilerConfig {
                    opt_level: level,
                    parallel: false,
                    ..CompilerConfig::jit_fast(Target::Aarch64)
                })
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &HashMap::new())
                .unwrap_or_else(|error| panic!("{}/{level:?}: {error}", case.name));
                let prepared = prepare_as(Prep::Jit, &lir, level);
                source_bound_a64_body(&lir, &prepared)
                    .unwrap_or_else(|refusal| panic!("{}/{level:?}: {refusal}", case.name));
                let raw = JitCompiler::new(JitConfig::default())
                    .compile_raw(&[prepared], &HashMap::new())
                    .unwrap_or_else(|error| panic!("{}/{level:?}: {error}", case.name));
                assert_eq!(
                    bytes(&raw, &symbol(case)),
                    bytes(&published.buffer, &symbol(case)),
                    "{}/{level:?}: the JIT preparation is not the published code",
                    case.name
                );
                compared += 1;
            }
        }
        println!("A64_BODY_JIT_PREPARATION byte_identical={compared}");
    });
}

/// Under Enforce the verifier rejects corrupted real bodies with the named
/// precondition failure (one corruption of each class per family at O2, in
/// both preparations); Warn reports and credits nothing.
#[test]
fn enforce_rejects_corrupted_real_bodies_by_name() {
    use trust_cg_verify::FunctionVerificationPreconditionFailure as F;
    use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
    use trust_cg_verify::{FunctionVerifier, VerificationConfig};
    on_big_stack(|| {
        trust_cg_verify::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let mut rejected = 0usize;
            for case in CASES {
                let lir = lir(&module(case));
                for prep in PREPS {
                    let machine = prepare_as(prep, &lir, OptLevel::O2);
                    let owner = source_bound_a64_body(&lir, &machine).unwrap();
                    let mut seen = std::collections::BTreeSet::new();
                    for (class, mutant) in mutants(&machine, owner.covered()) {
                        if !seen.insert(class) {
                            continue;
                        }
                        let report = verifier.verify_with_lir_source_and_mode(
                            &mutant,
                            Some(&lir),
                            ProvenanceXCheckMode::Enforce,
                        );
                        assert!(
                            matches!(
                                &report.precondition_failure,
                                Some(F::SourceBoundA64BodyMismatch(_))
                            ),
                            "{}/{prep:?} {class}: {:?}",
                            case.name,
                            report.precondition_failure
                        );
                        assert!(report.instructions.is_empty());
                        assert!(!report.emitted_opcode_inventory().is_promotable());
                        let warned = verifier.verify_with_lir_source_and_mode(
                            &mutant,
                            Some(&lir),
                            ProvenanceXCheckMode::Warn,
                        );
                        assert!(warned.precondition_failure.is_none());
                        assert_eq!(warned.formally_credited_count(), 0);
                        rejected += 1;
                    }
                }
            }
            println!("A64_BODY_ENFORCE_REJECTED corruptions={rejected}");
            assert!(rejected > 0);
        });
    });
}

/// The dummy source the probes' theorems are stated against: `(u64, u64,
/// u64, u64) -> u64` returning its first argument. Only the machine term of
/// each theorem is evaluated.
fn probe_source() -> trust_cg_lower::Function {
    let mut builder = trust_ir_build::ModuleBuilder::new("probe");
    let signature = builder.add_func_type(vec![trust_ir::Ty::U64; 4], vec![trust_ir::Ty::U64]);
    let mut f = builder.function("probe_source", signature);
    let entry = f.create_block();
    let params: Vec<_> = (0..4)
        .map(|_| f.add_block_param(entry, trust_ir::Ty::U64))
        .collect();
    f.switch_to_block(entry);
    f.ret(vec![params[0]]);
    f.build();
    lir(&builder.build().expect("ModuleBuilder::build: test fixture"))
}

/// The machine term of a body theorem at the four argument registers: its
/// named definitions in definition order, then the term. A probe reads no
/// register or flag it did not write or receive, and has no domain premise.
fn machine_value(obligation: &trust_cg_verify::ProofObligation, args: &[u64; 4]) -> u64 {
    use trust_cg_verify::smt::{EvalResult, SmtExpr};
    let eval = |expr: &SmtExpr, env: &HashMap<String, u64>| match expr.try_eval(env) {
        Ok(EvalResult::Bv(value)) => value,
        Ok(EvalResult::Bool(value)) => u64::from(value),
        other => panic!("{expr}: {other:?}"),
    };
    let mut env: HashMap<String, u64> = HashMap::new();
    for (name, _) in &obligation.inputs {
        if let Some(index) = name.strip_prefix('e').and_then(|n| n.parse::<usize>().ok()) {
            env.insert(name.clone(), args[index]);
        }
        assert!(!name.starts_with('g'), "the probe reads unwritten {name}");
    }
    for premise in obligation.preconditions.iter().rev() {
        let SmtExpr::Eq { lhs, rhs } = premise else {
            panic!("a probe theorem has no domain premise: {premise}")
        };
        let SmtExpr::Var { name, .. } = lhs.as_ref() else {
            panic!("not a definition: {premise}")
        };
        let value = eval(rhs, &env);
        env.insert(name.clone(), value);
    }
    eval(&obligation.aarch64_expr, &env)
}

/// Silicon differential of the owner's machine model: every admitted row in
/// hand-built probe bodies, run on this CPU through the JIT, against the
/// evaluation of the machine term of the body theorem the owner states for
/// the same body. Each probe's decoys (its row replaced by a mis-model of it)
/// must disagree with the CPU on some input, and every admitted row is the
/// subject of a probe with decoys. Testing evidence for the trusted word
/// semantics: finitely many inputs on one CPU, not a proof.
#[test]
fn admitted_rows_agree_with_the_host_cpu() {
    use trust_cg_codegen::jit::{JitCompiler, JitConfig};
    use trust_cg_verify::source_bound_a64_body::{
        ADMITTED_MACHINE_OPCODES, diagnostic_a64_body_obligation,
    };
    on_big_stack(|| {
        let source = probe_source();
        let probes = probes::probes();
        let functions: Vec<_> = probes.iter().map(|probe| probe.function.clone()).collect();
        let buffer = JitCompiler::new(JitConfig::default())
            .compile_raw(&functions, &HashMap::new())
            .expect("every probe encodes");
        let theorem = |function: &trust_cg_ir::MachFunction| {
            let mut renamed = function.clone();
            renamed.name = source.name.clone();
            diagnostic_a64_body_obligation(&source, &renamed)
        };
        const CORNERS: [u64; 14] = [
            0,
            1,
            2,
            8,
            0x7f,
            0x80,
            0x7fff_ffff,
            0x8000_0000,
            0xffff_ffff,
            0x1_0000_0000,
            0x7fff_ffff_ffff_ffff,
            0x8000_0000_0000_0000,
            u64::MAX,
            0xdead_beef_0123_4567,
        ];
        let mut state = 0x243f_6a88_85a3_08d3u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut samples: Vec<[u64; 4]> = Vec::new();
        for a in CORNERS {
            for b in CORNERS {
                samples.push([a, b, next(), next()]);
            }
        }
        for _ in 0..160 {
            samples.push([next(), next(), next(), next()]);
        }
        let mut subjects = std::collections::BTreeSet::new();
        let mut calls = 0usize;
        let mut decoys = 0usize;
        for probe in &probes {
            let obligation = theorem(&probe.function).unwrap_or_else(|refusal| {
                panic!("{}: the walk refuses the probe: {refusal}", probe.name)
            });
            // SAFETY: every probe has this AAPCS64 signature and the buffer
            // outlives the calls.
            let function = unsafe {
                buffer
                    .get_fn_bound::<extern "C" fn(u64, u64, u64, u64) -> u64>(&probe.function.name)
                    .unwrap()
            };
            let silicon: Vec<u64> = samples
                .iter()
                .map(|a| (function.as_ref())(a[0], a[1], a[2], a[3]))
                .collect();
            for (sample, actual) in samples.iter().zip(&silicon) {
                let model = machine_value(&obligation, sample);
                assert_eq!(
                    *actual, model,
                    "{} at {sample:x?}: the CPU returns {actual:#x}, the model {model:#x}",
                    probe.name
                );
            }
            calls += silicon.len();
            for (label, decoy) in &probe.decoys {
                // A decoy the walk refuses cannot reproduce the CPU either.
                if let Ok(obligation) = theorem(decoy) {
                    assert!(
                        samples
                            .iter()
                            .zip(&silicon)
                            .any(|(sample, actual)| machine_value(&obligation, sample) != *actual),
                        "{}: the decoy {label} agrees with the CPU on every sample",
                        probe.name
                    );
                }
                decoys += 1;
            }
            if !probe.decoys.is_empty() {
                subjects.insert(probe.row);
            }
        }
        let used: std::collections::BTreeSet<String> = probes
            .iter()
            .flat_map(|probe| {
                probe
                    .function
                    .insts
                    .iter()
                    .map(|inst| format!("{:?}", inst.opcode))
            })
            .collect();
        for name in ADMITTED_MACHINE_OPCODES {
            assert!(used.contains(*name), "no probe runs {name}");
            assert!(
                *name == "Ret" || subjects.contains(name),
                "no probe with decoys is for {name}"
            );
        }
        println!(
            "A64_BODY_ROW_SILICON host={} probes={} rows={} decoys={decoys} calls={calls}",
            trust_cg_codegen::target::TargetSpec::host_for_architecture(Target::Aarch64).triple(),
            probes.len(),
            used.len()
        );
    });
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
