// Copyright 2026 Andrew Yates | Apache-2.0
//! Construct sweep, MODULE TABLES (ledger L05-P2, Darwin row D05): tables
//! with no runtime behaviour of their own, compiled into native
//! aarch64-apple-darwin objects at O0-O3, run, and checked for the effect
//! each table has on the emitted artifact.
//!
//! * `files`: the interned source path is the one the object's DWARF
//!   (`__DWARF,__debug_line` / `__debug_info`, read back by the host
//!   `dwarfdump`) names, and a control module without the table does not
//!   name it; the program still computes what the interpreter computes.
//! * `proof_obligations`, `proof_certificates`, `obligation_diagnostics`,
//!   `spec_modules`, `imports`: a module carrying every one of them non-empty
//!   compiles to the BYTE-IDENTICAL object of the same module without them,
//!   and runs. That is the measured absence of an artifact effect, which is
//!   why the construct inventory keeps these rows model-only.
//!
//! Execution evidence on this host only; not a proof of any lowering.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/construct_sweep.rs"]
mod sweep;

use sweep::{
    Arg, Body, Call, LEVELS, compile, compile_with, define, driver, dwarfdump, has_tool, link,
    oracle_bits, run_calls, sweep_module,
};
use trust_ir::proof::{
    DiagnosticSeverity, ObligationDiagnostic, ObligationKind, ProofCertificate, ProofDigest,
    ProofEvidence, ProofObligation, ProofStatus,
};
use trust_ir::spec::SpecModule;
use trust_ir::value::SourceSpan;
use trust_ir::{BinOp, Constant, FuncId, Inst, Module, ModuleImport, ProofId, Ty, ValueId};

const SOURCE_PATH: &str = "sweep/construct_sweep_files_table_probe.rs";

fn int_const(body: &mut Body, ty: Ty, value: i128) -> ValueId {
    body.emit(Inst::Const {
        ty,
        value: Constant::Int(value),
    })
}

/// `x * 3 + 1`, with every node spanned into `Module.files` when `spanned`.
fn files_module(spanned: bool) -> Module {
    let mut module = sweep_module("construct_sweep_files");
    let file = spanned.then(|| {
        module
            .intern_file(SOURCE_PATH)
            .expect("Module::intern_file: test fixture")
    });
    let mut body = Body::new();
    let x = body.param(Ty::U64);
    let three = int_const(&mut body, Ty::U64, 3);
    let product = body.emit(Inst::BinOp {
        op: BinOp::Mul,
        ty: Ty::U64,
        lhs: x,
        rhs: three,
    });
    let one = int_const(&mut body, Ty::U64, 1);
    let sum = body.emit(Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::U64,
        lhs: product,
        rhs: one,
    });
    body.effect(Inst::Return { values: vec![sum] });
    let id = define(
        &mut module,
        "sweep_files_affine",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );
    if let Some(file) = file {
        let function = &mut module.functions[id.index() as usize];
        for (line, node) in function.blocks[0].body.iter_mut().enumerate() {
            node.span = Some(SourceSpan {
                file,
                line: 20 + line as u32,
                col: 5,
            });
        }
    }
    module
}

#[test]
fn native_files_table_names_the_dwarf_source_of_a_running_program_o0_through_o3() {
    assert!(
        has_tool("/usr/bin/dwarfdump"),
        "the host dwarfdump is required"
    );
    let module = files_module(true);
    let control = files_module(false);
    for candidate in [&module, &control] {
        let validation = trust_ir_build::validate_module(candidate);
        assert!(validation.is_empty(), "{validation:?}");
    }
    assert_eq!(module.files, vec![SOURCE_PATH.to_string()]);
    let calls: Vec<Call> = [0u64, 7, u64::MAX / 3]
        .into_iter()
        .map(|x| {
            Call::new(
                format!("files_affine_{x:x}"),
                "sweep_files_affine",
                vec![Arg(Ty::U64, u128::from(x))],
                Ty::U64,
            )
            .c("a0 * 3 + 1")
        })
        .collect();
    let source = driver(&module, &calls, &[], "", "");
    let leaf = SOURCE_PATH.rsplit('/').next().unwrap_or(SOURCE_PATH);
    for opt_level in LEVELS {
        let tag = format!("files-{opt_level:?}");
        let object =
            compile_with(&module, opt_level, true).unwrap_or_else(|error| panic!("{tag}: {error}"));
        let lines = dwarfdump(&tag, &object, &["--debug-line"]);
        let info = dwarfdump(&tag, &object, &["--debug-info"]);
        assert!(
            lines.contains(leaf) && info.contains(leaf),
            "{tag}: the DWARF does not name `{SOURCE_PATH}`:\n{lines}\n{info}"
        );
        let unspanned = compile_with(&control, opt_level, true)
            .unwrap_or_else(|error| panic!("{tag} control: {error}"));
        let control_dump = dwarfdump(&tag, &unspanned, &["--debug-line", "--debug-info"]);
        assert!(
            !control_dump.contains(leaf),
            "{tag}: a module without the files table must not name `{SOURCE_PATH}`"
        );
        let linked = link(&tag, &object, &source);
        let (native, verdict) = run_calls(&tag, &linked);
        assert_eq!(
            verdict,
            format!("PASS {} c-model checks", calls.len()),
            "{tag}"
        );
        for call in &calls {
            let want = oracle_bits(&module, call)
                .unwrap_or_else(|| panic!("{}: an interpreter oracle", call.key));
            assert_eq!(native.get(&call.key), Some(&want), "{tag}: `{}`", call.key);
        }
        eprintln!("{tag}: DWARF names {SOURCE_PATH}; {verdict}");
    }
}

fn obligation(id: u32, kind: ObligationKind, status: ProofStatus) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status,
        description: "construct sweep inert table".to_string(),
        formula: None,
        function: Some(FuncId::new(0)),
        source: None,
        site: None,
        spec: None,
    }
}

/// `x ^ 0x55`, optionally carrying every inert table non-empty.
fn inert_tables_module(with_tables: bool) -> Module {
    let mut module = sweep_module("construct_sweep_inert_tables");
    let mut body = Body::new();
    let x = body.param(Ty::U64);
    let mask = int_const(&mut body, Ty::U64, 0x55);
    let mixed = body.emit(Inst::BinOp {
        op: BinOp::Xor,
        ty: Ty::U64,
        lhs: x,
        rhs: mask,
    });
    body.effect(Inst::Return {
        values: vec![mixed],
    });
    define(
        &mut module,
        "sweep_inert_xor",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );
    if with_tables {
        module.proof_obligations.push(obligation(
            0,
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
        ));
        // A certificate beside a PENDING row: the honest evidence-awaiting-
        // replay carrier. A `Discharged` row whose certificate nothing replays
        // is `DischargedWithoutCertificate`, and since WS7.3 every ingestion
        // entry refuses what trust-ir's codegen admission refuses.
        module.proof_obligations.push(obligation(
            1,
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
        ));
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(1),
            prover: "construct-sweep".to_string(),
            evidence: ProofEvidence::Trusted("construct sweep inert table".to_string()),
            assurance: None,
        });
        module.obligation_diagnostics.push(ObligationDiagnostic {
            obligation: ProofId::new(0),
            severity: DiagnosticSeverity::Warning,
            message: "construct sweep inert table".to_string(),
            location: None,
            detail: None,
        });
        module
            .spec_modules
            .push(SpecModule::new("construct_sweep_spec"));
        let _import = module
            .intern_import(ModuleImport::new(
                "construct_sweep_dependency",
                ProofDigest::zero(),
            ))
            .expect("Module::intern_import: test fixture");
    }
    module
}

#[test]
fn inert_tables_leave_the_native_artifact_byte_identical_o0_through_o3() {
    let carried = inert_tables_module(true);
    let bare = inert_tables_module(false);
    assert!(
        !carried.proof_obligations.is_empty()
            && !carried.proof_certificates.is_empty()
            && !carried.obligation_diagnostics.is_empty()
            && !carried.spec_modules.is_empty()
            && !carried.imports.is_empty(),
        "every inert table must be non-empty"
    );
    let calls: Vec<Call> = [0u64, 0x55, 0xDEAD_BEEF]
        .into_iter()
        .map(|x| {
            Call::new(
                format!("inert_xor_{x:x}"),
                "sweep_inert_xor",
                vec![Arg(Ty::U64, u128::from(x))],
                Ty::U64,
            )
            .c("a0 ^ 0x55")
        })
        .collect();
    let source = driver(&carried, &calls, &[], "", "");
    for opt_level in LEVELS {
        let tag = format!("inert-tables-{opt_level:?}");
        let with_tables =
            compile(&carried, opt_level).unwrap_or_else(|error| panic!("{tag}: {error}"));
        let without = compile(&bare, opt_level).unwrap_or_else(|error| panic!("{tag}: {error}"));
        assert!(
            with_tables == without,
            "{tag}: the inert tables changed the emitted object"
        );
        let linked = link(&tag, &with_tables, &source);
        let (native, verdict) = run_calls(&tag, &linked);
        assert_eq!(
            verdict,
            format!("PASS {} c-model checks", calls.len()),
            "{tag}"
        );
        for call in &calls {
            let want = oracle_bits(&carried, call)
                .unwrap_or_else(|| panic!("{}: an interpreter oracle", call.key));
            assert_eq!(native.get(&call.key), Some(&want), "{tag}: `{}`", call.key);
        }
        eprintln!("{tag}: byte-identical object with and without the tables; {verdict}");
    }
}
