// trust-cg-cli/tests/fsym_flag.rs - Integration tests for --fsym (#377)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, ICmpOp, Inst, InstrNode,
    Module as TrustIrModule, SwitchCase, Ty, ValueId,
};
use trust_ir_build::ModuleBuilder;

fn make_signed_overflow_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_flag_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_signed_overflow", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let lhs = fb.iconst(Ty::I64, i64::MAX as i128);
    let rhs = fb.iconst(Ty::I64, 1);
    let sum = fb.add(Ty::I64, lhs, rhs);
    fb.ret(vec![sum]);
    fb.build();
    mb.build()
}

fn make_clean_and_overflow_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_status_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);

    let mut clean = mb.function("_clean_scanned", ty);
    let clean_entry = clean.create_block();
    clean.switch_to_block(clean_entry);
    let clean_value = clean.iconst(Ty::I64, 7);
    clean.ret(vec![clean_value]);
    clean.build();

    let mut ub = mb.function("_signed_overflow", ty);
    let ub_entry = ub.create_block();
    ub.switch_to_block(ub_entry);
    let lhs = ub.iconst(Ty::I64, i64::MAX as i128);
    let rhs = ub.iconst(Ty::I64, 1);
    let sum = ub.add(Ty::I64, lhs, rhs);
    ub.ret(vec![sum]);
    ub.build();

    mb.build()
}

fn make_null_deref_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_null_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_null_deref", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let ptr = fb.null_ptr();
    let value = fb.load(Ty::I64, ptr);
    fb.ret(vec![value]);
    fb.build();
    mb.build()
}

fn make_out_of_bounds_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_oob_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_out_of_bounds", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let base = fb.alloca(Ty::I64);
    let one = fb.iconst(Ty::I64, 1);
    let oob = fb.gep(Ty::I64, base, vec![one]);
    let value = fb.load(Ty::I64, oob);
    fb.ret(vec![value]);
    fb.build();
    mb.build()
}

fn make_use_after_free_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_uaf_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_use_after_free", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let ptr = fb.alloca(Ty::I64);
    fb.dealloc(ptr);
    let value = fb.load(Ty::I64, ptr);
    fb.ret(vec![value]);
    fb.build();
    mb.build()
}

fn make_symbolic_sadd_module(name: &str, rhs_value: i128) -> TrustIrModule {
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![Ty::I8], vec![Ty::I8]);
    let mut fb = mb.function("_symbolic_sadd", ty);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I8);
    fb.switch_to_block(entry);
    let guard = fb.icmp(ICmpOp::Eq, Ty::I8, x, x);
    fb.assume(guard);
    let rhs = fb.iconst(Ty::I8, rhs_value);
    let sum = fb.add(Ty::I8, x, rhs);
    fb.ret(vec![sum]);
    fb.build();
    mb.build()
}

fn make_symbolic_null_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_symbolic_null_test");
    let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("_symbolic_null", ty);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let guard = fb.icmp(ICmpOp::Eq, Ty::Ptr, ptr, ptr);
    fb.assume(guard);
    let value = fb.load(Ty::I64, ptr);
    fb.ret(vec![value]);
    fb.build();
    mb.build()
}

fn make_symbolic_out_of_bounds_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_symbolic_oob_test");
    let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("_symbolic_out_of_bounds", ty);
    let entry = fb.create_block();
    let index = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let base = fb.alloca(Ty::I64);
    let ptr = fb.gep(Ty::I64, base, vec![index]);
    let value = fb.load(Ty::I64, ptr);
    fb.ret(vec![value]);
    fb.build();
    mb.build()
}

fn make_symbolic_use_after_free_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_symbolic_uaf_test");
    let ty = mb.add_func_type(vec![Ty::Bool], vec![Ty::I64]);
    let mut fb = mb.function("_symbolic_use_after_free", ty);
    let entry = fb.create_block();
    let use_block = fb.create_block();
    let return_block = fb.create_block();
    let cond = fb.add_block_param(entry, Ty::Bool);

    fb.switch_to_block(entry);
    let ptr = fb.alloca(Ty::I64);
    fb.dealloc(ptr);
    fb.condbr(cond, use_block, vec![], return_block, vec![]);

    fb.switch_to_block(use_block);
    let value = fb.load(Ty::I64, ptr);
    fb.ret(vec![value]);

    fb.switch_to_block(return_block);
    let zero = fb.iconst(Ty::I64, 0);
    fb.ret(vec![zero]);

    fb.build();
    mb.build()
}

fn make_infeasible_arm_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_fsym_infeasible_arm_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_infeasible_arm", ty);
    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();

    fb.switch_to_block(entry);
    let lhs = fb.iconst(Ty::I64, 7);
    let rhs = fb.iconst(Ty::I64, 7);
    let cond = fb.icmp(ICmpOp::Eq, Ty::I64, lhs, rhs);
    fb.condbr(cond, then_block, vec![], else_block, vec![]);

    fb.switch_to_block(then_block);
    let zero = fb.iconst(Ty::I64, 0);
    fb.ret(vec![zero]);

    fb.switch_to_block(else_block);
    let ptr = fb.null_ptr();
    let value = fb.load(Ty::I64, ptr);
    fb.ret(vec![value]);

    fb.build();
    mb.build()
}

fn make_switch_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("cli_fsym_switch_skip_test");
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let cases = (0..16)
        .map(|value| SwitchCase {
            value: Constant::Int(value),
            target: BlockId::new(1),
            args: vec![],
        })
        .collect();
    let mut function = Function::new(
        FuncId::new(0),
        "_switch_skip",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    function.blocks = vec![
        Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Switch {
                    value: ValueId::new(0),
                    default: BlockId::new(1),
                    default_args: vec![],
                    cases,
                    exhaustive_enum_unreachable: false,
                }),
            ],
        },
        Block {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(1)],
                }),
            ],
        },
    ];
    module.functions.push(function);
    module
}

fn scratch_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_cli_fsym_{}_{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

fn write_tmbc(dir: &std::path::Path, module: TrustIrModule) -> PathBuf {
    let path = dir.join("module.tmbc");
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&path, tmbc).expect("write tmbc");
    path
}

fn run_compile(dir: &std::path::Path, input: &std::path::Path, mode: &str) -> std::process::Output {
    Command::new(trust_cg_bin())
        .arg(format!("--fsym={mode}"))
        .arg("-c")
        .arg("-o")
        .arg(dir.join("module.o"))
        .arg(input)
        .output()
        .expect("run trust-cg")
}

fn run_compile_with_args(
    dir: &std::path::Path,
    input: &std::path::Path,
    args: &[&str],
) -> std::process::Output {
    let mut command = Command::new(trust_cg_bin());
    for arg in args {
        command.arg(arg);
    }
    command
        .arg("-c")
        .arg("-o")
        .arg(dir.join("module.o"))
        .arg(input)
        .output()
        .expect("run trust-cg")
}

fn fsym_function_status<'a>(
    report: &'a serde_json::Value,
    function: &str,
) -> &'a serde_json::Value {
    report["functions"]
        .as_array()
        .expect("functions array")
        .iter()
        .find(|entry| entry["function"] == function)
        .unwrap_or_else(|| panic!("missing fsym function status for {function}: {report:#}"))
}

#[test]
fn fsym_warn_emits_warning_and_continues_codegen() {
    let dir = scratch_dir("warn");
    let input = write_tmbc(&dir, make_signed_overflow_module());
    let out_path = dir.join("module.o");

    let output = Command::new(trust_cg_bin())
        .arg("--fsym=warn")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&input)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--fsym=warn should continue compilation. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("warning[fsym]") && stderr.contains("arithmetic"),
        "expected fsym warning for concrete signed overflow. stderr:\n{stderr}"
    );
    assert!(
        out_path.exists(),
        "warn mode should still produce object file {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_error_rejects_before_codegen() {
    let dir = scratch_dir("error");
    let input = write_tmbc(&dir, make_signed_overflow_module());
    let out_path = dir.join("module.o");

    let output = Command::new(trust_cg_bin())
        .arg("--fsym=error")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&input)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "--fsym=error should reject concrete UB"
    );
    assert!(
        stderr.contains("error[fsym]") && stderr.contains("rejected"),
        "expected fsym error rejection. stderr:\n{stderr}"
    );
    assert!(
        !out_path.exists(),
        "error mode must exit before writing object file {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_off_preserves_current_compile_behavior() {
    let dir = scratch_dir("off");
    let input = write_tmbc(&dir, make_signed_overflow_module());
    let out_path = dir.join("module.o");

    let output = Command::new(trust_cg_bin())
        .arg("--fsym=off")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&input)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--fsym=off should preserve compile behavior. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("[fsym]"),
        "off mode should not emit fsym diagnostics. stderr:\n{stderr}"
    );
    assert!(out_path.exists(), "expected object file in off mode");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_warn_emits_json_report_and_continues_codegen() {
    let dir = scratch_dir("warn_report");
    let input = write_tmbc(&dir, make_signed_overflow_module());
    let out_path = dir.join("module.o");
    let report_path = dir.join("fsym-report.json");

    let output = Command::new(trust_cg_bin())
        .arg("--fsym=warn")
        .arg("--fsym-report-json")
        .arg(&report_path)
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&input)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--fsym=warn should continue compilation. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("warning[fsym]") && stderr.contains("arithmetic"),
        "expected existing fsym warning behavior. stderr:\n{stderr}"
    );

    let report: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&report_path).expect("read fsym report"))
            .expect("parse fsym report");
    assert_eq!(report["schema"], "trust-cg.fsym_preflight.v1");
    assert_eq!(report["mode"], "warn");
    assert_eq!(report["solver"], "off");
    assert_eq!(report["enabled"], true);
    assert_eq!(report["summary"]["concrete_ub_diagnostics"], 1);
    assert_eq!(report["summary"]["rejected"], false);
    assert_eq!(report["diagnostics"][0]["kind"], "arithmetic");
    assert!(
        out_path.exists(),
        "warn mode should still produce object file"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_json_report_lists_clean_scanned_function_statuses() {
    let dir = scratch_dir("status_report");
    let input = write_tmbc(&dir, make_clean_and_overflow_module());
    let out_path = dir.join("module.o");
    let report_path = dir.join("fsym-report.json");

    let output = Command::new(trust_cg_bin())
        .arg("--fsym=warn")
        .arg("--fsym-report-json")
        .arg(&report_path)
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&input)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--fsym=warn should continue compilation. stderr:\n{stderr}"
    );

    let report: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&report_path).expect("read fsym report"))
            .expect("parse fsym report");
    assert_eq!(report["schema"], "trust-cg.fsym_preflight.v1");
    assert_eq!(report["summary"]["scanned_functions"], 2);

    let clean = fsym_function_status(&report, "_clean_scanned");
    assert_eq!(clean["module"], "cli_fsym_status_test");
    assert_eq!(clean["status"], "clean_scanned");

    let ub = fsym_function_status(&report, "_signed_overflow");
    assert_eq!(ub["module"], "cli_fsym_status_test");
    assert_eq!(ub["status"], "concrete_ub");

    assert!(
        out_path.exists(),
        "warn mode should still produce object file"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_error_rejects_after_emitting_json_report() {
    let dir = scratch_dir("error_report");
    let input = write_tmbc(&dir, make_signed_overflow_module());
    let out_path = dir.join("module.o");
    let report_path = dir.join("fsym-report.json");

    let output = Command::new(trust_cg_bin())
        .arg("--fsym=error")
        .arg("--fsym-report-json")
        .arg(&report_path)
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&input)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "--fsym=error should reject concrete UB"
    );
    assert!(
        stderr.contains("error[fsym]") && stderr.contains("rejected"),
        "expected existing fsym error behavior. stderr:\n{stderr}"
    );

    let report: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&report_path).expect("read fsym report"))
            .expect("parse fsym report");
    assert_eq!(report["mode"], "error");
    assert_eq!(report["summary"]["concrete_ub_diagnostics"], 1);
    assert_eq!(report["summary"]["rejected"], true);
    assert_eq!(report["diagnostics"][0]["kind"], "arithmetic");
    assert!(
        !out_path.exists(),
        "error mode must exit before writing object file {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_report_off_mode_rejects_with_clear_diagnostic() {
    let dir = scratch_dir("off_report");
    let input = write_tmbc(&dir, make_signed_overflow_module());
    let out_path = dir.join("module.o");
    let report_path = dir.join("fsym-report.json");

    let output = Command::new(trust_cg_bin())
        .arg("--fsym=off")
        .arg("--fsym-report-json")
        .arg(&report_path)
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&input)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "--fsym-report-json should reject --fsym=off. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("[fsym]"),
        "off mode should not emit fsym diagnostics. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("--fsym-report-json requires --fsym=warn or --fsym=error"),
        "expected clear off-mode report rejection. stderr:\n{stderr}"
    );
    assert!(
        !report_path.exists(),
        "off-mode rejection should not create {}",
        report_path.display()
    );
    assert!(
        !out_path.exists(),
        "off-mode rejection must exit before writing object file {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_error_rejects_null_deref_oob_and_uaf_before_codegen() {
    for (name, module, expected_kind) in [
        (
            "null_deref",
            make_null_deref_module(),
            "null-deref in module",
        ),
        (
            "out_of_bounds",
            make_out_of_bounds_module(),
            "bounds in module",
        ),
        (
            "use_after_free",
            make_use_after_free_module(),
            "use-after-free in module",
        ),
    ] {
        let dir = scratch_dir(name);
        let input = write_tmbc(&dir, module);
        let out_path = dir.join("module.o");
        let output = run_compile(&dir, &input, "error");
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            !output.status.success(),
            "--fsym=error should reject {name}. stderr:\n{stderr}"
        );
        assert!(
            stderr.contains("error[fsym]")
                && stderr.contains(expected_kind)
                && stderr.contains("rejected"),
            "expected fsym error for {name}. stderr:\n{stderr}"
        );
        assert!(
            !out_path.exists(),
            "error mode must exit before writing object file for {name}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}

#[test]
fn fsym_warn_reports_null_deref_oob_and_uaf() {
    for (name, module, expected_kind) in [
        (
            "warn_null_deref",
            make_null_deref_module(),
            "null-deref in module",
        ),
        (
            "warn_out_of_bounds",
            make_out_of_bounds_module(),
            "bounds in module",
        ),
        (
            "warn_use_after_free",
            make_use_after_free_module(),
            "use-after-free in module",
        ),
    ] {
        let dir = scratch_dir(name);
        let input = write_tmbc(&dir, module);
        let output = run_compile(&dir, &input, "warn");
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            stderr.contains("warning[fsym]") && stderr.contains(expected_kind),
            "expected fsym warning for {name}. stderr:\n{stderr}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}

#[test]
fn fsym_suppresses_infeasible_branch_arm_diagnostic() {
    let dir = scratch_dir("infeasible_arm");
    let input = write_tmbc(&dir, make_infeasible_arm_module());
    let output = run_compile(&dir, &input, "warn");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "infeasible-arm module should compile. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("null pointer dereference"),
        "fsym should suppress concrete UB from the infeasible branch arm. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("unknown obligation"),
        "fully concrete infeasible-arm pruning should not leave unknown obligations. stderr:\n{stderr}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_warn_reports_typed_switch_skip_without_rejecting() {
    let dir = scratch_dir("switch_skip");
    let input = write_tmbc(&dir, make_switch_module());
    let out_path = dir.join("module.o");
    let output = run_compile(&dir, &input, "warn");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "--fsym=warn should not reject skipped switch functions. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("warning[fsym]")
            && stderr.contains("skipped function")
            && stderr.contains("reason=switch"),
        "expected typed fsym switch skip warning. stderr:\n{stderr}"
    );
    assert!(
        out_path.exists(),
        "warn mode should still produce object file {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_solver_defaults_off_for_symbolic_unknowns() {
    let dir = scratch_dir("solver_default_off");
    let input = write_tmbc(&dir, make_symbolic_sadd_module("cli_fsym_solver_off", 1));
    let output = run_compile_with_args(&dir, &input, &["--fsym=warn"]);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "default solver-off warn mode should continue compilation. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("warning[fsym]")
            && stderr.contains("unknown obligation")
            && stderr.contains("no solver was invoked"),
        "default solver-off mode should preserve existing unknown rendering. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("[fsym-solver]") && !stderr.contains("status=concrete_ub"),
        "default solver-off mode must not emit solver statuses. stderr:\n{stderr}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_solver_local_warn_renders_stable_statuses() {
    for (name, module, expected_status, expected_kind) in [
        (
            "solver_proven_safe",
            make_symbolic_sadd_module("cli_fsym_solver_safe", 0),
            "status=proven_safe",
            "kind=arithmetic",
        ),
        (
            "solver_concrete_ub",
            make_symbolic_sadd_module("cli_fsym_solver_ub", 1),
            "status=concrete_ub",
            "kind=arithmetic",
        ),
        (
            "solver_timeout",
            make_symbolic_null_module(),
            "status=timeout",
            "kind=null-deref",
        ),
        (
            "solver_timeout_oob",
            make_symbolic_out_of_bounds_module(),
            "status=timeout",
            "kind=bounds",
        ),
    ] {
        let dir = scratch_dir(name);
        let input = write_tmbc(&dir, module);
        let output = run_compile_with_args(&dir, &input, &["--fsym=warn", "--fsym-solver=local"]);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            stderr.contains("warning[fsym-solver]")
                && stderr.contains(expected_status)
                && stderr.contains(expected_kind),
            "expected stable solver warning for {name}. stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains("no solver was invoked"),
            "solver-enabled mode should not print the no-solver summary for {name}. stderr:\n{stderr}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}

#[test]
fn fsym_error_rejects_solver_found_concrete_ub() {
    let dir = scratch_dir("solver_error_reject");
    let input = write_tmbc(
        &dir,
        make_symbolic_sadd_module("cli_fsym_solver_error_reject", 1),
    );
    let out_path = dir.join("module.o");
    let output = run_compile_with_args(&dir, &input, &["--fsym=error", "--fsym-solver=local"]);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "--fsym=error should reject solver-found concrete UB. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("error[fsym-solver]")
            && stderr.contains("status=concrete_ub")
            && stderr.contains("rejected"),
        "expected solver-backed fsym error rejection. stderr:\n{stderr}"
    );
    assert!(
        !out_path.exists(),
        "solver-backed error mode must exit before writing object file"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fsym_solver_preserves_fail_closed_diagnostics() {
    for (name, module, expected_status, expected_kind) in [
        (
            "solver_oob_timeout",
            make_symbolic_out_of_bounds_module(),
            "status=timeout",
            "bounds",
        ),
        (
            "solver_uaf_unsupported",
            make_symbolic_use_after_free_module(),
            "status=unsupported",
            "use-after-free",
        ),
    ] {
        let dir = scratch_dir(name);
        let input = write_tmbc(&dir, module);
        let output = run_compile_with_args(&dir, &input, &["--fsym=warn", "--fsym-solver=local"]);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            stderr.contains("warning[fsym]")
                && stderr.contains("unknown obligation")
                && stderr.contains(expected_kind),
            "expected original unsupported obligation warning for {name}. stderr:\n{stderr}"
        );
        assert!(
            stderr.contains("warning[fsym-solver]")
                && stderr.contains(expected_status)
                && stderr.contains(expected_kind),
            "expected fail-closed solver status for {name}. stderr:\n{stderr}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}
