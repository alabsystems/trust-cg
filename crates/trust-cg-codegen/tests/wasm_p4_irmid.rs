// trust-cg-codegen/tests/wasm_p4_irmid.rs - wasm32 lane: the trust-ir mid-end
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The trust-ir mid-end (`trust_cg_irmid`, profile `Wasm32`) on the wasm32
//! lane:
//!
//! * at O0 it does not run, and the bytes are those of the lane with the
//!   mid-end switched off (`WasmOptOptions::mid_end = false`);
//! * at O1 and above it rewrites the bridge's frame-slot shape (copies, a
//!   `ptrtoint`/`add`/`inttoptr` chain into an `alloca`, a constant branch,
//!   dead arithmetic), its output is lowered, and the evidence says so: the
//!   passes, the functions changed, no rollback, the interpreter differential's
//!   coverage, and `optimization_pipeline` under `ran`;
//! * switched off, it reports why and the module is lowered as given;
//! * every form — O0, O2 with and without the mid-end, closed and linked —
//!   agrees with the trust-ir reference interpreter in node;
//! * stage B: a slot whose loads each have one dominating store is
//!   forwarded and leaves the frame, and a local constant table read through
//!   a checked variable index becomes read-only data, each agreeing with the
//!   interpreter in node;
//! * the promoted table's static data never shortens the stack the input
//!   module had: the sized closed module grows its memory, and under a
//!   caller's fixed policy (a closed page count, or an island's host-reserved
//!   region) promotion is withheld;
//! * the differential's view reads the bridge's global-address stub exactly
//!   as this crate's codec writes it.
//!
//! Node is required to execute the wasm and `wasm-ld` (`WASM_LD`) to link the
//! object; the absence of either is a loud SKIP.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmModulePolicy, WasmOptOptions};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty};

const PROGRAM: &str = "module \"p4\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i32\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
fn @frame(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   %3 = copy ptr %2\n\
\x20   %4 = ptrtoint ptr %3 to i32\n\
\x20   %5 = const i32 4\n\
\x20   %6 = copy i32 %5\n\
\x20   %7 = add i32 %4, %6\n\
\x20   %8 = inttoptr i32 %7 to ptr\n\
\x20   store i32 %0, ptr %8\n\
\x20   %9 = const i32 0\n\
\x20   %10 = add i32 %4, %9\n\
\x20   %11 = inttoptr i32 %10 to ptr\n\
\x20   store i32 %1, ptr %11\n\
\x20   %12 = const bool true\n\
\x20   condbr %12, bb1, bb2\n\
bb1:\n\
\x20   %13 = load i32, ptr %8\n\
\x20   %14 = load i32, ptr %11\n\
\x20   %15 = sub i32 %13, %14\n\
\x20   ret %15\n\
bb2:\n\
\x20   ret %0\n\
}\n\n\
fn @sum(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const i32 0\n\
\x20   br bb1(%2, %2)\n\
bb1(%3: i32, %4: i32):\n\
\x20   %5 = copy i32 %3\n\
\x20   %6 = icmp slt i32 %5, %1\n\
\x20   condbr %6, bb2, bb3\n\
bb2:\n\
\x20   %7 = add i32 %4, %0\n\
\x20   %8 = const i32 1\n\
\x20   %9 = add i32 %5, %8\n\
\x20   %10 = mul i32 %9, %9\n\
\x20   br bb1(%9, %7)\n\
bb3:\n\
\x20   ret %4\n\
}\n";

const ROWS: &[(i64, i64)] = &[(0, 0), (1, 2), (7, 3), (-5, 9), (100, 10), (3, 0), (-1, 1)];

fn program() -> Module {
    trust_ir::parser::parse_module(PROGRAM).expect("parse the test program")
}

fn options(level: OptLevel, mid_end: bool) -> WasmOptOptions {
    WasmOptOptions { level, mid_end }
}

fn sized(module: &Module, opts: WasmOptOptions) -> (Vec<u8>, wasm::WasmCompileEvidence) {
    wasm::compile_sized_closed_module_with_evidence_license_options(
        module,
        &permit_unlicensed(),
        opts,
    )
    .expect("compile the sized closed module")
}

fn closed(module: &Module, opts: WasmOptOptions) -> (Vec<u8>, wasm::WasmCompileEvidence) {
    wasm::compile_module_with_evidence_policy_license_options(
        module,
        &WasmModulePolicy::closed(),
        &permit_unlicensed(),
        opts,
    )
    .expect("compile the closed module")
}

fn interpret(module: &Module, name: &str, a: i64, b: i64) -> i64 {
    let f = module.function_by_name(name).expect("function");
    let args = [a, b].map(|v| InterpretValue::int(Ty::I32, i128::from(v)).expect("i32"));
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 64,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, args)
        .unwrap_or_else(|e| panic!("{name}({a}, {b}) is refused by the interpreter: {e:?}"));
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => i64::from(i.as_signed() as i32),
        other => panic!("{name} returned {other:?}"),
    }
}

fn node() -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("node"))
        .find(|p| p.is_file())
}

fn wasm_ld() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("WASM_LD") {
        return Some(PathBuf::from(p));
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("wasm-ld"))
        .find(|p| p.is_file())
}

fn scratch(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("tcg_wasm_p4_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run `name(a, b)` for every row in node; `None` when node is absent.
fn run(bytes: &[u8], name: &str) -> Option<Vec<i64>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; the module was not executed");
        return None;
    };
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let rows: Vec<String> = ROWS.iter().map(|(a, b)| format!("[{a},{b}]")).collect();
    let js = format!(
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const imports = {{}};\n\
         for (const i of WebAssembly.Module.imports(m)) {{ imports[i.module] ??= {{}}; }}\n\
         const inst = new WebAssembly.Instance(m, imports);\n\
         const out = [{}].map(([a, b]) => inst.exports['{name}'](a, b));\n\
         process.stdout.write(JSON.stringify(out));\n",
        rows.join(",")
    );
    std::fs::write(dir.join("run.js"), js).unwrap();
    let out = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "node failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    Some(serde_json::from_slice(&out.stdout).expect("node JSON"))
}

fn assert_agrees(tag: &str, bytes: &[u8], module: &Module) {
    assert_agrees_on(tag, bytes, module, &["frame", "sum"]);
}

fn assert_agrees_on(tag: &str, bytes: &[u8], module: &Module, names: &[&str]) {
    for &name in names {
        let want: Vec<i64> = ROWS
            .iter()
            .map(|&(a, b)| interpret(module, name, a, b))
            .collect();
        if let Some(got) = run(bytes, name) {
            assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
        }
    }
}

#[test]
fn o0_is_unchanged_by_the_mid_end() {
    let module = program();
    let (with, evidence) = closed(&module, options(OptLevel::O0, true));
    let (without, _) = closed(&module, options(OptLevel::O0, false));
    assert_eq!(
        with, without,
        "O0 bytes do not depend on the mid-end switch"
    );
    assert!(!evidence.mid_end.enabled);
    assert_eq!(
        evidence.mid_end.not_run.as_deref(),
        Some("O0 runs no mid-end")
    );
    assert!(evidence.not_run.contains(&"optimization_pipeline"));
    assert_agrees("O0", &with, &module);
}

#[test]
fn the_mid_end_rewrites_the_frame_shape_and_reports_it() {
    let module = program();
    let (bytes, evidence) = closed(&module, options(OptLevel::O2, true));
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{:?}", mid);
    assert_eq!(mid.functions, 2);
    assert_eq!(mid.functions_changed, 2);
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    assert_eq!(mid.fallback, None);
    let pass = |name: &str| mid.passes.iter().find(|p| p.name == name).unwrap();
    assert_eq!(pass("ptr_gep").exact, 2, "both chains are in bounds");
    assert!(pass("copy_prop").exact >= 3);
    assert_eq!(pass("branch_fold").exact, 2, "one fold, one dead block");
    assert!(pass("dce").exact + pass("dce").refinements >= 4);
    assert!(
        pass("dce").refinements >= 1,
        "the dead multiply and the chain arithmetic are refinements"
    );
    assert!(mid.tv.samples_compared > 0, "{:?}", mid.tv);
    assert!(evidence.ran.contains(&"optimization_pipeline"));
    assert!(evidence.ran.contains(&"trust_ir_mid_witness_tv"));
    assert!(evidence.ran.contains(&"trust_ir_mid_interp_differential"));
    assert!(!evidence.not_run.contains(&"optimization_pipeline"));
    assert_eq!(
        evidence.verdict.as_str(),
        "missing_evidence",
        "the mid-end's checks do not verify the lowering"
    );
    let json = evidence.to_json();
    assert_eq!(json["irmid"]["functions_changed"], 2);
    assert_eq!(json["irmid"]["applied"], true);
    assert_agrees("O2", &bytes, &module);

    for level in [OptLevel::O1, OptLevel::O3] {
        let (other, _) = closed(&module, options(level, true));
        assert_eq!(other, bytes, "{level:?} emits the O2 bytes");
    }
}

#[test]
fn the_kill_switch_lowers_the_module_as_given() {
    let module = program();
    let (on, _) = closed(&module, options(OptLevel::O2, true));
    let (off, evidence) = closed(&module, options(OptLevel::O2, false));
    assert_ne!(on, off, "the mid-end changes the emitted code");
    assert!(!evidence.mid_end.enabled);
    assert_eq!(
        evidence.mid_end.not_run.as_deref(),
        Some("switched off by the caller")
    );
    assert!(evidence.not_run.contains(&"optimization_pipeline"));
    assert!(
        evidence.local_emission.enabled,
        "the local emission pass still runs"
    );
    assert_agrees("O2 without the mid-end", &off, &module);
}

#[test]
fn the_object_lane_runs_the_mid_end_and_links() {
    let module = program();
    let (object, evidence) = wasm::compile_object_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2, true),
    )
    .expect("compile the object");
    assert!(evidence.mid_end.applied);
    assert_eq!(evidence.mid_end.functions_changed, 2);
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP: wasm-ld not found (set WASM_LD); the object was not linked");
        return;
    };
    let dir = scratch("link");
    std::fs::write(dir.join("m0.o"), &object).unwrap();
    let out = Command::new(&ld)
        .args([
            "--no-entry",
            "--export-dynamic",
            "--stack-first",
            "-z",
            "stack-size=1048576",
            "-o",
        ])
        .arg(dir.join("m.wasm"))
        .arg(dir.join("m0.o"))
        .output()
        .expect("run wasm-ld");
    assert!(
        out.status.success(),
        "wasm-ld refused the object: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let linked = std::fs::read(dir.join("m.wasm")).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert_agrees("linked O2", &linked, &module);
}

/// Dead code the lane refuses stays refused: the mid-end would remove the
/// unused `undef`, but the input is lowered too and its refusal is the
/// compile's, closed and object alike.
#[test]
fn a_refused_dead_construct_stays_refused() {
    let text = "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
        type ty.0 = (u8, u32)\n\n\
        functy.0 = (i64, i64) -> (i64)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i64, %1: i64):\n\
        \x20   %2 = undef [ty.0 x 4611686018427387904]\n\
        \x20   ret %0\n\
        }\n";
    let module = trust_ir::parser::parse_module(text).expect("parse");
    for mid_end in [false, true] {
        let closed = wasm::compile_module_with_evidence_policy_license_options(
            &module,
            &WasmModulePolicy::closed(),
            &permit_unlicensed(),
            options(OptLevel::O2, mid_end),
        )
        .map(drop)
        .expect_err("the closed module is refused");
        assert!(
            closed.to_string().contains("larger than the wasm32 space"),
            "{closed}"
        );
        let object = wasm::compile_object_with_license_options(
            &module,
            &permit_unlicensed(),
            options(OptLevel::O2, mid_end),
        )
        .expect_err("the object is refused");
        assert!(
            object.to_string().contains("larger than the wasm32 space"),
            "{object}"
        );
    }
}

/// Stage B's shapes as the rustc bridge writes them: `fields` stores both
/// arguments into a two-field local and reads one per arm (forwarding, then
/// the slot is dead); `table` builds `[3, 1, 4, 1, 5, 9, 2, 6]` on every
/// call and reads `t[a & 7]` behind the bounds check (promotion).
const STAGE_B: &str = "module \"p4b\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i32\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
fn @fields(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   %3 = ptrtoint ptr %2 to i32\n\
\x20   %4 = const i32 4\n\
\x20   %5 = add i32 %3, %4\n\
\x20   %6 = inttoptr i32 %5 to ptr\n\
\x20   store i32 %0, ptr %2\n\
\x20   store i32 %1, ptr %6\n\
\x20   %7 = icmp slt i32 %0, %1\n\
\x20   condbr %7, bb1, bb2\n\
bb1:\n\
\x20   %8 = load i32, ptr %2\n\
\x20   br bb3(%8)\n\
bb2:\n\
\x20   %9 = load i32, ptr %6\n\
\x20   br bb3(%9)\n\
bb3(%10: i32):\n\
\x20   %11 = load i32, ptr %2\n\
\x20   %12 = sub i32 %10, %11\n\
\x20   ret %12\n\
}\n\n\
fn @table(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 8], align 4\n\
\x20   %3 = ptrtoint ptr %2 to i32\n\
\x20   %10 = const i32 3\n\
\x20   store i32 %10, ptr %2\n\
\x20   %11 = const i32 1\n\
\x20   %21 = const i32 4\n\
\x20   %31 = add i32 %3, %21\n\
\x20   %41 = inttoptr i32 %31 to ptr\n\
\x20   store i32 %11, ptr %41\n\
\x20   %12 = const i32 4\n\
\x20   %22 = const i32 8\n\
\x20   %32 = add i32 %3, %22\n\
\x20   %42 = inttoptr i32 %32 to ptr\n\
\x20   store i32 %12, ptr %42\n\
\x20   %13 = const i32 1\n\
\x20   %23 = const i32 12\n\
\x20   %33 = add i32 %3, %23\n\
\x20   %43 = inttoptr i32 %33 to ptr\n\
\x20   store i32 %13, ptr %43\n\
\x20   %14 = const i32 5\n\
\x20   %24 = const i32 16\n\
\x20   %34 = add i32 %3, %24\n\
\x20   %44 = inttoptr i32 %34 to ptr\n\
\x20   store i32 %14, ptr %44\n\
\x20   %15 = const i32 9\n\
\x20   %25 = const i32 20\n\
\x20   %35 = add i32 %3, %25\n\
\x20   %45 = inttoptr i32 %35 to ptr\n\
\x20   store i32 %15, ptr %45\n\
\x20   %16 = const i32 2\n\
\x20   %26 = const i32 24\n\
\x20   %36 = add i32 %3, %26\n\
\x20   %46 = inttoptr i32 %36 to ptr\n\
\x20   store i32 %16, ptr %46\n\
\x20   %17 = const i32 6\n\
\x20   %27 = const i32 28\n\
\x20   %37 = add i32 %3, %27\n\
\x20   %47 = inttoptr i32 %37 to ptr\n\
\x20   store i32 %17, ptr %47\n\
\x20   %50 = const i32 7\n\
\x20   %51 = and i32 %0, %50\n\
\x20   %52 = bitcast i32 %51 to u32\n\
\x20   %53 = const u32 8\n\
\x20   %54 = icmp ult u32 %52, %53\n\
\x20   condbr %54, bb1, bb2\n\
bb2:\n\
\x20   unreachable\n\
bb1:\n\
\x20   %55 = ptrtoint ptr %2 to i32\n\
\x20   %56 = const i32 4\n\
\x20   %57 = mul i32 %51, %56\n\
\x20   %58 = add i32 %55, %57\n\
\x20   %59 = inttoptr i32 %58 to ptr\n\
\x20   %60 = load i32, ptr %59\n\
\x20   %61 = add i32 %60, %1\n\
\x20   ret %61\n\
}\n";

#[test]
fn stage_b_forwards_stores_and_promotes_a_constant_table() {
    let module = trust_ir::parser::parse_module(STAGE_B).expect("parse the stage-B program");
    let names = ["fields", "table"];
    let (bytes, evidence) = sized(&module, options(OptLevel::O2, true));
    let mid = &evidence.mid_end;
    assert!(mid.enabled && mid.applied, "{mid:?}");
    assert_eq!(mid.rollback_count(), 0, "{:?}", mid.rollbacks);
    assert_eq!(mid.fallback, None);
    let pass = |name: &str| mid.passes.iter().find(|p| p.name == name).unwrap();
    assert_eq!(
        pass("store_fwd").exact,
        3,
        "three loads, one dominating store each"
    );
    assert_eq!(
        pass("dead_slot").refinements,
        2,
        "the forwarded slot's two stores"
    );
    assert_eq!(pass("ctp").refinements, 1, "one promoted table");
    assert!(mid.tv.samples_compared > 0, "{:?}", mid.tv);
    assert_agrees_on("O2 stage B", &bytes, &module, &names);

    // The promoted table is data: no store is left in `table`, and the
    // module grew by the eight words.
    let (without, _) = sized(&module, options(OptLevel::O2, false));
    assert!(
        bytes.len() < without.len(),
        "{} >= {}",
        bytes.len(),
        without.len()
    );
    assert_agrees_on("O2 without the mid-end", &without, &module, &names);
    let (o0, _) = sized(&module, options(OptLevel::O0, true));
    assert_agrees_on("O0", &o0, &module, &names);

    // Under the caller's fixed one-page policy the table stays in the frame
    // (its data would come out of that page's stack); forwarding still runs.
    let (fixed, evidence) = closed(&module, options(OptLevel::O2, true));
    let mid = &evidence.mid_end;
    assert!(mid.applied, "{mid:?}");
    assert!(
        mid.passes.iter().all(|p| p.name != "ctp"),
        "{:?}",
        mid.passes
    );
    assert!(mid.passes_withheld.contains_key("ctp"), "{mid:?}");
    assert_eq!(mid.globals_added, 0);
    assert_eq!(
        evidence.mid_end.to_json()["passes_withheld"]["ctp"],
        serde_json::json!(mid.passes_withheld["ctp"])
    );
    assert_eq!(
        layout_of(&fixed).data_end,
        0,
        "no static data under a fixed policy"
    );
    assert_agrees_on("O2 under a fixed policy", &fixed, &module, &names);

    let (object, evidence) = wasm::compile_object_with_evidence_license_options(
        &module,
        &permit_unlicensed(),
        options(OptLevel::O2, true),
    )
    .expect("compile the object");
    assert!(evidence.mid_end.applied);
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP: wasm-ld not found (set WASM_LD); the object was not linked");
        return;
    };
    let dir = scratch("link_b");
    std::fs::write(dir.join("m0.o"), &object).unwrap();
    let out = Command::new(&ld)
        .args([
            "--no-entry",
            "--export-dynamic",
            "--stack-first",
            "-z",
            "stack-size=1048576",
            "-o",
        ])
        .arg(dir.join("m.wasm"))
        .arg(dir.join("m0.o"))
        .output()
        .expect("run wasm-ld");
    assert!(
        out.status.success(),
        "wasm-ld refused the object: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let linked = std::fs::read(dir.join("m.wasm")).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert_agrees_on("linked O2 stage B", &linked, &module, &names);
}

/// A `words`-word constant table read through a checked index (`table`),
/// which constant-table promotion turns into `4 * words` bytes of static
/// data, beside a recursion (`deep(n, p)`, `n * (n + 1) / 2 + 7`) whose
/// 256-byte frame slot escapes into the call, so every level keeps its frame;
/// no result depends on where the stack lies.
fn table_and_recursion(words: usize) -> Module {
    use std::fmt::Write as _;
    let mut t = String::from(
        "module \"ctpstack\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         type ty.0 = i32\n\nfuncty.0 = (i32, i32) -> (i32)\n\n\
         fn @table(functy.0) {\nbb0(%0: i32, %1: i32):\n",
    );
    writeln!(t, "    %2 = alloca [ty.0 x {words}], align 4").unwrap();
    t.push_str("    %3 = ptrtoint ptr %2 to i32\n");
    let mut v = 10;
    for i in 0..words {
        let (c, o, a, p) = (v, v + 1, v + 2, v + 3);
        v += 4;
        writeln!(t, "    %{c} = const i32 {}", (i * 7919 + 13) % 100_003).unwrap();
        writeln!(t, "    %{o} = const i32 {}", 4 * i).unwrap();
        writeln!(t, "    %{a} = add i32 %3, %{o}").unwrap();
        writeln!(t, "    %{p} = inttoptr i32 %{a} to ptr").unwrap();
        writeln!(t, "    store i32 %{c}, ptr %{p}").unwrap();
    }
    let (m, b, cc, q) = (v, v + 1, v + 2, v + 3);
    writeln!(t, "    %{m} = const u32 {words}").unwrap();
    writeln!(t, "    %{b} = bitcast i32 %0 to u32").unwrap();
    writeln!(t, "    %{cc} = icmp ult u32 %{b}, %{m}").unwrap();
    writeln!(t, "    condbr %{cc}, bb1, bb2\nbb2:\n    unreachable\nbb1:").unwrap();
    writeln!(t, "    %{q} = const i32 4").unwrap();
    writeln!(t, "    %{} = mul i32 %0, %{q}", q + 1).unwrap();
    writeln!(t, "    %{} = add i32 %3, %{}", q + 2, q + 1).unwrap();
    writeln!(t, "    %{} = inttoptr i32 %{} to ptr", q + 3, q + 2).unwrap();
    writeln!(t, "    %{} = load i32, ptr %{}", q + 4, q + 3).unwrap();
    writeln!(t, "    %{} = add i32 %{}, %1", q + 5, q + 4).unwrap();
    writeln!(t, "    ret %{}\n}}\n", q + 5).unwrap();
    t.push_str(
        "fn @deep(functy.0) {\n\
         bb0(%0: i32, %1: i32):\n\
         \x20   %2 = const i32 0\n\
         \x20   %3 = icmp eq i32 %0, %2\n\
         \x20   condbr %3, bb1, bb2\n\
         bb1:\n\
         \x20   %11 = const i32 7\n\
         \x20   ret %11\n\
         bb2:\n\
         \x20   %4 = alloca [ty.0 x 64], align 4\n\
         \x20   store i32 %0, ptr %4\n\
         \x20   %5 = ptrtoint ptr %4 to i32\n\
         \x20   %6 = const i32 1\n\
         \x20   %7 = sub i32 %0, %6\n\
         \x20   %8 = call @func.1(%7, %5)\n\
         \x20   %9 = load i32, ptr %4\n\
         \x20   %10 = add i32 %8, %9\n\
         \x20   ret %10\n\
         }\n",
    );
    trust_ir::parser::parse_module(&t).expect("parse the table-and-recursion program")
}

/// A closed module's owned pages and where its static data ends (0 without
/// any).
struct Layout {
    pages: u64,
    data_end: u64,
}

fn layout_of(bytes: &[u8]) -> Layout {
    let mut pages = 0;
    let mut data_end = 0;
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        match payload.expect("parse") {
            wasmparser::Payload::MemorySection(r) => {
                for m in r {
                    pages = m.expect("memory").initial;
                }
            }
            wasmparser::Payload::DataSection(r) => {
                for d in r {
                    let d = d.expect("data segment");
                    if let wasmparser::DataKind::Active { offset_expr, .. } = d.kind {
                        let mut ops = offset_expr.get_operators_reader();
                        let Ok(wasmparser::Operator::I32Const { value }) = ops.read() else {
                            panic!("a data segment at a non-constant offset");
                        };
                        data_end = data_end.max(value as u32 as u64 + d.data.len() as u64);
                    }
                }
            }
            _ => {}
        }
    }
    Layout { pages, data_end }
}

/// The shadow stack above a closed module's static data, measured as the
/// lane's stack guard and `WASM_CLOSED_MIN_STACK_BYTES` measure it.
fn stack_bytes(layout: &Layout) -> u64 {
    let floor = layout.data_end.max(u64::from(wasm::WASM_STATIC_DATA_BASE));
    layout.pages * 65_536 - floor.div_ceil(8) * 8
}

/// `deep(n, 0)` for each `n` and `table(5, 0)` in one fresh instance each:
/// `Err` is a trap. `None` without node.
fn run_deep(bytes: &[u8], depths: &[i64]) -> Option<Vec<Result<i64, String>>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; the module was not executed");
        return None;
    };
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
    let dir = scratch("deep");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let calls: Vec<String> = depths
        .iter()
        .map(|n| format!("() => fresh().deep({n}, 0)"))
        .chain(std::iter::once("() => fresh().table(5, 0)".to_string()))
        .collect();
    let js = format!(
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const fresh = () => new WebAssembly.Instance(m, {{}}).exports;\n\
         const out = [{}].map(f => {{ try {{ return {{ok: f()}}; }} \
         catch (e) {{ return {{trap: String(e.message)}}; }} }});\n\
         process.stdout.write(JSON.stringify(out));\n",
        calls.join(",")
    );
    std::fs::write(dir.join("run.js"), js).unwrap();
    let out = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "node failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let rows: Vec<serde_json::Value> = serde_json::from_slice(&out.stdout).expect("node JSON");
    Some(
        rows.into_iter()
            .map(|row| match row.get("ok") {
                Some(v) => Ok(v.as_i64().expect("an i32 result")),
                None => Err(row["trap"].to_string()),
            })
            .collect(),
    )
}

/// A PROMOTED TABLE NEVER SHORTENS THE STACK. Constant-table promotion moves
/// a 60,000-byte table out of `table`'s frame into static data. In the sized
/// closed module (the CLI's route) static data sits below the shadow stack,
/// so the memory must grow by what the data took: the optimized module keeps
/// at least the stack the input module had, and a recursion that runs at O0
/// runs at O2. (Sized for the input alone, one page kept about 5.5 KB of
/// stack and `deep(100)` trapped in the stack guard.) Under a caller's fixed
/// one-page policy, and on an island whose host reserved a data region the
/// input never used, promotion is withheld: no static data appears.
#[test]
fn a_promoted_table_never_shortens_the_inputs_stack() {
    let module = table_and_recursion(15_000);
    let depths = [20, 100, 200];

    let (o0, _) = sized(&module, options(OptLevel::O0, true));
    let (o2, evidence) = sized(&module, options(OptLevel::O2, true));
    let mid = &evidence.mid_end;
    assert!(mid.applied, "{mid:?}");
    assert_eq!(mid.globals_added, 1, "the table is promoted: {mid:?}");
    // Only the passes withheld for missing implementation custody (OD-155,
    // OD-164): constant-table promotion is not withheld.
    assert_eq!(
        mid.passes_withheld.keys().copied().collect::<Vec<_>>(),
        ["fill_call", "mem_cmp"],
        "{mid:?}"
    );
    let (before, after) = (layout_of(&o0), layout_of(&o2));
    assert_eq!(before.data_end, 0, "O0 has no static data");
    assert!(
        after.data_end >= 60_000,
        "the promoted table is static data: {}",
        after.data_end
    );
    assert!(
        stack_bytes(&after) >= stack_bytes(&before),
        "O2 keeps {} bytes of stack, the input {} ({} pages vs {})",
        stack_bytes(&after),
        stack_bytes(&before),
        after.pages,
        before.pages
    );
    assert!(stack_bytes(&after) >= u64::from(wasm::WASM_CLOSED_MIN_STACK_BYTES));
    assert_eq!(after.pages, 2, "one page grown for the table");
    // Without the mid-end, the sized entry is the sized policy's compile.
    let policy = wasm::sized_closed_policy(&module).expect("size");
    let (plain, _) = wasm::compile_module_with_evidence_policy_license_options(
        &module,
        &policy,
        &permit_unlicensed(),
        options(OptLevel::O2, false),
    )
    .expect("compile under the sized policy");
    assert_eq!(sized(&module, options(OptLevel::O2, false)).0, plain);

    let want = run_deep(&o0, &depths);
    if let Some(want) = &want {
        let sums: Vec<Result<i64, String>> = depths
            .iter()
            .map(|n| Ok(n * (n + 1) / 2 + 7))
            .chain(std::iter::once(Ok(5 * 7919 + 13)))
            .collect();
        assert_eq!(want, &sums, "O0 runs every depth");
        assert_eq!(run_deep(&o2, &depths).as_ref(), Some(want), "sized O2");
    }

    // The caller's fixed one-page policy: promotion is withheld.
    let (fixed, evidence) = closed(&module, options(OptLevel::O2, true));
    let mid = &evidence.mid_end;
    assert!(mid.passes_withheld.contains_key("ctp"), "{mid:?}");
    assert_eq!(mid.globals_added, 0, "{mid:?}");
    let fixed_layout = layout_of(&fixed);
    assert_eq!((fixed_layout.pages, fixed_layout.data_end), (1, 0));
    if let Some(want) = &want {
        assert_eq!(run_deep(&fixed, &depths).as_ref(), Some(want), "fixed O2");
    }

    // An island whose host reserved a data region: the input writes nothing
    // there, so the optimized module may not take a grant either.
    let island = wasm::WasmModulePolicy {
        static_data: wasm::WasmStaticDataPolicy::HostReservedAt { base: 4096 },
        ..wasm::WasmModulePolicy::island("ctp")
    };
    for level in [OptLevel::O0, OptLevel::O2] {
        let (_, evidence) = wasm::compile_module_with_evidence_policy_license_options(
            &module,
            &island,
            &permit_unlicensed(),
            options(level, true),
        )
        .expect("compile the island");
        assert!(
            !evidence
                .host_contract
                .iter()
                .any(|t| t.starts_with("data ")),
            "{level:?}: no data grant: {:?}",
            evidence.host_contract
        );
        assert_eq!(evidence.mid_end.globals_added, 0, "{level:?}");
    }
}

/// The differential interprets the bridge's global-address stub constant as
/// the global's address (`trust_ir_mid_tv::global_addr_stub`); its decoder
/// must read every stub this crate's codec writes, and nothing else.
#[test]
fn the_differential_view_decodes_the_global_address_stub() {
    use trust_cg_codegen::global_stub::{decode_global_addr_stub, encode_global_addr_stub};
    use trust_cg_verify::trust_ir_mid_tv::global_addr_stub;
    for (index, offset) in [
        (0, 0),
        (1, 0),
        (7, 12),
        (0xFFFF, 0xFFFF_FFFF),
        (300, 65_536),
    ] {
        let stub = encode_global_addr_stub(index, offset).expect("in range");
        let expected = decode_global_addr_stub(stub);
        assert_eq!(expected, Some((index, offset as u32)));
        assert_eq!(global_addr_stub(stub), expected, "{stub:#x}");
    }
    for value in [
        0i128,
        7,
        -1,
        0xFADD_0000_0000_0000,
        1 << 64,
        0x0FAD_E000_0000_0000,
    ] {
        assert_eq!(
            global_addr_stub(value),
            decode_global_addr_stub(value),
            "{value:#x}"
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
