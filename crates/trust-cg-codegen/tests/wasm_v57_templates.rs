// trust-cg-codegen/tests/wasm_v57_templates.rs — trust-ir amendment S (wire
// v57, level-S generic templates) on both wasm32 lanes and the mid-end.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Amendment S adds no level-R construct: `Ty`, `Constant`, `Inst` and
//! `Module` are the generic carriers at the uninhabited `NoExt`, so the new
//! `Ext` arms cannot be built, decoded or handed to a lane. What it does add
//! is a second artifact, the level-S template, and a producer route: a host
//! instantiates a template into an ordinary level-R module. This target pins
//! both ends on the closed-module and the object lane:
//!
//! * level R carries no extension value (checked at compile time);
//! * the pinned corpus's three amendment-S refuse rows (a template blob, and
//!   the `Ext` tags of a type and of a constant under the module magic) and
//!   a template in binary and text form are refused by trust-cg's reader, by
//!   name, before any lane or the mid-end sees a module;
//! * an instance as a host produces it carries a body gate: the license
//!   layer decides first on both lanes at O0 and O2 (an `ungated` instance is
//!   refused there), and the mid-end treats the gated body as a barrier and
//!   leaves it alone;
//! * an instance body without a gate is driven through the mid-end at O2
//!   (whose witness checker and interpreter differential accept each kept
//!   rewrite) and through both lanes at O0 and O2, and every form agrees
//!   with the trust-ir reference interpreter in node (the object linked by
//!   `wasm-ld`, `WASM_LD`).
//!
//! Node and `wasm-ld` are required to execute; the absence of either is a
//! loud SKIP. Test-rung evidence; no proof of the lowering is claimed.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::CodegenLicensePolicy;
use trust_cg_codegen::pipeline::{self, FormatMode, OptLevel, TEMPLATE_IS_NOT_A_MODULE};
use trust_cg_codegen::wasm::{self, WasmLowerError, WasmModulePolicy, WasmOptOptions};
use trust_cg_irmid::{MidConfig, optimize_module};
use trust_ir::template::{
    HoleAnswer, InstArg, InstanceHeader, ScriptedAnswer, ScriptedHost, Template,
};
use trust_ir::{
    BodyGate, CallingConv, Constant, InterpretOptions, InterpretValue, InterpretValueKind,
    Interpreter, Linkage, Module, NoExt, Ty, TyG, Visibility,
};
use trust_ir_conformance::refuse::corpus;

/// A gate authority this target recognizes for its own run only.
const TEST_AUTHORITY: &str = "trust-cg-test-wasm-v57";

/// `fn identity<T>(x: T) -> T`, through a copy and a constant branch.
const IDENT: &str = "; TrustIr template text format v1\n\
template \"t::identity\"\n\
param $0 type\n\
; TrustIr text format v1\n\
module \"t\"\n\
target \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = ($0) -> ($0)\n\n\
fn @\"!template_body\"(functy.0) {\n\
bb0(%0: $0):\n\
\x20   %1 = copy $0 %0\n\
\x20   %2 = const bool true\n\
\x20   condbr %2, bb1, bb2\n\
bb1:\n\
\x20   ret %1\n\
bb2:\n\
\x20   ret %0\n\
}\n";

/// `fn frame<const K: i32>(x: i32, y: i32) -> i32 { x * K + y }`, written in
/// the rustc bridge's frame-slot shape (a `ptrtoint`/`add`/`inttoptr` chain
/// into an `alloca`, copies, a constant branch, a dead multiply).
const FRAME: &str = "; TrustIr template text format v1\n\
template \"t::frame::<K>\"\n\
param $0 const i32\n\
; TrustIr text format v1\n\
module \"t\"\n\
target \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i32\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
fn @\"!template_body\"(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   %3 = copy ptr %2\n\
\x20   %4 = ptrtoint ptr %3 to i32\n\
\x20   %5 = const i32 4\n\
\x20   %6 = copy i32 %5\n\
\x20   %7 = add i32 %4, %6\n\
\x20   %8 = inttoptr i32 %7 to ptr\n\
\x20   store i32 %0, ptr %8\n\
\x20   %9 = const i32 $0\n\
\x20   %10 = copy i32 %9\n\
\x20   %11 = mul i32 %10, %10\n\
\x20   %12 = const bool true\n\
\x20   condbr %12, bb1, bb2\n\
bb1:\n\
\x20   %13 = load i32, ptr %8\n\
\x20   %14 = mul i32 %13, %10\n\
\x20   %15 = add i32 %14, %1\n\
\x20   ret %15\n\
bb2:\n\
\x20   ret %1\n\
}\n";

/// `fn plus_size<T>(n: usize) -> usize { n + size_of::<T>() }`: a const hole.
const PLUS_SIZE: &str = "; TrustIr template text format v1\n\
template \"t::plus_size::<T>\"\n\
param $0 type\n\
hole ?0 const usize key \"rust\" [116, 58, 58, 115, 105, 122, 101] args ($0)\n\
; TrustIr text format v1\n\
module \"t\"\n\
target \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (usize) -> (usize)\n\n\
fn @\"!template_body\"(functy.0) {\n\
bb0(%0: usize):\n\
\x20   %1 = const usize ?0\n\
\x20   %2 = copy usize %1\n\
\x20   %3 = add usize %0, %2\n\
\x20   ret %3\n\
}\n";

/// One instantiation: the template, its symbol, the host's arguments and
/// hole answers, and whether the mid-end must change the body at O2.
struct Case {
    template: &'static str,
    symbol: &'static str,
    arguments: Vec<InstArg>,
    holes: Vec<ScriptedAnswer>,
    rewritten: bool,
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            template: IDENT,
            symbol: "identity_i32",
            arguments: vec![InstArg::Type(Ty::I32)],
            holes: vec![],
            rewritten: true,
        },
        Case {
            template: IDENT,
            symbol: "identity_u32",
            arguments: vec![InstArg::Type(Ty::U32)],
            holes: vec![],
            rewritten: true,
        },
        Case {
            template: FRAME,
            symbol: "frame_3",
            arguments: vec![InstArg::Const(Constant::Int(3))],
            holes: vec![],
            rewritten: true,
        },
        Case {
            template: FRAME,
            symbol: "frame_minus_7",
            arguments: vec![InstArg::Const(Constant::Int(-7))],
            holes: vec![],
            rewritten: true,
        },
        Case {
            template: PLUS_SIZE,
            symbol: "plus_size_u64",
            arguments: vec![InstArg::Type(Ty::U64)],
            holes: vec![ScriptedAnswer::Answer(HoleAnswer::Const(Constant::Int(8)))],
            rewritten: true,
        },
    ]
}

/// Inputs every case runs on (truncated to each parameter's type).
const ROWS: &[(i64, i64)] = &[(0, 0), (1, 2), (7, 3), (-5, 9), (100, 10), (-1, 1)];

fn template(text: &str) -> Template {
    trust_ir::parser::parse_template(text).expect("parse the test template")
}

/// The instance `case`'s host produces, its body gated by `gate`.
fn instance(case: &Case, gate: BodyGate) -> Module {
    let template = template(case.template);
    let mut host = ScriptedHost {
        arguments: case.arguments.clone(),
        holes: case.holes.clone(),
        header: Some(InstanceHeader {
            symbol: case.symbol.to_string(),
            linkage: Linkage::External,
            visibility: Visibility::Default,
            calling_conv: CallingConv::default(),
            attrs: Default::default(),
            display_path: None,
            body_gate: gate,
        }),
        ..ScriptedHost::default()
    };
    let instance = trust_ir_build::template::instantiate(&template, &mut host)
        .unwrap_or_else(|e| panic!("{}: instantiation refused: {e:?}", case.symbol));
    let module = instance.module;
    assert_eq!(
        module.target_info.as_ref().map(|t| t.triple.as_str()),
        Some("wasm32-unknown-unknown"),
        "{}",
        case.symbol
    );
    assert!(
        trust_ir_build::validate_module(&module).is_empty(),
        "{}",
        case.symbol
    );
    module
}

/// The instance with its body's gate removed: a body the default license
/// admits and the mid-end may rewrite.
fn ungated_free(case: &Case) -> Module {
    let mut module = instance(case, BodyGate::Ungated);
    for func in &mut module.functions {
        func.body_gate = None;
    }
    module
}

fn test_license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_recognized_authority(TEST_AUTHORITY)
}

fn gated() -> BodyGate {
    BodyGate::gated(TEST_AUTHORITY.to_string())
}

fn opts(level: OptLevel) -> WasmOptOptions {
    WasmOptOptions {
        level,
        mid_end: true,
    }
}

type Lane = fn(
    &Module,
    &CodegenLicensePolicy,
    WasmOptOptions,
) -> Result<(Vec<u8>, wasm::WasmCompileEvidence), WasmLowerError>;

fn closed_lane(
    m: &Module,
    l: &CodegenLicensePolicy,
    o: WasmOptOptions,
) -> Result<(Vec<u8>, wasm::WasmCompileEvidence), WasmLowerError> {
    wasm::compile_module_with_evidence_policy_license_options(m, &WasmModulePolicy::closed(), l, o)
}

fn object_lane(
    m: &Module,
    l: &CodegenLicensePolicy,
    o: WasmOptOptions,
) -> Result<(Vec<u8>, wasm::WasmCompileEvidence), WasmLowerError> {
    wasm::compile_object_with_evidence_license_options(m, l, o)
}

const LANES: &[(&str, Lane)] = &[("wasm-module", closed_lane), ("wasm-object", object_lane)];
const LEVELS: &[OptLevel] = &[OptLevel::O0, OptLevel::O2];

// ---------------------------------------------------------------------------
// Execution
// ---------------------------------------------------------------------------

fn params(module: &Module, name: &str) -> Vec<Ty> {
    let f = module.function_by_name(name).expect("function");
    module.func_type(f.ty).expect("signature").params.clone()
}

/// `row` as `name`'s arguments, each truncated to its parameter type.
fn arguments(module: &Module, name: &str, row: (i64, i64)) -> Vec<InterpretValue> {
    params(module, name)
        .into_iter()
        .zip([row.0, row.1])
        .map(|(ty, v)| {
            let bits = ty.bit_width().unwrap_or(32);
            let v = i128::from(v);
            let v = if ty.is_signed() {
                v
            } else {
                v & ((1i128 << bits) - 1)
            };
            InterpretValue::int(ty, v).expect("an in-range scalar")
        })
        .collect()
}

/// `name(row)` by the reference interpreter, as the i32 node reports.
fn interpret(module: &Module, name: &str, row: (i64, i64)) -> i64 {
    let f = module.function_by_name(name).expect("function");
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 64,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, arguments(module, name, row))
        .unwrap_or_else(|e| panic!("{name}{row:?} is refused by the interpreter: {e:?}"));
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
    let dir = std::env::temp_dir().join(format!("tcg_wasm_v57_{tag}_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// `name` over [`ROWS`] in node (arguments truncated as [`arguments`]
/// truncates them); `None` when node is absent.
fn run(bytes: &[u8], module: &Module, name: &str) -> Option<Vec<i64>> {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; the module was not executed");
        return None;
    };
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("the module does not validate: {e}"));
    let arity = params(module, name).len();
    let dir = scratch("run");
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let rows: Vec<String> = ROWS
        .iter()
        .map(|&row| {
            let args: Vec<String> = arguments(module, name, row)
                .iter()
                .map(|v| match &v.kind {
                    InterpretValueKind::Int(i) => (i.as_signed() as i32).to_string(),
                    other => panic!("{other:?}"),
                })
                .collect();
            format!("[{}]", args.join(","))
        })
        .collect();
    assert!(
        rows.iter()
            .all(|r| r.matches(',').count() + 1 == arity.max(1))
    );
    let js = format!(
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const imports = {{}};\n\
         for (const i of WebAssembly.Module.imports(m)) {{ imports[i.module] ??= {{}}; }}\n\
         const inst = new WebAssembly.Instance(m, imports);\n\
         const out = [{}].map((a) => inst.exports['{name}'](...a));\n\
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

/// Link a wasm object into a module exporting every symbol; `None` when
/// `wasm-ld` is absent.
fn link(object: &[u8]) -> Option<Vec<u8>> {
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP: wasm-ld not found (set WASM_LD); the object was not linked");
        return None;
    };
    let dir = scratch("link");
    std::fs::write(dir.join("m0.o"), object).unwrap();
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
    Some(linked)
}

fn assert_agrees(tag: &str, bytes: &[u8], module: &Module, name: &str) {
    let want: Vec<i64> = ROWS
        .iter()
        .map(|&row| interpret(module, name, row))
        .collect();
    if let Some(got) = run(bytes, module, name) {
        assert_eq!(got, want, "{tag}: {name} disagrees with the interpreter");
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Level R has no extension value: every `Ext` arm a lane or a mid-end pass
/// could meet is uninhabited. Compiles only while `NoExt` has no variant and
/// the level-R aliases are the `NoExt` carriers.
#[test]
fn level_r_carries_no_extension_value() {
    fn absurd(e: NoExt) -> ! {
        match e {}
    }
    fn ty_ext(t: &Ty) -> bool {
        match t {
            TyG::Ext(e) => absurd(*e),
            _ => false,
        }
    }
    fn constant_ext(c: &Constant) -> bool {
        match c {
            trust_ir::ConstantG::Ext(e) => absurd(*e),
            _ => false,
        }
    }
    let _: fn(Ty) -> TyG<NoExt> = |t| t;
    let _: fn(Module) -> trust_ir::ModuleG<NoExt> = |m| m;
    assert!(!ty_ext(&Ty::I32));
    assert!(!constant_ext(&Constant::Int(0)));
}

/// The three amendment-S rows of the pinned must-refuse corpus are `bytes`
/// rows: trust-cg's reader refuses each before any lane or the mid-end could
/// see a module, and names a template as one.
#[test]
fn amendment_s_refuse_rows_are_refused_by_the_reader() {
    let rows = corpus().expect("the pinned must-refuse corpus loads");
    let expected: &[(&str, &[&str])] = &[
        (
            "template_blob_is_not_a_module",
            &[TEMPLATE_IS_NOT_A_MODULE, pipeline::NOT_A_BINARY_MODULE],
        ),
        ("ty_ext_tag_under_module_magic", &["tag"]),
        ("constant_ext_tag_under_module_magic", &["tag"]),
    ];
    for (id, needles) in expected {
        let row = rows
            .iter()
            .find(|row| row.id() == *id)
            .unwrap_or_else(|| panic!("the pinned corpus has no row `{id}`"));
        assert!(row.module().is_none(), "{id}: expected a `bytes` row");
        let error = pipeline::load_module_from_bytes(row.wire_bytes())
            .expect_err(&format!("{id}: trust-cg's reader decoded the row"))
            .to_string();
        for needle in *needles {
            assert!(
                error.to_lowercase().contains(&needle.to_lowercase()),
                "{id}: refused without `{needle}`: {error}"
            );
        }
        let decoded = pipeline::decode_binary(row.wire_bytes());
        assert!(decoded.is_err(), "{id}: decode_binary accepted the row");
    }
}

/// A template, in binary and in text form, through every reader entry: each
/// refuses it by name, whatever the file is called.
#[test]
fn a_template_is_refused_by_name_by_every_reader_entry() {
    let ident = template(IDENT);
    let blob = trust_ir::binary::serialize_template(&ident).expect("serialize the template");
    assert_eq!(&blob[..8], b"TRUST_IS");
    let dir = scratch("reader");
    for (form, bytes) in [
        ("binary", blob.clone()),
        ("text", IDENT.as_bytes().to_vec()),
    ] {
        let error = pipeline::load_module_from_bytes(&bytes)
            .expect_err(&format!("{form}: the template decoded as a module"))
            .to_string();
        assert!(error.contains(TEMPLATE_IS_NOT_A_MODULE), "{form}: {error}");
        for (file, modes) in [
            ("t.tmbc", &[FormatMode::Auto, FormatMode::Tmbc][..]),
            ("t.trust_ir", &[FormatMode::Auto, FormatMode::Text][..]),
            ("t.bin", &[FormatMode::Auto][..]),
        ] {
            let path = dir.join(file);
            std::fs::write(&path, &bytes).unwrap();
            for &mode in modes {
                let error = pipeline::load_module_as(&path, mode)
                    .expect_err(&format!("{form} {file} {mode:?}: decoded as a module"))
                    .to_string();
                let named = error.contains(TEMPLATE_IS_NOT_A_MODULE)
                    // `.tmbc` text is read as binary and refused by magic.
                    || (form == "text" && error.contains(pipeline::NOT_A_BINARY_MODULE));
                assert!(named, "{form} {file} {mode:?}: {error}");
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// An instance as a host produces it carries the host's body gate. The
/// license layer decides first on both lanes at every level: `ungated` is
/// refused before the mid-end or the lowering; a gate the caller recognizes
/// compiles, the mid-end leaves the gated body alone (a barrier, reported as
/// `body_gate`), and the result agrees with the interpreter.
#[test]
fn instances_as_produced_are_licensed_first_and_the_mid_end_leaves_them_alone() {
    for case in cases() {
        let ungated = instance(&case, BodyGate::Ungated);
        for (lane, compile) in LANES {
            for &level in LEVELS {
                let error = compile(&ungated, &test_license(), opts(level)).expect_err(&format!(
                    "{lane} {level:?}: the ungated {} compiled",
                    case.symbol
                ));
                assert!(
                    matches!(error, WasmLowerError::CodegenLicense(_)),
                    "{lane} {level:?} {}: expected the license refusal first, got {error:?}",
                    case.symbol
                );
            }
        }

        let module = instance(&case, gated());
        let (out, report) = optimize_module(&module, &MidConfig::wasm32());
        assert_eq!(
            out, module,
            "{}: the mid-end changed a gated body",
            case.symbol
        );
        assert_eq!(report.functions_changed, 0, "{}", case.symbol);
        assert_eq!(
            report.skipped.get("body_gate").copied(),
            Some(1),
            "{}: {:?}",
            case.symbol,
            report.skipped
        );
        for (lane, compile) in LANES {
            for &level in LEVELS {
                let (bytes, evidence) = compile(&module, &test_license(), opts(level))
                    .unwrap_or_else(|e| panic!("{lane} {level:?} {}: {e}", case.symbol));
                assert_eq!(evidence.mid_end.functions_changed, 0, "{lane} {level:?}");
                if *lane == "wasm-module" {
                    assert_agrees(&format!("{lane} {level:?}"), &bytes, &module, case.symbol);
                }
            }
        }
    }
}

/// An instance body without a gate through the mid-end at O2 (every kept
/// rewrite accepted by its witness checker and the interpreter differential)
/// and through both lanes at O0 and O2; every form agrees with the
/// interpreter in node.
#[test]
fn instance_bodies_through_the_mid_end_at_o2_and_both_lanes() {
    for case in cases() {
        let module = ungated_free(&case);
        let (optimized, report) = optimize_module(&module, &MidConfig::wasm32());
        assert_eq!(
            report.rollback_count(),
            0,
            "{}: {:?}",
            case.symbol,
            report.rollbacks
        );
        assert_eq!(
            report.skipped_count(),
            0,
            "{}: {:?}",
            case.symbol,
            report.skipped
        );
        if case.rewritten {
            assert_eq!(report.functions_changed, 1, "{}: {report:?}", case.symbol);
        }
        assert!(trust_ir_build::validate_module(&optimized).is_empty());
        for &row in ROWS {
            assert_eq!(
                interpret(&optimized, case.symbol, row),
                interpret(&module, case.symbol, row),
                "{}{row:?}: the mid-end's output disagrees with its input",
                case.symbol
            );
        }

        for &level in LEVELS {
            // This branch deliberately removes the source body's gate. Keep
            // its lowering comparison separate from strict license controls.
            let license = CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit);
            let (bytes, evidence) = closed_lane(&module, &license, opts(level))
                .unwrap_or_else(|e| panic!("wasm-module {level:?} {}: {e}", case.symbol));
            if level == OptLevel::O2 && case.rewritten {
                assert!(
                    evidence.mid_end.applied,
                    "{}: {:?}",
                    case.symbol, evidence.mid_end
                );
                assert_eq!(evidence.mid_end.functions_changed, 1, "{}", case.symbol);
            }
            assert_agrees(
                &format!("wasm-module {level:?}"),
                &bytes,
                &module,
                case.symbol,
            );

            let (object, evidence) = object_lane(&module, &license, opts(level))
                .unwrap_or_else(|e| panic!("wasm-object {level:?} {}: {e}", case.symbol));
            if level == OptLevel::O2 && case.rewritten {
                assert!(
                    evidence.mid_end.applied,
                    "{}: {:?}",
                    case.symbol, evidence.mid_end
                );
            }
            if let Some(linked) = link(&object) {
                assert_agrees(
                    &format!("wasm-object {level:?}"),
                    &linked,
                    &module,
                    case.symbol,
                );
            }
        }
    }
}
