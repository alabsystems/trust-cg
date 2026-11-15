// trust-cg-codegen/tests/wasm_g2_lane_objects.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The wasm32 relocatable-object and link path: symbol kinds and bindings,
//! relocation order, the indirect function table, and the closed module's
//! null function pointer.
//!
//! Every module below is valid trust-ir. Where the trust-ir interpreter
//! executes it, the linked (or closed) module must compute what the
//! interpreter computes; where it does not (`reify_fn_pointer` and a pointer
//! loaded from `symaddr` data are outside the pinned interpreter), the
//! expected values are exact and stated with the reason.
//!
//! Structure is asserted on the object itself (its symbol table, imports and
//! relocations, decoded by `wasmparser`). Execution needs `wasm-ld`
//! (`$WASM_LD` or PATH) and `node`; without them the execution leg is a loud
//! SKIP, never a silent pass.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm;
use trust_ir::{
    InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, parser,
};
use wasmparser::{KnownCustom, Linking, Parser, Payload, RelocationType, SymbolInfo, TypeRef};

/// `WASM_SYM_UNDEFINED`.
const UNDEFINED: u32 = 0x10;
/// `WASM_SYM_VISIBILITY_HIDDEN`.
const HIDDEN: u32 = 0x4;
/// `WASM_SYM_NO_STRIP`.
const NO_STRIP: u32 = 0x80;

fn parse(text: &str) -> Module {
    parser::parse_module(text).unwrap_or_else(|e| panic!("test module failed to parse: {e}"))
}

fn validate(bytes: &[u8]) {
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("emitted wasm does not validate: {e}"));
}

/// `compile_object`, validated.
fn object(text: &str) -> Vec<u8> {
    let bytes = wasm::compile_object_with_license(&parse(text), &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_object: {e}"));
    validate(&bytes);
    bytes
}

/// `compile_module` (closed), validated.
fn closed(text: &str) -> Vec<u8> {
    let bytes = wasm::compile_module_with_license(&parse(text), &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_module: {e}"));
    validate(&bytes);
    bytes
}

/// One symbol-table entry of an object.
#[derive(Debug)]
struct Sym {
    kind: &'static str,
    name: String,
    flags: u32,
}

/// One object relocation's kind, section offset and symbol index.
type ObjectRelocation = (RelocationType, u32, u32);

/// What a relocatable object declares: imports, symbols and relocations.
#[derive(Debug, Default)]
struct ObjectView {
    /// `(module, name, kind)`.
    imports: Vec<(String, String, &'static str)>,
    symbols: Vec<Sym>,
    /// `(section name, [(type, offset, symbol index)])`.
    relocs: Vec<(String, Vec<ObjectRelocation>)>,
    data_segments: u32,
}

impl ObjectView {
    fn symbol(&self, kind: &str, name: &str) -> &Sym {
        self.symbols
            .iter()
            .find(|s| s.kind == kind && s.name == name)
            .unwrap_or_else(|| panic!("no {kind} symbol `{name}` in {:?}", self.symbols))
    }

    fn relocs_of(&self, section: &str) -> &[(RelocationType, u32, u32)] {
        self.relocs
            .iter()
            .find(|(n, _)| n == section)
            .map(|(_, r)| r.as_slice())
            .unwrap_or(&[])
    }

    fn imports_table(&self) -> bool {
        self.imports
            .iter()
            .any(|(m, n, k)| m == "env" && n == "__indirect_function_table" && *k == "table")
    }
}

fn view(bytes: &[u8]) -> ObjectView {
    let mut v = ObjectView::default();
    let mut func_imports: Vec<String> = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.expect("parse object") {
            Payload::ImportSection(r) => {
                for import in r {
                    let import = import.expect("import");
                    let kind = match import.ty {
                        TypeRef::Func(_) => {
                            func_imports.push(import.name.to_string());
                            "func"
                        }
                        TypeRef::Table(_) => "table",
                        TypeRef::Memory(_) => "memory",
                        TypeRef::Global(_) => "global",
                        _ => "other",
                    };
                    v.imports
                        .push((import.module.to_string(), import.name.to_string(), kind));
                }
            }
            Payload::DataSection(r) => v.data_segments = r.count(),
            Payload::CustomSection(c) => match c.as_known() {
                KnownCustom::Linking(linking) => {
                    for sub in linking.subsections() {
                        let Linking::SymbolTable(map) = sub.expect("linking subsection") else {
                            continue;
                        };
                        for info in map {
                            let sym = match info.expect("symbol") {
                                SymbolInfo::Func { flags, index, name } => Sym {
                                    kind: "func",
                                    name: name
                                        .map(str::to_string)
                                        .or_else(|| func_imports.get(index as usize).cloned())
                                        .unwrap_or_default(),
                                    flags: flags.bits(),
                                },
                                SymbolInfo::Data { flags, name, .. } => Sym {
                                    kind: "data",
                                    name: name.to_string(),
                                    flags: flags.bits(),
                                },
                                SymbolInfo::Table { flags, name, .. } => Sym {
                                    kind: "table",
                                    name: name.unwrap_or("__indirect_function_table").to_string(),
                                    flags: flags.bits(),
                                },
                                SymbolInfo::Global { flags, name, .. } => Sym {
                                    kind: "global",
                                    name: name.unwrap_or_default().to_string(),
                                    flags: flags.bits(),
                                },
                                _ => continue,
                            };
                            v.symbols.push(sym);
                        }
                    }
                }
                KnownCustom::Reloc(r) => {
                    let entries = r
                        .entries()
                        .into_iter()
                        .map(|e| {
                            let e = e.expect("relocation");
                            (e.ty, e.offset, e.index)
                        })
                        .collect();
                    v.relocs.push((c.name().to_string(), entries));
                }
                _ => {}
            },
            _ => {}
        }
    }
    v
}

fn wasm_ld() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("WASM_LD").filter(|p| !p.is_empty()) {
        return Some(PathBuf::from(p));
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|d| d.join("wasm-ld"))
        .find(|p| p.is_file())
}

fn node() -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|d| d.join("node"))
        .find(|p| p.is_file())
}

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_wasm_g2_{tag}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Link `objects` with `wasm-ld` as the CLI and rustc do (`--gc-sections`,
/// the linker's default), exporting every defined symbol. `Ok(None)` when no
/// linker is available.
fn link(tag: &str, objects: &[&[u8]], extra: &[&str]) -> Option<Result<Vec<u8>, String>> {
    let ld = wasm_ld()?;
    let dir = scratch(tag);
    let mut cmd = Command::new(ld);
    cmd.args(["--no-entry", "--export-dynamic"]).args(extra);
    for (i, bytes) in objects.iter().enumerate() {
        let path = dir.join(format!("in{i}.o"));
        std::fs::write(&path, bytes).unwrap();
        cmd.arg(path);
    }
    let out = dir.join("out.wasm");
    let run = cmd.arg("-o").arg(&out).output().expect("run wasm-ld");
    let result = if run.status.success() {
        Ok(std::fs::read(&out).unwrap())
    } else {
        Err(format!(
            "{} ({})",
            String::from_utf8_lossy(&run.stderr),
            run.status
        ))
    };
    let _ = std::fs::remove_dir_all(&dir);
    Some(result)
}

/// Evaluate each JS expression (over the module's exports) under node; a
/// trap is `"trap"`. `None` without node.
fn run(tag: &str, bytes: &[u8], calls: &[&str]) -> Option<Vec<String>> {
    let node = node()?;
    let dir = scratch(tag);
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    std::fs::write(
        dir.join("run.js"),
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const env = { fmod: (a, b) => a % b, fmodf: (a, b) => Math.fround(Math.fround(a) % Math.fround(b)) };\n\
         const E = new WebAssembly.Instance(m, { env }).exports;\n\
         const calls = JSON.parse(fs.readFileSync(process.argv[3]));\n\
         const out = calls.map(c => { try { return String(Function('E', 'with (E) { return (' + c + '); }')(E)); } catch (e) { return 'trap'; } });\n\
         process.stdout.write(JSON.stringify(out));\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("calls.json"),
        serde_json::to_string(calls).unwrap(),
    )
    .unwrap();
    let out = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(dir.join("calls.json"))
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

fn skip(test: &str, what: &str) {
    eprintln!("SKIP {test}: {what} needs wasm-ld (set WASM_LD) and node");
}

/// The interpreter's integer answer for `name(args)`, `None` if it refuses.
fn interpret_int(module: &Module, name: &str, args: &[(Ty, i128)]) -> Option<i128> {
    let f = module.function_by_name(name).expect("function");
    let values: Vec<InterpretValue> = args
        .iter()
        .map(|(ty, v)| InterpretValue::int(ty.clone(), *v).expect("int value"))
        .collect();
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 64,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, values)
        .ok()?;
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => Some(i.as_signed()),
        InterpretValueKind::Bool(b) => Some(i128::from(*b)),
        other => panic!("{name} returned {other:?}"),
    }
}

/// The interpreter's `f64` answer for `name(a, b)`.
fn interpret_f64(module: &Module, name: &str, a: f64, b: f64) -> f64 {
    let f = module.function_by_name(name).expect("function");
    let arg = |x: f64| InterpretValue {
        ty: Ty::F64,
        kind: InterpretValueKind::FloatBits(x.to_bits()),
    };
    let out = Interpreter::with_module(module)
        .execute_func(f.id, vec![arg(a), arg(b)])
        .unwrap_or_else(|e| panic!("interpreter refused {name}({a}, {b}): {e}"));
    match &out.returns[0].kind {
        InterpretValueKind::FloatBits(bits) => f64::from_bits(*bits),
        other => panic!("{name} returned {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// An initializer-less weak / linkonce global is a STRONG undefined reference.
// ---------------------------------------------------------------------------

const WEAK_FAMILY: [&str; 4] = ["weak", "linkonce", "weak_odr", "linkonce_odr"];

fn alias_text(l1: &str, l2: &str) -> String {
    format!(
        "module \"alias\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i32, i32) -> (i32)\n\n\
         global {l1} mut @w1 i32\nglobal {l2} mut @w2 i32\n\n\
         fn @alias_test(functy.0) {{\nbb0(%1: i32, %2: i32):\n\
         \x20   %3 = global_addr @global.0\n    %4 = global_addr @global.1\n\
         \x20   store i32 %1, ptr %3\n    store i32 %2, ptr %4\n\
         \x20   %5 = load i32, ptr %3\n    ret %5\n}}\n"
    )
}

const W_DEFS: &str = "module \"defs\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
                      global mut @w1 i32 = 0\nglobal mut @w2 i32 = 0\n";

/// A weak undefined wasm symbol resolves to address 0 when nothing defines
/// it, so two such globals aliased at address 0 (`alias_test(1, 2)` was 2).
/// The symbol is now a strong `U`, as on every native object lane: an
/// unresolved reference fails the link by name, and a definition in another
/// object is bound and gives the interpreter's answer.
#[test]
fn initializerless_weak_family_global_is_a_strong_undefined_data_symbol() {
    for l in WEAK_FAMILY {
        let text = alias_text(l, l);
        let obj = object(&text);
        let v = view(&obj);
        for name in ["w1", "w2"] {
            assert_eq!(
                v.symbol("data", name).flags,
                UNDEFINED,
                "`global {l} mut @{name} i32` must be a strong undefined data symbol"
            );
        }
        let Some(alone) = link(&format!("weak_alone_{l}"), &[&obj], &[]) else {
            return skip(
                "initializerless_weak_family_global_is_a_strong_undefined_data_symbol",
                "linking",
            );
        };
        let err = alone.expect_err("an unresolved reference must fail the link");
        assert!(err.contains("undefined symbol: w1"), "{err}");

        let defs = object(W_DEFS);
        let linked = link(&format!("weak_def_{l}"), &[&obj, &defs], &[])
            .unwrap()
            .unwrap_or_else(|e| panic!("link against the definitions: {e}"));
        let want = interpret_int(&parse(&text), "alias_test", &[(Ty::I32, 1), (Ty::I32, 2)])
            .expect("interpreter runs alias_test");
        assert_eq!(want, 1);
        let Some(got) = run(&format!("weak_{l}"), &linked, &["alias_test(1, 2)"]) else {
            return skip(
                "initializerless_weak_family_global_is_a_strong_undefined_data_symbol",
                "execution",
            );
        };
        assert_eq!(got, [want.to_string()], "linkage {l}");
    }
}

/// An initializer-less import marked retained has no bytes to retain; it is
/// refused, as the Mach-O lanes refuse it, rather than emitted as a
/// `NO_STRIP` undefined symbol (the ELF lanes admit it and write nothing for
/// the flag, as llc's ELF writer does).
#[test]
fn retained_data_import_is_refused() {
    let module = parse(
        "module \"r\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = () -> (i32)\n\nglobal mut retained @w i32\n\n\
         fn @read(functy.0) {\nbb0:\n    %1 = global_addr @global.0\n\
         \x20   %2 = load i32, ptr %1\n    ret %2\n}\n",
    );
    let err = wasm::compile_object_with_license(&module, &permit_unlicensed())
        .expect_err("a retained import is refused");
    assert!(err.to_string().contains("marked retained"), "{err}");
}

// ---------------------------------------------------------------------------
// `frem` binds only the C library routine.
// ---------------------------------------------------------------------------

fn frem_text(extra: &str, ty: &str) -> String {
    format!(
        "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = ({ty}, {ty}) -> ({ty})\nfuncty.1 = (i32, i32) -> (i32)\n\n\
         {extra}\n\
         fn @rem(functy.0) {{\nbb0(%1: {ty}, %2: {ty}):\n    %3 = frem {ty} %1, %2\n    ret %3\n}}\n"
    )
}

/// A module-local `fmod` body used to be what `frem` called (`rem(7.5, 2)`
/// was `9.5`, the body's `fadd`). Every non-routine binding is now refused by
/// name; the routine itself (imported, or declared with its exact signature)
/// is still bound, and the linked result agrees with the interpreter.
#[test]
fn frem_binds_only_the_c_library_routine() {
    let refused = [
        (
            frem_text(
                "internal fn @fmod(functy.0) {\nbb0(%1: f64, %2: f64):\n    %3 = fadd f64 %1, %2\n    ret %3\n}\n",
                "f64",
            ),
            "module-local function `fmod`",
        ),
        (
            frem_text(
                "private fn @fmodf(functy.0) {\nbb0(%1: f32, %2: f32):\n    %3 = fmul f32 %1, %2\n    ret %3\n}\n",
                "f32",
            ),
            "module-local function `fmodf`",
        ),
        (
            frem_text("fn @fmod(functy.1) {\n}\n", "f64"),
            "has wasm signature",
        ),
        (frem_text("global @fmod i32 = 7\n", "f64"), "`fmod`"),
    ];
    for (text, why) in &refused {
        let err = wasm::compile_object_with_license(&parse(text), &permit_unlicensed())
            .expect_err("refused");
        let err = err.to_string();
        assert!(err.contains(why), "expected `{why}` in: {err}");
        assert!(
            err.contains("fail-closed") || err.contains("refusing"),
            "{err}"
        );
    }

    // Imported routine, and a declaration of it: one `env.fmod` import.
    for extra in ["", "fn @fmod(functy.0) {\n}\n"] {
        let text = frem_text(extra, "f64");
        let obj = object(&text);
        let fmods: Vec<_> = view(&obj)
            .imports
            .into_iter()
            .filter(|(m, n, k)| m == "env" && n == "fmod" && *k == "func")
            .collect();
        assert_eq!(fmods.len(), 1, "extra = {extra:?}");

        let Some(linked) = link("frem", &[&obj], &["--allow-undefined"]) else {
            return skip("frem_binds_only_the_c_library_routine", "linking");
        };
        let linked = linked.unwrap_or_else(|e| panic!("link: {e}"));
        let module = parse(&text);
        let points = [
            (7.5, 2.0),
            (10.0, 3.0),
            (-7.5, 2.0),
            (1e300, 7.0),
            (0.5, -0.25),
        ];
        let calls: Vec<String> = points
            .iter()
            .map(|(a, b)| format!("rem({a:e}, {b:e})"))
            .collect();
        let calls: Vec<&str> = calls.iter().map(String::as_str).collect();
        let Some(got) = run("frem", &linked, &calls) else {
            return skip("frem_binds_only_the_c_library_routine", "execution");
        };
        for ((a, b), got) in points.iter().zip(got) {
            let want = interpret_f64(&module, "rem", *a, *b);
            let got: f64 = got.parse().expect("f64");
            assert_eq!(got.to_bits(), want.to_bits(), "rem({a}, {b})");
        }
    }
}

/// The object lane calls only `fmod` / `fmodf` by name, so a module-local
/// body or datum named like some OTHER runtime symbol (`malloc`, `memcpy`), or
/// a local `fmod` in a module with no `frem`, is not a shadow here: it
/// compiles, is a LOCAL symbol, and the linked caller reaches the module's own
/// body, exactly as the interpreter does.
#[test]
fn runtime_named_module_local_symbols_compile_when_not_referenced_by_name() {
    let text = "module \"mc\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
                functy.0 = (i32) -> (i32)\n\n\
                global internal @memcpy i32 = 4\n\n\
                internal fn @malloc(functy.0) {\nbb0(%1: i32):\n    %2 = const i32 3\n\
                \x20   %3 = mul i32 %1, %2\n    ret %3\n}\n\n\
                internal fn @fmod(functy.0) {\nbb0(%1: i32):\n    %2 = global_addr @global.0\n\
                \x20   %3 = load i32, ptr %2\n    %4 = add i32 %1, %3\n    ret %4\n}\n\n\
                fn @user(functy.0) {\nbb0(%1: i32):\n    %2 = call @func.0(%1)\n\
                \x20   %3 = call @func.1(%2)\n    ret %3\n}\n";
    let module = parse(text);
    let obj = object(text);
    let v = view(&obj);
    assert!(
        !v.imports
            .iter()
            .any(|(_, n, _)| n == "malloc" || n == "fmod"),
        "{:?}",
        v.imports
    );
    let Some(linked) = link("runtime_named", &[&obj], &[]) else {
        return skip(
            "runtime_named_module_local_symbols_compile_when_not_referenced_by_name",
            "linking",
        );
    };
    let linked = linked.unwrap_or_else(|e| panic!("link: {e}"));
    let args = [0i128, 5, -7, 0x7fff_ffff];
    let calls: Vec<String> = args.iter().map(|a| format!("user({a})")).collect();
    let calls: Vec<&str> = calls.iter().map(String::as_str).collect();
    let Some(got) = run("runtime_named", &linked, &calls) else {
        return skip(
            "runtime_named_module_local_symbols_compile_when_not_referenced_by_name",
            "execution",
        );
    };
    for (a, got) in args.iter().zip(got) {
        let want = interpret_int(&module, "user", &[(Ty::I32, *a)]).expect("interpreter");
        assert_eq!(got, want.to_string(), "user({a})");
    }
}

// ---------------------------------------------------------------------------
// Closed modules: table slot 0 is the null function pointer.
// ---------------------------------------------------------------------------

const FIRST_ADDR: &str = "module \"min\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (i32) -> (i32)\nfuncty.1 = () -> (u32)\n\n\
fn @first(functy.0) {\nbb0(%1: i32):\n    ret %1\n}\n\n\
fn @first_addr_is_null(functy.1) {\nbb0:\n    %1 = const functy.0 fndef<func.0>\n\
\x20   %2 = reify_fn_pointer functy.0 %1 to ptr\n    %3 = ptrtoint ptr %2 to u32\n\
\x20   %4 = const u32 0\n    %5 = icmp eq u32 %3, %4\n    %6 = zext bool %5 to u32\n    ret %6\n}\n\n\
fn @call_first(functy.0) {\nbb0(%1: i32):\n    %2 = const functy.0 fndef<func.0>\n\
\x20   %3 = call_indirect %2(functy.0)(%1)\n    ret %3\n}\n\n\
fn @call_null(functy.0) {\nbb0(%1: i32):\n    %2 = const ptr 0\n\
\x20   %3 = call_indirect %2(functy.0)(%1)\n    ret %3\n}\n";

const NICHE_OPT_FN: &str = "module \"niche\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
enum @OptFn repr(u32) { None = 0, Some(functy.0) = 1 } layout(niche untagged=1 variants=0..=0 \
start=0 lane=u32@0 size=4 align=4 offsets=[[], [0]]) id=0\n\n\
functy.0 = (i32) -> (i32)\nfuncty.1 = (i32) -> (i32)\n\n\
fn @first(functy.0) {\nbb0(%1: i32):\n    %2 = const i32 1000\n    %3 = add i32 %1, %2\n    ret %3\n}\n\n\
fn @call_opt(functy.1) {\nbb0(%1: i32):\n    %2 = const functy.0 fndef<func.0>\n\
\x20   %3 = make_aggregate enum.0 variant 1 (%2)\n    %4 = alloca enum.0\n\
\x20   store enum.0 %3, ptr %4\n    %5 = load enum.0, ptr %4\n    %6 = extractfield u32 %5, 0\n\
\x20   switch %6 [ 1: bb1 default: bb2 ]\nbb1:\n    %7 = extractfield functy.0 %5, 1\n\
\x20   %8 = call_indirect %7(functy.0)(%1)\n    ret %8\nbb2:\n    %9 = const i32 -1\n    ret %9\n}\n";

/// A closed module's first function was table element 0, so its address was
/// the null pointer: `first_addr_is_null()` was 1 and a niche `Some(first)`
/// read as `None` (`call_opt(7)` was -1). trust-ir's null pointer is distinct
/// from every `fndef`, and element 0 is now the null funcref, so a call
/// through null traps. (The pinned interpreter refuses `reify_fn_pointer`;
/// the expected values are exact and match the object lane linked by
/// `wasm-ld`, whose table base is 1.)
#[test]
fn closed_function_pointer_is_never_null() {
    let bytes = closed(FIRST_ADDR);
    // The element segment fills the table from index 1.
    for payload in Parser::new(0).parse_all(&bytes) {
        if let Payload::ElementSection(r) = payload.expect("parse") {
            for e in r {
                let e = e.expect("element");
                let wasmparser::ElementKind::Active { offset_expr, .. } = e.kind else {
                    panic!("closed element segment is not active");
                };
                let mut ops = offset_expr.get_operators_reader();
                assert!(matches!(
                    ops.read().expect("op"),
                    wasmparser::Operator::I32Const { value: 1 }
                ));
            }
        }
    }
    let niche = closed(NICHE_OPT_FN);
    let (Some(got), Some(got_niche)) = (
        run(
            "closed_first",
            &bytes,
            &["first_addr_is_null()", "call_first(7)", "call_null(7)"],
        ),
        run("closed_niche", &niche, &["call_opt(7)"]),
    ) else {
        return skip("closed_function_pointer_is_never_null", "execution");
    };
    assert_eq!(got, ["0", "7", "trap"]);
    assert_eq!(got_niche, ["1007"]);

    // The object lane agrees (wasm-ld's table base is 1).
    let Some(linked) = link("closed_vs_object", &[&object(NICHE_OPT_FN)], &[]) else {
        return;
    };
    let linked = linked.unwrap_or_else(|e| panic!("link: {e}"));
    assert_eq!(
        run("object_niche", &linked, &["call_opt(7)"]).unwrap(),
        ["1007"]
    );
}

// ---------------------------------------------------------------------------
// A function address imports the table (NO_STRIP) with no `call_indirect`.
// ---------------------------------------------------------------------------

const P_TAKES_ADDRESS: &str = "module \"p\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (u32) -> (u32)\n\n\
fn @p(functy.0) {\nbb0(%1: u32):\n    %2 = const functy.0 fndef<func.1>\n\
\x20   %3 = reify_fn_pointer functy.0 %2 to ptr\n    %4 = ptrtoint ptr %3 to u32\n\
\x20   %5 = const u32 0\n    %6 = icmp ne u32 %4, %5\n    %7 = zext bool %6 to u32\n\
\x20   %8 = add u32 %7, %1\n    ret %8\n}\n\nfn @add1(functy.0) {\n}\n";

const ADD1: &str = "module \"add1\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (u32) -> (u32)\n\nfn @add1(functy.0) {\nbb0(%1: u32):\n    ret %1\n}\n";

const DATA_ONLY: &str = "module \"data_only\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = () -> (i32)\n\nglobal @fp ptr = symaddr<g0>\n\n\
fn @g0(functy.0) {\nbb0:\n    %1 = global_addr @global.0\n    %2 = load ptr, ptr %1\n\
\x20   %3 = ptrtoint ptr %2 to i32\n    ret %3\n}\n";

/// The only `call_indirect` is in a dead (internal, unreferenced) function,
/// which `--gc-sections` drops with its table-number relocation.
const DEAD_INDIRECT: &str = "module \"dead\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = () -> (i32)\nfuncty.1 = (ptr) -> (i32)\n\n\
fn @f0(functy.0) {\nbb0:\n    %1 = const ptr symaddr<f0>\n    %2 = ptrtoint ptr %1 to i32\n    ret %2\n}\n\n\
internal fn @dead(functy.1) {\nbb0(%1: ptr):\n    %2 = call_indirect %1(functy.0)()\n    ret %2\n}\n";

const EMPTY: &str = "module \"empty\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = () -> (i32)\n\nfn @zero(functy.0) {\nbb0:\n    %1 = const i32 0\n    ret %1\n}\n";

/// A table-index relocation without a table symbol crashed `wasm-ld`
/// (SIGSEGV in `ElemSection::writeBody`), and so did a table symbol without
/// `NO_STRIP` whose only `call_indirect` was garbage-collected. Every object
/// with a function address now imports the table and marks its symbol
/// `NO_STRIP`, as LLVM's object writer does.
#[test]
fn function_address_imports_the_table_without_an_indirect_call() {
    for (tag, text) in [
        ("code", P_TAKES_ADDRESS),
        ("data", DATA_ONLY),
        ("dead", DEAD_INDIRECT),
    ] {
        let v = view(&object(text));
        assert!(
            v.imports_table(),
            "[{tag}] no table import: {:?}",
            v.imports
        );
        assert_eq!(
            v.symbol("table", "__indirect_function_table").flags,
            UNDEFINED | NO_STRIP,
            "[{tag}]"
        );
    }
    // No function address, no call_indirect: no table.
    assert!(!view(&object(EMPTY)).imports_table());

    let empty = object(EMPTY);
    let Some(p) = link(
        "fnaddr_code",
        &[&object(P_TAKES_ADDRESS), &object(ADD1)],
        &[],
    ) else {
        return skip(
            "function_address_imports_the_table_without_an_indirect_call",
            "linking",
        );
    };
    let p = p.unwrap_or_else(|e| panic!("link: {e}"));
    let data = link("fnaddr_data", &[&object(DATA_ONLY), &empty], &[])
        .unwrap()
        .unwrap_or_else(|e| panic!("link: {e}"));
    let dead = link("fnaddr_dead", &[&object(DEAD_INDIRECT), &empty], &[])
        .unwrap()
        .unwrap_or_else(|e| panic!("link: {e}"));
    // A function address is a nonzero table index (the interpreter refuses
    // `reify_fn_pointer`, so these are exact: `p(x) = (addr != 0) + x`).
    let (Some(gp), Some(gd), Some(gx)) = (
        run("fnaddr_p", &p, &["p(0)", "p(5)", "p(0xfffffffe)"]),
        run("fnaddr_d", &data, &["g0() !== 0"]),
        run("fnaddr_x", &dead, &["f0() !== 0"]),
    ) else {
        return skip(
            "function_address_imports_the_table_without_an_indirect_call",
            "execution",
        );
    };
    assert_eq!(gp, ["1", "6", "-1"]);
    assert_eq!(gd, ["true"]);
    assert_eq!(gx, ["true"]);
}

// ---------------------------------------------------------------------------
// Relocations are emitted in offset order.
// ---------------------------------------------------------------------------

const REV_GLOBAL: &str = "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
struct @Rev { : ptr @4, : ptr @0 } size=8 align=4 id=0\n\nfuncty.0 = () -> (i32)\n\n\
global @x i32 = 111\nglobal @y i32 = 222\nglobal @pair struct.0 = { symaddr<x>, symaddr<y> }\n\n\
fn @at0(functy.0) {\nbb0:\n    %1 = global_addr @global.2\n    %2 = load ptr, ptr %1\n\
\x20   %3 = load i32, ptr %2\n    ret %3\n}\n";

const REV_POOL: &str = "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
struct @Rev { : ptr @4, : ptr @0 } size=8 align=4 id=0\n\nfuncty.0 = () -> (i32)\n\n\
global @x i32 = 111\nglobal @y i32 = 222\n\n\
fn @at0(functy.0) {\nbb0:\n    %1 = const struct.0 { symaddr<x>, symaddr<y> }\n\
\x20   %2 = extractfield ptr %1, 0\n    %3 = load i32, ptr %2\n    ret %3\n}\n";

const REV_ENUM: &str = "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
enum @E repr(u32) { A(ptr, ptr) = 7 } layout(direct tag@8 size=12 align=4 offsets=[[4, 0]]) id=0\n\n\
functy.0 = () -> (i32)\n\n\
global @x i32 = 111\nglobal @y i32 = 222\nglobal @e enum.0 = { 7, symaddr<x>, symaddr<y> }\n\n\
fn @at0(functy.0) {\nbb0:\n    %1 = global_addr @global.2\n    %2 = load ptr, ptr %1\n\
\x20   %3 = load i32, ptr %2\n    ret %3\n}\n";

/// A data image lists its pointers in field-declaration order, which trust-ir
/// does not tie to offset order; `wasm-ld` refused the object ("relocations
/// not in offset order"). Every relocation section is now sorted, and the
/// linked module reads what the closed module reads. (The pinned interpreter
/// cannot load a pointer out of `symaddr` data, so the closed lane — which
/// patches bytes in place and never had the defect — is the reference.)
#[test]
fn relocations_are_sorted_by_offset() {
    for (tag, text, want) in [
        ("global", REV_GLOBAL, "222"),
        ("pool", REV_POOL, "111"),
        ("enum", REV_ENUM, "222"),
    ] {
        let obj = object(text);
        let v = view(&obj);
        for (section, relocs) in &v.relocs {
            assert!(
                relocs.windows(2).all(|w| w[0].1 <= w[1].1),
                "[{tag}] {section} out of offset order: {relocs:?}"
            );
        }
        assert!(
            v.relocs_of("reloc.DATA").len() >= 2,
            "[{tag}] {:?}",
            v.relocs
        );
        let Some(linked) = link(&format!("reloc_{tag}"), &[&obj], &[]) else {
            return skip("relocations_are_sorted_by_offset", "linking");
        };
        let linked = linked.unwrap_or_else(|e| panic!("[{tag}] link: {e}"));
        let (Some(got), Some(reference)) = (
            run(&format!("reloc_{tag}"), &linked, &["at0()"]),
            run(&format!("reloc_closed_{tag}"), &closed(text), &["at0()"]),
        ) else {
            return skip("relocations_are_sorted_by_offset", "execution");
        };
        assert_eq!(reference, [want], "[{tag}] closed");
        assert_eq!(got, [want], "[{tag}] linked");
    }
}

// ---------------------------------------------------------------------------
// Function pointers in static data are FUNCTION symbols.
// ---------------------------------------------------------------------------

const STATIC_TABLE: &str = "module \"s\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = () -> ()\n\nfuncty.1 = (u32) -> (u32)\n\n\
global align(4) @T ptr = symaddr<inc>\n\n\
internal fn @anchor(functy.0) {\nbb0:\n    ret\n}\n\nfn @inc(functy.1) {\n}\n";

const USES_TABLE: &str = "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
functy.0 = (u32) -> (u32)\n\nglobal @T ptr\n\n\
fn @inc(functy.0) {\nbb0(%1: u32):\n    %2 = const u32 1\n    %3 = add u32 %1, %2\n    ret %3\n}\n\n\
fn @e(functy.0) {\nbb0(%1: u32):\n    %2 = global_addr @global.0\n    %3 = load ptr, ptr %2\n\
\x20   %5 = call_indirect %3(functy.0)(%1)\n    ret %5\n}\n";

/// `symaddr<f>` in static data, where `f` is a function defined in ANOTHER
/// object and declared here, is an undefined FUNCTION symbol with an
/// `R_WASM_TABLE_INDEX_I32` relocation — never a data symbol with a memory
/// address relocation, which `wasm-ld` refuses against the function's
/// definition ("symbol type mismatch"), and the object imports the table
/// that relocation indexes.
///
/// Evidence boundary: the lane already typed a DECLARED function this way;
/// on the earlier lane this test failed only through the missing
/// `__indirect_function_table` import (the `wasm-ld` crash). The rustc
/// bridge's side of the fix — declaring every function it stores in a
/// static, vtable or constant, so the lane sees a declaration and not a bare
/// name — is guarded by the bridge corpus crate
/// `tests/support/wasm32_differential/static_fn_pointers.rs`, which its
/// `wasm32_differential` test links and runs against LLVM.
#[test]
fn static_function_pointer_to_another_object_is_a_function_symbol() {
    let obj = object(STATIC_TABLE);
    let v = view(&obj);
    assert_eq!(v.symbol("func", "inc").flags, UNDEFINED);
    assert!(
        !v.symbols
            .iter()
            .any(|s| s.kind == "data" && s.name == "inc"),
        "{:?}",
        v.symbols
    );
    assert_eq!(
        v.relocs_of("reloc.DATA")
            .iter()
            .map(|r| r.0)
            .collect::<Vec<_>>(),
        [RelocationType::TableIndexI32]
    );
    assert!(v.imports_table());

    let Some(linked) = link("static_fnptr", &[&obj, &object(USES_TABLE)], &[]) else {
        return skip(
            "static_function_pointer_to_another_object_is_a_function_symbol",
            "linking",
        );
    };
    let linked = linked.unwrap_or_else(|e| panic!("link: {e}"));
    // `e(x)` calls `inc` through the pointer the static holds (exact: the
    // interpreter cannot call through a pointer loaded from `symaddr` data).
    let Some(got) = run("static_fnptr", &linked, &["e(0)", "e(41)", "e(0xffffffff)"]) else {
        return skip(
            "static_function_pointer_to_another_object_is_a_function_symbol",
            "execution",
        );
    };
    assert_eq!(got, ["1", "42", "0"]);
}

/// Raw function-item constants are not pointer data, and a loaded pointer
/// is already the call target rather than a function item to reify.
#[test]
fn invalid_function_item_storage_and_pointer_reification_are_refused() {
    let item = DATA_ONLY.replace("symaddr<g0>", "fndef<func.0>");
    let reify = USES_TABLE.replace(
        "%5 = call_indirect %3(functy.0)(%1)",
        "%4 = reify_fn_pointer ptr %3 to functy.0\n    %5 = call_indirect %4(functy.0)(%1)",
    );
    for (text, reason) in [
        (item, "const type mismatch"),
        (reify, "reify_fn_pointer source must be a function item"),
    ] {
        let error = wasm::compile_object_with_license(&parse(&text), &permit_unlicensed())
            .expect_err("invalid function-pointer construction must remain refused");
        assert!(error.to_string().contains(reason), "{error}");
    }
}

/// A function's address is its table index; a byte offset from it addresses
/// nothing, so `symaddr<f + k>` on a function is refused by both lanes rather
/// than turned into a data reference against the function's name.
#[test]
fn function_symaddr_with_an_addend_is_refused() {
    let text = "module \"s\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
                functy.0 = (u32) -> (u32)\n\nglobal @T ptr = symaddr<inc + 4>\n\n\
                fn @inc(functy.0) {\nbb0(%1: u32):\n    ret %1\n}\n";
    let module = parse(text);
    for err in [
        wasm::compile_object_with_license(&module, &permit_unlicensed())
            .expect_err("object refuses"),
        wasm::compile_module_with_license(&module, &permit_unlicensed())
            .expect_err("closed refuses"),
    ] {
        assert!(err.to_string().contains("table index"), "{err}");
    }
}

// ---------------------------------------------------------------------------
// The object lane's own symbol policy governs its functions.
// ---------------------------------------------------------------------------

/// The object lane re-ran the CLOSED module's surface check on every
/// function, refusing a hidden function and an `available_externally` global
/// that its own object policy admits. Both compile now: a hidden definition
/// or declaration carries `WASM_SYM_VISIBILITY_HIDDEN`, protected maps to the
/// default visibility (wasm has no preemption), and an
/// `available_externally` global is an undefined data symbol bound to the
/// definition in another object.
#[test]
fn object_lane_admits_hidden_functions_and_available_externally_globals() {
    let hidden_def = object(
        "module \"hid\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i32) -> (i32)\n\n\
         fn @hid(functy.0) {\n; #visibility: hidden\nbb0(%1: i32):\n    ret %1\n}\n\n\
         fn @prot(functy.0) {\n; #visibility: protected\nbb0(%1: i32):\n    ret %1\n}\n",
    );
    let v = view(&hidden_def);
    assert_eq!(v.symbol("func", "hid").flags & HIDDEN, HIDDEN);
    assert_eq!(v.symbol("func", "prot").flags & HIDDEN, 0);

    let hidden_decl = object(
        "module \"hdd\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         functy.0 = (i32) -> (i32)\n\n\
         fn @ext(functy.0) {\n; #visibility: hidden\n}\n\n\
         fn @user(functy.0) {\nbb0(%1: i32):\n    %2 = call @func.0(%1)\n    ret %2\n}\n",
    );
    assert_eq!(
        view(&hidden_decl).symbol("func", "ext").flags,
        UNDEFINED | HIDDEN
    );

    let gae_text = "module \"gae\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
                    functy.0 = () -> (i32)\n\n\
                    global available_externally @shared_val i32 = 5\n\n\
                    fn @read_shared(functy.0) {\nbb0:\n    %1 = global_addr @global.0\n\
                    \x20   %2 = load i32, ptr %1\n    ret %2\n}\n";
    let gae = object(gae_text);
    let v = view(&gae);
    assert_eq!(v.symbol("data", "shared_val").flags, UNDEFINED);
    assert_eq!(v.data_segments, 0, "the initializer is not a definition");
    // A closed module still has no data-import channel.
    assert!(wasm::compile_module_with_license(&parse(gae_text), &permit_unlicensed()).is_err());

    let def = object(
        "module \"d\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
         global @shared_val i32 = 5\n",
    );
    let Some(linked) = link("gae", &[&gae, &def], &[]) else {
        return skip(
            "object_lane_admits_hidden_functions_and_available_externally_globals",
            "linking",
        );
    };
    let linked = linked.unwrap_or_else(|e| panic!("link: {e}"));
    let want = interpret_int(&parse(gae_text), "read_shared", &[]).expect("interpreter");
    let Some(got) = run("gae", &linked, &["read_shared()"]) else {
        return skip(
            "object_lane_admits_hidden_functions_and_available_externally_globals",
            "execution",
        );
    };
    assert_eq!(got, [want.to_string()]);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
