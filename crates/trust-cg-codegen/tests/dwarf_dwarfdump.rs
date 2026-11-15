// trust-cg-codegen/tests/dwarf_dwarfdump.rs - DWARF external-tool contract
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Part of #326: validate baseline O0 DWARF through macOS dwarfdump.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::pipeline::{DispatchVerifyMode, OptLevel, Pipeline, PipelineConfig};
use trust_ir::{
    Block as TrustIrBlock, BlockId, EnumDef, EnumId, EnumVariant, FieldDef, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, SourceSpan, StructDef,
    StructId, Ty, ValueId,
};

fn dwarfdump_path() -> Option<&'static str> {
    let path = "/usr/bin/dwarfdump";
    Path::new(path).exists().then_some(path)
}

fn write_temp_object(bytes: &[u8], name: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "trust_cg_326_dwarf_{}_{}.o",
        std::process::id(),
        name
    ));
    fs::write(&path, bytes).expect("write DWARF test object");
    path
}

fn run_dwarfdump(path: &Path, args: &[&str]) -> String {
    let Some(dwarfdump) = dwarfdump_path() else {
        eprintln!("skipping #326 dwarfdump check: /usr/bin/dwarfdump is not available");
        return String::new();
    };

    let output = Command::new(dwarfdump)
        .args(args)
        .arg(path)
        .output()
        .expect("run dwarfdump");

    assert!(
        output.status.success(),
        "dwarfdump {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let mut combined = String::from_utf8(output.stdout).expect("dwarfdump stdout should be UTF-8");
    combined.push_str(&String::from_utf8_lossy(&output.stderr));
    combined
}

fn assert_contains(haystack: &str, needle: &str) {
    assert!(
        haystack.contains(needle),
        "missing {needle:?} in dwarfdump output:\n{haystack}"
    );
}

fn line_dump_mentions_source_line(dump: &str, line: u32) -> bool {
    let needle = line.to_string();
    dump.lines()
        .filter(|row| row.contains("0x"))
        .flat_map(|row| row.split_whitespace())
        .any(|token| token == needle)
}

fn occurrence_count(haystack: &str, needle: &str) -> usize {
    haystack.matches(needle).count()
}

fn span(line: u32, col: u32) -> SourceSpan {
    SourceSpan { file: 0, line, col }
}

fn build_debug_fixture() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("debug_info_fixture");
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "left".to_string(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "right".to_string(),
                ty: Ty::I32,
                offset: Some(4),
            },
        ],
        size: Some(8),
        align: Some(4),
        repr: Default::default(),
    });
    module.add_enum(EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "Color".to_string(),
        variants: vec![
            EnumVariant {
                name: "Red".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Green".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    });
    let ft_id = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func =
        TrustIrFunction::new(FuncId::new(0), "debug_info_fixture", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(ValueId::new(1))
            .with_span(span(10, 9)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                value: ValueId::new(0),
                align: None,
                volatile: false,
            })
            .with_span(span(11, 5)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                align: None,
                volatile: false,
            })
            .with_result(ValueId::new(2))
            .with_span(span(12, 13)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            })
            .with_span(span(13, 1)),
        ],
    }];
    module
        .try_add_function(func.clone())
        .expect("Module::try_add_function: test fixture");
    (func, module)
}

fn compile_debug_fixture_object() -> Vec<u8> {
    let (trust_ir_func, module) = build_debug_fixture();
    let (lir_func, _) = trust_cg_lower::translate_function_with_license(
        &trust_ir_func,
        &module,
        &permit_unlicensed(),
    )
    .expect("adapter should translate debug fixture");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: true,
        verify_dispatch: DispatchVerifyMode::Off,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    });

    pipeline
        .compile_function(&lir_func)
        .expect("O0 emit_debug pipeline should compile debug fixture")
}

#[test]
fn dwarfdump_verifies_o0_pipeline_debug_info_contract() {
    if !cfg!(target_os = "macos") {
        eprintln!("skipping #326 dwarfdump check: requires macOS Mach-O dwarfdump");
        return;
    }
    if dwarfdump_path().is_none() {
        eprintln!("skipping #326 dwarfdump check: /usr/bin/dwarfdump is not available");
        return;
    }

    let obj = compile_debug_fixture_object();
    let path = write_temp_object(&obj, "o0_pipeline_contract");
    run_dwarfdump(&path, &["--verify", "--debug-info", "--debug-line"]);
    let dump = run_dwarfdump(&path, &["--debug-info", "--debug-line"]);

    for needle in [
        "debug_info_fixture.rs",
        "DW_TAG_subprogram",
        "debug_info_fixture",
        "DW_TAG_formal_parameter",
        "arg0",
        "DW_TAG_variable",
        "local_0",
        "DW_AT_location",
        "DW_TAG_structure_type",
        "Pair",
        "left",
        "right",
        "DW_AT_data_member_location",
        "DW_TAG_enumeration_type",
        "Color",
        "DW_TAG_enumerator",
        "Red",
        "Green",
    ] {
        assert_contains(&dump, needle);
    }

    assert!(
        occurrence_count(&dump, "DW_TAG_member") >= 2,
        "struct DIE should contain at least two member children:\n{dump}"
    );
    assert!(
        occurrence_count(&dump, "DW_AT_data_member_location") >= 2,
        "struct members should carry data-member locations:\n{dump}"
    );
    assert!(
        occurrence_count(&dump, "DW_TAG_enumerator") >= 2,
        "enum DIE should contain at least two enumerator children:\n{dump}"
    );

    assert!(
        line_dump_mentions_source_line(&dump, 11) && line_dump_mentions_source_line(&dump, 12),
        "line table should mention fixture source lines 11 and 12:\n{dump}"
    );

    let _ = fs::remove_file(path);
}

/// One function `name: () -> i64` returning `value`, its two instructions
/// spanned at `lines` of module file `file`.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn spanned_function(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    file: u32,
    lines: [u32; 2],
    value: i128,
) -> TrustIrFunction {
    let ft_id = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(id), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: trust_ir::Constant::Int(value),
            })
            .with_result(ValueId::new(0))
            .with_span(SourceSpan {
                file,
                line: lines[0],
                col: 5,
            }),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })
            .with_span(SourceSpan {
                file,
                line: lines[1],
                col: 1,
            }),
        ],
    }];
    func
}

/// The `(line, file)` of every row of a `dwarfdump --debug-line` row table.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn line_rows(dump: &str) -> Vec<(u32, u32)> {
    dump.lines()
        .filter_map(|row| {
            let mut fields = row.split_whitespace();
            fields.next()?.strip_prefix("0x")?;
            let line = fields.next()?.parse().ok()?;
            let _column: u32 = fields.next()?.parse().ok()?;
            let file = fields.next()?.parse().ok()?;
            Some((line, file))
        })
        .collect()
}

/// The `DW_TAG_subprogram` DIE of `dump` whose `DW_AT_name` is `name`.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn subprogram_die<'a>(dump: &'a str, name: &str) -> &'a str {
    let needle = format!("DW_AT_name\t(\"{name}\")");
    dump.split("DW_TAG_subprogram")
        .skip(1)
        .map(|die| die.split("\n\n").next().unwrap_or(die))
        .find(|die| die.contains(&needle))
        .unwrap_or_else(|| panic!("no subprogram named {name:?}:\n{dump}"))
}

/// A whole-module Mach-O object from the `Compiler` path (the one the rustc
/// bridge drives) whose functions come from two source files: the line
/// program lists both files and switches to each function's own file, and a
/// function the producer named (`Function::display_path`) is described by
/// that name rather than its object symbol, while an unnamed one keeps its
/// symbol (ledger L06-P7). `dwarfdump --verify` accepts the object.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn dwarfdump_verifies_a_two_file_module_with_producer_named_subprograms() {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{Compiler, CompilerConfig};
    assert!(
        dwarfdump_path().is_some(),
        "/usr/bin/dwarfdump is required on the aarch64-apple-darwin floor"
    );
    let mut module = TrustIrModule::new("two_file_unit");
    module.files = vec!["/src/first.rs".to_string(), "/src/second.rs".to_string()];
    let first = spanned_function(&mut module, 0, "first_symbol", 0, [3, 4], 11);
    let mut second = spanned_function(&mut module, 1, "__private.cgu.0.1", 1, [7, 8], 22);
    second.display_path = Some("krate::second".to_string());
    module
        .try_add_function(first)
        .expect("Module::try_add_function: test fixture");
    module
        .try_add_function(second)
        .expect("Module::try_add_function: test fixture");
    let compiled = Compiler::new_for_target_spec(
        CompilerConfig {
            emit_debug: true,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("Darwin target"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .expect("emit_debug Compiler should compile the two-file module");
    let path = write_temp_object(&compiled.object_code, "two_file_module");
    run_dwarfdump(&path, &["--verify", "--debug-info", "--debug-line"]);
    let lines = run_dwarfdump(&path, &["--debug-line"]);
    let info = run_dwarfdump(&path, &["--debug-info"]);
    let _ = fs::remove_file(&path);

    for needle in ["\"/src/first.rs\"", "\"/src/second.rs\""] {
        assert_contains(&lines, needle);
    }
    let rows = line_rows(&lines);
    for (line, file) in [(3, 1), (4, 1), (7, 2), (8, 2)] {
        assert!(
            rows.contains(&(line, file)),
            "line {line} must be a row of file {file}: {rows:?}\n{lines}"
        );
    }
    assert!(
        rows.iter()
            .all(|&(line, file)| (file == 1) == (line < 7) && (file == 2) == (line >= 7)),
        "every row must be in its own function's file: {rows:?}"
    );

    // The producer-named function is described by its name, never by its
    // producer-private object symbol; the unnamed one keeps its symbol.
    let named = subprogram_die(&info, "krate::second");
    assert!(
        named.contains("DW_AT_decl_file\t(\"/src/second.rs\")"),
        "{named}"
    );
    assert!(
        !info.contains("__private.cgu.0.1"),
        "the object symbol of a producer-named function must not name it:\n{info}"
    );
    let unnamed = subprogram_die(&info, "first_symbol");
    assert!(
        unnamed.contains("DW_AT_decl_file\t(\"/src/first.rs\")"),
        "{unnamed}"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
