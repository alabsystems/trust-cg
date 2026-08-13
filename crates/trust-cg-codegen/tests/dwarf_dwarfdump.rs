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
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
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
    module.add_function(func.clone());
    (func, module)
}

fn compile_debug_fixture_object() -> Vec<u8> {
    let (trust_ir_func, module) = build_debug_fixture();
    let (lir_func, _) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate debug fixture");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: true,
        verify_dispatch: DispatchVerifyMode::Off,
        ..Default::default()
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
