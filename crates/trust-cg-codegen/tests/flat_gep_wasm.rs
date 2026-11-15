//! Execute flat TrustIR GEPs in an independent WebAssembly runtime.
use std::process::Command;
use trust_cg_codegen::wasm;
use trust_ir::{FieldDef, StructDef, StructId, StructRepr, Ty};
use trust_ir_build::ModuleBuilder;

fn run(count: usize, constant_second: bool) {
    let mut mb = ModuleBuilder::new("flat_gep_wasm");
    let mut shapes = vec![("scalar", Ty::U32, 4)];
    for (id, name, repr, size) in [
        (0, "record", StructRepr::C, 8),
        (1, "packed", StructRepr::Packed(1), 5),
    ] {
        let id = mb.add_struct(StructDef {
            id: StructId::new(id),
            name: name.into(),
            origin: None,
            fields: vec![
                FieldDef {
                    name: "a".into(),
                    ty: Ty::U8,
                    offset: Some(0),
                },
                FieldDef {
                    name: "b".into(),
                    ty: Ty::U32,
                    offset: Some(if name == "packed" { 1 } else { 4 }),
                },
            ],
            size: Some(size),
            align: Some(if name == "packed" { 1 } else { 4 }),
            repr,
        });
        shapes.push((name, Ty::Struct(id), size));
    }
    let elem = mb.add_type(Ty::U32);
    shapes.push(("array", Ty::Array(elem, 3), 12));
    let mut expected_shapes = Vec::new();
    for (name, pointee, stride) in shapes {
        // The old two-index struct path accepted a constant second index and
        // returned a field address. Keep that exact trigger as a native twin.
        if constant_second && name != "record" {
            continue;
        }
        let signature = mb.add_func_type(vec![Ty::Ptr, Ty::I32, Ty::I32, Ty::I32], vec![Ty::Ptr]);
        let mut fb = mb.function(name, signature);
        let entry = fb.create_block();
        let base = fb.add_block_param(entry, Ty::Ptr);
        let args: Vec<_> = (0..3).map(|_| fb.add_block_param(entry, Ty::I32)).collect();
        fb.switch_to_block(entry);
        let mut indices: Vec<_> = args.into_iter().take(count).collect();
        if constant_second {
            indices[1] = fb.iconst(Ty::I32, 1);
        }
        let result = fb.gep(pointee, base, indices);
        fb.ret(vec![result]);
        fb.build();
        expected_shapes.push((name, stride));
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(wasm::target::wasm32_target_info());
    assert_eq!(trust_ir_build::validate_module(&module), []);
    let bytes = wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("defined flat GEP must lower to wasm");
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .expect("valid emitted wasm");
    if Command::new("node").arg("--version").output().is_err() {
        eprintln!("SKIP: flat GEP wasm execution requires node on PATH; byte validation passed");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let wasm_path = dir.path().join("flat.wasm");
    let driver_path = dir.path().join("run.mjs");
    std::fs::write(&wasm_path, bytes).unwrap();
    let driver = format!(
        r#"
import {{ readFileSync }} from 'node:fs';
const {{ instance }} = await WebAssembly.instantiate(readFileSync(process.argv[2]), {{}});
const shapes = {};
const count = {count};
const constantSecond = {constant_second};
let checks = 0;
for (const [name, stride] of shapes) {{
    for (const row of [[0,0,0], [0,1,0], [1,0,0], [1,2,3], [9,7,5]]) {{
        const indices = row.slice(0, count);
        if (constantSecond) indices[1] = 1;
        const expected = 4096 + indices.reduce((a,b) => a+b, 0) * stride;
        const actual = instance.exports[name](4096, ...row);
        if (actual !== expected) throw new Error(`${{name}}(${{row}}): ${{actual}} != ${{expected}}`);
        checks++;
    }}
}}
console.log(`FLAT_GEP_WASM checks=${{checks}}`);
"#,
        serde_json::to_string(&expected_shapes).unwrap()
    );
    std::fs::write(&driver_path, driver).unwrap();
    let result = Command::new("node")
        .arg(driver_path)
        .arg(wasm_path)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert_eq!(
        stdout.trim(),
        format!("FLAT_GEP_WASM checks={}", expected_shapes.len() * 5)
    );
    print!("{stdout}");
}

#[test]
fn empty_indices_preserve_the_base() {
    run(0, false);
}

#[test]
fn single_index_control() {
    run(1, false);
}

#[test]
fn constant_second_index_strides_a_whole_struct() {
    run(2, true);
}

#[test]
fn two_dynamic_indices_keep_one_scale() {
    run(2, false);
}

#[test]
fn three_dynamic_indices_keep_one_scale() {
    run(3, false);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
