#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use trust_cg_codegen::compiler::module_object_globals;
use trust_ir::{Constant, Global, Linkage, Module, Ty, Visibility};

fn global(linkage: Linkage, initialized: bool) -> Global {
    Global {
        name: "shared_word".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: initialized.then_some(Constant::Int(42)),
        linkage,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

#[test]
fn odr_global_definitions_and_imports_preserve_linker_binding() {
    for linkage in [
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        for initialized in [false, true] {
            let mut module = Module::new("global_linkage");
            module.globals.push(global(linkage, initialized));
            let globals = module_object_globals(&module).unwrap();
            let actual = &globals[0];
            assert!(actual.is_external, "{linkage:?}, initialized={initialized}");
            assert_eq!(actual.is_import, !initialized, "{linkage:?}");
            assert_eq!(actual.is_weak, initialized, "{linkage:?}");
            assert_eq!(
                actual.data,
                if initialized {
                    42u64.to_le_bytes().to_vec()
                } else {
                    Vec::new()
                }
            );
        }
    }
}

#[test]
fn external_weak_global_is_a_weak_import_only_as_a_declaration() {
    let mut module = Module::new("global_linkage");
    module.globals.push(global(Linkage::ExternalWeak, false));
    let globals = module_object_globals(&module).unwrap();
    let actual = &globals[0];
    assert!(actual.is_external && actual.is_import && actual.is_weak);
    assert!(actual.data.is_empty() && actual.symbol_refs.is_empty());

    let mut initialized = Module::new("global_linkage");
    initialized
        .globals
        .push(global(Linkage::ExternalWeak, true));
    let error = module_object_globals(&initialized).unwrap_err().to_string();
    assert!(
        error.contains("external_weak") && error.contains("initializer"),
        "{error}"
    );

    let mut thread_local = Module::new("global_linkage");
    let mut tls = global(Linkage::ExternalWeak, false);
    tls.tls = Some(trust_ir::TlsModel::InitialExec);
    thread_local.globals.push(tls);
    let error = module_object_globals(&thread_local)
        .unwrap_err()
        .to_string();
    assert!(error.contains("thread-local"), "{error}");

    // Every other import stays a strong undefined reference.
    for linkage in [Linkage::External, Linkage::AvailableExternally] {
        let mut module = Module::new("global_linkage");
        module.globals.push(global(linkage, false));
        let globals = module_object_globals(&module).unwrap();
        assert!(globals[0].is_import && !globals[0].is_weak, "{linkage:?}");
    }
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/native_host.rs"]
mod native_host;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn odr_globals_coalesce_across_native_objects_and_imports() {
    use std::{fs, process::Command, time::Duration};
    use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
    use trust_ir::{
        Block, BlockId, Endianness, FuncId, FuncTy, Function, Inst, InstrNode, StructPassingPolicy,
        TargetInfo, ValueId, value::GlobalId,
    };

    fn command(cmd: &mut Command) -> String {
        let result = process::command_output_with_timeout(cmd, Duration::from_secs(60)).unwrap();
        assert!(
            !result.timed_out && result.output.status.success(),
            "{cmd:?}: {}",
            String::from_utf8_lossy(&result.output.stderr)
        );
        String::from_utf8(result.output.stdout).unwrap()
    }

    for linkage in [Linkage::WeakOdr, Linkage::LinkOnceOdr] {
        for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let directory = fresh_dir::create("tcg-odr-globals-");
            let mut objects = Vec::new();
            for (name, initialized) in [("first", true), ("second", true), ("imported", false)] {
                let mut module = Module::new(name);
                module.target_info = Some(TargetInfo {
                    triple: native_host::TRIPLE.into(),
                    pointer_size: 8,
                    endianness: Endianness::Little,
                    abi: Some("aapcs64".into()),
                    struct_passing: StructPassingPolicy::NativeC,
                });
                module.globals.push(global(linkage, initialized));
                let signature = module
                    .add_func_type(FuncTy {
                        params: vec![],
                        returns: vec![Ty::Ptr],
                        abi: None,
                        is_vararg: false,
                    })
                    .expect("Module::add_func_type: test fixture");
                let mut function = Function::new(FuncId::new(0), name, signature, BlockId::new(0));
                let mut block = Block::new(BlockId::new(0));
                block.body.push(
                    InstrNode::new(Inst::GlobalAddr {
                        global: GlobalId::new(0),
                    })
                    .with_result(ValueId::new(0)),
                );
                block.body.push(InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }));
                function.blocks.push(block);
                module.functions.push(function);
                let compiler = Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level,
                        ..Default::default()
                    },
                    TargetSpec::parse(native_host::TRIPLE).unwrap(),
                )
                .with_codegen_license(permit_unlicensed());
                let object = compiler.compile(&module).unwrap().object_code;
                native_host::assert_native_object(&object);
                let path = directory.join(format!("{name}.o"));
                fs::write(&path, object).unwrap();
                // Inspect the binding with the host's own object tool.
                if native_host::DARWIN {
                    let symbols =
                        command(Command::new("nm").env("LC_ALL", "C").arg("-m").arg(&path));
                    let row = symbols
                        .lines()
                        .find(|line| line.split_whitespace().last() == Some("_shared_word"))
                        .unwrap();
                    assert!(row.contains("external"), "{row}");
                    assert_eq!(row.contains("weak external"), initialized, "{row}");
                    assert_eq!(row.contains("(undefined)"), !initialized, "{row}");
                } else {
                    let symbols = command(
                        Command::new("readelf")
                            .env("LC_ALL", "C")
                            .args(["--wide", "--symbols"])
                            .arg(&path),
                    );
                    let row = symbols
                        .lines()
                        .find(|line| line.split_whitespace().last() == Some("shared_word"))
                        .unwrap();
                    assert!(
                        row.contains(if initialized { "WEAK" } else { "GLOBAL" }),
                        "{row}"
                    );
                    assert_eq!(row.contains("UND"), !initialized, "{row}");
                }
                objects.push(path);
            }
            let driver = directory.join("driver.c");
            fs::write(&driver, "#include <stdint.h>\nextern uint64_t shared_word;\nextern uint64_t *first(void), *second(void), *imported(void);\nint main(void) { if (first()!=&shared_word || second()!=&shared_word || imported()!=&shared_word || shared_word!=42) return 1; *first()=73; return *second()!=73 || *imported()!=73; }\n").unwrap();
            let binary = directory.join("driver");
            command(
                Command::new("cc")
                    .args(["-fPIE", "-pie"])
                    .arg(&driver)
                    .args(&objects)
                    .arg("-o")
                    .arg(&binary),
            );
            command(&mut Command::new(&binary));
            eprintln!("ODR native coalescence passed: {linkage:?} {opt_level:?} {directory:?}");
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
///
/// Its only callers are the native-host controls, so it is compiled under
/// their gate (elsewhere it would be dead code, which `-D warnings` refuses).
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
