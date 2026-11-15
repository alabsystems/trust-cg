// Ordinary direct calls must respect source module linkage in JIT resolution
// and in AOT objects.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::collections::HashMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompileError, Compiler, CompilerConfig};
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
    Ty, ValueId,
};

fn direct_call_module(linkage: Linkage) -> Module {
    let mut module = Module::new("ordinary_direct_binding");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut target = Function::new(FuncId::new(0), "add_one", sig, BlockId::new(0));
    target.linkage = linkage;
    let mut target_entry = Block::new(BlockId::new(0));
    target_entry.params.push((ValueId::new(0), Ty::I64));
    target_entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(1)),
    );
    target_entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    target_entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    target.blocks.push(target_entry);
    module.functions.push(target);

    let mut caller = Function::new(FuncId::new(1), "entry", sig, BlockId::new(0));
    let mut caller_entry = Block::new(BlockId::new(0));
    caller_entry.params.push((ValueId::new(0), Ty::I64));
    caller_entry.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    caller_entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    caller.blocks.push(caller_entry);
    module.functions.push(caller);
    module
}

fn add_div_annotation_clone_trigger(module: &mut Module) {
    let caller = module
        .functions
        .iter_mut()
        .find(|function| function.name == "entry")
        .expect("entry function");
    caller.blocks[0].body.splice(
        0..0,
        [
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(84),
            })
            .with_result(ValueId::new(100)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
            })
            .with_result(ValueId::new(101)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::UDiv,
                ty: Ty::I64,
                lhs: ValueId::new(100),
                rhs: ValueId::new(101),
            })
            .with_result(ValueId::new(102)),
        ],
    );
}

extern "C" fn malicious_add_one_override(input: i64) -> i64 {
    input.wrapping_sub(1000)
}

fn run_entry(linkage: Linkage, with_override: bool, input: i64) -> i64 {
    let mut externs = HashMap::new();
    if with_override {
        externs.insert(
            "add_one".to_string(),
            malicious_add_one_override as *const () as *const u8,
        );
    }
    let jit = Compiler::new(CompilerConfig::for_host_jit_unchecked())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&direct_call_module(linkage), &externs)
        .expect("direct-call module JITs");
    let entry = unsafe {
        jit.buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>("entry")
            .expect("entry symbol")
    };
    entry.as_ref()(input)
}

#[test]
fn internal_and_private_direct_calls_ignore_same_name_extern_override() {
    for linkage in [Linkage::Internal, Linkage::Private] {
        for input in [i64::MIN + 1, -41, -1, 0, 1, 41, i64::MAX - 1] {
            assert_eq!(run_entry(linkage, true, input), input + 1, "{linkage}");
        }
    }
}

#[test]
fn external_direct_call_remains_interposable_and_control_is_load_bearing() {
    for input in [i64::MIN + 1, -41, -1, 0, 1, 41, i64::MAX - 1] {
        assert_eq!(run_entry(Linkage::External, false, input), input + 1);
        assert_eq!(
            run_entry(Linkage::External, true, input),
            input.wrapping_sub(1000)
        );
    }
}

#[test]
fn internal_intrinsic_like_name_uses_its_exact_module_body() {
    let mut module = direct_call_module(Linkage::Internal);
    module.functions[0].name = "llvm.bitreverse.i64".to_string();
    let externs = HashMap::from([(
        "llvm.bitreverse.i64".to_string(),
        malicious_add_one_override as *const () as *const u8,
    )]);
    let jit = Compiler::new(CompilerConfig::for_host_jit_unchecked())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module, &externs)
        .expect("module-local intrinsic-like body JITs through exact binding");
    let entry = unsafe {
        jit.buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>("entry")
            .expect("entry symbol")
    };
    for input in [i64::MIN + 1, -41, -1, 0, 1, 41, i64::MAX - 1] {
        assert_eq!(entry.as_ref()(input), input + 1);
    }
}

/// On an object path that cannot show that a reference to an Internal or
/// Private definition binds locally, AOT refuses the direct call before any
/// object or proof output; an External call still compiles. That is every
/// path but AArch64 and x86-64 ELF and Mach-O (ruling
/// OD-X86-ELF-LOCAL-BINDING-20261027).
#[test]
fn aot_refuses_internal_and_private_direct_calls_off_locally_binding_objects() {
    for triple in ["x86_64-pc-windows-msvc", "riscv64-unknown-linux-gnu"] {
        let spec = TargetSpec::parse(triple).expect("triple");
        for linkage in [Linkage::Internal, Linkage::Private] {
            let mut config = CompilerConfig::for_host_jit_unchecked();
            config.emit_proofs = true;
            let error = Compiler::new_for_target_spec(config, spec)
                .with_codegen_license(permit_unlicensed())
                .compile(&direct_call_module(linkage))
                .expect_err(
                    "non-preemptible direct AOT edge must fail before object/proof emission",
                );
            assert!(
                matches!(
                    &error,
                    CompileError::AotDirectModuleFunctionBindingUnsupported { call_count: 1, target }
                        if target == triple
                ),
                "unexpected AOT refusal for {triple} {linkage}: {error}"
            );
        }

        Compiler::new_for_target_spec(CompilerConfig::default(), spec)
            .with_codegen_license(permit_unlicensed())
            .compile(&direct_call_module(Linkage::External))
            .unwrap_or_else(|error| {
                panic!("{triple}: interposable external direct AOT call remains supported: {error}")
            });
    }
}

/// On AArch64 ELF the same direct call compiles: the callee is the object's
/// one `add_one` symbol, a defined `STB_LOCAL` `STT_FUNC`, and at O0 (no
/// module inliner) the call is a branch relocation against it. (Proof
/// promotion is not requested: it refuses the caller's frame `STP`/`LDP`
/// whatever the callee's linkage.)
#[test]
fn aot_binds_internal_and_private_direct_calls_locally_on_aarch64_elf() {
    const STB_LOCAL: u8 = 0;
    const STT_FUNC: u8 = 2;
    const R_AARCH64_JUMP26: u32 = 282;
    const R_AARCH64_CALL26: u32 = 283;
    let spec = TargetSpec::parse("aarch64-unknown-linux-gnu").expect("triple");
    for linkage in [Linkage::Internal, Linkage::Private] {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let mut config = CompilerConfig::for_host_jit_unchecked();
            config.opt_level = opt_level;
            let compiler = Compiler::new_for_target_spec(config, spec)
                .with_codegen_license(permit_unlicensed());
            assert!(compiler.object_binds_module_local_functions());
            let object = compiler
                .compile(&direct_call_module(linkage))
                .unwrap_or_else(|error| panic!("{linkage} {opt_level:?}: {error}"))
                .object_code;
            let records = trust_cg_codegen::elf::reparse::read_object_records(&object)
                .expect("AArch64 ELF object");
            let add_one: Vec<(usize, &trust_cg_codegen::elf::reparse::ElfSymbolRecord)> = records
                .symbols
                .iter()
                .enumerate()
                .filter(|(_, symbol)| symbol.name == "add_one")
                .collect();
            assert!(
                matches!(
                    add_one.as_slice(),
                    [(_, symbol)] if symbol.binding == STB_LOCAL
                        && symbol.symbol_type == STT_FUNC
                        && symbol.section_index != 0
                ),
                "{linkage} {opt_level:?}: {add_one:?}"
            );
            let calls = records
                .relocations
                .iter()
                .filter(|relocation| relocation.record.symbol_index as usize == add_one[0].0)
                .filter(|relocation| {
                    [R_AARCH64_CALL26, R_AARCH64_JUMP26].contains(&relocation.record.reloc_type)
                })
                .count();
            if opt_level == OptLevel::O0 {
                assert_eq!(calls, 1, "{linkage}: the O0 call relocates against add_one");
            }
        }
    }
}

/// On AArch64 Mach-O the same direct call compiles: the callee is the
/// object's one `_add_one` symbol, a non-external `N_SECT` definition in
/// `__TEXT,__text` (`n_type` exactly `N_SECT`), and at O0 (no module inliner)
/// the call is one external `ARM64_RELOC_BRANCH26` naming it. No symbol of
/// the object spells `_add_one` any other way.
#[test]
fn aot_binds_internal_and_private_direct_calls_locally_on_aarch64_macho() {
    const N_SECT: u8 = 0x0e;
    const ARM64_RELOC_BRANCH26: u8 = 2;
    let spec = TargetSpec::parse("aarch64-apple-darwin").expect("triple");
    for linkage in [Linkage::Internal, Linkage::Private] {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let mut config = CompilerConfig::for_host_jit_unchecked();
            config.opt_level = opt_level;
            let compiler = Compiler::new_for_target_spec(config, spec)
                .with_codegen_license(permit_unlicensed());
            assert!(compiler.object_binds_module_local_functions());
            let object = compiler
                .compile(&direct_call_module(linkage))
                .unwrap_or_else(|error| panic!("{linkage} {opt_level:?}: {error}"))
                .object_code;
            let records = trust_cg_codegen::macho::reparse::read_object_records(&object)
                .expect("AArch64 Mach-O object");
            let add_one: Vec<(usize, &trust_cg_codegen::macho::reparse::MachoSymbolRecord)> =
                records
                    .symbols
                    .iter()
                    .enumerate()
                    .filter(|(_, symbol)| symbol.name == "_add_one")
                    .collect();
            assert!(
                matches!(
                    add_one.as_slice(),
                    [(_, symbol)] if symbol.n_type == N_SECT
                        && records.section(symbol.n_sect).is_some_and(|section| {
                            section.segname == "__TEXT" && section.sectname == "__text"
                        })
                ),
                "{linkage} {opt_level:?}: {add_one:?}"
            );
            let calls = records.section_relocations[0]
                .iter()
                .filter(|record| {
                    record.r_extern
                        && record.r_symbolnum as usize == add_one[0].0
                        && record.r_type == ARM64_RELOC_BRANCH26
                })
                .count();
            if opt_level == OptLevel::O0 {
                assert_eq!(
                    calls, 1,
                    "{linkage}: the O0 call relocates against _add_one"
                );
            }
        }
    }
}

#[test]
fn jit_fails_closed_instead_of_interposing_local_calls_after_adapter_clone() {
    let mut module = direct_call_module(Linkage::Internal);
    add_div_annotation_clone_trigger(&mut module);
    let externs = HashMap::from([(
        "add_one".to_string(),
        malicious_add_one_override as *const () as *const u8,
    )]);
    let error = Compiler::new(CompilerConfig::for_host_jit_unchecked())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module, &externs)
        .expect_err("a cloned module cannot silently downgrade exact local binding");
    assert!(
        matches!(&error, CompileError::Adapter(_))
            && error.to_string().contains("adapter-owned module clone")
            && error.to_string().contains("1 direct edge(s)"),
        "unexpected clone refusal: {error}"
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
