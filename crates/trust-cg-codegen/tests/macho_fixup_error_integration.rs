// trust-cg-codegen/tests/macho_fixup_error_integration.rs
// Regression coverage for crash-free Mach-O fixup error propagation.
//
// Part of #386.

use std::collections::HashMap;
use trust_cg_codegen::macho::linker::{LinkerError, MachOParser, ParsedObject, link};
use trust_cg_codegen::macho::reloc::AArch64RelocKind;
use trust_cg_codegen::macho::{Fixup, FixupError, FixupList, FixupTarget};
use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};
use trust_cg_codegen::{JitCompiler, JitConfig, JitError};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature};

fn caller_with_unresolved_symbol(symbol: &str) -> MachFunction {
    let mut func = MachFunction::new("caller".to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;

    let call = MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol(symbol.to_string())],
    );
    let call_id = func.push_inst(call);
    func.append_inst(entry, call_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

fn empty_helper() -> MachFunction {
    let mut func = MachFunction::new("helper".to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

fn assert_undefined_external_branch_symbol(bytes: &[u8], symbol: &str) -> ParsedObject {
    let object = MachOParser::parse(bytes).expect("pipeline should emit parseable Mach-O object");
    let expected_name = format!("_{symbol}");
    let symbol_index = object
        .symbols
        .iter()
        .position(|sym| sym.name == expected_name && sym.is_undefined() && sym.is_external())
        .expect("unresolved module call should be emitted as an undefined external symbol");

    let text = object
        .sections
        .iter()
        .find(|section| section.name == "__text")
        .expect("module object should contain __text");

    assert!(
        text.relocations.iter().any(|reloc| {
            reloc.kind == AArch64RelocKind::Branch26
                && reloc.is_extern
                && reloc.symbol_index as usize == symbol_index
        }),
        "branch relocation should reference the undefined external symbol"
    );

    object
}

fn assert_link_rejects_undefined_external(object: ParsedObject, symbol: &str) {
    let expected_name = format!("_{symbol}");
    match link(&[object]) {
        Err(LinkerError::UndefinedSymbol(name)) => assert_eq!(name, expected_name),
        Err(other) => panic!("expected LinkerError::UndefinedSymbol, got {other:?}"),
        Ok(_) => panic!("link should reject unresolved external symbol"),
    }
}

#[test]
fn resolve_named_symbols_unresolved_name_returns_typed_error() {
    let mut list = FixupList::new();
    list.push(Fixup::branch_sym(0, "missing".to_string()));

    let err = list
        .resolve_named_symbols(|_| None)
        .expect_err("unresolved named symbol fixup should return Err");

    assert_eq!(
        err,
        FixupError::UnresolvedSymbol {
            name: "missing".to_string()
        }
    );
}

#[test]
fn resolve_to_relocations_unresolved_named_symbol_returns_typed_error() {
    let mut list = FixupList::new();
    list.push(Fixup {
        offset: 4,
        kind: AArch64RelocKind::Branch26,
        tls_model: None,
        target: FixupTarget::NamedSymbol("missing".to_string()),
        addend: 0,
    });

    let err = list
        .resolve_to_relocations()
        .expect_err("unresolved named symbol should return Err");

    assert_eq!(
        err,
        FixupError::UnresolvedNamedSymbolAtOffset {
            offset: 4,
            name: "missing".to_string()
        }
    );
}

#[test]
fn compile_module_unresolved_symbol_emits_undefined_external_symbol() {
    let pipeline = Pipeline::new(PipelineConfig::default());
    let caller = caller_with_unresolved_symbol("missing");

    let bytes = pipeline
        .compile_module(&[caller])
        .expect("module emission should allow undefined external symbols");

    let object = assert_undefined_external_branch_symbol(&bytes, "missing");
    assert_link_rejects_undefined_external(object, "missing");
}

#[test]
fn compile_module_parallel_unresolved_symbol_emits_undefined_external_symbol() {
    let pipeline = Pipeline::new(PipelineConfig::default());
    let caller = caller_with_unresolved_symbol("missing");
    let helper = empty_helper();

    let bytes = pipeline
        .compile_module_parallel(&[caller, helper])
        .expect("parallel module emission should allow undefined external symbols");

    assert_undefined_external_branch_symbol(&bytes, "missing");
}

#[test]
fn jit_raw_unresolved_symbol_remains_rejection_boundary() {
    let jit = JitCompiler::new(JitConfig::default());
    let caller = caller_with_unresolved_symbol("_trust_cg_jit_missing_symbol_for_386_contract");
    let extern_symbols = HashMap::new();

    match jit.compile_raw(&[caller], &extern_symbols) {
        Err(JitError::UnresolvedSymbol(name)) => {
            assert_eq!(name, "_trust_cg_jit_missing_symbol_for_386_contract");
        }
        Err(other) => panic!("expected JitError::UnresolvedSymbol, got {other:?}"),
        Ok(_) => panic!("JIT should reject unresolved external symbol"),
    }
}
