//! The compiler's empty-filter carrier survives lowering exactly and refuses
//! personalities or clause combinations that would change forced unwinding.
use trust_cg_lower::function::RUST_EH_EMPTY_FILTER;
use trust_cg_lower::{GuardCarrierArch, TlsDialect, translate_module_for_arch_with_tls};
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Producer, ValueId,
};

fn module(rust: bool, cleanup: bool, indices: Vec<u32>) -> Module {
    let mut module = Module::new("rust_empty_filter");
    let sig = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    module.functions.push(Function::new(
        FuncId::new(0),
        "may_throw",
        sig,
        BlockId::new(0),
    ));
    let mut function = Function::new(FuncId::new(1), "boundary", sig, BlockId::new(0));
    if rust {
        function.producer = Some(Producer::TRust);
    }
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(InstrNode::new(Inst::Invoke {
        callee: FuncId::new(0),
        args: vec![],
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(2),
    }));
    let mut normal = Block::new(BlockId::new(1));
    normal
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut handler = Block::new(BlockId::new(2));
    handler.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: cleanup,
            catch_type_indices: indices,
        })
        .with_results(vec![ValueId::new(0), ValueId::new(1)]),
    );
    handler.body.push(InstrNode::new(Inst::Unreachable));
    function.blocks = vec![entry, normal, handler];
    module.functions.push(function);
    module
}

#[test]
fn rust_empty_filter_is_preserved_without_a_typeinfo_table() {
    let functions = translate_module_for_arch_with_tls(
        &module(true, false, vec![RUST_EH_EMPTY_FILTER]),
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
    )
    .unwrap();
    let (boundary, _) = functions.iter().find(|(f, _)| f.name == "boundary").unwrap();
    assert_eq!(
        boundary.eh_info.personality.as_deref(),
        Some("rust_eh_personality")
    );
    assert!(boundary.eh_type_table.is_empty());
    assert_eq!(boundary.eh_info.landing_pads.len(), 1);
    assert_eq!(
        boundary.eh_info.landing_pads[0].catch_type_indices,
        [RUST_EH_EMPTY_FILTER]
    );
    assert!(!boundary.eh_info.landing_pads[0].is_cleanup);
}

#[test]
fn rust_empty_filter_rejects_wrong_personality_cleanup_or_mixed_clauses() {
    for (rust, cleanup, indices) in [
        (false, false, vec![RUST_EH_EMPTY_FILTER]),
        (true, true, vec![RUST_EH_EMPTY_FILTER]),
        (true, false, vec![0, RUST_EH_EMPTY_FILTER]),
        (true, false, vec![RUST_EH_EMPTY_FILTER, 1]),
        (true, false, vec![RUST_EH_EMPTY_FILTER; 2]),
    ] {
        let error = translate_module_for_arch_with_tls(
            &module(rust, cleanup, indices),
            GuardCarrierArch::AArch64,
            TlsDialect::default(),
        )
        .unwrap_err();
        assert!(error.to_string().contains("TCG-EH-FILTER"), "{error}");
    }
}
