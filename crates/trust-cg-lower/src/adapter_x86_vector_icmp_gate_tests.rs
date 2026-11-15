// trust-cg-lower/adapter_x86_vector_icmp_gate_tests.rs - the x86-64 vector
// compare gate's refusal arm, witnessed with a synthetic cell reader.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! At the pinned trust-ir no `chc_x86` cell answers fail-closed, so
//! `tests/x86_vector_icmp_admission.rs`, which drives module entry through
//! trust-ir's real reader, has no real subject for the gate's refusal arm, and
//! deleting the gate call would fail nothing there. These tests hold the two
//! halves that remain checkable without a real fail-closed row:
//!
//! * the gate itself, over a synthetic reader: it asks the reader about
//!   exactly the `(lane bits, lanes, op)` cell of each vector `ICmp`, refuses a
//!   fail-closed answer by name, and admits an available or ungoverned
//!   (`None`) answer;
//! * the wiring: module entry calls the gate with trust-ir's reader under the
//!   x86-64 guard, once, and nothing else calls it (a token scan of this
//!   crate's non-test source with `source_scan`).
//!
//! Test rung. The scan sees the call, not that every x86-64 module entry
//! reaches it; the per-cell equality with the real manifest stays with the
//! admission test.

use std::cell::RefCell;

use super::*;
use crate::source_scan::{Tok, crate_scans, lex, matching_close};
use trust_ir::{
    ChcX86VectorIcmpCell, FuncTy, HardwareVectorContractReason, HardwareVectorContractStatus,
};

const OPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
];

/// A deferred cell, as trust-ir published the unsigned `v16_i8` compares
/// before trust-ir `72dee4b6`.
const FAIL_CLOSED: ChcX86VectorIcmpCell = ChcX86VectorIcmpCell {
    status: HardwareVectorContractStatus::Deferred,
    reason: HardwareVectorContractReason::UnsignedVectorCompareProofBlocked,
    feature_guard: None,
};

const AVAILABLE: ChcX86VectorIcmpCell = ChcX86VectorIcmpCell {
    status: HardwareVectorContractStatus::Available,
    reason: HardwareVectorContractReason::CanonicalContract,
    feature_guard: Some("x86.sse2"),
};

/// `cmp(a, b) -> <lanes x bool>` comparing two `<lanes x elem>` with `op`.
fn compare_module(elem: &Ty, lanes: u32, op: ICmpOp) -> TrustIrModule {
    let ty = Ty::Vector(Box::new(elem.clone()), lanes);
    let mut module = TrustIrModule::new("x86_vector_icmp_gate");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![Ty::Vector(Box::new(Ty::Bool), lanes)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "cmp", sig, BlockId::new(0));
    let mut block = TrustIrBlock::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())];
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op,
            ty,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    func.blocks.push(block);
    module.functions.push(func);
    module
}

/// MUTATION CONTROL (recorded when this landed): inverting the gate's
/// `fail_closed()` test, or asking the reader with the lanes and bits
/// swapped, fails this test.
#[test]
fn a_fail_closed_answer_is_refused_by_name_for_the_asked_cell() {
    for (elem, lanes) in [(Ty::I32, 4), (Ty::I64, 2), (Ty::I8, 16), (Ty::I16, 8)] {
        let bits = elem.bit_width().expect("integer lanes");
        let contract = trust_ir::chc_x86_hardware_vector_contract_descriptors()
            .into_iter()
            .find(|d| d.element_bits == bits && d.lane_count == lanes)
            .expect("a chc_x86 descriptor covers the shape")
            .contract_name;
        for op in OPS {
            let asked = RefCell::new(Vec::new());
            let verdict = reject_x86_vector_icmp_cell_not_available(
                &compare_module(&elem, lanes, op),
                |b, l, o| {
                    asked.borrow_mut().push((b, l, o));
                    Some(FAIL_CLOSED)
                },
            );
            assert_eq!(
                asked.into_inner(),
                [(bits, lanes, op)],
                "<{lanes} x i{bits}> {op:?}: the gate asks about exactly the compare's cell"
            );
            match verdict {
                Err(AdapterError::VectorCompareCellFailClosed {
                    function,
                    contract: named,
                    operation,
                    reason,
                }) => {
                    assert_eq!(function, "cmp");
                    assert_eq!(named, contract);
                    assert_eq!(operation, chc_x86_icmp_operation_name(op));
                    assert_eq!(reason, FAIL_CLOSED.reason.code());
                }
                other => panic!(
                    "<{lanes} x i{bits}> {op:?}: a fail-closed answer must be refused by name, \
                     got {other:?}"
                ),
            }
        }
    }
}

#[test]
fn an_available_or_ungoverned_answer_is_admitted() {
    let module = compare_module(&Ty::I8, 16, ICmpOp::Ult);
    assert!(reject_x86_vector_icmp_cell_not_available(&module, |_, _, _| Some(AVAILABLE)).is_ok());
    // `None`: no descriptor covers the shape. Not governed by the manifest, a
    // stated gap rather than a grant (see the gate's doc).
    assert!(reject_x86_vector_icmp_cell_not_available(&module, |_, _, _| None).is_ok());
}

/// `tokens` with every `,` that directly precedes a closing bracket removed,
/// so rustfmt's trailing comma does not decide a match.
fn without_trailing_commas(tokens: &[Tok]) -> Vec<Tok> {
    tokens
        .iter()
        .enumerate()
        .filter(|(at, token)| {
            !(**token == Tok::Punct(',')
                && matches!(tokens.get(at + 1), Some(Tok::Punct(')' | ']' | '}'))))
        })
        .map(|(_, token)| token.clone())
        .collect()
}

/// MUTATION CONTROL (recorded when this landed): deleting the call, keying it
/// on `GuardCarrierArch::AArch64`, or passing a reader other than trust-ir's
/// fails this test.
#[test]
fn module_entry_asks_trust_irs_reader_on_x86_64() {
    const GATE: &str = "reject_x86_vector_icmp_cell_not_available";
    let scans = crate_scans(&std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src"));
    let tokens = &scans["adapter.rs"].tokens;
    let entry = tokens
        .windows(2)
        .position(|pair| {
            pair[0] == Tok::Ident("fn".into())
                && pair[1] == Tok::Ident("translate_module_with_backend_symbol_check".into())
        })
        .expect("the module entry every translate_module_* reaches");
    let open = (entry..tokens.len())
        .find(|&at| tokens[at] == Tok::Punct('{'))
        .expect("its body");
    let body = without_trailing_commas(&tokens[open..matching_close(tokens, open)]);
    let call = without_trailing_commas(&lex("if guard_carrier_arch == GuardCarrierArch::X86_64 {
             reject_x86_vector_icmp_cell_not_available(
                 module,
                 trust_ir::chc_x86_vector_icmp_cell_status,
             )?;
         }"));
    assert_eq!(
        body.windows(call.len())
            .filter(|window| *window == call.as_slice())
            .count(),
        1,
        "module entry must call `{GATE}` with trust-ir's reader under the x86-64 guard, once"
    );
    // Nothing else calls the gate: every mention in the crate's non-test code
    // is that call or the definition.
    let mentions: usize = scans
        .values()
        .map(|scan| {
            scan.tokens
                .iter()
                .filter(|token| **token == Tok::Ident(GATE.into()))
                .count()
        })
        .sum();
    assert_eq!(
        mentions, 2,
        "`{GATE}` is defined once and called once, from module entry"
    );
}
