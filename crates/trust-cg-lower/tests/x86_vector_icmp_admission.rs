// trust-cg-lower/tests/x86_vector_icmp_admission.rs — x86-64 module entry
// admits exactly the vector-compare cells trust-ir's manifest makes available.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir `docs/dialects.md` ("Vector compares on x86-64 follow one per-cell
//! rule", trust-ir `7b0947ee`): for each `chc_x86` descriptor (`v4_i32`,
//! `v2_i64`, `v16_i8`, `v8_i16`) and each `ICmpOp`, the `icmp.<op>` row decides
//! whether that cell may be lowered to x86-64, read through the table's ONE
//! reader, `trust_ir::chc_x86_vector_icmp_cell_status`. An x86-64 consumer MUST
//! refuse a module whose vector `ICmp` lands on a fail-closed cell. At the
//! pinned trust-ir no covered cell is fail-closed; trust-cg-verify
//! `fail_closed_icmp_cells_carry_no_certificate_pin` holds that at whatever
//! rev is pinned, since the reader's fail-closed set must equal its empty
//! `REVIEWED_FAIL_CLOSED_CELLS`. The four unsigned `v16_i8` compares, the last
//! ones, were published available at trust-ir `72dee4b6`, and their
//! must-refuse corpus row
//! (`vector_unsigned_cmp_bytes_x86`) retired with them. trust-ir records the
//! clause as the `none` corpus row `refuse/vector_icmp_fail_closed_cell_x86`.
//!
//! This backend's x86-64 module entry asks that reader
//! (`reject_x86_vector_icmp_cell_not_available`, beside the DarwinPCS check).
//! The test holds admission EQUAL to the manifest, cell by cell, derived from
//! the reader (no count is spelled here):
//!
//! * x86-64 (`x86_64-unknown-linux-gnu`): admitted iff the cell is available;
//!   a refused cell is refused by name (`VectorCompareCellFailClosed`, with
//!   the descriptor, the operation and the published reason). The four
//!   unsigned `v16_i8` cells are also pinned ADMITTED by name, so the step
//!   that made them available is recorded here and a reader that turns one
//!   fail-closed again changes this line deliberately. With no fail-closed
//!   cell at this pin, the refused-by-name arm has no real subject here; the
//!   gate's refusal arm is witnessed over a synthetic reader by the unit tests
//!   in `src/adapter_x86_vector_icmp_gate_tests.rs`, which also scan module
//!   entry for the call with trust-ir's reader. A newly deferred cell is
//!   reviewed in ONE place, trust-cg-verify `tests/x86_icmp_manifest_cells.rs`
//!   (`REVIEWED_FAIL_CLOSED_CELLS`); this test holds admission equal to
//!   whatever set the reader answers, so it needs no edit for one. Admission
//!   itself reads the reader, so the move that made the four admitted changed
//!   no gate code;
//! * AArch64 (`aarch64-apple-darwin`): every cell admitted — the rule governs
//!   x86-64 only;
//! * `<8 x i8>` `eq` on x86-64: NO descriptor covers the shape (the reader
//!   answers `None`), and this backend lowers it (`V8I8Icmp`, `PCMPEQB`) with
//!   no registered x86 obligation — the named, UNGOVERNED gap, pinned here so
//!   that closing it later flips this line deliberately.
//!
//! What this does not cover, stated: an available cell's `feature_guard` is
//! held where the instruction is chosen (the x86 pipeline refuses `pcmpeqq` /
//! `pcmpgtq` on a target without SSE4.1 / SSE4.2), pinned per cell by
//! trust-cg-codegen `tests/x86_vector_icmp_feature_guard.rs`; the LIR-direct and
//! function-level entries (`translate_function`) do not pass through module
//! entry. Test rung, not proof.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::{
    GuardCarrierArch, TlsDialect, translate_module_for_arch_with_tls_with_license,
};
use trust_ir::{
    Block, BlockId, Endianness, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Module,
    StructPassingPolicy, TargetInfo, Ty, ValueId,
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

/// The four `chc_x86` descriptor shapes, as the signed element types this
/// backend lowers: `(element, lanes)`.
fn shapes() -> [(Ty, u32); 4] {
    [(Ty::I32, 4), (Ty::I64, 2), (Ty::I8, 16), (Ty::I16, 8)]
}

/// `cmp(a: <lanes x elem>, b: <lanes x elem>) -> <lanes x bool>` on `triple`.
fn compare_module(triple: &str, op: ICmpOp, elem: &Ty, lanes: u32) -> Module {
    let ty = Ty::Vector(Box::new(elem.clone()), lanes);
    let mask = Ty::Vector(Box::new(Ty::Bool), lanes);
    let mut module = Module::new("x86_vector_icmp_admission");
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![mask],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "cmp", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
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

fn manifest_operation(op: ICmpOp) -> String {
    format!("icmp.{op:?}").to_ascii_lowercase()
}

/// MUTATION CONTROLS: keying the gate on AArch64 instead of x86-64 refuses
/// the AArch64 rows and fails this test (recorded at the rule's landing).
/// Deleting the x86-64 gate call failed it while the manifest published the
/// `v16_i8` unsigned cells fail-closed; at this pin it no longer can, because
/// no cell is fail-closed, and the deletion is caught by the adapter's
/// `module_entry_asks_trust_irs_reader_on_x86_64` scan instead.
#[test]
fn x86_vector_icmp_admission_is_the_manifest() {
    let mut failures = Vec::new();
    let mut admitted_x86: Vec<(u32, u32, ICmpOp)> = Vec::new();
    for (elem, lanes) in shapes() {
        let bits = elem.bit_width().expect("integer lanes");
        let descriptor = trust_ir::chc_x86_hardware_vector_contract_descriptors()
            .into_iter()
            .find(|d| d.element_bits == bits && d.lane_count == lanes)
            .expect("a chc_x86 descriptor covers the shape");
        for op in OPS {
            let cell = trust_ir::chc_x86_vector_icmp_cell_status(bits, lanes, op)
                .expect("the descriptor publishes a row for every ICmpOp");
            let what = format!("{} {}", descriptor.contract_name, manifest_operation(op));
            let x86 = permit_translate_module_for_arch(
                &compare_module("x86_64-unknown-linux-gnu", op, &elem, lanes),
                GuardCarrierArch::X86_64,
            );
            match (cell.fail_closed(), x86) {
                (false, Ok(_)) => admitted_x86.push((bits, lanes, op)),
                (
                    true,
                    Err(AdapterError::VectorCompareCellFailClosed {
                        function,
                        contract,
                        operation,
                        reason,
                    }),
                ) => {
                    if function != "cmp"
                        || contract != descriptor.contract_name
                        || operation != manifest_operation(op)
                        || reason != cell.reason.code()
                    {
                        failures.push(format!(
                            "{what}: refused under the wrong identity: {function} {contract} \
                             {operation} {reason}"
                        ));
                    }
                }
                (true, Ok(_)) => failures.push(format!(
                    "{what}: the manifest publishes it {:?} ({}), and x86-64 module entry ADMITTED it",
                    cell.status,
                    cell.reason.code()
                )),
                (true, Err(other)) => failures.push(format!(
                    "{what}: fail-closed, but refused by another arm: {other:?}"
                )),
                (false, Err(error)) => failures.push(format!(
                    "{what}: available, and x86-64 module entry REFUSED it: {error:?}"
                )),
            }
            if let Err(error) = permit_translate_module_for_arch(
                &compare_module("aarch64-apple-darwin", op, &elem, lanes),
                GuardCarrierArch::AArch64,
            ) {
                failures.push(format!(
                    "{what}: the rule governs x86-64 only, and AArch64 refused it: {error:?}"
                ));
            }
        }
    }

    // The UNGOVERNED gap: no descriptor covers <8 x i8>, and this backend
    // lowers its eq on x86-64 with no registered x86 obligation.
    assert_eq!(
        trust_ir::chc_x86_vector_icmp_cell_status(8, 8, ICmpOp::Eq),
        None
    );
    // (The mask is not returned: a `<8 x bool>` return value is refused by
    // an unrelated carrier rule, and the question here is only the gate.)
    let mut gap = compare_module("x86_64-unknown-linux-gnu", ICmpOp::Eq, &Ty::I8, 8);
    let sig = gap.functions[0].ty.as_usize();
    gap.func_types[sig].returns.clear();
    let body = &mut gap.functions[0].blocks[0].body;
    body.pop();
    body.push(InstrNode::new(Inst::Return { values: vec![] }));
    if let Err(error) = permit_translate_module_for_arch(&gap, GuardCarrierArch::X86_64) {
        failures.push(format!(
            "<8 x i8> icmp.eq on x86-64: the named ungoverned gap is admitted today; it was \
             refused ({error:?}) — if that is the gap closing, update this line and the report"
        ));
    }
    assert!(
        failures.is_empty(),
        "{} finding(s):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    // The four unsigned `v16_i8` compares, by name: available at trust-ir
    // `72dee4b6`, admitted by the x86-64 module entry since this backend's pin
    // reached it.
    for op in [ICmpOp::Ult, ICmpOp::Ule, ICmpOp::Ugt, ICmpOp::Uge] {
        assert!(
            admitted_x86.contains(&(8, 16, op)),
            "chc_x86.v16_i8 {}: not admitted on x86-64 (the reader answers {:?})",
            manifest_operation(op),
            trust_ir::chc_x86_vector_icmp_cell_status(8, 16, op)
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so every
/// admission or refusal asserted above is the vector-compare gate's, never the
/// license's.
fn permit_translate_module_for_arch(
    module: &trust_ir::Module,
    arch: GuardCarrierArch,
) -> Result<Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>, AdapterError> {
    translate_module_for_arch_with_tls_with_license(
        module,
        arch,
        TlsDialect::default(),
        &trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    )
}
