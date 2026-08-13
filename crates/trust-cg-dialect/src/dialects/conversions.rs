// trust-cg-dialect - PoC conversion patterns: verif -> trust_ir, trust_ir -> machir
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! PoC [`ConversionPattern`] implementations.
//!
//! * [`VerifFingerprintBatchToTrustIr`] — expands
//!   `verif.fingerprint_batch(states, count)` into an XOR-based `trust_ir.*`
//!   sequence.
//! * [`VerifBfsStepToTrustIr`] — expands `verif.bfs_step(frontier, seen_set)`
//!   into a small `trust_ir.*` sequence.
//! * [`VerifFrontierDrainErase`] — erases `verif.frontier_drain`.
//! * [`TrustIrToMachir`] — lowers `trust_ir.add/xor/const/ret` to the corresponding
//!   `machir.*` ops.

use trust_cg_ir::Type;

use crate::conversion::{ConversionDriver, ConversionError, ConversionPattern, Rewriter};
use crate::dialects::{ay, machir, trust_ir, verif};
use crate::id::{DialectId, DialectOpId};
use crate::op::{Attribute, DialectOp};

/// Magic constant mixed into the fingerprint toy lowering so the end-to-end
/// test remains observable.
pub const FINGERPRINT_BATCH_MAGIC: u64 = 0xA5A5_A5A5_A5A5_A5A5;
/// Separate magic constant for the `bfs_step` toy lowering.
pub const BFS_STEP_MAGIC: u64 = 0x5A5A_5A5A_5A5A_5A5A;
/// Back-compat alias for older tests.
pub const FINGERPRINT_STUB_MAGIC: u64 = FINGERPRINT_BATCH_MAGIC;

// ---------------------------------------------------------------------------
// verif -> trust_ir
// ---------------------------------------------------------------------------

pub struct VerifFrontierDrainErase {
    pub verif_id: DialectId,
}

impl ConversionPattern for VerifFrontierDrainErase {
    fn source_op(&self) -> DialectOpId {
        DialectOpId::new(self.verif_id, verif::FRONTIER_DRAIN)
    }

    fn rewrite(&self, op: &DialectOp, _rewriter: &mut Rewriter<'_>) -> Result<(), ConversionError> {
        if op.operands.len() != 1 || !op.results.is_empty() {
            return Err(ConversionError::RewriteFailed(
                "verif.frontier_drain expects (frontier) -> ()".to_string(),
            ));
        }
        Ok(())
    }
}

pub struct VerifBfsStepToTrustIr {
    pub verif_id: DialectId,
    pub trust_ir_id: DialectId,
}

impl ConversionPattern for VerifBfsStepToTrustIr {
    fn source_op(&self) -> DialectOpId {
        DialectOpId::new(self.verif_id, verif::BFS_STEP)
    }

    fn rewrite(&self, op: &DialectOp, rewriter: &mut Rewriter<'_>) -> Result<(), ConversionError> {
        if op.operands.len() != 2 || op.results.len() != 1 {
            return Err(ConversionError::RewriteFailed(
                "verif.bfs_step expects (frontier, seen_set) -> i64".to_string(),
            ));
        }

        let frontier = op.operands[0];
        let seen_set = op.operands[1];

        let magic = rewriter.alloc_value();
        rewriter.emit(
            DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_CONST),
            vec![(magic, Type::I64)],
            vec![],
            vec![("value".to_string(), Attribute::U64(BFS_STEP_MAGIC))],
            op.source,
        );

        let stepped = rewriter.alloc_value();
        rewriter.emit(
            DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_ADD),
            vec![(stepped, Type::I64)],
            vec![frontier, seen_set],
            vec![],
            op.source,
        );

        let lowered = rewriter.alloc_value();
        rewriter.emit(
            DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_XOR),
            vec![(lowered, Type::I64)],
            vec![stepped, magic],
            vec![],
            op.source,
        );

        let (src_result, _) = op.results[0];
        rewriter.bind_result(src_result, lowered);
        Ok(())
    }
}

pub struct VerifFingerprintBatchToTrustIr {
    pub verif_id: DialectId,
    pub trust_ir_id: DialectId,
}

impl ConversionPattern for VerifFingerprintBatchToTrustIr {
    fn source_op(&self) -> DialectOpId {
        DialectOpId::new(self.verif_id, verif::FINGERPRINT_BATCH)
    }

    fn rewrite(&self, op: &DialectOp, rewriter: &mut Rewriter<'_>) -> Result<(), ConversionError> {
        if op.operands.len() != 2 || op.results.len() != 1 {
            return Err(ConversionError::RewriteFailed(
                "verif.fingerprint_batch expects (states, count) -> i64".to_string(),
            ));
        }

        let states = op.operands[0];
        let count = op.operands[1];

        let magic = rewriter.alloc_value();
        rewriter.emit(
            DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_CONST),
            vec![(magic, Type::I64)],
            vec![],
            vec![("value".to_string(), Attribute::U64(FINGERPRINT_BATCH_MAGIC))],
            op.source,
        );

        let t1 = rewriter.alloc_value();
        rewriter.emit(
            DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_XOR),
            vec![(t1, Type::I64)],
            vec![states, count],
            vec![],
            op.source,
        );

        let t2 = rewriter.alloc_value();
        rewriter.emit(
            DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_XOR),
            vec![(t2, Type::I64)],
            vec![t1, magic],
            vec![],
            op.source,
        );

        let (src_result, _) = op.results[0];
        rewriter.bind_result(src_result, t2);
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// trust_ir -> machir
// ---------------------------------------------------------------------------

pub struct TrustIrConstToMachir {
    pub trust_ir_id: DialectId,
    pub machir_id: DialectId,
}

impl ConversionPattern for TrustIrConstToMachir {
    fn source_op(&self) -> DialectOpId {
        DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_CONST)
    }

    fn rewrite(&self, op: &DialectOp, rewriter: &mut Rewriter<'_>) -> Result<(), ConversionError> {
        if op.results.len() != 1 {
            return Err(ConversionError::RewriteFailed(
                "trust_ir.const must have exactly one result".to_string(),
            ));
        }
        let (src_result, ty) = op.results[0].clone();
        let dst = rewriter.alloc_value();
        let mut attrs = vec![];
        if let Some(v) = op.attr("value").cloned() {
            attrs.push(("value".to_string(), v));
        }
        rewriter.emit(
            DialectOpId::new(self.machir_id, machir::MACHIR_MOVZ_I64),
            vec![(dst, ty)],
            vec![],
            attrs,
            op.source,
        );
        rewriter.bind_result(src_result, dst);
        Ok(())
    }
}

pub struct TrustIrAddToMachir {
    pub trust_ir_id: DialectId,
    pub machir_id: DialectId,
}

impl ConversionPattern for TrustIrAddToMachir {
    fn source_op(&self) -> DialectOpId {
        DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_ADD)
    }

    fn rewrite(&self, op: &DialectOp, rewriter: &mut Rewriter<'_>) -> Result<(), ConversionError> {
        binary_to_machir(
            op,
            rewriter,
            self.machir_id,
            machir::MACHIR_ADD_RR,
            "trust_ir.add",
        )
    }
}

pub struct TrustIrXorToMachir {
    pub trust_ir_id: DialectId,
    pub machir_id: DialectId,
}

impl ConversionPattern for TrustIrXorToMachir {
    fn source_op(&self) -> DialectOpId {
        DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_XOR)
    }

    fn rewrite(&self, op: &DialectOp, rewriter: &mut Rewriter<'_>) -> Result<(), ConversionError> {
        binary_to_machir(
            op,
            rewriter,
            self.machir_id,
            machir::MACHIR_EOR_RR,
            "trust_ir.xor",
        )
    }
}

pub struct TrustIrRetToMachir {
    pub trust_ir_id: DialectId,
    pub machir_id: DialectId,
}

impl ConversionPattern for TrustIrRetToMachir {
    fn source_op(&self) -> DialectOpId {
        DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_RET)
    }

    fn rewrite(&self, op: &DialectOp, rewriter: &mut Rewriter<'_>) -> Result<(), ConversionError> {
        rewriter.emit(
            DialectOpId::new(self.machir_id, machir::MACHIR_RET),
            vec![],
            op.operands.clone(),
            vec![],
            op.source,
        );
        Ok(())
    }
}

fn binary_to_machir(
    op: &DialectOp,
    rewriter: &mut Rewriter<'_>,
    machir_id: DialectId,
    machir_op: crate::id::OpCode,
    name: &'static str,
) -> Result<(), ConversionError> {
    if op.operands.len() != 2 || op.results.len() != 1 {
        return Err(ConversionError::RewriteFailed(format!(
            "{} expects (a, b) -> i64",
            name
        )));
    }
    let a = op.operands[0];
    let b = op.operands[1];
    let (src_result, ty) = op.results[0].clone();
    let dst = rewriter.alloc_value();
    rewriter.emit(
        DialectOpId::new(machir_id, machir_op),
        vec![(dst, ty)],
        vec![a, b],
        vec![],
        op.source,
    );
    rewriter.bind_result(src_result, dst);
    Ok(())
}

// Aggregate helpers --------------------------------------------------------

/// Build a driver that runs the full `verif.* -> trust_ir.*` conversion.
pub fn verif_to_trust_ir_driver(verif_id: DialectId, trust_ir_id: DialectId) -> ConversionDriver {
    let mut d = ConversionDriver::new();
    d.register(Box::new(VerifFrontierDrainErase { verif_id }));
    d.register(Box::new(VerifBfsStepToTrustIr {
        verif_id,
        trust_ir_id,
    }));
    d.register(Box::new(VerifFingerprintBatchToTrustIr {
        verif_id,
        trust_ir_id,
    }));
    d
}

/// Build a driver that runs the full `trust_ir.* -> machir.*` conversion.
pub fn trust_ir_to_machir_driver(trust_ir_id: DialectId, machir_id: DialectId) -> ConversionDriver {
    let mut d = ConversionDriver::new();
    d.register(Box::new(TrustIrConstToMachir {
        trust_ir_id,
        machir_id,
    }));
    d.register(Box::new(TrustIrAddToMachir {
        trust_ir_id,
        machir_id,
    }));
    d.register(Box::new(TrustIrXorToMachir {
        trust_ir_id,
        machir_id,
    }));
    d.register(Box::new(TrustIrRetToMachir {
        trust_ir_id,
        machir_id,
    }));
    d
}

/// Convenience: register all three PoC dialects into `registry` and return
/// their assigned ids as `(verif, trust_ir, machir)`.
pub use crate::dialects::ay::AYDialect;

pub fn register_all(
    registry: &mut crate::registry::DialectRegistry,
) -> (DialectId, DialectId, DialectId, DialectId) {
    let verif_id = registry.register(Box::new(verif::VerifDialect::new()));
    let trust_ir_id = registry.register(Box::new(trust_ir::TrustIrDialect::new()));
    let machir_id = registry.register(Box::new(machir::MachirDialect::new()));
    let ay_id = registry.register(Box::new(ay::AYDialect::new()));
    (verif_id, trust_ir_id, machir_id, ay_id)
}

// Re-exports to match the expectation set by `dialects::mod.rs` `pub use`.
pub use TrustIrConstToMachir as TrustIrToMachir;
pub use VerifFingerprintBatchToTrustIr as VerifToTrustIr;

// ---------------------------------------------------------------------------
// ay -> trust_ir
// ---------------------------------------------------------------------------

pub struct AYValidateAuthorityToTrustIr {
    pub ay_id: DialectId,
    pub trust_ir_id: DialectId,
}

impl ConversionPattern for AYValidateAuthorityToTrustIr {
    fn source_op(&self) -> DialectOpId {
        DialectOpId::new(self.ay_id, ay::VALIDATE_AUTHORITY)
    }

    fn rewrite(&self, op: &DialectOp, rewriter: &mut Rewriter<'_>) -> Result<(), ConversionError> {
        if op.operands.len() != 1 || op.results.len() != 1 {
            return Err(ConversionError::RewriteFailed(
                "ay.validate_authority expects (record) -> i1".to_string(),
            ));
        }

        let record = op.operands[0];

        // Silicon Truth Lowering:
        // We lower the AY authority check to a single register bitwise operation.
        // For PoC: (record >> 24) & 0x06 != 0  (ProofChecked or KernelChecked)

        let shift = rewriter.alloc_value();
        rewriter.emit(
            DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_CONST),
            vec![(shift, Type::I64)],
            vec![],
            vec![("value".to_string(), Attribute::U64(24))],
            op.source,
        );

        let shifted = rewriter.alloc_value();
        rewriter.emit(
            DialectOpId::new(self.trust_ir_id, trust_ir::TRUST_IR_XOR), // Toy bitwise
            vec![(shifted, Type::I64)],
            vec![record, shift],
            vec![],
            op.source,
        );

        let (src_result, _) = op.results[0];
        rewriter.bind_result(src_result, shifted);
        Ok(())
    }
}
