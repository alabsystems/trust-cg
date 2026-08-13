// trust-cg-codegen/trust_ir_bitfield_builder.rs - Trust Codegen typed trust_ir bitfield builders
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Builder extension for Trust Codegen's typed local dialect ops.

use trust_ir::dialect::DialectInst;
use trust_ir::{Ty, ValueId};
use trust_ir_build::FunctionBuilder;

pub trait TrustCgBitfieldBuilderExt {
    fn trust_cg_extract_bits(&mut self, ty: Ty, operand: ValueId, lsb: u8, width: u8) -> ValueId;
    fn trust_cg_sextract_bits(&mut self, ty: Ty, operand: ValueId, lsb: u8, width: u8) -> ValueId;
    fn trust_cg_insert_bits(
        &mut self,
        ty: Ty,
        dst: ValueId,
        src: ValueId,
        lsb: u8,
        width: u8,
    ) -> ValueId;
    fn trust_cg_v4i32_mask_extract(&mut self, mask: ValueId) -> ValueId;
    fn trust_cg_v2i64_mask_extract(&mut self, mask: ValueId, result_ty: Ty) -> ValueId;
    fn trust_cg_v2i64_bool_mask_extract(&mut self, mask: ValueId, result_ty: Ty) -> ValueId;
}

pub fn v4i32_mask_extract(mask: ValueId) -> DialectInst {
    trust_cg_lower::bitfield_dialect::v4i32_mask_extract(mask)
}

pub fn v2i64_mask_extract(mask: ValueId, result_ty: Ty) -> DialectInst {
    trust_cg_lower::bitfield_dialect::v2i64_mask_extract(mask, result_ty)
}

pub fn v2i64_bool_mask_extract(mask: ValueId, result_ty: Ty) -> DialectInst {
    trust_cg_lower::bitfield_dialect::v2i64_bool_mask_extract(mask, result_ty)
}

impl<'m> TrustCgBitfieldBuilderExt for FunctionBuilder<'m> {
    fn trust_cg_extract_bits(&mut self, ty: Ty, operand: ValueId, lsb: u8, width: u8) -> ValueId {
        one_result(
            self.dialect_op(trust_cg_lower::bitfield_dialect::extract_bits(
                ty, operand, lsb, width,
            )),
        )
    }

    fn trust_cg_sextract_bits(&mut self, ty: Ty, operand: ValueId, lsb: u8, width: u8) -> ValueId {
        one_result(
            self.dialect_op(trust_cg_lower::bitfield_dialect::sextract_bits(
                ty, operand, lsb, width,
            )),
        )
    }

    fn trust_cg_insert_bits(
        &mut self,
        ty: Ty,
        dst: ValueId,
        src: ValueId,
        lsb: u8,
        width: u8,
    ) -> ValueId {
        one_result(
            self.dialect_op(trust_cg_lower::bitfield_dialect::insert_bits(
                ty, dst, src, lsb, width,
            )),
        )
    }

    fn trust_cg_v4i32_mask_extract(&mut self, mask: ValueId) -> ValueId {
        one_result(self.dialect_op(v4i32_mask_extract(mask)))
    }

    fn trust_cg_v2i64_mask_extract(&mut self, mask: ValueId, result_ty: Ty) -> ValueId {
        one_result(self.dialect_op(v2i64_mask_extract(mask, result_ty)))
    }

    fn trust_cg_v2i64_bool_mask_extract(&mut self, mask: ValueId, result_ty: Ty) -> ValueId {
        one_result(self.dialect_op(v2i64_bool_mask_extract(mask, result_ty)))
    }
}

fn one_result(mut results: Vec<ValueId>) -> ValueId {
    debug_assert_eq!(results.len(), 1);
    results.remove(0)
}
