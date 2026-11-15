// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Preserve provenance for a qualified constant MIR `Offset`.
//!
//! Rust's MIR operation carries the in-bounds pointer-arithmetic contract.
//! Spelling its positive constant byte displacement as a GEP keeps the base
//! allocation. Integer casts instead discard and recover provenance, possibly
//! selecting an adjacent allocation. This normalization grants no allocation,
//! lifetime, dereference or backend proof authority by itself.
//!
//! The pinned GEP model rejects negative indices. Negative, dynamic and large
//! offsets keep their existing transport; `arith_offset` is a separate wrapping
//! operation and never calls this module. Zero displacement is the base itself,
//! including for a zero-sized pointee, rather than a GEP of a possibly null base.

use trust_ir::{Block, Constant, Inst, InstrNode, Ty, ValueId};

pub(crate) fn qualified_target(triple: &str, pointer_bits: u64) -> bool {
    triple == "aarch64-unknown-linux-gnu" && pointer_bits == 64
}

pub(crate) struct ConstantOffset {
    bytes: u64,
}

impl ConstantOffset {
    /// The caller must have the actual MIR `BinOp::Offset`, its evaluated
    /// constant count (if any), and rustc's actual pointee-layout stride.
    pub(crate) fn from_mir_count(count: Option<i128>, stride: u64) -> Option<Self> {
        if stride == 0 {
            return Some(Self { bytes: 0 });
        }
        let count = u64::try_from(count?).ok()?;
        let bytes = count.checked_mul(stride)?;
        (bytes <= i64::MAX as u64).then_some(Self { bytes })
    }

    /// `base` is already normalized to the plain pointer carrier. Only the
    /// authenticated MIR offset path calls this; a wrapping address expression
    /// cannot acquire an in-bounds promise merely from having constant bits.
    pub(crate) fn emit(
        self,
        block: &mut Block,
        base: ValueId,
        mut fresh: impl FnMut() -> ValueId,
    ) -> ValueId {
        if self.bytes == 0 {
            return base;
        }
        let index = fresh();
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(self.bytes)),
            })
            .with_result(index),
        );
        let result = fresh();
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U8,
                base,
                indices: vec![index],
                inbounds: true,
            })
            .with_result(result),
        );
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
    use trust_ir::{BinOp, BlockId, CastOp, FuncId, FuncTy, Function, Module};

    fn fixture(offset: u64, legacy: bool) -> Module {
        let mut block = Block::new(BlockId::new(0));
        block.body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(4),
            })
            .with_result(ValueId(1)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::U8,
                count: Some(ValueId(1)),
                align: Some(1),
            })
            .with_result(ValueId(2)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::U8,
                count: Some(ValueId(1)),
                align: Some(1),
            })
            .with_result(ValueId(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(77),
            })
            .with_result(ValueId(4)),
        ];
        let address = if legacy {
            block.body.extend([
                InstrNode::new(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::I64,
                    operand: ValueId(2),
                })
                .with_result(ValueId(10)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(i128::from(offset)),
                })
                .with_result(ValueId(11)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId(10),
                    rhs: ValueId(11),
                })
                .with_result(ValueId(12)),
                InstrNode::new(Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::I64,
                    dst_ty: Ty::Ptr,
                    operand: ValueId(12),
                })
                .with_result(ValueId(13)),
            ]);
            ValueId(13)
        } else {
            let mut id = 100;
            ConstantOffset::from_mir_count(Some(i128::from(offset)), 1)
                .unwrap()
                .emit(&mut block, ValueId(2), || {
                    let result = ValueId(id);
                    id += 1;
                    result
                })
        };
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::U8,
            ptr: address,
            value: ValueId(4),
            volatile: false,
            align: Some(1),
        }));
        // Observe through an independently formed address, so a wrong emitted
        // displacement cannot pass just because the same wrong pointer is read.
        let observed = if offset == 4 {
            ValueId(3)
        } else {
            block.body.extend([
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(i128::from(offset)),
                })
                .with_result(ValueId(20)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: ValueId(2),
                    indices: vec![ValueId(20)],
                    inbounds: true,
                })
                .with_result(ValueId(21)),
            ]);
            ValueId(21)
        };
        block.body.extend([
            InstrNode::new(Inst::Load {
                ty: Ty::U8,
                ptr: observed,
                volatile: false,
                align: Some(1),
            })
            .with_result(ValueId(30)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId(30)],
            }),
        ]);
        let mut module = Module::new("constant_mir_pointer_offset");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U8],
                abi: None,
                is_vararg: false,
            })
            .unwrap();
        let mut function = Function::new(FuncId::new(0), "offset", signature, block.id);
        function.blocks.push(block);
        module.try_add_function(function).unwrap();
        module
    }

    #[test]
    fn adjacent_allocation_cannot_supply_provenance_to_an_offset() {
        let module = fixture(4, false);
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert!(error.message.contains("out of bounds"), "{error:?}");

        let legacy = fixture(4, true);
        let outcome = Interpreter::with_module(&legacy)
            .execute_func(FuncId::new(0), [])
            .unwrap();
        assert_eq!(outcome.host_calls, 0);
        assert_eq!(outcome.returns, [InterpretValue::int(Ty::U8, 77).unwrap()]);
    }

    #[test]
    fn valid_bytes_are_observed_through_independent_addresses() {
        for offset in 0..4 {
            let module = fixture(offset, false);
            let outcome = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [])
                .unwrap();
            assert_eq!(outcome.host_calls, 0);
            assert_eq!(outcome.returns, [InterpretValue::int(Ty::U8, 77).unwrap()]);
        }
    }

    #[test]
    fn offset_plan_preserves_zero_and_refuses_unqualified_index_shapes() {
        for (count, stride) in [(None, 0), (Some(-1), 0), (Some(i128::MAX), 0), (Some(0), 4)] {
            assert_eq!(
                ConstantOffset::from_mir_count(count, stride).unwrap().bytes,
                0
            );
        }
        assert_eq!(
            ConstantOffset::from_mir_count(Some(3), 4).unwrap().bytes,
            12
        );
        for (count, stride) in [
            (None, 4),
            (Some(-1), 4),
            (Some(i128::MAX), 4),
            (Some(2), u64::MAX),
        ] {
            assert!(ConstantOffset::from_mir_count(count, stride).is_none());
        }
    }

    #[test]
    fn target_scope_is_the_qualified_linux_aarch64_abi() {
        assert!(qualified_target("aarch64-unknown-linux-gnu", 64));
        for (triple, bits) in [
            ("aarch64-unknown-linux-gnu", 32),
            ("aarch64_be-unknown-linux-gnu", 64),
            ("aarch64-apple-darwin", 64),
            ("x86_64-unknown-linux-gnu", 64),
            ("wasm32-unknown-unknown", 32),
        ] {
            assert!(!qualified_target(triple, bits));
        }
    }
}
