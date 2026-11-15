// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Materialize an already authenticated CTFE data allocation address.
//!
//! The caller owns allocation emission and resolves its exact module-global
//! index. This helper preserves that index and byte addend in address nodes;
//! it never infers provenance from an integer or changes the global's storage.

use trust_cg_codegen::global_stub::{GLOBAL_ADDR_STUB_MAX_INDEX, GLOBAL_ADDR_STUB_MAX_OFFSET};
use trust_ir::value::GlobalId;
use trust_ir::{Block, CastOp, Constant, Inst, InstrNode, Ty, ValueId};

/// Retain the old producer's index/addend limits while removing its tagged
/// integer placeholder. I64 is the existing address carrier requested by scalar
/// lowering, not permission to reinterpret unrelated numerical literals.
pub(super) fn emit(
    block: &mut Block,
    global_index: u64,
    offset: u64,
    ty: Ty,
    mut fresh: impl FnMut() -> ValueId,
) -> Result<ValueId, String> {
    if global_index > GLOBAL_ADDR_STUB_MAX_INDEX {
        return Err(format!(
            "const-alloc global index {global_index} exceeds the 16-bit global-address stub range"
        ));
    }
    if offset > GLOBAL_ADDR_STUB_MAX_OFFSET {
        return Err(format!(
            "const pointer offset {offset} exceeds the 32-bit global-address stub range"
        ));
    }
    if ty != Ty::I64 && !super::runtime_pointer_value::is_thin_pointer(&ty) {
        return Err(format!(
            "const allocation address requested as unsupported carrier {ty:?}"
        ));
    }

    let base = fresh();
    block.body.push(
        InstrNode::new(Inst::GlobalAddr {
            global: GlobalId::new(global_index as u32),
        })
        .with_result(base),
    );
    let address = if offset == 0 {
        base
    } else {
        let addend = fresh();
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(offset)),
            })
            .with_result(addend),
        );
        let address = fresh();
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base,
                indices: vec![addend],
                inbounds: false,
            })
            .with_result(address),
        );
        address
    };
    if ty == Ty::Ptr {
        return Ok(address);
    }
    let result = fresh();
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: if ty == Ty::I64 {
                CastOp::PtrToInt
            } else {
                CastOp::PtrToPtr
            },
            src_ty: Ty::Ptr,
            dst_ty: ty,
            operand: address,
        })
        .with_result(result),
    );
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_codegen::compiler::module_object_globals;
    use trust_cg_lower::adapter::{AdapterError, validate_codegen_prerequisites};

    /// These fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Their translations state `Permit` explicitly, so
    /// none passes, and no refusal is the license's, by accident.
    fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
        trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
    }
    use trust_ir::{BlockId, FuncId, FuncTy, Function, Global, Linkage, Module, TyId};

    fn fixture(ty: Ty, bytes: Vec<u8>) -> (Module, Function, Block) {
        let mut module = Module::new("const_allocation_address");
        module.types.push(Ty::U8);
        module.globals.push(Global {
            name: "preceding_global".into(),
            ty: Ty::U32,
            mutable: false,
            initializer: Some(Constant::Int(17)),
            linkage: Linkage::Internal,
            tls: None,
            align: Some(4),
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        module.globals.push(Global {
            name: "actual_allocation".into(),
            ty: Ty::Array(TyId::new(0), bytes.len() as u64),
            mutable: false,
            initializer: Some(if Constant::is_uniform_bytes(&bytes, false) {
                Constant::splat(Constant::Int(i128::from(bytes[0])), bytes.len() as u64)
            } else {
                Constant::bytes(bytes)
            }),
            linkage: Linkage::Internal,
            tls: None,
            align: Some(8),
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        module.globals.push(Global {
            name: "relocation_to_allocation".into(),
            ty: Ty::Ptr,
            mutable: false,
            initializer: Some(Constant::SymbolAddr {
                symbol: "actual_allocation".into(),
                addend: 0,
            }),
            linkage: Linkage::Internal,
            tls: None,
            align: Some(8),
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        let signature = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![ty],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let function = Function::new(FuncId::new(0), "address", signature, BlockId::new(0));
        (module, function, Block::new(BlockId::new(0)))
    }

    fn finish(
        mut module: Module,
        mut function: Function,
        mut block: Block,
        result: ValueId,
    ) -> Module {
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![result],
        }));
        function.blocks.push(block);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        module
    }

    #[test]
    fn original_global_offset_and_exact_thin_carriers_pass_the_shared_typed_floor() {
        for ty in [
            Ty::Ptr,
            Ty::Ref(Box::new(Ty::U32)),
            Ty::RefMut(Box::new(Ty::U64)),
            Ty::PtrConst(Box::new(Ty::U8)),
            Ty::PtrMut(Box::new(Ty::U8)),
            Ty::I64,
        ] {
            for offset in [0, 8] {
                let (module, function, mut block) = fixture(ty.clone(), vec![0xA5; 32]);
                let images = module_object_globals(&module).unwrap();
                let mut next = 11;
                let result = emit(&mut block, 1, offset, ty.clone(), || {
                    let id = ValueId::new(next);
                    next += 1;
                    id
                })
                .unwrap();
                assert_eq!(
                    block.body[0].inst,
                    Inst::GlobalAddr {
                        global: GlobalId::new(1)
                    }
                );
                assert_eq!(block.body[0].results, vec![ValueId::new(11)]);
                let address = if offset == 0 {
                    assert_eq!(block.body.len(), if ty == Ty::Ptr { 1 } else { 2 });
                    ValueId::new(11)
                } else {
                    assert_eq!(
                        block.body[1].inst,
                        Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(i128::from(offset)),
                        }
                    );
                    assert_eq!(
                        block.body[2].inst,
                        Inst::GEP {
                            pointee_ty: Ty::I8,
                            base: ValueId::new(11),
                            indices: vec![ValueId::new(12)],
                            inbounds: false,
                        }
                    );
                    ValueId::new(13)
                };
                if ty == Ty::Ptr {
                    assert_eq!(result, address);
                } else {
                    assert_eq!(
                        block.body.last().unwrap().inst,
                        Inst::Cast {
                            op: if ty == Ty::I64 {
                                CastOp::PtrToInt
                            } else {
                                CastOp::PtrToPtr
                            },
                            src_ty: Ty::Ptr,
                            dst_ty: ty.clone(),
                            operand: address,
                        }
                    );
                }
                let module = finish(module, function, block, result);
                assert_eq!(module_object_globals(&module).unwrap(), images);
                validate_codegen_prerequisites(&module).unwrap();
                trust_cg_lower::translate_function_with_license(
                    &module.functions[0],
                    &module,
                    &permit_unlicensed(),
                )
                .unwrap();
            }
        }
    }

    #[test]
    fn empty_real_allocation_keeps_its_global_and_alignment_without_a_fake_ref_constant() {
        let ty = Ty::Ref(Box::new(Ty::Unit));
        let (module, function, mut block) = fixture(ty.clone(), vec![]);
        let images = module_object_globals(&module).unwrap();
        let mut next = 0;
        let result = emit(&mut block, 1, 0, ty, || {
            let id = ValueId::new(next);
            next += 1;
            id
        })
        .unwrap();
        assert_eq!(block.body.len(), 2);
        let module = finish(module, function, block, result);
        assert_eq!(module_object_globals(&module).unwrap(), images);
        validate_codegen_prerequisites(&module).unwrap();
        trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
    }

    #[test]
    fn the_original_uniform_bytes_fixture_remains_an_exact_negative() {
        let (mut module, function, mut block) = fixture(Ty::Ptr, vec![0xA5; 32]);
        module.globals[1].initializer = Some(Constant::bytes(vec![0xA5; 32]));
        let result = emit(&mut block, 1, 0, Ty::Ptr, || ValueId::new(0)).unwrap();
        let module = finish(module, function, block, result);
        let error = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert!(
            matches!(&error, AdapterError::TrustIrAdmissionRefused { error }
            if error == "global `actual_allocation` initializer: non-canonical uniform array: a bytes constant of 32 equal bytes is spelled `splat[ 165; 32 ]` (one spelling per construct, SPEC_RATIFICATIONS §3.1)"),
            "{error:?}"
        );
    }

    #[test]
    fn full_original_offset_is_unsigned_byte_arithmetic_not_a_tagged_integer() {
        let (module, function, mut block) = fixture(Ty::Ptr, vec![1]);
        let mut next = 0;
        let result = emit(&mut block, 1, GLOBAL_ADDR_STUB_MAX_OFFSET, Ty::Ptr, || {
            let id = ValueId::new(next);
            next += 1;
            id
        })
        .unwrap();
        assert_eq!(
            block.body[1].inst,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(u32::MAX)),
            }
        );
        let module = finish(module, function, block, result);
        validate_codegen_prerequisites(&module).unwrap();
        trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
    }

    #[test]
    fn bad_bounds_and_nonaddress_carriers_refuse_without_emitting_partial_nodes() {
        for (index, offset, ty) in [
            (GLOBAL_ADDR_STUB_MAX_INDEX + 1, 0, Ty::Ptr),
            (u64::MAX, 0, Ty::Ptr),
            (0, GLOBAL_ADDR_STUB_MAX_OFFSET + 1, Ty::Ptr),
            (0, u64::MAX, Ty::Ptr),
            (0, 0, Ty::U64),
            (0, 0, Ty::I32),
            (0, 0, Ty::Bool),
            (0, 0, Ty::Tuple(vec![])),
        ] {
            let mut block = Block::new(BlockId::new(0));
            assert!(
                emit(&mut block, index, offset, ty, || {
                    panic!("refused input must not allocate a value ID")
                })
                .is_err()
            );
            assert!(block.body.is_empty());
        }
    }

    #[test]
    fn numerical_and_legacy_tagged_ref_literals_still_fail_the_shared_typed_floor() {
        let ty = Ty::Ref(Box::new(Ty::U32));
        for value in [
            0,
            trust_cg_codegen::global_stub::encode_global_addr_stub(1, 0).unwrap(),
        ] {
            let (module, function, mut block) = fixture(ty.clone(), vec![0; 8]);
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: ty.clone(),
                    value: Constant::Int(value),
                })
                .with_result(ValueId::new(0)),
            );
            let module = finish(module, function, block, ValueId::new(0));
            let error = validate_codegen_prerequisites(&module).unwrap_err();
            assert!(
                matches!(&error, AdapterError::TrustIrAdmissionRefused { error }
                if error.contains("const type mismatch: expected &u32, got int")),
                "untyped reference integer {value}: {error:?}"
            );
        }
    }
}
