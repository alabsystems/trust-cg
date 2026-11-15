// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_lower::instructions::Opcode as L;

#[derive(serde::Deserialize)]
struct Capture {
    case: String,
    module: Module,
    lir: Function,
}

fn captures() -> Vec<Capture> {
    serde_json::from_str(include_str!("source_bound_cell_sources.json")).unwrap()
}

#[test]
fn original_invalid_pointer_copies_cannot_supply_source_binding() {
    let before: Vec<Capture> =
        serde_json::from_str(include_str!("source_bound_cell_sources_before.json")).unwrap();
    assert_eq!(before.len(), 24);
    for c in before {
        let errors = trust_ir_build::validate_module(&c.module);
        assert_eq!(errors.len(), 1, "{}: {errors:?}", c.case);
        assert!(
            matches!(&errors[0], trust_ir_build::ValidationError::OperandTypeMismatch { op, .. } if op == "copy")
        );
        assert!(matches!(
            check_aarch64_scalar_cell_source(&c.module, &c.lir),
            Err(ScalarCellSourceError::Source(
                "copy changes scalar or cell type"
            ))
        ));
    }
}

fn read_case(width: usize) -> Capture {
    captures()
        .into_iter()
        .find(|c| c.case == format!("aliased_f{}_read-O0", width * 8))
        .unwrap()
}

fn source_inst(module: &mut Module, predicate: impl Fn(&Inst) -> bool) -> &mut Inst {
    &mut module.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
        .find(|n| predicate(&n.inst))
        .unwrap()
        .inst
}

fn lir_inst(
    lir: &mut Function,
    predicate: impl Fn(&L) -> bool,
) -> &mut trust_cg_lower::instructions::Instruction {
    lir.blocks
        .values_mut()
        .flat_map(|b| &mut b.instructions)
        .find(|i| predicate(&i.opcode))
        .unwrap()
}

#[test]
fn binds_all_twenty_four_fresh_trust_caller_captures() {
    let cases = captures();
    assert_eq!(cases.len(), 24);
    for c in cases {
        let errors = trust_ir_build::validate_module(&c.module);
        assert!(errors.is_empty(), "{}: {errors:?}", c.case);
        let checked = check_aarch64_scalar_cell_source(&c.module, &c.lir)
            .unwrap_or_else(|e| panic!("{}: {e}", c.case));
        assert!(std::ptr::eq(checked.module(), &c.module));
        assert!(std::ptr::eq(checked.lir(), &c.lir));
        assert!(std::ptr::eq(checked.source(), &c.module.functions[0]));
        assert_eq!(
            checked.cell_width(),
            if c.case.contains("f32") { 4 } else { 8 }
        );
        assert_eq!(checked.call_count(), 1);
        let trace = &checked.contract;
        assert_eq!(trace.calls[0].name, "c_change");
        assert_eq!(trace.cell_after, bytes(trace.width, |b| Byte::Call(0, b)));
        assert_eq!(trace.result, trace.cell_after);
    }
}

#[test]
fn original_declared_abi_is_required_even_when_lir_is_identical() {
    for width in [4, 8] {
        let c = read_case(width);
        for which in [0, 1] {
            for convention in [
                CallingConv::Fast,
                CallingConv::Cold,
                CallingConv::Rust,
                CallingConv::Swift,
            ] {
                let mut bad = c.module.clone();
                bad.functions[which].calling_conv = convention;
                assert!(check_aarch64_scalar_cell_source(&bad, &c.lir).is_err());
            }
            for flag in 0..4 {
                let mut bad = c.module.clone();
                match flag {
                    0 => bad.functions[which].attrs.readnone = true,
                    1 => bad.functions[which].attrs.readonly = true,
                    2 => bad.functions[which].attrs.naked = true,
                    _ => bad.functions[which]
                        .attrs
                        .target_features
                        .push("sve".into()),
                }
                assert!(check_aarch64_scalar_cell_source(&bad, &c.lir).is_err());
            }
        }
        let ty = if width == 4 { Ty::F32 } else { Ty::F64 };
        for pointer in [
            Ty::Ptr,
            Ty::PtrConst(Box::new(ty.clone())),
            Ty::RefMut(Box::new(ty)),
            Ty::PtrMut(Box::new(Ty::I8)),
        ] {
            let mut bad = c.module.clone();
            bad.func_types[1].params[0] = pointer;
            assert!(check_aarch64_scalar_cell_source(&bad, &c.lir).is_err());
        }
        for change in 0..6 {
            let mut bad = c.module.clone();
            match change {
                0 => bad.func_types[1].is_vararg = true,
                1 => bad.func_types[1].returns = vec![Ty::F32],
                2 => {
                    bad.func_types[1].params.pop();
                }
                3 => bad.functions[1].linkage = Linkage::ExternalWeak,
                4 => bad.functions[1].blocks = bad.functions[0].blocks.clone(),
                _ => bad.func_types[0].is_vararg = true,
            }
            assert!(check_aarch64_scalar_cell_source(&bad, &c.lir).is_err());
        }
    }
}

#[test]
fn independent_source_observations_reject_valid_semantic_mutations() {
    for width in [4, 8] {
        let c = read_case(width);
        let parameters = c.module.functions[0].blocks[0].params.clone();
        for change in 0..4 {
            let mut bad = c.module.clone();
            match change {
                0 => {
                    let Inst::Store { value, .. } =
                        source_inst(&mut bad, |i| matches!(i, Inst::Store { .. }))
                    else {
                        unreachable!()
                    };
                    *value = parameters[1].0;
                }
                1 => {
                    let Inst::Call { args, .. } =
                        source_inst(&mut bad, |i| matches!(i, Inst::Call { .. }))
                    else {
                        unreachable!()
                    };
                    args[1] = parameters[0].0;
                }
                2 => bad.functions[1].name = "different_callee".into(),
                _ => {
                    let Inst::Return { values } =
                        source_inst(&mut bad, |i| matches!(i, Inst::Return { .. }))
                    else {
                        unreachable!()
                    };
                    values[0] = parameters[0].0;
                }
            }
            assert!(trust_ir_build::validate_module(&bad).is_empty());
            assert!(
                matches!(
                    check_aarch64_scalar_cell_source(&bad, &c.lir),
                    Err(ScalarCellSourceError::LoweringMismatch)
                ),
                "{width}/{change}"
            );
        }
        for change in 0..4 {
            let mut bad = c.lir.clone();
            match change {
                0 => lir_inst(&mut bad, |i| matches!(i, L::Store { .. })).args[0].0 = 1,
                1 => lir_inst(&mut bad, |i| matches!(i, L::Call { .. })).args[1].0 = 0,
                2 => {
                    let L::Call { name, .. } =
                        &mut lir_inst(&mut bad, |i| matches!(i, L::Call { .. })).opcode
                    else {
                        unreachable!()
                    };
                    *name = "different_callee".into();
                }
                _ => lir_inst(&mut bad, |i| matches!(i, L::Return)).args[0].0 = 0,
            }
            assert!(
                matches!(
                    check_aarch64_scalar_cell_source(&c.module, &bad),
                    Err(ScalarCellSourceError::LoweringMismatch)
                ),
                "{width}/{change}"
            );
        }
    }
}

#[test]
fn refuses_malformed_or_out_of_domain_source_before_binding() {
    for width in [4, 8] {
        let c = read_case(width);
        for change in 0..18 {
            let mut bad = c.module.clone();
            match change {
                0 => bad.functions.push(bad.functions[1].clone()),
                1 => bad.functions[1].name = bad.functions[0].name.clone(),
                2 => bad.functions[1].id = bad.functions[0].id,
                3 => bad.functions[1].name.clear(),
                4 => {
                    let block = bad.functions[0].blocks[0].clone();
                    bad.functions[0].blocks.push(block);
                }
                5 => {
                    bad.functions[0].blocks[0].params[1].0 = bad.functions[0].blocks[0].params[0].0
                }
                6 => bad.functions[0].blocks[0].body[0].results.clear(),
                7 => {
                    bad.functions[0].blocks[0].body[0].results[0] =
                        bad.functions[0].blocks[0].params[0].0
                }
                8 => bad.functions[0].blocks[0]
                    .body
                    .retain(|n| !matches!(n.inst, Inst::Store { .. })),
                9 => {
                    let Inst::Load { volatile, .. } =
                        source_inst(&mut bad, |i| matches!(i, Inst::Load { .. }))
                    else {
                        unreachable!()
                    };
                    *volatile = true;
                }
                10 => {
                    let Inst::Store { volatile, .. } =
                        source_inst(&mut bad, |i| matches!(i, Inst::Store { .. }))
                    else {
                        unreachable!()
                    };
                    *volatile = true;
                }
                11 => {
                    let Inst::Alloca { align, .. } =
                        source_inst(&mut bad, |i| matches!(i, Inst::Alloca { .. }))
                    else {
                        unreachable!()
                    };
                    *align = Some(32);
                }
                12 => {
                    let Inst::Load { align, .. } =
                        source_inst(&mut bad, |i| matches!(i, Inst::Load { .. }))
                    else {
                        unreachable!()
                    };
                    *align = Some(0);
                }
                13 => {
                    let node = bad.functions[0].blocks[0].body[0].clone();
                    bad.functions[0].blocks[1].body.push(node);
                }
                14 => {
                    let entry = bad.functions[0].entry;
                    let Inst::Br { target, .. } =
                        source_inst(&mut bad, |i| matches!(i, Inst::Br { .. }))
                    else {
                        unreachable!()
                    };
                    *target = entry;
                }
                15 => bad.target_info.as_mut().unwrap().endianness = Endianness::Big,
                16 => bad.target_info.as_mut().unwrap().pointer_size = 4,
                _ => bad.target_info = None,
            }
            assert!(
                check_aarch64_scalar_cell_source(&bad, &c.lir).is_err(),
                "{width}/{change}"
            );
        }
    }
}

#[test]
fn ordered_calls_have_distinct_opaque_byte_results() {
    for width in [4, 8] {
        let mut c = read_case(width);
        let body = &mut c.module.functions[0].blocks[0].body;
        let call = body
            .iter()
            .find(|n| matches!(n.inst, Inst::Call { .. }))
            .unwrap()
            .clone();
        body.insert(body.len() - 1, call);
        let entry = c.lir.entry_block;
        let body = &mut c.lir.blocks.get_mut(&entry).unwrap().instructions;
        let call = body
            .iter()
            .find(|n| matches!(n.opcode, L::Call { .. }))
            .unwrap()
            .clone();
        body.insert(body.len() - 1, call);
        assert!(trust_ir_build::validate_module(&c.module).is_empty());
        let checked = check_aarch64_scalar_cell_source(&c.module, &c.lir).unwrap();
        assert_eq!(checked.call_count(), 2);
        assert_eq!(
            checked.contract.calls[1].cell_before,
            bytes(width, |b| Byte::Call(0, b))
        );
        assert_eq!(checked.contract.result, bytes(width, |b| Byte::Call(1, b)));
        // Removing the second call changes the public call trace and the
        // opaque result, even with the same cell.
        c.module.functions[0].blocks[0].body.remove(4);
        assert!(matches!(
            check_aarch64_scalar_cell_source(&c.module, &c.lir),
            Err(ScalarCellSourceError::LoweringMismatch)
        ));
    }
}

#[test]
fn literal_bits_and_signed_zero_are_bound_independently() {
    for mut c in captures()
        .into_iter()
        .filter(|c| c.case.starts_with("local_cell") && c.case.ends_with("O0"))
    {
        let Inst::Const { value, .. } =
            source_inst(&mut c.module, |i| matches!(i, Inst::Const { .. }))
        else {
            unreachable!()
        };
        *value = Constant::Float(-0.0);
        assert!(matches!(
            check_aarch64_scalar_cell_source(&c.module, &c.lir),
            Err(ScalarCellSourceError::LoweringMismatch)
        ));
        let L::Fconst { imm, .. } =
            &mut lir_inst(&mut c.lir, |i| matches!(i, L::Fconst { .. })).opcode
        else {
            unreachable!()
        };
        *imm = -0.0;
        let checked = check_aarch64_scalar_cell_source(&c.module, &c.lir).unwrap();
        assert_eq!(
            checked.contract.calls[0].cell_before.last(),
            Some(&Byte::Constant(128))
        );
        for value in [0.0, f64::INFINITY, f64::NAN] {
            let Inst::Const {
                value: constant, ..
            } = source_inst(&mut c.module, |i| matches!(i, Inst::Const { .. }))
            else {
                unreachable!()
            };
            *constant = Constant::Float(value);
            assert!(check_aarch64_scalar_cell_source(&c.module, &c.lir).is_err());
        }
    }
}
