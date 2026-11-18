// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::*;
use trust_ir::{
    Block, BlockId, ClosureLayoutDescriptor, ClosureTy, ClosureTyId, Inst, InstrNode, ValueId,
};

use crate::native_scalar_c_abi::test_fixture as fixture;

fn source() -> Module {
    let mut module = fixture::fixture(
        "aarch64-apple-darwin",
        vec![Ty::U64],
        vec![Ty::U64],
        Some(Ty::U64),
        false,
    );
    let abi = module.func_types[0].abi.as_mut().unwrap();
    abi.convention = "Rust".into();
    abi.lowered_convention = CallingConv::Rust;
    abi.source_abi = "Rust".into();
    abi.can_unwind = false;
    module.functions[0].calling_conv = CallingConv::Rust;
    let mut entry = Block::new(BlockId::new(0));
    entry.params = vec![(ValueId::new(0), Ty::U64)];
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    module.functions[0].blocks.push(entry);
    module
}

fn native() -> NativeAbiContext {
    NativeAbiContext::aarch64("aarch64-apple-darwin".into()).unwrap()
}

#[test]
fn defined_rust_and_indirect_signature_use_the_actual_native_consumer() {
    let mut module = source();
    let signature = module.functions[0].ty;
    let target = module.functions[0].id;
    module.types.push(Ty::Func(signature));
    module.functions[1].blocks[0].body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Func(signature),
            value: trust_ir::Constant::FnDef(target),
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(2),
            sig: signature,
            args: vec![ValueId::new(0)],
            calling_conv: CallingConv::Rust,
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    native().admit_module(&module).unwrap();
    let before = module.clone();
    // Census is an actual consumer of all records, not a metadata mutation.
    native().admit_module(&module).unwrap();
    assert_eq!(before, module);
    if let Inst::CallIndirect { calling_conv, .. } = &mut module.functions[1].blocks[0].body[1].inst
    {
        *calling_conv = CallingConv::C;
    }
    assert!(
        native().admit_module(&module).is_err(),
        "a recorded Rust signature cannot be called as C"
    );
    let x86 = NativeAbiContext::x86_system_v("x86_64-apple-darwin".into()).unwrap();
    assert!(
        x86.admit_module(&module)
            .unwrap_err()
            .to_string()
            .contains("TCG-SOURCE-ABI")
    );
}

#[test]
fn source_extension_binding_and_selected_target_are_checked_even_when_unused() {
    for poison in 0..5 {
        let mut module = source();
        let abi = module.func_types[0].abi.as_mut().unwrap();
        match poison {
            0 => {
                if let AbiPassMode::Direct(lane) = &mut abi.arguments[0].mode {
                    lane.attributes.extension = AbiExtension::Sign;
                }
            }
            1 => abi.target.triple = "aarch64-unknown-linux-gnu".into(),
            2 => abi.arguments[0].bindings[0].carrier_bytes = 4,
            3 => abi.arguments[0].align = 4,
            4 => abi.can_unwind = true,
            _ => unreachable!(),
        }
        assert!(native().admit_module(&module).is_err(), "poison {poison}");
    }
}

#[test]
fn ignored_source_slots_have_no_fabricated_parameter_or_register() {
    let mut module = source();
    let abi = module.func_types[0].abi.as_mut().unwrap();
    let ignored = trust_ir::signature_abi::AbiArgument {
        size: 0,
        align: 64,
        mode: AbiPassMode::Ignore,
        bindings: vec![],
    };
    abi.arguments.insert(0, ignored.clone());
    abi.arguments.push(ignored.clone());
    abi.fixed_count = 3;
    let before = module.clone();
    native().admit_module(&module).unwrap();
    let locations = native()
        .classify_source(
            &module,
            &module.func_types[0].params,
            &module.func_types[0].returns,
        )
        .unwrap();
    assert!(matches!(locations.as_slice(), [ArgLocation::Reg(_)]));
    assert_eq!(
        module, before,
        "source argument census does not rewrite physical parameters"
    );
    assert_eq!(module.func_types[0].params, [Ty::U64]);
    let mut shifted = module.clone();
    shifted.func_types[0].abi.as_mut().unwrap().arguments[1].bindings[0].place =
        AbiBindingPlace::Parameter(1);
    assert!(native().admit_module(&shifted).is_err());
    let mut fabricated = module.clone();
    let active_bindings = fabricated.func_types[0].abi.as_ref().unwrap().arguments[1]
        .bindings
        .clone();
    fabricated.func_types[0].abi.as_mut().unwrap().arguments[0].bindings = active_bindings;
    assert!(native().admit_module(&fabricated).is_err());
    // A genuinely ignored aligned result has no return register either. Its
    // source alignment is retained without inventing storage for the result.
    module.functions.truncate(1);
    module.func_types[0].returns.clear();
    module.func_types[0].abi.as_mut().unwrap().result = ignored;
    module.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return { values: vec![] })];
    native().admit_module(&module).unwrap();
}

fn pair() -> Module {
    let mut module = source();
    let closure = ClosureTyId::new(0);
    module.closure_types.push(ClosureTy {
        func: module.functions[1].ty,
        captures: vec![Ty::U64, Ty::U64],
    });
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure,
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    module.func_types[0].params = vec![Ty::Closure(closure)];
    let abi = module.func_types[0].abi.as_mut().unwrap();
    let mut first = match &abi.arguments[0].mode {
        AbiPassMode::Direct(lane) => lane.clone(),
        _ => unreachable!(),
    };
    first.source_offset = 0;
    let mut second = first.clone();
    second.source_offset = 8;
    abi.arguments[0].size = 16;
    abi.arguments[0].mode = AbiPassMode::Pair(first, second);
    abi.arguments[0].bindings[0].source_bytes = 16;
    abi.arguments[0].bindings[0].carrier_bytes = 16;
    module.functions.truncate(1);
    let entry = &mut module.functions[0].blocks[0];
    entry.params = vec![(ValueId::new(0), Ty::Closure(closure))];
    entry.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: trust_ir::Constant::Int(0),
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    module
}

#[test]
fn pair_transport_uses_observed_word_order_and_native_register_classification() {
    let mut module = pair();
    native().admit_module(&module).unwrap();
    if let AbiPassMode::Pair(_, second) =
        &mut module.func_types[0].abi.as_mut().unwrap().arguments[0].mode
    {
        second.source_offset = 4;
    }
    assert!(native().admit_module(&module).is_err());
    let mut module = pair();
    module.func_types[0].params.extend(vec![Ty::U64; 8]);
    // A source pair that spills is not silently accepted as two independent
    // Rust scalar registers: that transport needs a separate real transform.
    let native = native();
    let signature = &module.func_types[0];
    let locations = native
        .classify_source(&module, &signature.params, &signature.returns)
        .unwrap();
    assert!(matches!(locations[0], ArgLocation::RegPair(..)));
    assert!(
        locations
            .iter()
            .any(|location| matches!(location, ArgLocation::Stack { .. }))
    );
}

fn word_aggregate(array: bool, cast: bool) -> Module {
    let mut module = pair();
    module.closure_types.clear();
    module.closure_layouts.clear();
    // Use the independent ordinary callable row, avoiding a recursive type.
    let pointer = Ty::Func(trust_ir::FuncTyId::new(1));
    let ty = if array {
        let element = trust_ir::TyId::new(module.types.len() as u32);
        module.types.push(pointer);
        Ty::Array(element, 2)
    } else {
        let id = trust_ir::StructId::new(0);
        module.structs.push(trust_ir::StructDef {
            id,
            name: "TwoCallbacks".into(),
            fields: (0..2)
                .map(|index| trust_ir::FieldDef {
                    name: format!("callback{index}"),
                    ty: pointer.clone(),
                    offset: Some(index * 8),
                })
                .collect(),
            size: Some(16),
            align: Some(8),
            repr: trust_ir::StructRepr::C,
            origin: None,
        });
        Ty::Struct(id)
    };
    module.func_types[0].params = vec![ty.clone()];
    module.func_types[0].returns = vec![ty.clone()];
    let abi = module.func_types[0].abi.as_mut().unwrap();
    if cast {
        abi.arguments[0].mode = AbiPassMode::Cast {
            pad_i32: false,
            prefix: vec![],
            rest_offset: None,
            rest: trust_ir::signature_abi::AbiUniform {
                unit: trust_ir::signature_abi::AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 8,
                },
                total: 16,
                consecutive: false,
            },
            attributes: trust_ir::signature_abi::AbiAttributes::default(),
        };
    }
    abi.result = abi.arguments[0].clone();
    abi.result.bindings[0].place = AbiBindingPlace::Result(0);
    module.functions[0].blocks[0].params = vec![(ValueId::new(0), ty)];
    module.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    })];
    module
}

fn lower_words(module: &Module) -> Vec<(crate::Function, crate::ProofContext)> {
    let policy =
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit);
    let admitted = crate::admit_module(module, &policy, &[]).unwrap();
    crate::translate_admitted_module_for_native_scalar_c_abi(
        &admitted,
        crate::GuardCarrierArch::AArch64,
        crate::ObjectAccessModel::macho_dyld(),
        crate::ObjectSymbolPolicy::default(),
        &native(),
    )
    .unwrap()
    .0
}

#[test]
fn exact_pointer_aggregate_pair_and_cast_use_real_native_argument_and_return_carriers() {
    for array in [false, true] {
        for cast in [false, true] {
            let module = word_aggregate(array, cast);
            let before = module.clone();
            native().admit_module(&module).unwrap();
            let signature = &module.func_types[0];
            assert!(matches!(
                native()
                    .classify_source(&module, &signature.params, &signature.returns)
                    .unwrap()
                    .as_slice(),
                [ArgLocation::RegPair(..)]
            ));
            assert!(matches!(
                source_result_locations(&module, &signature.returns)
                    .unwrap()
                    .as_slice(),
                [ArgLocation::RegPair(..)]
            ));
            let recorded = lower_words(&module);
            let mut canonical = module.clone();
            canonical.func_types[0].abi = None;
            let canonical = lower_words(&canonical);
            assert_eq!(
                recorded[0].0.blocks.values().next().unwrap().instructions,
                canonical[0].0.blocks.values().next().unwrap().instructions,
                "recorded native placement uses the actual aggregate emitter without changing payload semantics"
            );
            assert_eq!(module, before);
        }
    }
}

#[test]
fn aggregate_transport_checks_recursive_leaf_frame_and_exact_integer_cast_geometry() {
    for poison in 0..7 {
        let mut module = word_aggregate(false, true);
        match poison {
            0 => module.structs[0].fields[1].ty = Ty::FnItem(module.functions[0].id),
            1 => module.structs[0].fields[1].offset = Some(4),
            2 => module.structs[0].size = Some(24),
            3 => module.structs[0].fields[0].ty = Ty::Func(trust_ir::FuncTyId::new(999)),
            4..=6 => {
                let AbiPassMode::Cast {
                    rest, attributes, ..
                } = &mut module.func_types[0].abi.as_mut().unwrap().arguments[0].mode
                else {
                    unreachable!()
                };
                match poison {
                    4 => rest.total = 8,
                    5 => rest.unit.bytes = 4,
                    6 => attributes.extension = AbiExtension::Zero,
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
        assert!(native().admit_module(&module).is_err(), "poison {poison}");
    }
    let mut spilled = word_aggregate(false, true);
    let mut word = source().func_types[0].abi.as_ref().unwrap().arguments[0].clone();
    let signature = &mut spilled.func_types[0];
    let aggregate = signature.params[0].clone();
    signature.params = vec![Ty::U64; 7];
    signature.params.push(aggregate);
    let abi = signature.abi.as_mut().unwrap();
    let mut aggregate = abi.arguments.remove(0);
    aggregate.bindings[0].place = AbiBindingPlace::Parameter(7);
    for index in 0..7 {
        word.bindings[0].place = AbiBindingPlace::Parameter(index);
        abi.arguments.push(word.clone());
    }
    abi.arguments.push(aggregate);
    abi.fixed_count = 8;
    spilled.functions[0].blocks[0].params = spilled.func_types[0]
        .params
        .iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(index as u32), ty.clone()))
        .collect();
    spilled.functions[0].blocks[0].body = vec![InstrNode::new(Inst::Return {
        values: vec![ValueId::new(7)],
    })];
    assert!(
        native().admit_module(&spilled).is_err(),
        "native whole-value stack placement cannot borrow the register-only equivalence"
    );
}

#[test]
fn full_width_integer_scalar_records_use_the_native_pair_argument_and_result_path() {
    for ty in [Ty::I128, Ty::U128] {
        let mut module = source();
        module.functions.truncate(1);
        module.func_types[0].params = vec![ty.clone()];
        module.func_types[0].returns = vec![ty.clone()];
        let abi = module.func_types[0].abi.as_mut().unwrap();
        let argument = &mut abi.arguments[0];
        argument.size = 16;
        argument.align = 16;
        argument.bindings[0].source_bytes = 16;
        argument.bindings[0].carrier_bytes = 16;
        let AbiPassMode::Direct(lane) = &mut argument.mode else {
            unreachable!()
        };
        lane.register.bytes = 16;
        lane.source_bytes = 16;
        lane.value_bits = 128;
        abi.result = argument.clone();
        abi.result.bindings[0].place = AbiBindingPlace::Result(0);
        module.functions[0].blocks[0].params[0].1 = ty;
        native().admit_module(&module).unwrap();
        let signature = &module.func_types[0];
        assert!(matches!(
            native()
                .classify_source(&module, &signature.params, &signature.returns)
                .unwrap()
                .as_slice(),
            [ArgLocation::RegPair(..)]
        ));
        assert!(matches!(
            source_result_locations(&module, &signature.returns)
                .unwrap()
                .as_slice(),
            [ArgLocation::RegPair(..)]
        ));
        let actual = lower_words(&module);
        let mut canonical = module.clone();
        canonical.func_types[0].abi = None;
        let canonical = lower_words(&canonical);
        assert_eq!(
            actual[0].0.blocks.values().next().unwrap().instructions,
            canonical[0].0.blocks.values().next().unwrap().instructions
        );
        let mut bad_alignment = module.clone();
        bad_alignment.func_types[0].abi.as_mut().unwrap().arguments[0].align = 8;
        assert!(native().admit_module(&bad_alignment).is_err());
        let AbiPassMode::Direct(lane) =
            &mut module.func_types[0].abi.as_mut().unwrap().arguments[0].mode
        else {
            unreachable!()
        };
        lane.value_bits = 64;
        assert!(native().admit_module(&module).is_err());
    }
}

fn scalar_environment(captures: Vec<Ty>) -> Module {
    let mut module = pair();
    let mut offsets = Vec::new();
    let mut size: u64 = 0;
    let mut alignment: u64 = 1;
    let mut lanes = Vec::new();
    for ty in &captures {
        let machine = source_scalar_type(ty).unwrap();
        let width = u64::from(machine.bytes());
        alignment = alignment.max(width);
        size = size.div_ceil(width) * width;
        offsets.push(size);
        lanes.push(trust_ir::signature_abi::AbiScalar {
            register: trust_ir::signature_abi::AbiRegister {
                class: if matches!(ty, Ty::F32 | Ty::F64) {
                    AbiRegisterClass::Float
                } else {
                    AbiRegisterClass::Integer
                },
                bytes: width,
            },
            source_offset: size,
            source_bytes: width,
            value_bits: (width * 8) as u16,
            attributes: trust_ir::signature_abi::AbiAttributes {
                no_undef: true,
                ..Default::default()
            },
        });
        size += width;
    }
    size = size.div_ceil(alignment) * alignment;
    module.closure_types[0].captures = captures;
    module.closure_layouts[0].size = size;
    module.closure_layouts[0].align = alignment;
    module.closure_layouts[0].capture_offsets = offsets;
    let argument = &mut module.func_types[0].abi.as_mut().unwrap().arguments[0];
    argument.size = size;
    argument.align = alignment;
    argument.bindings[0].source_bytes = size;
    argument.bindings[0].carrier_bytes = size;
    argument.mode = match lanes.as_slice() {
        [one] => AbiPassMode::Direct(one.clone()),
        [first, second] => AbiPassMode::Pair(first.clone(), second.clone()),
        _ => unreachable!(),
    };
    module
}

#[test]
fn scalar_closure_arguments_follow_actual_float_sequences_and_wide_integer_pairs() {
    for captures in [
        vec![Ty::F32],
        vec![Ty::F64],
        vec![Ty::F32, Ty::F32],
        vec![Ty::F64, Ty::F64],
        vec![Ty::U128],
    ] {
        let module = scalar_environment(captures.clone());
        native().admit_module(&module).unwrap();
        let signature = &module.func_types[0];
        let locations = native()
            .classify_source(&module, &signature.params, &signature.returns)
            .unwrap();
        if captures == [Ty::U128] {
            assert!(matches!(locations.as_slice(), [ArgLocation::RegPair(..)]));
        } else {
            assert!(
                matches!(locations.as_slice(), [ArgLocation::RegSequence(registers)] if registers.len() == captures.len())
            );
        }
        let before = module.clone();
        let actual = lower_words(&module);
        let mut canonical = module.clone();
        canonical.func_types[0].abi = None;
        let canonical = lower_words(&canonical);
        assert_eq!(
            actual[0].0.blocks.values().next().unwrap().instructions,
            canonical[0].0.blocks.values().next().unwrap().instructions
        );
        assert_eq!(module, before);
    }
}

#[test]
fn rust_scalar_pair_banks_must_not_borrow_native_aggregate_integer_registers() {
    for captures in [
        vec![Ty::F64, Ty::U64],
        vec![Ty::U64, Ty::F64],
        vec![Ty::F64, Ty::F32],
    ] {
        let module = scalar_environment(captures);
        let signature = &module.func_types[0];
        assert!(matches!(
            native()
                .classify_source(&module, &signature.params, &signature.returns)
                .unwrap()
                .as_slice(),
            [ArgLocation::RegPair(..)]
        ));
        assert!(
            native().admit_module(&module).is_err(),
            "one or both real Rust scalar lanes use FP registers; the native aggregate would use GPRs"
        );
    }
    let mut spilled = scalar_environment(vec![Ty::F64, Ty::F64]);
    let scalar = scalar_environment(vec![Ty::F64]).func_types[0]
        .abi
        .as_ref()
        .unwrap()
        .arguments[0]
        .clone();
    let signature = &mut spilled.func_types[0];
    let closure = signature.params[0].clone();
    signature.params = vec![Ty::F64; 7];
    signature.params.push(closure);
    let abi = signature.abi.as_mut().unwrap();
    let mut environment = abi.arguments.remove(0);
    environment.bindings[0].place = AbiBindingPlace::Parameter(7);
    for index in 0..7 {
        let mut scalar = scalar.clone();
        scalar.bindings[0].place = AbiBindingPlace::Parameter(index);
        abi.arguments.push(scalar);
    }
    abi.arguments.push(environment);
    abi.fixed_count = 8;
    spilled.functions[0].blocks[0].params = spilled.func_types[0]
        .params
        .iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(index as u32), ty.clone()))
        .collect();
    spilled.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: trust_ir::Constant::Int(0),
        })
        .with_result(ValueId::new(8)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(8)],
        }),
    ];
    assert!(matches!(
        native()
            .classify_source(
                &spilled,
                &spilled.func_types[0].params,
                &spilled.func_types[0].returns,
            )
            .unwrap()
            .last(),
        Some(ArgLocation::Stack { .. })
    ));
    assert!(
        native().admit_module(&spilled).is_err(),
        "a grouped native HFA spill cannot stand in for Rust scalar-lane placement"
    );
}
