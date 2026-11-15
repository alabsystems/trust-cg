// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use trust_ir::signature_abi::*;
use trust_ir::{
    Block, BlockId, CallingConv, Endianness, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    StructPassingPolicy, TargetInfo, Ty, ValueId,
};

fn extension(triple: &str, ty: &Ty, result: bool) -> AbiExtension {
    let extend = triple.contains("-apple-") || (triple.starts_with("x86_64-") && !result);
    match ty {
        Ty::I8 | Ty::I16 if extend => AbiExtension::Sign,
        Ty::U8 | Ty::U16 if extend => AbiExtension::Zero,
        Ty::Bool if extend || triple.starts_with("x86_64-") => AbiExtension::Zero,
        _ => AbiExtension::None,
    }
}

fn argument(triple: &str, ty: &Ty, place: AbiBindingPlace, result: bool) -> AbiArgument {
    let (class, bytes, bits) = match ty {
        Ty::Bool => (AbiRegisterClass::Integer, 1, 1),
        Ty::I8 | Ty::U8 => (AbiRegisterClass::Integer, 1, 8),
        Ty::I16 | Ty::U16 => (AbiRegisterClass::Integer, 2, 16),
        Ty::I32 | Ty::U32 => (AbiRegisterClass::Integer, 4, 32),
        Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize | Ty::Ptr => (AbiRegisterClass::Integer, 8, 64),
        Ty::F32 => (AbiRegisterClass::Float, 4, 32),
        Ty::F64 => (AbiRegisterClass::Float, 8, 64),
        _ => panic!("not a scalar fixture"),
    };
    AbiArgument {
        size: bytes,
        align: bytes,
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister { class, bytes },
            source_offset: 0,
            source_bytes: bytes,
            value_bits: bits,
            attributes: AbiAttributes {
                extension: extension(triple, ty, result),
                no_undef: true,
                ..AbiAttributes::default()
            },
        }),
        bindings: vec![AbiBinding {
            place,
            source_offset: 0,
            source_bytes: bytes,
            carrier_offset: 0,
            carrier_bytes: bytes,
        }],
    }
}

/// A recorded external prototype and an unrecorded ordinary caller. Actual
/// anonymous operands are separate from the prototype's fixed argument census.
pub fn fixture(
    triple: &str,
    fixed: Vec<Ty>,
    actual: Vec<Ty>,
    result: Option<Ty>,
    variadic: bool,
) -> Module {
    let mut module = Module::new("native_recorded_scalar_c");
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let returns: Vec<Ty> = result.clone().into_iter().collect();
    let abi = SignatureAbi {
        target: AbiTarget {
            triple: triple.into(),
            data_layout: "e-p:64:64-i64:64-n32:64-S128".into(),
            abi: String::new(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "fixture-v1".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "native-scalar-c-fixture".into(),
            revision: "v1".into(),
        },
        convention: "C".into(),
        lowered_convention: CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic,
        fixed_count: fixed.len() as u32,
        arguments: fixed
            .iter()
            .enumerate()
            .map(|(index, ty)| {
                argument(triple, ty, AbiBindingPlace::Parameter(index as u32), false)
            })
            .collect(),
        result: match &result {
            Some(ty) => argument(triple, ty, AbiBindingPlace::Result(0), true),
            None => AbiArgument {
                size: 0,
                align: 1,
                mode: AbiPassMode::Ignore,
                bindings: vec![],
            },
        },
    };
    let declaration = module
        .add_func_type(FuncTy {
            params: fixed,
            returns: returns.clone(),
            is_vararg: variadic,
            abi: Some(abi),
        })
        .unwrap();
    let caller = module
        .add_func_type(FuncTy {
            params: actual.clone(),
            returns: returns.clone(),
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let foreign = Function::new(
        FuncId::new(0),
        "foreign_scalar",
        declaration,
        BlockId::new(0),
    );
    let mut function = Function::new(
        FuncId::new(1),
        "call_foreign_scalar",
        caller,
        BlockId::new(0),
    );
    let mut entry = Block::new(BlockId::new(0));
    entry.params = actual
        .iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(index as u32), ty.clone()))
        .collect();
    let mut call = InstrNode::new(Inst::Call {
        callee: foreign.id,
        args: entry.params.iter().map(|(value, _)| *value).collect(),
    });
    if result.is_some() {
        call.results.push(ValueId::new(actual.len() as u32));
    }
    let returned = call.results.clone();
    entry.body.push(call);
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: returned }));
    function.blocks.push(entry);
    module.functions = vec![foreign, function];
    module
}
