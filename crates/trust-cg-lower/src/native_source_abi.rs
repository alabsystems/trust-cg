// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! A native consumer of recorded Rust scalar and observed closure carriers.
//! The driver's selected target, actual native type translation and classifier
//! decide transport. Descriptor identity is untrusted and earns no proof credit.

use crate::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation};
use crate::adapter::{AdapterError, translate_type_in_module};
use crate::native_scalar_c_abi::{
    NativeAbi, NativeAbiContext, classify_attributes, same_scalar_target, scalar_type,
};
use crate::types::Type;
use trust_ir::signature_abi::{
    AbiArgument, AbiBindingPlace, AbiExtension, AbiPassMode, AbiRegisterClass, AbiScalar,
};
use trust_ir::{CallingConv, FuncTy, Module, StructPassingPolicy, Ty};

impl NativeAbiContext {
    pub(super) fn source_prototype(
        &self,
        module: &Module,
        signature: &FuncTy,
        convention: CallingConv,
    ) -> Result<(), AdapterError> {
        let abi = signature
            .abi
            .as_ref()
            .ok_or_else(|| refusal("missing source ABI"))?;
        abi.validate(signature).map_err(refusal)?;
        abi.validate_target(module.target_info.as_ref())
            .map_err(refusal)?;
        // The current Rust profile is the actual Darwin AArch64 transport;
        // other targets keep their own foreign-scalar consumer and refuse here.
        if !matches!(self.abi, NativeAbi::Aarch64(AArch64AbiVariant::Darwin))
            || !matches!(convention, CallingConv::Rust | CallingConv::C)
            || abi.lowered_convention != convention
            || abi.convention
                != if convention == CallingConv::Rust {
                    "Rust"
                } else {
                    "C"
                }
            || abi.variadic
            || abi.can_unwind
            || abi.fixed_count as usize > abi.arguments.len()
            || !same_scalar_target(&abi.target.triple, &self.triple)
            || !abi.target.abi.is_empty()
            || abi.target.pointer_bytes != 8
            || !abi.target.little_endian
            || module
                .target_info
                .as_ref()
                .is_none_or(|target| target.struct_passing != StructPassingPolicy::NativeC)
        {
            return Err(refusal(
                "recorded source signature is outside the selected Darwin Rust profile",
            ));
        }
        let locations = self.classify_source(module, &signature.params, &signature.returns)?;
        let result_locations = source_result_locations(module, &signature.returns)?;
        let mut covered = vec![false; signature.params.len()];
        for argument in &abi.arguments {
            if matches!(argument.mode, AbiPassMode::Ignore) {
                // Ignore is a complete source argument without any lowered
                // parameter. The source-owned projection separately validates
                // its real singleton and every entry/call/result replacement.
                if argument.size != 0 || !argument.bindings.is_empty() {
                    return Err(refusal(
                        "ignored source argument has storage or a fabricated carrier",
                    ));
                }
                continue;
            }
            let [binding] = argument.bindings.as_slice() else {
                return Err(refusal(
                    "source argument needs one complete lowered parameter",
                ));
            };
            let AbiBindingPlace::Parameter(parameter) = binding.place else {
                return Err(refusal(
                    "source argument does not bind an ordinary parameter",
                ));
            };
            let index = parameter as usize;
            let Some(slot) = covered.get_mut(index) else {
                return Err(refusal(
                    "source argument binding exceeds the actual lowered signature",
                ));
            };
            if std::mem::replace(slot, true) {
                return Err(refusal("native source profile repeats a lowered parameter"));
            }
            self.source_argument(
                module,
                argument,
                &signature.params[index],
                binding.place,
                Some(&locations[index]),
                convention,
            )?;
        }
        if covered.iter().any(|covered| !covered) {
            return Err(refusal("native source profile omits a lowered parameter"));
        }
        match signature.returns.as_slice() {
            [] if abi.result.size == 0
                && matches!(abi.result.mode, AbiPassMode::Ignore)
                && abi.result.bindings.is_empty() => {}
            [ty] => self.source_argument(
                module,
                &abi.result,
                ty,
                AbiBindingPlace::Result(0),
                result_locations.first(),
                convention,
            )?,
            _ => {
                return Err(refusal(
                    "source result must be one direct scalar or ignored unit",
                ));
            }
        }
        // The actual source path is non-unwinding. This profile cannot grant
        // an unwinding function contract from placement equivalence alone.
        // Existing body/Invoke/runtime/output gates remain independent.
        Ok(())
    }

    pub(super) fn classify_source(
        &self,
        module: &Module,
        params: &[Ty],
        returns: &[Ty],
    ) -> Result<Vec<ArgLocation>, AdapterError> {
        let NativeAbi::Aarch64(variant @ AArch64AbiVariant::Darwin) = self.abi else {
            return Err(refusal(
                "source carriers require the selected Darwin AArch64 classifier",
            ));
        };
        let params = params
            .iter()
            .map(|ty| source_type(module, ty))
            .collect::<Result<Vec<_>, _>>()?;
        source_result_locations(module, returns)?;
        let locations = AppleAArch64ABI::classify_params_with(variant, &params);
        if locations.len() != params.len()
            || locations.iter().any(|location| {
                !matches!(
                    location,
                    ArgLocation::Reg(_)
                        | ArgLocation::RegPair(..)
                        | ArgLocation::RegSequence(_)
                        | ArgLocation::Stack { .. }
                )
            })
        {
            return Err(refusal(
                "native classifier selected an unimplemented source carrier",
            ));
        }
        Ok(locations)
    }

    fn source_argument(
        &self,
        module: &Module,
        argument: &AbiArgument,
        ty: &Ty,
        place: AbiBindingPlace,
        location: Option<&ArgLocation>,
        convention: CallingConv,
    ) -> Result<(), AdapterError> {
        let machine = source_type(module, ty)?;
        let [binding] = argument.bindings.as_slice() else {
            return Err(refusal(
                "source argument needs one complete logical carrier binding",
            ));
        };
        if machine.checked_bytes() != Some(argument.size)
            || argument.align != u64::from(machine.align())
            || binding.place != place
            || binding.source_offset != 0
            || binding.source_bytes != argument.size
            || binding.carrier_offset != 0
            || binding.carrier_bytes != argument.size
        {
            return Err(refusal(
                "source storage/binding disagrees with the emitted native value",
            ));
        }
        match (&argument.mode, ty) {
            (_, Ty::Struct(_) | Ty::Array(_, _)) => {
                check_integer_aggregate(module, argument, ty, location)?;
            }
            (AbiPassMode::Direct(lane), Ty::Closure(id)) => {
                let layout = module
                    .closure_layout_descriptor(*id)
                    .map_err(refusal)?
                    .ok_or_else(|| refusal("closure carrier lacks observed layout"))?;
                let closure = module
                    .closure_type(*id)
                    .ok_or_else(|| refusal("missing closure"))?;
                if closure.captures.len() != 1
                    || layout.capture_offsets != [0]
                    || place == AbiBindingPlace::Result(0)
                    || convention != CallingConv::Rust
                {
                    return Err(refusal(
                        "closure Direct lacks its exact observed scalar argument",
                    ));
                }
                check_scalar(lane, &closure.captures[0], 0, AbiExtension::None)?;
                let placed = match (&lane.register.class, lane.register.bytes, location) {
                    (AbiRegisterClass::Integer, 1 | 2 | 4 | 8, Some(ArgLocation::Reg(_))) => true,
                    (AbiRegisterClass::Integer, 16, Some(ArgLocation::RegPair(..))) => true,
                    (AbiRegisterClass::Float, 4 | 8, Some(ArgLocation::RegSequence(registers))) => {
                        registers.len() == 1
                    }
                    _ => false,
                };
                if !placed {
                    return Err(refusal(
                        "closure Direct scalar and actual native register bank/width disagree",
                    ));
                }
            }
            (AbiPassMode::Pair(first, second), Ty::Closure(id)) => {
                let layout = module
                    .closure_layout_descriptor(*id)
                    .map_err(refusal)?
                    .ok_or_else(|| refusal("closure pair lacks observed layout"))?;
                let closure = module
                    .closure_type(*id)
                    .ok_or_else(|| refusal("missing closure"))?;
                if closure.captures.len() != 2
                    || argument.size > 16
                    || place == AbiBindingPlace::Result(0)
                    || convention != CallingConv::Rust
                {
                    return Err(refusal(
                        "closure Pair lacks its exact observed two-scalar argument",
                    ));
                }
                let mut fields = [0, 1];
                fields.sort_by_key(|&index| layout.capture_offsets[index]);
                let offset = layout.capture_offsets[fields[1]];
                if layout.capture_offsets[fields[0]] != 0 {
                    return Err(refusal(
                        "closure pair does not start at its actual first scalar",
                    ));
                }
                check_scalar(first, &closure.captures[fields[0]], 0, AbiExtension::None)?;
                check_scalar(
                    second,
                    &closure.captures[fields[1]],
                    offset,
                    AbiExtension::None,
                )?;
                let placed = match (&first.register.class, &second.register.class, location) {
                    (
                        AbiRegisterClass::Integer,
                        AbiRegisterClass::Integer,
                        Some(ArgLocation::RegPair(..)),
                    ) => argument.size > 8 && offset == 8,
                    (
                        AbiRegisterClass::Float,
                        AbiRegisterClass::Float,
                        Some(ArgLocation::RegSequence(registers)),
                    ) => {
                        registers.len() == 2
                            && first.register.bytes == second.register.bytes
                            && offset == first.register.bytes
                            && argument.size == first.register.bytes * 2
                    }
                    _ => false,
                };
                if !placed {
                    return Err(refusal(
                        "closure Pair scalar banks/offsets disagree with actual native aggregate placement; a real scalar carrier transform is required",
                    ));
                }
            }
            (AbiPassMode::Direct(lane), _) => check_scalar(
                lane,
                ty,
                0,
                if convention == CallingConv::Rust {
                    AbiExtension::None
                } else {
                    self.extension(ty, place == AbiBindingPlace::Result(0))
                },
            )?,
            _ => {
                return Err(refusal(
                    "source Pair/Cast/Indirect/Ignore requires an implemented native value transform",
                ));
            }
        }
        Ok(())
    }
}

fn source_type(module: &Module, ty: &Ty) -> Result<Type, AdapterError> {
    if let Ty::Closure(id) = ty {
        let closure = module
            .closure_type(*id)
            .ok_or_else(|| refusal("missing closure type"))?;
        if !matches!(closure.captures.len(), 1 | 2) {
            return Err(refusal(
                "closure carrier needs one or two actual scalar captures",
            ));
        }
        for capture in &closure.captures {
            source_scalar_in_module(module, capture)?;
        }
        module.validate_closure_layouts().map_err(refusal)?;
        translate_type_in_module(module, ty)
    } else if matches!(ty, Ty::Struct(_) | Ty::Array(_, _)) {
        integer_words(module, ty)?;
        translate_type_in_module(module, ty)
    } else {
        source_scalar_in_module(module, ty)
    }
}

fn source_result_locations(
    module: &Module,
    returns: &[Ty],
) -> Result<Vec<ArgLocation>, AdapterError> {
    let types = returns
        .iter()
        .map(|ty| source_type(module, ty))
        .collect::<Result<Vec<_>, _>>()?;
    let locations = AppleAArch64ABI::classify_returns(&types);
    if returns.len() > 1
        || locations.len() != returns.len()
        || locations
            .iter()
            .any(|location| !matches!(location, ArgLocation::Reg(_) | ArgLocation::RegPair(..)))
    {
        return Err(refusal(
            "native source result requires an implemented direct register carrier",
        ));
    }
    Ok(locations)
}

/// Exact whole integer words have no padding to initialize or discard. Keep
/// table-indexed type custody all the way to every live leaf; an aggregate
/// shell alone cannot establish the absence of nominal/proof-only data.
fn integer_words(module: &Module, ty: &Ty) -> Result<Vec<Ty>, AdapterError> {
    fn visit(
        module: &Module,
        ty: &Ty,
        words: &mut Vec<Ty>,
        depth: usize,
    ) -> Result<(), AdapterError> {
        if depth >= 32 {
            return Err(refusal(
                "integer aggregate type nesting exceeds the checked carrier bound",
            ));
        }
        match ty {
            Ty::Struct(id) => {
                let mut definitions = module.structs.iter().filter(|row| row.id == *id);
                let definition = definitions
                    .next()
                    .ok_or_else(|| refusal("integer aggregate has no actual struct definition"))?;
                if definitions.next().is_some()
                    || definition.fields.is_empty()
                    || definition.fields.len() > 2
                {
                    return Err(refusal(
                        "integer aggregate struct has ambiguous or unsupported fields",
                    ));
                }
                let first = words.len();
                for field in &definition.fields {
                    if field.offset != Some((words.len() - first) as u64 * 8) {
                        return Err(refusal(
                            "integer aggregate field offset is not the actual whole-word offset",
                        ));
                    }
                    visit(module, &field.ty, words, depth + 1)?;
                }
                if definition.size != Some((words.len() - first) as u64 * 8)
                    || definition.align != Some(8)
                {
                    return Err(refusal(
                        "integer aggregate lacks the exact observed whole-word frame",
                    ));
                }
            }
            Ty::Array(id, count) => {
                if !matches!(*count, 1 | 2) {
                    return Err(refusal(
                        "integer aggregate array needs one or two complete words",
                    ));
                }
                let element = module
                    .types
                    .get(id.as_usize())
                    .ok_or_else(|| refusal("integer aggregate array has no actual element type"))?;
                for _ in 0..*count {
                    visit(module, element, words, depth + 1)?;
                }
            }
            _ => {
                if source_scalar_in_module(module, ty)? != Type::I64 || words.len() >= 2 {
                    return Err(refusal(
                        "integer aggregate requires at most two exact integer or pointer words",
                    ));
                }
                words.push(ty.clone());
            }
        }
        Ok(())
    }
    let mut words = Vec::new();
    visit(module, ty, &mut words, 0)?;
    let machine = translate_type_in_module(module, ty)?;
    if words.is_empty()
        || machine.checked_bytes() != Some(words.len() as u64 * 8)
        || machine.align() != 8
    {
        return Err(refusal(
            "integer aggregate has padding or a different native layout",
        ));
    }
    Ok(words)
}

fn check_integer_aggregate(
    module: &Module,
    argument: &AbiArgument,
    ty: &Ty,
    location: Option<&ArgLocation>,
) -> Result<(), AdapterError> {
    let words = integer_words(module, ty)?;
    let placed = match words.len() {
        1 => matches!(location, Some(ArgLocation::Reg(_))),
        2 => matches!(location, Some(ArgLocation::RegPair(..))),
        _ => false,
    };
    if !placed {
        return Err(refusal(
            "integer aggregate ABI needs exact native register transport; spill/indirect geometry is not implemented",
        ));
    }
    match &argument.mode {
        AbiPassMode::Direct(lane) if words.len() == 1 => {
            check_scalar(lane, &words[0], 0, AbiExtension::None)?
        }
        AbiPassMode::Pair(first, second) if words.len() == 2 => {
            check_scalar(first, &words[0], 0, AbiExtension::None)?;
            check_scalar(second, &words[1], 8, AbiExtension::None)?;
        }
        AbiPassMode::Cast {
            pad_i32,
            prefix,
            rest_offset,
            rest,
            attributes,
        } => {
            let word = |register: &trust_ir::signature_abi::AbiRegister| {
                register.class == AbiRegisterClass::Integer && register.bytes == 8
            };
            let prefix_bytes = prefix.len() as u64 * 8;
            if *pad_i32
                || prefix.len() > words.len()
                || !prefix.iter().all(word)
                || rest_offset.is_some_and(|offset| offset != prefix_bytes)
                || !word(&rest.unit)
                || prefix_bytes.checked_add(rest.total) != Some(argument.size)
                || attributes.extension != AbiExtension::None
                || attributes.in_reg
            {
                return Err(refusal(
                    "integer Cast disagrees with the complete native word carriers",
                ));
            }
            // Both allocation-group forms have the same physical placement
            // here: the complete value actually fits in native registers.
            // A spill never borrows this equivalence.
            classify_attributes(attributes);
        }
        _ => {
            return Err(refusal(
                "integer aggregate needs actual Direct, Pair or exact integer Cast transport",
            ));
        }
    }
    Ok(())
}

fn source_scalar_in_module(module: &Module, ty: &Ty) -> Result<Type, AdapterError> {
    if let Ty::Func(id) = ty
        && module.func_type(*id).is_none()
    {
        return Err(refusal(
            "source function-pointer carrier names a missing signature",
        ));
    }
    source_scalar_type(ty)
}

fn source_scalar_type(ty: &Ty) -> Result<Type, AdapterError> {
    match ty {
        Ty::Func(_) => Ok(Type::I64),
        Ty::Char => Ok(Type::I32),
        Ty::I128 | Ty::U128 => Ok(Type::I128),
        _ => scalar_type(ty).map(|row| row.0),
    }
}

fn check_scalar(
    lane: &AbiScalar,
    ty: &Ty,
    offset: u64,
    extension: AbiExtension,
) -> Result<(), AdapterError> {
    let machine = source_scalar_type(ty)?;
    let bytes = u64::from(machine.bytes());
    let bits = if matches!(ty, Ty::Bool) {
        1
    } else {
        (bytes * 8) as u16
    };
    let class = if matches!(ty, Ty::F32 | Ty::F64) {
        AbiRegisterClass::Float
    } else {
        AbiRegisterClass::Integer
    };
    if lane.register.class != class
        || lane.register.bytes != bytes
        || lane.source_offset != offset
        || lane.source_bytes != bytes
        || lane.value_bits != bits
        || lane.attributes.extension != extension
        || lane.attributes.in_reg
    {
        return Err(refusal(
            "source lane/class/extension disagrees with native Rust marshalling",
        ));
    }
    classify_attributes(&lane.attributes);
    Ok(())
}

fn refusal(reason: impl std::fmt::Display) -> AdapterError {
    AdapterError::UnsupportedInstruction(format!("[TCG-SOURCE-ABI] {reason}"))
}

#[cfg(test)]
#[path = "native_source_abi_tests.rs"]
mod tests;
