// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Checked use of recorded scalar C prototypes by the native byte path.
//! This is a finite ABI consumer, not proof authority or a general FnAbi.

use crate::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation};
use crate::adapter::{AdapterError, GuardCarrierArch, ObjectAccessModel};
use crate::types::Type;
use crate::x86_64_isel::{self, X86CallAbi};
use trust_ir::signature_abi::{
    AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiExtension, AbiFrontend,
    AbiPassMode, AbiRegister, AbiRegisterClass, AbiScalar, AbiTarget, SignatureAbi,
};
use trust_ir::{CallingConv, Constant, FuncTy, Function, Inst, Module, Ty};

#[derive(Clone, Copy, Debug)]
enum NativeAbi {
    Aarch64(AArch64AbiVariant),
    X86SystemV,
}

/// The native caller's selected target, supplied by the compile driver.
/// Module metadata cannot construct an implicit native context. Existing
/// contextless, wasm and template entries keep refusing recorded signatures.
#[derive(Clone, Debug)]
pub struct NativeScalarCAbi {
    triple: String,
    abi: NativeAbi,
}

impl NativeScalarCAbi {
    pub fn aarch64(triple: String) -> Result<Self, AdapterError> {
        let variant = AArch64AbiVariant::from_target_triple(&triple)
            .map_err(|error| refusal(error.to_string()))?;
        if !triple.starts_with("aarch64-") {
            return Err(refusal(
                "native scalar C context requires an aarch64 target",
            ));
        }
        Ok(Self {
            triple,
            abi: NativeAbi::Aarch64(variant),
        })
    }

    /// The compiler calls this only after selecting its System V pipeline.
    /// Restrict the public constructor to modeled Unix target families too.
    pub fn x86_system_v(triple: String) -> Result<Self, AdapterError> {
        if !triple.starts_with("x86_64-")
            || !(triple.contains("-apple-")
                || triple.contains("-linux-")
                || triple.contains("-freebsd")
                || triple.contains("-netbsd")
                || triple.contains("-openbsd")
                || triple.contains("-dragonfly"))
            || triple.contains("windows")
        {
            return Err(refusal(
                "native scalar C context requires a modeled x86-64 System V target",
            ));
        }
        Ok(Self {
            triple,
            abi: NativeAbi::X86SystemV,
        })
    }

    /// Diagnostic census under this same explicit native target. Like the
    /// compiler's preflight it emits no object or evidence and admits nothing.
    pub fn census_module_translation(
        &self,
        module: &Module,
        arch: GuardCarrierArch,
        access: ObjectAccessModel,
        license: &crate::CodegenLicensePolicy,
        policy: crate::ObjectSymbolPolicy,
    ) -> Result<Vec<(trust_ir::FuncId, AdapterError)>, AdapterError> {
        crate::adapter::census_module_translation_with_native_context(
            module,
            arch,
            access,
            license,
            policy,
            Some(self),
        )
    }

    pub(crate) fn reconcile_driver(
        &self,
        arch: GuardCarrierArch,
        access: ObjectAccessModel,
    ) -> Result<(), AdapterError> {
        let matches = match (&self.abi, arch) {
            (NativeAbi::Aarch64(variant), GuardCarrierArch::AArch64) => {
                let selected = match access.tls_dialect() {
                    crate::TlsDialect::MachOTlv => Some(AArch64AbiVariant::Darwin),
                    crate::TlsDialect::ElfLocalExec
                    | crate::TlsDialect::ElfInitialExec
                    | crate::TlsDialect::ElfExecutable
                    | crate::TlsDialect::ElfSharedObject => Some(AArch64AbiVariant::Aapcs64),
                    crate::TlsDialect::RejectThreadLocals => None,
                };
                selected == Some(*variant)
            }
            (NativeAbi::X86SystemV, GuardCarrierArch::X86_64) => true,
            _ => false,
        };
        if matches {
            Ok(())
        } else {
            Err(refusal(
                "native scalar C context disagrees with the lowering target",
            ))
        }
    }

    pub(crate) fn admit_module(&self, module: &Module) -> Result<(), AdapterError> {
        for (index, signature) in module.func_types.iter().enumerate() {
            if signature.abi.is_none() {
                continue;
            }
            let owners = module
                .functions
                .iter()
                .filter(|function| function.ty.as_usize() == index);
            let mut found = false;
            for function in owners {
                self.prototype(module, function, signature)?;
                found = true;
            }
            if !found {
                return Err(refusal("recorded signature has no foreign declaration"));
            }
        }
        let mut pointer_signature = false;
        module.visit_types(|ty| {
            if let Ty::Func(id) = ty {
                pointer_signature |= module
                    .func_type(*id)
                    .is_some_and(|signature| signature.abi.is_some());
            }
        });
        if pointer_signature
            || module.closure_types.iter().any(|closure| {
                module
                    .func_type(closure.func)
                    .is_some_and(|signature| signature.abi.is_some())
            })
        {
            return Err(refusal(
                "recorded function-pointer or closure ABI is outside the scalar direct-call profile",
            ));
        }
        let recorded = |function: &Function| {
            module
                .func_type(function.ty)
                .is_some_and(|sig| sig.abi.is_some())
        };
        let escaped = |constant: &Constant| {
            constant
                .try_visit_constants(|nested| {
                    let escaped = match nested {
                        Constant::FnDef(id) | Constant::Closure { func: id, .. } => {
                            module.functions.iter().any(|f| f.id == *id && recorded(f))
                        }
                        Constant::SymbolAddr { symbol, .. } => module
                            .functions
                            .iter()
                            .any(|f| f.name == *symbol && recorded(f)),
                        _ => false,
                    };
                    if escaped {
                        std::ops::ControlFlow::Break(())
                    } else {
                        std::ops::ControlFlow::Continue(())
                    }
                })
                .is_break()
        };
        for global in &module.globals {
            if global.initializer.as_ref().is_some_and(escaped) {
                return Err(refusal(
                    "recorded foreign function address escapes into a global",
                ));
            }
        }
        for node in module.instructions() {
            match &node.inst {
                Inst::MakeClosure { func, .. }
                    if module
                        .functions
                        .iter()
                        .any(|function| function.id == *func && recorded(function)) =>
                {
                    return Err(refusal("recorded foreign function escapes as closure code"));
                }
                Inst::Const { value, .. } if escaped(value) => {
                    return Err(refusal(
                        "recorded foreign function address escapes into a value",
                    ));
                }
                Inst::Invoke { callee, .. } | Inst::CallCannotUnwind { callee, .. }
                    if module
                        .functions
                        .iter()
                        .any(|f| f.id == *callee && recorded(f)) =>
                {
                    return Err(refusal(
                        "recorded scalar C ABI is supported only by an ordinary direct Call",
                    ));
                }
                Inst::CallIndirect { sig, .. }
                | Inst::InvokeIndirect { sig, .. }
                | Inst::CallIndirectCannotUnwind { sig, .. }
                    if module
                        .func_type(*sig)
                        .is_some_and(|signature| signature.abi.is_some()) =>
                {
                    return Err(refusal(
                        "recorded indirect ABI is outside the scalar direct-call profile",
                    ));
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn prototype(
        &self,
        module: &Module,
        function: &Function,
        signature: &FuncTy,
    ) -> Result<(), AdapterError> {
        let view = function
            .fn_abi(module)
            .map_err(refusal)?
            .ok_or_else(|| refusal("missing recorded prototype"))?;
        let abi = view.placement();
        // New schema facts must be classified explicitly at this consumer.
        let SignatureAbi {
            target: _,
            frontend: _,
            convention: _,
            lowered_convention: _,
            source_abi: _,
            can_unwind: _,
            variadic: _,
            fixed_count: _,
            arguments: _,
            result: _,
        } = abi;
        let AbiTarget {
            triple: _,
            data_layout: _,
            abi: _,
            cpu: _,
            features: _,
            target_spec: _,
            pointer_bytes: _,
            little_endian: _,
        } = &abi.target;
        let AbiFrontend {
            name: _,
            revision: _,
        } = &abi.frontend;
        if !function.is_declaration()
            || function.linkage != trust_ir::Linkage::External
            || function.calling_conv != CallingConv::C
            || abi.lowered_convention != CallingConv::C
            || !matches!(abi.source_abi.as_str(), "C" | "system" | "cdecl")
            || abi.convention != "C"
            || abi.can_unwind
            || !same_scalar_target(&abi.target.triple, &self.triple)
            || !abi.target.abi.is_empty()
            || abi.target.pointer_bytes != 8
            || !abi.target.little_endian
            || abi.arguments.len() != signature.params.len()
            || abi.fixed_count as usize != signature.params.len()
            || signature.returns.len() > 1
        {
            return Err(refusal(
                "recorded prototype is outside the selected non-unwinding scalar C profile",
            ));
        }
        // The default ABI-name selector is checked above; nondefault target
        // ABI variants require an explicitly modeled driver context.
        // CPU/features, data-layout and target-spec strings remain producer
        // identity claims. They grant no target authority. This profile checks
        // every scalar's actual storage, alignment, register class and value
        // width against the native lowerer's fixed scalar types below. It
        // admits no vector, aggregate or hidden lane; pointer-sized integers are
        // admitted only at the checked eight-byte target width.
        for (index, (argument, ty)) in abi.arguments.iter().zip(&signature.params).enumerate() {
            self.scalar(
                argument,
                ty,
                AbiBindingPlace::Parameter(index as u32),
                false,
            )?;
        }
        match signature.returns.as_slice() {
            [] if abi.result.size == 0
                && abi.result.align == 1
                && matches!(abi.result.mode, AbiPassMode::Ignore)
                && abi.result.bindings.is_empty() => {}
            [ty] => self.scalar(&abi.result, ty, AbiBindingPlace::Result(0), true)?,
            _ => {
                return Err(refusal(
                    "recorded result is not one scalar or a zero-sized ignored result",
                ));
            }
        }
        self.classify(
            &signature.params,
            &signature.returns,
            signature.is_vararg,
            signature.params.len(),
        )
    }

    fn scalar(
        &self,
        argument: &AbiArgument,
        ty: &Ty,
        place: AbiBindingPlace,
        result: bool,
    ) -> Result<(), AdapterError> {
        let AbiArgument {
            size: _,
            align: _,
            mode: _,
            bindings: _,
        } = argument;
        let (machine, class, bytes, bits) = scalar_type(ty)?;
        let AbiPassMode::Direct(scalar) = &argument.mode else {
            return Err(refusal(
                "only Direct scalar arguments/results are implemented",
            ));
        };
        let AbiScalar {
            register: _,
            source_offset: _,
            source_bytes: _,
            value_bits: _,
            attributes: _,
        } = scalar;
        let AbiRegister { class: _, bytes: _ } = &scalar.register;
        let expected_extension = self.extension(ty, result);
        let [binding] = argument.bindings.as_slice() else {
            return Err(refusal("scalar requires exactly one binding"));
        };
        let AbiBinding {
            place: _,
            source_offset: _,
            source_bytes: _,
            carrier_offset: _,
            carrier_bytes: _,
        } = binding;
        if argument.size != bytes
            || argument.align != u64::from(machine.align())
            || scalar.register.class != class
            || scalar.register.bytes != bytes
            || scalar.source_offset != 0
            || scalar.source_bytes != bytes
            || scalar.value_bits != bits
            || scalar.attributes.extension != expected_extension
            || scalar.attributes.in_reg
            || binding.place != place
            || binding.source_offset != 0
            || binding.source_bytes != bytes
            || binding.carrier_offset != 0
            || binding.carrier_bytes != bytes
        {
            return Err(refusal(
                "recorded scalar lane or extension disagrees with native marshalling",
            ));
        }
        classify_attributes(&scalar.attributes);
        Ok(())
    }

    fn extension(&self, ty: &Ty, result: bool) -> AbiExtension {
        let extends_narrow = match self.abi {
            NativeAbi::Aarch64(AArch64AbiVariant::Darwin) => true,
            NativeAbi::Aarch64(AArch64AbiVariant::Aapcs64) => false,
            NativeAbi::X86SystemV => !result || self.triple.contains("-apple-"),
        };
        match ty {
            Ty::I8 | Ty::I16 if extends_narrow => AbiExtension::Sign,
            Ty::U8 | Ty::U16 if extends_narrow => AbiExtension::Zero,
            Ty::Bool if extends_narrow || matches!(self.abi, NativeAbi::X86SystemV) => {
                AbiExtension::Zero
            }
            _ => AbiExtension::None,
        }
    }

    pub(crate) fn call(
        &self,
        params: &[Ty],
        returns: &[Ty],
        variadic: bool,
        fixed: usize,
    ) -> Result<(), AdapterError> {
        for ty in params.iter().skip(fixed) {
            if !matches!(
                ty,
                Ty::I32 | Ty::U32 | Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize | Ty::Ptr | Ty::F64
            ) {
                return Err(refusal(
                    "anonymous scalar C arguments must already have default promotions",
                ));
            }
        }
        self.classify(params, returns, variadic, fixed)
    }

    fn classify(
        &self,
        params: &[Ty],
        returns: &[Ty],
        variadic: bool,
        fixed: usize,
    ) -> Result<(), AdapterError> {
        let params = params
            .iter()
            .map(|ty| scalar_type(ty).map(|row| row.0))
            .collect::<Result<Vec<_>, _>>()?;
        let returns = returns
            .iter()
            .map(|ty| scalar_type(ty).map(|row| row.0))
            .collect::<Result<Vec<_>, _>>()?;
        match self.abi {
            NativeAbi::Aarch64(variant) => {
                let locations = if variadic {
                    AppleAArch64ABI::classify_params_variadic_with(variant, fixed, &params)
                } else {
                    AppleAArch64ABI::classify_params_with(variant, &params)
                };
                if locations.len() != params.len()
                    || locations.iter().any(|location| {
                        !matches!(location, ArgLocation::Reg(_) | ArgLocation::Stack { .. })
                    })
                    || AppleAArch64ABI::classify_returns(&returns)
                        .iter()
                        .any(|location| !matches!(location, ArgLocation::Reg(_)))
                {
                    return Err(refusal(
                        "native scalar classifier selected an unsupported carrier",
                    ));
                }
            }
            NativeAbi::X86SystemV => {
                x86_64_isel::x86_sysv_param_locations(&params, false)
                    .map_err(|error| refusal(error.to_string()))?;
                if x86_64_isel::x86_scalar_return_result_regs(&returns, X86CallAbi::SystemV)
                    .is_none()
                    || x86_64_isel::x86_sysv_returns_exceed_c_return_file(&returns)
                {
                    return Err(refusal(
                        "native System V classifier selected an unsupported result",
                    ));
                }
            }
        }
        Ok(())
    }
}

fn scalar_type(ty: &Ty) -> Result<(Type, AbiRegisterClass, u64, u16), AdapterError> {
    let (machine, class, bytes, bits) = match ty {
        Ty::Bool => (Type::B1, AbiRegisterClass::Integer, 1, 1),
        Ty::I8 | Ty::U8 => (Type::I8, AbiRegisterClass::Integer, 1, 8),
        Ty::I16 | Ty::U16 => (Type::I16, AbiRegisterClass::Integer, 2, 16),
        Ty::I32 | Ty::U32 => (Type::I32, AbiRegisterClass::Integer, 4, 32),
        Ty::I64 | Ty::U64 | Ty::Isize | Ty::Usize | Ty::Ptr => {
            (Type::I64, AbiRegisterClass::Integer, 8, 64)
        }
        Ty::F32 => (Type::F32, AbiRegisterClass::Float, 4, 32),
        Ty::F64 => (Type::F64, AbiRegisterClass::Float, 8, 64),
        _ => return Err(refusal("type is outside the fixed-width scalar C profile")),
    };
    Ok((machine, class, bytes, bits))
}

/// These aliases choose the same fixed scalar PCS. Resolve both source and
/// compiler strings independently; the source never selects the native ABI.
/// A macOS deployment version remains part of each recorded identity and the
/// emitted object's minimum OS, but changes none of this profile's scalar
/// register/stack rules. Other OS/environment/vendor components remain exact.
fn same_scalar_target(source: &str, compiler: &str) -> bool {
    fn key(triple: &str) -> Option<(String, String, String, String)> {
        let parts: Vec<_> = triple.split('-').collect();
        if !matches!(parts.len(), 3 | 4) {
            return None;
        }
        let arch = match parts[0] {
            "arm64" | "aarch64" => "aarch64",
            "x86_64" => "x86_64",
            _ => return None,
        };
        let environment = parts.get(3).copied().unwrap_or("");
        let apple_os = ["macosx", "macos", "darwin"].iter().any(|prefix| {
            parts[2].strip_prefix(prefix).is_some_and(|version| {
                version.is_empty()
                    || version.split('.').all(|piece| {
                        !piece.is_empty() && piece.bytes().all(|byte| byte.is_ascii_digit())
                    })
            })
        });
        let os = if parts[1] == "apple" && environment.is_empty() && apple_os {
            "darwin"
        } else {
            parts[2]
        };
        Some((arch.into(), parts[1].into(), os.into(), environment.into()))
    }
    matches!((key(source), key(compiler)), (Some(source), Some(compiler)) if source == compiler)
}

fn classify_attributes(attributes: &AbiAttributes) {
    let AbiAttributes {
        extension: _,
        in_reg: _,
        // These are source/optimization claims; native marshalling does not
        // rely on them or grant proof credit from their presence.
        no_alias: _,
        nonnull: _,
        readonly: _,
        no_undef: _,
        writable: _,
        no_free: _,
        capture: _,
        pointee_size: _,
        pointee_align: _,
    } = attributes;
}

fn refusal(detail: impl Into<String>) -> AdapterError {
    AdapterError::UnsupportedInstruction(format!("[TCG-SCALAR-C-ABI] {}", detail.into()))
}

#[cfg(test)]
#[path = "../tests/common/native_scalar_c_abi.rs"]
mod test_fixture;

#[cfg(test)]
mod tests {
    use super::*;

    /// Exercise this admission itself, independently of any earlier IR
    /// validator refusal. The full-entry controls live in the integration test.
    #[test]
    fn closure_and_function_address_carriers_reach_the_named_native_floor() {
        let native = NativeScalarCAbi::aarch64("aarch64-apple-darwin".into()).unwrap();
        let base = test_fixture::fixture(
            "aarch64-apple-darwin",
            vec![Ty::I64],
            vec![Ty::I64],
            Some(Ty::I64),
            false,
        );
        for constant in [
            Constant::FnDef(base.functions[0].id),
            Constant::Closure {
                func: base.functions[0].id,
                captures: vec![],
            },
            Constant::SymbolAddr {
                symbol: base.functions[0].name.clone(),
                addend: 0,
            },
        ] {
            let mut module = base.clone();
            module.functions[1].blocks[0].body.insert(
                0,
                trust_ir::InstrNode::new(Inst::Const {
                    ty: Ty::Ptr,
                    value: constant,
                })
                .with_result(trust_ir::ValueId::new(9)),
            );
            let error = native.admit_module(&module).unwrap_err().to_string();
            assert!(
                error.contains("[TCG-SCALAR-C-ABI]") && error.contains("escapes"),
                "{error}"
            );
        }
    }
}
