//! Compatibility entry points for codegen metadata admission.

use crate::{AdapterError, CodegenLicensePolicy};
use trust_ir::{CallingConv, FuncTy, Function, Linkage, Module};

/// Apply the default codegen-license policy and conservative standalone-body
/// requirements when no target profile is available. Native module entries
/// use their explicit target profile and license policy instead.
///
/// The license is decided against `module` (as it holds exactly `function`),
/// because an evidence-bound authority's certificate lives on the module
/// (roadmap WS7.5(b)); the default policy refuses a claim-less body (DG-73).
pub fn validate_function_codegen_metadata(
    function: &Function,
    module: &Module,
) -> Result<(), AdapterError> {
    validate_function_codegen_metadata_with_license(
        function,
        module,
        &CodegenLicensePolicy::default(),
    )
}

/// [`validate_function_codegen_metadata`] under the caller's codegen-license
/// policy: an entry that admits a module under a non-default policy (the wasm
/// lane's `*_license` entries) applies the SAME policy to each function it
/// lowers, so the per-function check can neither widen nor narrow the
/// module's verdict.
pub fn validate_function_codegen_metadata_with_license(
    function: &Function,
    module: &Module,
    license: &CodegenLicensePolicy,
) -> Result<(), AdapterError> {
    license.verdict(
        &crate::adapter::module_holding_function(function, module),
        function.id,
    )?;
    validate_function_codegen_metadata_floor(function)
}

/// The conservative standalone-body requirements ALONE (a naked body,
/// function-specific target features and an `external_weak` body are
/// refused). NOT a codegen admission: it decides no license. A caller uses it
/// only for a function of a module whose license it has JUST decided with
/// [`CodegenLicensePolicy::enforce_module`] (the wasm module entry, which
/// would otherwise re-run the module-wide license once per function).
pub fn validate_function_codegen_metadata_floor(function: &Function) -> Result<(), AdapterError> {
    if function.blocks.is_empty() {
        return Ok(());
    }
    let reason = if function.attrs.naked {
        Some("naked function ABI is not implemented".to_owned())
    } else if !function.attrs.target_features.is_empty() {
        Some(format!(
            "function-specific target features {:?} require a modeled target profile",
            function.attrs.target_features
        ))
    } else if matches!(function.linkage, Linkage::ExternalWeak) {
        Some("an `external_weak` function is a weak declaration and cannot carry a body".to_owned())
    } else {
        None
    };
    if let Some(reason) = reason {
        return Err(AdapterError::UnsupportedInstruction(format!(
            "[TCG-CODEGEN-METADATA] function `{}`: {reason}",
            function.name
        )));
    }
    Ok(())
}

/// Refuse emitting a variadic function DEFINITION.
///
/// This is the single refusal every lowering entry applies (native adapter,
/// the pipeline's TrustIR-sourced instruction selection, the JIT compile
/// service's typed install boundary, the wasm lane, and through them the CLI):
/// see [`AdapterError::VariadicDefinitionUnsupported`]. Declarations (bodyless
/// `External` and `AvailableExternally` functions) are not definitions and are
/// accepted, so variadic calls to them keep working when the declaration
/// states its fixed prefix ([`reject_unsigned_variadic_callee`]).
pub fn reject_variadic_definition(
    function: &Function,
    module: &Module,
) -> Result<(), AdapterError> {
    if function.blocks.is_empty() || function.linkage == Linkage::AvailableExternally {
        return Ok(());
    }
    let signature = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or(AdapterError::InvalidFuncTyId(function.ty.index()))?;
    if signature.is_vararg {
        return Err(AdapterError::VariadicDefinitionUnsupported {
            function: function.name.clone(),
        });
    }
    Ok(())
}

/// Refuse a direct call (or invoke) whose callee declaration is variadic but
/// states no fixed-argument count this backend can trust; see
/// [`AdapterError::UnsignedVariadicCallee`].
///
/// `signature` is `callee`'s own `FuncTy`. Two shapes are unsigned: no fixed
/// parameter at all (`params: []` with `is_vararg`, the producer's `(...)`
/// for a callee it could not sign), and a variadic `CallingConv::Rust`
/// signature (the Rust ABI has no variadic form). Every other variadic
/// signature states its fixed prefix, and its call lowers with exactly
/// `params.len()` fixed arguments; a non-variadic signature is untouched.
///
/// The single refusal every direct-call path applies: the native adapter's
/// direct-call and invoke validation (all its module and function entries,
/// and through them the AOT compiler, the JIT and the CLI) and the wasm
/// lane's shared signature-surface check.
pub fn reject_unsigned_variadic_callee(
    callee: &Function,
    signature: &FuncTy,
) -> Result<(), AdapterError> {
    if !signature.is_vararg {
        return Ok(());
    }
    let reason = if signature.params.is_empty() {
        "`(...)`: no fixed parameter is stated"
    } else if callee.calling_conv == CallingConv::Rust {
        "a variadic Rust-convention signature: the Rust ABI has no variadic form, so its fixed \
         prefix is a producer placeholder"
    } else {
        return Ok(());
    };
    Err(AdapterError::UnsignedVariadicCallee {
        callee: callee.name.clone(),
        reason,
    })
}

/// Refuse `ParamAttrs::byval` on `function`'s parameters.
///
/// Applied to every function a general entry lowers and to every direct
/// callee, whatever its calling convention: no lowering implements the
/// caller-copy ABI, so the attribute must never be read as a plain pointer.
/// See [`AdapterError::ByvalParamUnsupported`].
pub fn reject_byval_params(function: &Function) -> Result<(), AdapterError> {
    if let Some(index) = function.attrs.params.iter().position(|attrs| attrs.byval) {
        return Err(AdapterError::ByvalParamUnsupported {
            function: function.name.clone(),
            index,
        });
    }
    Ok(())
}

/// Apply the target-neutral contract-surface checks and the default license.
/// Target-specific entries must also validate their own feature vocabulary
/// and representability; a generic IR report cannot establish either fact.
///
/// The surface floor is decided FIRST, as on every adapter module entry
/// (`translate_module*`: surface, then license), so a module that is both
/// claim-less and carries an unconsumable construct is refused by the
/// construct's own name on every entry.
pub fn validate_codegen_metadata(module: &Module) -> Result<(), AdapterError> {
    validate_codegen_metadata_with_license(module, &CodegenLicensePolicy::default())
}

/// [`validate_codegen_metadata`] under an explicit codegen-license policy.
pub fn validate_codegen_metadata_with_license(
    module: &Module,
    license: &CodegenLicensePolicy,
) -> Result<(), AdapterError> {
    crate::reject_unconsumed_v41_target_neutral_surface(module)?;
    license.enforce_module(module)
}
