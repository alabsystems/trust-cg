// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The adapter's own refusal, reached below TrustIR's typed admission.
//!
//! Every codegen entry (`translate_function` and the `translate_module*`
//! family) consumes TrustIR's typed admission first, so a malformed constant
//! or descriptor stops at TrustIR's verdict there and the adapter's own check
//! behind it does not run. This helper uses two of the public entries that
//! run no typed admission: `translate_body_template` lowers one bodied
//! function with the adapter alone, and `translate_type_in_module` converts
//! one type with the module's tables. (The `translate_type*` family,
//! `translate_inline_only_bodies`, the shared v41 floor
//! `reject_unconsumed_v41_*surface*` and codegen's `module_object_globals`
//! skip it too.) A target pins an adapter check through one of them, next to
//! the typed refusal that shadows the check on the codegen entries.

use trust_cg_lower::adapter::{AdapterError, translate_type_in_module};
use trust_cg_lower::{
    CodegenLicensePolicy, GuardCarrierArch, ObjectAccessModel, UnlicensedBodyPolicy,
    translate_body_template,
};
use trust_ir::{Module, Ty};

/// The adapter alone lowering `module`'s first function: `Err` is
/// `translate_body_template`'s report (`not lowerable: <AdapterError>`).
///
/// The fixtures are claim-less (no `body_gate`), and the default license
/// policy refuses an unlicensed body before the adapter runs, so the helper
/// states `Permit` like every other claim-less test entry: otherwise the
/// license refusal would shadow the adapter check it exists to reach.
#[allow(dead_code)] // Not every target that includes this file lowers a body.
pub(crate) fn body_below_admission(module: &Module) -> Result<(), String> {
    let func = module.functions.first().expect("one function");
    translate_body_template(
        module,
        func,
        GuardCarrierArch::AArch64,
        ObjectAccessModel::default(),
        &CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
    .map(drop)
}

/// The adapter's own refusal of `module`'s first function, as
/// `translate_body_template` reports it (`not lowerable: <AdapterError>`).
#[allow(dead_code)] // Not every target that includes this file lowers a body.
#[track_caller]
pub(crate) fn body_refusal_below_admission(module: &Module) -> String {
    body_below_admission(module)
        .expect_err("the adapter must refuse the body below typed admission")
}

/// The module-aware type conversion's own refusal of `ty`.
#[allow(dead_code)] // Not every target that includes this file converts a type.
#[track_caller]
pub(crate) fn type_refusal_below_admission(module: &Module, ty: &Ty) -> AdapterError {
    translate_type_in_module(module, ty)
        .expect_err("the conversion must refuse the type below typed admission")
}
