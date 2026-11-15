// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0.
//! One retained binary module through the ordinary prepared translation API.
//! This diagnoses lowering only: it neither binds extern addresses nor emits code.

use trust_cg_lower::adapter::{GuardCarrierArch, TlsDialect, prepare_module_for_lir};
use trust_cg_lower::{CodegenLicensePolicy, UnlicensedBodyPolicy};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let input = args.next().ok_or("expected binary module path")?;
    let mut license = CodegenLicensePolicy::default();
    if let Some(option) = args.next() {
        if option != "--permit-unlicensed" || args.next().is_some() {
            return Err("only optional --permit-unlicensed is supported".into());
        }
        license = license.with_unlicensed(UnlicensedBodyPolicy::Permit);
    }
    let bytes = std::fs::read(input)?;
    let module = trust_ir::binary::deserialize_module(&bytes)
        .map_err(|error| format!("failed to decode binary module: {error}"))?;
    let started = std::time::Instant::now();
    let prepared = prepare_module_for_lir(&module, GuardCarrierArch::AArch64)?;
    let (functions, validation) =
        prepared.translate_with_tls_and_validation_with_license(TlsDialect::default(), &license)?;
    validation.replay_exact_module_bindings(&functions)?;
    println!(
        "module={:?} source_functions={} translated_functions={} translation_and_binding_replay={:?}",
        module.name,
        module.functions.len(),
        functions.len(),
        started.elapsed(),
    );
    Ok(())
}
