//! Preserve the compiling session's native object format and ABI selection.

use rustc_codegen_ssa::back::versioned_llvm_target;
use rustc_session::Session;
use trust_cg_codegen::target::{Target, TargetSpec};

pub(super) fn for_session(sess: &Session, architecture: Target) -> Result<TargetSpec, String> {
    let refuse = |reason| {
        format!(
            "rustc_codegen_trust_cg: cannot bind native target `{}`: {reason}",
            sess.opts.target_triple
        )
    };
    if sess.target.pointer_width != 64 || sess.target.endian != rustc_abi::Endian::Little {
        return Err(refuse(
            "native object emission requires a 64-bit little-endian target".to_owned(),
        ));
    }
    // This is the compiler's own effective triple, including its validated
    // Apple deployment version. Do not read the environment independently or
    // substitute the host's object format for a requested target.
    let triple = versioned_llvm_target(sess);
    sess.dcx().abort_if_errors();
    let spec = TargetSpec::parse(&triple).map_err(|error| refuse(error.to_string()))?;
    if !spec.has_explicit_os_abi() {
        return Err(refuse(
            "LLVM target must name an explicit OS and ABI".to_owned(),
        ));
    }
    let os = match sess.target.os.desc() {
        "macos" => "darwin",
        os => os,
    };
    let environment = match sess.target.env.desc() {
        "" => "unknown",
        environment => environment,
    };
    // A custom target can disagree with its LLVM triple. Such a target must
    // not receive a plausible object for a different ABI or architecture.
    if spec.architecture != architecture
        || spec.operating_system.triple_component() != os
        || spec.vendor.triple_component() != sess.target.vendor_symbol().as_str()
        || spec.environment.triple_component() != environment
    {
        return Err(refuse(format!(
            "LLVM target `{triple}` disagrees with the session's architecture, vendor, OS or ABI"
        )));
    }
    Ok(spec)
}
