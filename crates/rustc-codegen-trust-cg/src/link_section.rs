//! `#[link_section]` on statics and functions (ledger L06-P8).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! A section name is a placement claim: the definition's bytes must land in
//! that section, with the loader semantics the name carries (a Mach-O
//! `__DATA,__mod_init_func` constructor table runs before `main`). Emitting
//! the definition in the default section would silently drop the claim.
//!
//! * A STATIC carries the name to trust-ir (`Global.section`, v41) on the
//!   AArch64 Mach-O and ELF targets, whose object emitters place it or refuse
//!   it with a stable `[TCG-SECTION-*]` code
//!   (`trust_cg_codegen::object_sections`: on Mach-O a
//!   `segment,section[,type[,attributes]]` name in `__DATA`, `__DATA_CONST` or
//!   `__TEXT`, a `__mod_init_func` table only of relocated function pointers,
//!   reserved names refused). Every other target refuses it here.
//! * A thread-local static keeps its own refusal: its bytes are the TLV
//!   template the descriptor names (`compile_thread_local_static_object`).
//! * A FUNCTION is refused by name on every target: this frontend does not
//!   carry `Function.section` (v45), and the Mach-O module emitter places
//!   every function in `__TEXT,__text` and refuses an explicit function
//!   section itself (`ExplicitFunctionSectionUnsupported`). It used to be
//!   dropped silently.

use super::*;

/// Mirrors `trust_cg_codegen::object_sections::SectionRefusal::TargetUnsupported`.
const TARGET_REFUSAL: &str = "[TCG-SECTION-TARGET]";

/// The explicit section a `what` definition (`"static"`) carries to trust-ir:
/// `None` without `#[link_section]`, the name on the AArch64 Mach-O and ELF
/// targets, and a named refusal everywhere else.
pub(crate) fn explicit_section(
    tcx: TyCtxt<'_>,
    section: Option<rustc_span::Symbol>,
    what: &str,
) -> Result<Option<String>, String> {
    let Some(section) = section else {
        return Ok(None);
    };
    let target = &tcx.sess.target;
    let placed = target.arch.desc() == "aarch64"
        && (target.is_like_darwin || target.os == rustc_target::spec::Os::Linux);
    if !placed {
        return Err(format!(
            "{TARGET_REFUSAL} {what} with explicit #[link_section = \"{section}\"]: the {} \
             object emission places no explicit sections (default-section emission only)",
            tcx.sess.opts.target_triple
        ));
    }
    Ok(Some(section.as_str().to_owned()))
}

/// The named refusal of a function definition with `#[link_section]`, or
/// `None` when it has none.
pub(crate) fn function_refusal<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    symbol: &str,
) -> Option<String> {
    let section = tcx.codegen_instance_attrs(instance.def).link_section?;
    let why = if tcx.sess.target.is_like_darwin {
        "the Mach-O module emitter places every function in `__TEXT,__text` and has no \
         per-function `segment,section` placement"
    } else {
        "this frontend does not carry a function's explicit section to the object emitter"
    };
    Some(format!(
        "{TARGET_REFUSAL} function `{symbol}` ({}) has #[link_section = \"{section}\"]: {why}; \
         refusing rather than placing it in the default text section",
        tcx.def_path_str(instance.def_id())
    ))
}
