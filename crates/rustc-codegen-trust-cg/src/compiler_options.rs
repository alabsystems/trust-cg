// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Actual compiler crate-kind and sample-profile requests. Namespace selection
//! preserves the executable/rlib policies and the requested profile path.

#[cfg(not(rustc_structures_crate_type))]
pub(super) use rustc_session::config::CrateType;
#[cfg(rustc_structures_crate_type)]
pub(super) use rustc_structures::CrateType;

pub(super) fn executable_only(kinds: &[CrateType]) -> bool {
    kinds
        .iter()
        .all(|kind| matches!(kind, CrateType::Executable))
}

pub(super) fn rlib_only(kinds: &[CrateType]) -> bool {
    !kinds.is_empty() && kinds.iter().all(|kind| matches!(kind, CrateType::Rlib))
}

#[cfg(rustc_codegen_sample_profile)]
pub(super) const SAMPLE_PROFILE_OPTION: &str = "`-C profile-sample-use`";
#[cfg(not(rustc_codegen_sample_profile))]
pub(super) const SAMPLE_PROFILE_OPTION: &str = "`-Z profile-sample-use`";

pub(super) fn sample_profile(opts: &rustc_session::config::Options) -> Option<&std::path::Path> {
    #[cfg(rustc_codegen_sample_profile)]
    let profile = &opts.cg.profile_sample_use;
    #[cfg(not(rustc_codegen_sample_profile))]
    let profile = &opts.unstable_opts.profile_sample_use;
    profile.as_deref()
}
