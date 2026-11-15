// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

//! Rust cfg and ABI feature facts from the compiling toolchain's target catalog.
//!
//! LLVM supplies configuration data only. Instruction admission, lowering,
//! object generation and proof authority remain owned by Trust Codegen.

use crate::InitSession;
use rustc_codegen_ssa::TargetConfig;

pub(crate) fn for_session(sess: &InitSession) -> TargetConfig {
    // A full-session caller may already have rejected an invalid profile path.
    // Do not repeat its validation in another session or publish partial cfg.
    sess.dcx().abort_if_errors();
    #[cfg(rustc_session_split)]
    if sess.target.arch.desc() == "wasm32" {
        return crate::wasm_target_configuration::for_session(sess);
    }
    // A separate metadata session preserves CPU/spec/global-feature semantics
    // without changing the caller's options, providers or proof state. These
    // codegen-only controls must not make a metadata query load Enzyme, parse
    // ignored LLVM arguments or create a second profiling output.
    let options = metadata_options(sess);

    #[cfg(not(rustc_session_split))]
    let metadata_session = rustc_session::build_session(
        options,
        rustc_session::CompilerIO {
            input: rustc_session::config::Input::Str {
                name: rustc_span::FileName::Custom("<trust-cg-target-configuration>".into()),
                input: String::new(),
            },
            output_dir: None,
            output_file: None,
            temps_dir: None,
        },
        Default::default(),
        sess.target.clone(),
        sess.cfg_version,
        None,
        sess.using_internal_features,
    );
    #[cfg(rustc_session_split)]
    let metadata_session = rustc_session::build_early_session(options, sess.target.clone(), None);

    #[cfg(not(rustc_session_split))]
    let metadata_backend = rustc_codegen_llvm::LlvmCodegenBackend::new();
    #[cfg(rustc_session_split)]
    let mut metadata_backend = rustc_codegen_llvm::LlvmCodegenBackend::new();
    metadata_backend.init(&metadata_session);
    metadata_session.dcx().abort_if_errors();
    let mut config = metadata_backend.target_config(&metadata_session);
    // Diagnostics belong to this metadata session. Returning its feature set
    // after an error would leave the caller's error count clear: tied-feature
    // errors would print, yet compilation could succeed. Propagate the fatal
    // exit before publishing any configuration to the caller.
    metadata_session.dcx().abort_if_errors();

    // Catalog support does not establish Trust Codegen's floating-point
    // lowering/reliability contract. Keep its conservative declarations.
    config.has_reliable_f16 = false;
    config.has_reliable_f16_math = false;
    #[cfg(rustc_session_split)]
    {
        config.has_reliable_f16b = false;
    }
    config.has_reliable_f128 = false;
    config.has_reliable_f128_math = false;
    config
}

/// Copy only configuration-relevant requests into a metadata session. Profile
/// files and instrumentation belong to the caller's codegen-option contract;
/// a second session must not validate those paths or consume their contents.
pub(crate) fn metadata_options(sess: &InitSession) -> rustc_session::config::Options {
    let mut options = sess.opts.clone();
    options.cg.llvm_args.clear();
    options.cg.profile_generate = rustc_session::config::SwitchWithOptPath::Disabled;
    options.cg.profile_use = None;
    #[cfg(rustc_codegen_sample_profile)]
    {
        options.cg.profile_sample_use = None;
    }
    #[cfg(not(rustc_codegen_sample_profile))]
    {
        options.unstable_opts.profile_sample_use = None;
    }
    options.unstable_opts.autodiff = Default::default();
    options.unstable_opts.self_profile = rustc_session::config::SwitchWithOptPath::Disabled;
    options.unstable_opts.llvm_time_trace = false;
    options
}
