// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

//! Wasm configuration for compiler packages that omit LLVM's Wasm backend.

use crate::InitSession;
use crate::wasm_cpu_features::Features;
use rustc_codegen_ssa::TargetConfig;
use rustc_codegen_ssa::target_features;
use rustc_target::spec::PanicStrategy;

pub(crate) fn for_session(sess: &InitSession) -> TargetConfig {
    if sess.opts.unstable_opts.fixed_x18 {
        sess.dcx()
            .fatal("-Zfixed-x18 is only supported on AArch64 targets");
    }
    // Refuse an expanded compiler catalog until its CPU mapping is modelled.
    for &(feature, _, _) in sess.target.rust_target_features() {
        if !Features::knows(feature) {
            sess.dcx().fatal(format!(
                "[TCG-WASM-CPU-CATALOG] unmodelled Rust feature `{feature}`"
            ));
        }
    }
    let requested_cpu = sess
        .opts
        .cg
        .target_cpu
        .as_deref()
        .unwrap_or(&sess.target.cpu);
    let (cpu, native_features) = if requested_cpu == "native" {
        native_configuration(sess)
    } else {
        (requested_cpu.to_owned(), Vec::new())
    };
    let (mut features, recognized) = Features::for_cpu(&cpu);
    if !recognized {
        sess.dcx().warn(format!(
            "'{cpu}' is not a recognized processor for this target (ignoring processor)"
        ));
    }
    // A spec CPU named "native" resolves the host's CPU name, but LLVM adds
    // the host feature string only for an explicit -Ctarget-cpu=native.
    if sess.opts.cg.target_cpu.as_deref() == Some("native") {
        for flag in native_features {
            apply_backend_flag(&mut features, &flag);
        }
    }
    target_features::target_spec_to_backend_features(sess, |feature, enabled| {
        features.set(feature, enabled);
    });
    if rustc_codegen_ssa::base::wants_wasm_eh(&sess.target)
        && sess.panic_strategy() == PanicStrategy::Unwind
    {
        features.set("exception-handling", true);
    }
    // These flags currently introduce no Wasm feature, but keep their ordering
    // explicit rather than treating them as global Rust feature overrides.
    let mut by_flags = Vec::new();
    target_features::retpoline_features_by_flags(sess, &mut by_flags);
    target_features::sanitizer_features_by_flags(sess, &mut by_flags);
    for flag in by_flags {
        apply_backend_flag(&mut features, &flag);
    }
    for flag in sess
        .opts
        .unstable_opts
        .llvm_target_feature
        .split(',')
        .filter(|s| !s.is_empty())
    {
        if flag.starts_with(['+', '-']) {
            if !apply_backend_flag(&mut features, flag) {
                sess.dcx().warn(format!(
                    "'{flag}' is not a recognized WebAssembly backend feature (ignoring feature)"
                ));
            }
        } else {
            sess.dcx().warn(format!("unknown feature `{flag}` specified for `-Zllvm-target-feature` (missing `+` or `-` prefix)"));
        }
    }
    // Apply global Rust flags exactly once, including Rust implications and
    // stability/ABI diagnostics. The backend graph above is deliberately not
    // substituted for the Rust graph (e.g. relaxed-simd implies simd128 here).
    let internal_target_features = target_features::internal_target_features::<1>(
        sess,
        |feature| std::iter::once(feature).collect(),
        |feature| features.has(feature),
    );
    sess.dcx().abort_if_errors();
    TargetConfig {
        internal_target_features,
        has_reliable_f16: false,
        has_reliable_f16_math: false,
        has_reliable_f16b: false,
        has_reliable_f128: false,
        has_reliable_f128_math: false,
    }
}

fn apply_backend_flag(features: &mut Features, flag: &str) -> bool {
    if let Some(feature) = flag.strip_prefix('+') {
        features.set(feature, true)
    } else if let Some(feature) = flag.strip_prefix('-') {
        features.set(feature, false)
    } else {
        false
    }
}

/// Obtain native CPU metadata from the host target, whose LLVM catalog is
/// present even when Wasm is omitted. No input, providers or codegen are handed
/// to LLVM. Only the returned CPU name and raw host feature flags are used.
fn native_configuration(sess: &InitSession) -> (String, Vec<String>) {
    let mut options = crate::target_configuration::metadata_options(sess);
    options.cg.target_cpu = Some("native".into());
    options.cg.target_feature.clear();
    options.unstable_opts.llvm_target_feature.clear();
    options.unstable_opts.fixed_x18 = false;
    options.target_triple =
        rustc_target::spec::TargetTuple::from_tuple(rustc_session::config::host_tuple());
    let mut host = sess.host.clone();
    host.features = "".into();
    let metadata_session = rustc_session::build_early_session(options, host, None);
    let mut backend = rustc_codegen_llvm::LlvmCodegenBackend::new();
    let initialized = backend.init(&metadata_session);
    metadata_session.dcx().abort_if_errors();
    let features = initialized.global_backend_features.clone();
    static INTERNAL_FEATURES: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(false);
    let session = rustc_session::build_session(
        metadata_session,
        initialized,
        rustc_session::CompilerIO {
            input: rustc_session::config::Input::Str {
                name: rustc_span::FileName::Custom("<trust-cg-native-cpu-configuration>".into()),
                input: String::new(),
            },
            output_dir: None,
            output_file: None,
            temps_dir: None,
        },
        Default::default(),
        rustc_interface::util::rustc_version_str().unwrap_or("unknown"),
        &INTERNAL_FEATURES,
    );
    let cpu = backend.target_cpu(&session);
    session.dcx().abort_if_errors();
    (cpu, features)
}
