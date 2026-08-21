#[path = "support/target_dir.rs"]
mod target_dir_support;

use std::ffi::OsStr;
use std::path::Path;

#[test]
fn unset_defaults_to_manifest_target() {
    assert_eq!(
        target_dir_support::resolve_target_dir(
            Path::new("/workspace/bridge"),
            Path::new("/invocation"),
            None,
        ),
        Path::new("/workspace/bridge/target")
    );
}

#[test]
fn absolute_target_dir_is_preserved_and_normalized() {
    assert_eq!(
        target_dir_support::resolve_target_dir(
            Path::new("/workspace/bridge"),
            Path::new("/invocation"),
            Some(OsStr::new("/cache/a/../cargo-target")),
        ),
        Path::new("/cache/cargo-target")
    );
}

#[test]
fn relative_target_dir_is_relative_to_invocation_directory() {
    assert_eq!(
        target_dir_support::resolve_target_dir(
            Path::new("/workspace/bridge"),
            Path::new("/invocation/work"),
            Some(OsStr::new("../shared/./target")),
        ),
        Path::new("/invocation/shared/target")
    );
}

#[test]
fn normalization_clamps_parent_components_at_the_root() {
    assert_eq!(
        target_dir_support::resolve_target_dir(
            Path::new("/workspace/bridge"),
            Path::new("/invocation"),
            Some(OsStr::new("../../../shared/target")),
        ),
        Path::new("/shared/target")
    );
}

#[test]
fn custom_profile_is_not_collapsed_to_debug_or_release() {
    assert_eq!(
        target_dir_support::artifact_dir(Path::new("/target"), None, "proof-audit"),
        Path::new("/target/proof-audit")
    );
}

#[test]
fn explicit_target_triple_precedes_profile() {
    assert_eq!(
        target_dir_support::artifact_dir(
            Path::new("/target"),
            Some("aarch64-unknown-linux-gnu"),
            "release",
        ),
        Path::new("/target/aarch64-unknown-linux-gnu/release")
    );
}

#[test]
fn custom_target_json_uses_its_file_stem_not_its_path() {
    assert_eq!(
        target_dir_support::target_output_component(
            "/workspace/targets/aarch64-proof.json",
            None,
        ),
        Some(Path::new("aarch64-proof").to_path_buf())
    );
    assert_eq!(
        target_dir_support::target_output_component("targets/x86-proof.json", None),
        Some(Path::new("x86-proof").to_path_buf())
    );
}

#[test]
fn host_tuple_uses_the_resolved_rustc_host_directory() {
    assert_eq!(
        target_dir_support::target_output_component(
            "host-tuple",
            Some("aarch64-apple-darwin"),
        ),
        Some(Path::new("aarch64-apple-darwin").to_path_buf())
    );
    assert_eq!(
        target_dir_support::target_output_component("host-tuple", None),
        None,
        "Cargo's special spelling must never become a literal output directory"
    );
}
