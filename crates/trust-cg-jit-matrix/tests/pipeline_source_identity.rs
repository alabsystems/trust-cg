// trust-cg-jit-matrix - pipeline source identity regression tests

#[path = "../src/pipeline_source_identity.rs"]
mod pipeline_source_identity;

use pipeline_source_identity::{
    CLEAN_PIPELINE_CRATES, PIPELINE_CRATES, TRUST_IR_PIPELINE_CRATES,
    compute_pipeline_source_identity, compute_source_identity,
};
use std::fs;
use std::path::PathBuf;

fn identity(root: &std::path::Path) -> String {
    compute_source_identity(
        root,
        &[PathBuf::from("crate/src"), PathBuf::from("assets")],
        &[
            PathBuf::from("crate/Cargo.toml"),
            PathBuf::from("Cargo.lock"),
        ],
    )
    .expect("fixture identity")
    .hex
}

fn fixture() -> tempfile::TempDir {
    let root = tempfile::tempdir().expect("temp source tree");
    fs::create_dir_all(root.path().join("crate/src/nested")).unwrap();
    fs::create_dir_all(root.path().join("assets")).unwrap();
    fs::write(
        root.path().join("crate/src/lib.rs"),
        "pub fn value() -> u8 { 1 }\n",
    )
    .unwrap();
    fs::write(root.path().join("crate/src/nested/lower.rs"), "lower-v1\n").unwrap();
    fs::write(
        root.path().join("crate/Cargo.toml"),
        "[package]\nname='fixture'\n",
    )
    .unwrap();
    fs::write(root.path().join("assets/verdict.vdb"), "accepted\n").unwrap();
    fs::write(root.path().join("Cargo.lock"), "version = 4\n").unwrap();
    root
}

#[test]
fn identity_is_path_independent_and_stable_for_equal_content() {
    let first = fixture();
    let second = fixture();
    assert_eq!(identity(first.path()), identity(second.path()));
    assert_eq!(identity(first.path()), identity(first.path()));
}

#[test]
fn mutation_add_delete_and_rename_each_change_identity() {
    let root = fixture();
    let baseline = identity(root.path());

    fs::write(
        root.path().join("crate/src/lib.rs"),
        "pub fn value() -> u8 { 2 }\n",
    )
    .unwrap();
    let mutated = identity(root.path());
    assert_ne!(baseline, mutated, "content mutation must invalidate");

    fs::write(root.path().join("crate/src/new_pass.rs"), "new-pass\n").unwrap();
    let added = identity(root.path());
    assert_ne!(mutated, added, "source addition must invalidate");

    fs::remove_file(root.path().join("assets/verdict.vdb")).unwrap();
    let deleted = identity(root.path());
    assert_ne!(added, deleted, "asset deletion must invalidate");

    fs::rename(
        root.path().join("crate/src/nested/lower.rs"),
        root.path().join("crate/src/nested/lowering.rs"),
    )
    .unwrap();
    let renamed = identity(root.path());
    assert_ne!(deleted, renamed, "source rename must invalidate");
}

#[test]
fn closure_names_every_machine_code_pipeline_crate() {
    assert_eq!(
        PIPELINE_CRATES,
        [
            "trust-cg-jit-matrix",
            "trust-cg-codegen",
            "trust-cg-ir",
            "trust-cg-dialect",
            "trust-cg-lower",
            "trust-cg-opt",
            "trust-cg-regalloc",
            "trust-cg-verify",
            "trust-cg-drat-trim",
        ]
    );
    assert_eq!(
        TRUST_IR_PIPELINE_CRATES,
        ["trust-ir", "trust-ir-build", "trust-ir-giveback"]
    );
    assert_eq!(CLEAN_PIPELINE_CRATES, ["clean-kernel"]);

    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest_dir
        .parent()
        .and_then(std::path::Path::parent)
        .unwrap();
    let production = compute_pipeline_source_identity(workspace_root)
        .expect("the production closure must be complete and readable");
    assert_eq!(production.hex.len(), 64);
    assert!(
        production
            .hashed_relative_paths
            .iter()
            .any(|path| { path == "crates/trust-cg-verify/verdict_db/tier0.vdb" })
    );
    assert!(
        production
            .hashed_relative_paths
            .iter()
            .any(|path| { path == "third_party/vendor/drat-trim/drat-trim.c" })
    );
    assert!(
        production
            .watched_paths
            .iter()
            .any(|path| { path == &workspace_root.join("crates/trust-cg-opt") })
    );
    if workspace_root
        .parent()
        .is_some_and(|parent| parent.join("trust-ir/crates/trust-ir/Cargo.toml").is_file())
    {
        assert!(
            production
                .hashed_relative_paths
                .iter()
                .any(|path| { path == "external-trust-ir/crates/trust-ir-build/src/validate.rs" })
        );
    }
    if workspace_root.parent().is_some_and(|parent| {
        parent
            .join("clean/crates/clean-kernel/Cargo.toml")
            .is_file()
    }) {
        assert!(
            production
                .hashed_relative_paths
                .iter()
                .any(|path| { path == "external-clean/crates/clean-kernel/src/lib.rs" })
        );
        assert!(
            production
                .hashed_relative_paths
                .iter()
                .any(|path| { path == "external-clean/data/soundness_tcb.json" })
        );
    }
}

#[test]
fn missing_required_root_fails_closed() {
    let root = fixture();
    let error = compute_source_identity(
        root.path(),
        &[PathBuf::from("missing/src")],
        &[PathBuf::from("Cargo.lock")],
    )
    .expect_err("missing source root must abort identity construction");
    assert_eq!(error.kind(), std::io::ErrorKind::NotFound);
}
