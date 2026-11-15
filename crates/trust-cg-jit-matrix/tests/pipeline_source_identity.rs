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

    let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("Cargo's current source package");
    let workspace_root = manifest_dir
        .ancestors()
        .take(5)
        .find(|root| {
            root.join("crates/trust-cg-jit-matrix/src/pipeline_source_identity.rs")
                .is_file()
        })
        .expect("the original CG source workspace");
    let production = compute_pipeline_source_identity(workspace_root)
        .expect("the production closure must be complete and readable");
    assert_eq!(production.hex.len(), 64);
    assert!(
        production
            .hashed_relative_paths
            .iter()
            .any(|path| { path == "crates/trust-cg-jit-matrix/src/pipeline_watch_plan.rs" })
    );
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

#[test]
fn recursive_watch_roots_cover_sources_without_repeated_descendants() {
    let root = fixture();
    let identity = compute_source_identity(
        root.path(),
        &[PathBuf::from("crate/src"), PathBuf::from("assets")],
        &[
            PathBuf::from("crate/Cargo.toml"),
            PathBuf::from("Cargo.lock"),
        ],
    )
    .unwrap();
    let mut expected = ["crate/src", "assets", "crate/Cargo.toml", "Cargo.lock"]
        .map(|path| root.path().join(path))
        .to_vec();
    expected.sort();
    assert_eq!(identity.watched_paths, expected);
    assert_eq!(
        identity.hashed_relative_paths,
        [
            "Cargo.lock",
            "assets/verdict.vdb",
            "crate/Cargo.toml",
            "crate/src/lib.rs",
            "crate/src/nested/lower.rs",
        ]
    );
}

#[test]
fn similar_names_and_parent_components_keep_their_own_declarations() {
    let root = fixture();
    fs::create_dir(root.path().join("crate-other")).unwrap();
    fs::write(root.path().join("crate-other/data"), "separate\n").unwrap();
    let identity = compute_source_identity(
        root.path(),
        &[PathBuf::from("crate")],
        &[
            PathBuf::from("crate/src/../Cargo.toml"),
            PathBuf::from("crate-other/data"),
        ],
    )
    .unwrap();
    assert_eq!(identity.watched_paths.len(), 3);
    for path in ["crate", "crate/src/../Cargo.toml", "crate-other/data"] {
        assert!(identity.watched_paths.contains(&root.path().join(path)));
    }
}

#[cfg(unix)]
#[test]
fn symlink_roots_keep_explicit_descendants_and_nested_links_still_refuse() {
    let root = fixture();
    let link = root.path().join("linked-src");
    std::os::unix::fs::symlink("crate/src", &link).unwrap();
    let identity =
        compute_source_identity(root.path(), &[PathBuf::from("linked-src")], &[]).unwrap();
    assert!(identity.watched_paths.contains(&link));
    assert!(identity.watched_paths.contains(&link.join("lib.rs")));
    assert!(identity.watched_paths.contains(&link.join("nested")));
    // The plain nested directory covers only its own descendant.
    assert!(
        !identity
            .watched_paths
            .contains(&link.join("nested/lower.rs"))
    );
    std::os::unix::fs::symlink("lib.rs", root.path().join("crate/src/alias.rs")).unwrap();
    assert_eq!(
        compute_source_identity(root.path(), &[PathBuf::from("linked-src")], &[])
            .unwrap_err()
            .kind(),
        std::io::ErrorKind::InvalidData,
    );
}

#[test]
fn crate_root_watch_observes_a_new_optional_build_script() {
    let world = tempfile::tempdir().unwrap();
    let root = world.path().join("cg");
    for name in PIPELINE_CRATES {
        let crate_root = root.join("crates").join(name);
        fs::create_dir_all(crate_root.join("src")).unwrap();
        fs::write(crate_root.join("src/lib.rs"), "// fixture source\n").unwrap();
        fs::write(crate_root.join("Cargo.toml"), "// fixture manifest\n").unwrap();
    }
    for path in [
        "Cargo.toml",
        "Cargo.lock",
        "third_party/vendor/drat-trim/drat-trim.c",
        "crates/trust-cg-verify/verdict_db/fixture.vdb",
        "crates/trust-cg-verify/lrat_fixtures/fixture.lrat",
    ] {
        let path = root.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, "fixture\n").unwrap();
    }
    let before = compute_pipeline_source_identity(&root).unwrap();
    let build = root.join("crates/trust-cg-opt/build.rs");
    fs::write(&build, "fn main() {}\n").unwrap();
    let after = compute_pipeline_source_identity(&root).unwrap();
    assert_ne!(before.hex, after.hex);
    assert_eq!(before.watched_paths, after.watched_paths);
    assert!(
        after
            .watched_paths
            .contains(&root.join("crates/trust-cg-opt"))
    );
    assert!(!after.watched_paths.contains(&build));
    fs::remove_file(build).unwrap();
    assert_eq!(before, compute_pipeline_source_identity(&root).unwrap());
}
