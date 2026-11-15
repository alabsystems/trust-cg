//! Exercise actual integration-test artifact selectors under ordinary Cargo.
//! The imported compiler differential tests are deliberately not selected.

#[path = "../../../../crates/rustc-codegen-trust-cg/tests/support/backend_artifact.rs"]
#[allow(dead_code)]
mod artifact;

#[allow(dead_code)]
mod fat_leaf {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../../crates/rustc-codegen-trust-cg/tests/dyn_fat_leaf_differential.rs"
    ));

    pub(super) fn select() -> std::path::PathBuf {
        ensure_dylib_built()
    }
}

#[allow(dead_code)]
mod boolean_knob {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../../crates/rustc-codegen-trust-cg/tests/boolean_knob_value_grammar.rs"
    ));

    pub(super) fn select() -> std::path::PathBuf {
        ensure_dylib_built()
    }
}

fn expected_library() -> std::path::PathBuf {
    // The process owner reads this path from Cargo's actual compiler-artifact
    // message, independently of the selector under test.
    std::env::var_os("BRIDGE_ARTIFACT_EXPECTED_LIBRARY")
        .map(std::path::PathBuf::from)
        .expect("owner must bind Cargo's emitted library")
}

fn assert_cargo_library(selected: std::path::PathBuf) {
    let expected = expected_library();
    assert_export_matches(&selected, &expected);
}

fn assert_export_matches(selected: &std::path::Path, expected: &std::path::Path) {
    let expected_metadata = std::fs::symlink_metadata(expected).unwrap();
    let selected_metadata = std::fs::symlink_metadata(selected).unwrap();
    assert!(expected_metadata.file_type().is_file());
    assert!(selected_metadata.file_type().is_file());
    assert!(expected_metadata.len() > 0);
    // Cargo exports the selected library by copying it on older toolchains
    // and hardlinking it on the current one. The export must belong to the
    // same profile and contain exactly the selected dependency's bytes.
    if selected != expected {
        let directory = selected.parent().unwrap();
        let profile = match directory.file_name().and_then(|name| name.to_str()) {
            Some("deps") => directory.parent().unwrap(),
            Some("out") => directory.ancestors().nth(4).unwrap(),
            _ => panic!("unknown selected Cargo library layout: {selected:?}"),
        };
        assert_eq!(
            expected,
            profile.join(selected.file_name().unwrap()),
            "Cargo export must name the selected dependency's own profile"
        );
    }
    assert_eq!(
        std::fs::read(selected).unwrap(),
        std::fs::read(expected).unwrap(),
        "selected {selected:?}, Cargo emitted {expected:?}"
    );
}

#[test]
fn fat_leaf_selects_current_cargo_library() {
    assert_cargo_library(fat_leaf::select());
}

#[test]
fn boolean_knob_selects_current_cargo_library() {
    assert_cargo_library(boolean_knob::select());
}

fn case_directory(label: &str) -> std::path::PathBuf {
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "tcg-artifact-{label}-{}-{stamp}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).unwrap();
    directory
}

#[test]
fn copied_export_requires_exact_bytes_and_its_own_profile() {
    let root = case_directory("copied-export");
    let name = expected_library().file_name().unwrap().to_owned();
    let selected = root.join("debug/deps").join(&name);
    let exported = root.join("debug").join(&name);
    let other = root.join("release").join(&name);
    std::fs::create_dir_all(selected.parent().unwrap()).unwrap();
    std::fs::create_dir_all(other.parent().unwrap()).unwrap();
    let bytes = b"current copy control, not an executable backend";
    for path in [&selected, &exported, &other] {
        std::fs::write(path, bytes).unwrap();
    }
    assert_export_matches(&selected, &exported);
    assert!(std::panic::catch_unwind(|| assert_export_matches(&selected, &other)).is_err());
    std::fs::write(&exported, b"different export bytes").unwrap();
    assert!(std::panic::catch_unwind(|| assert_export_matches(&selected, &exported)).is_err());
}

#[test]
fn isolated_unit_export_requires_exact_bytes_and_its_own_profile() {
    let root = case_directory("unit-export");
    let name = expected_library().file_name().unwrap().to_owned();
    let selected = root
        .join("debug/build/rustc_codegen_trust_cg/1111111111111111/out")
        .join(&name);
    let exported = root.join("debug").join(&name);
    let other = root.join("release").join(&name);
    std::fs::create_dir_all(selected.parent().unwrap()).unwrap();
    std::fs::create_dir_all(other.parent().unwrap()).unwrap();
    let bytes = b"current unit export control, not an executable backend";
    for path in [&selected, &exported, &other] {
        std::fs::write(path, bytes).unwrap();
    }
    assert_export_matches(&selected, &exported);
    assert!(std::panic::catch_unwind(|| assert_export_matches(&selected, &other)).is_err());
    std::fs::write(&exported, b"different unit export bytes").unwrap();
    assert!(std::panic::catch_unwind(|| assert_export_matches(&selected, &exported)).is_err());
}

#[test]
fn missing_current_library_never_selects_another_profile() {
    let root = case_directory("missing");
    let name = expected_library().file_name().unwrap().to_owned();
    for profile in ["debug", "release"] {
        let directory = root.join(profile);
        std::fs::create_dir(&directory).unwrap();
        std::fs::write(directory.join(&name), b"stale profile fixture").unwrap();
    }
    let executable = root.join("custom/deps/test");
    std::fs::create_dir_all(executable.parent().unwrap()).unwrap();
    assert!(artifact::backend_for_test_executable(&executable).is_err());
    let current = executable.parent().unwrap().join(name);
    std::fs::write(&current, b"current selection fixture, not a backend").unwrap();
    assert_eq!(
        artifact::backend_for_test_executable(&executable),
        Ok(current)
    );
}

#[test]
fn invalid_executable_locations_are_refused() {
    for path in ["deps/test", "test", "/tmp/test", "/tmp/release/test"] {
        assert!(artifact::backend_for_test_executable(std::path::Path::new(path)).is_err());
    }
}

#[test]
fn empty_or_directory_library_is_refused() {
    let root = case_directory("invalid");
    let directory = root.join("deps");
    std::fs::create_dir(&directory).unwrap();
    let library = directory.join(expected_library().file_name().unwrap());
    std::fs::write(&library, b"").unwrap();
    assert!(artifact::backend_for_test_executable(&directory.join("test")).is_err());
    // Preserve the empty-file control; the next candidate is a directory.
    std::fs::rename(&library, directory.join("empty-control")).unwrap();
    std::fs::create_dir(&library).unwrap();
    assert!(artifact::backend_for_test_executable(&directory.join("test")).is_err());
}

#[cfg(unix)]
#[test]
fn symlink_library_is_refused() {
    let root = case_directory("symlink");
    let directory = root.join("deps");
    std::fs::create_dir(&directory).unwrap();
    let foreign = root.join("foreign-library");
    std::fs::write(&foreign, b"foreign selection fixture, not a backend").unwrap();
    let library = directory.join(expected_library().file_name().unwrap());
    std::os::unix::fs::symlink(foreign, library).unwrap();
    assert!(artifact::backend_for_test_executable(&directory.join("test")).is_err());
}

fn cargo_unit_case(label: &str) -> (std::path::PathBuf, std::path::PathBuf, std::path::PathBuf) {
    let root = case_directory(label);
    let package = root.join("custom/build/fixture");
    let unit = package.join("1111111111111111");
    let library_unit = package.join("2222222222222222");
    for directory in [&unit, &library_unit] {
        std::fs::create_dir_all(directory.join("out")).unwrap();
        std::fs::create_dir(directory.join("fingerprint")).unwrap();
    }
    let input = serde_json::json!({"rustc": 1, "config": 2, "compile_kind": 0,
        "deps": [[17, "rustc_codegen_trust_cg", false, 6]]});
    let dependency = serde_json::json!({"rustc": 1, "config": 2, "compile_kind": 0});
    std::fs::write(
        unit.join("fingerprint/test-integration-test-fixture.json"),
        input.to_string(),
    )
    .unwrap();
    std::fs::write(
        library_unit.join("fingerprint/lib-rustc_codegen_trust_cg"),
        "0600000000000000",
    )
    .unwrap();
    std::fs::write(
        library_unit.join("fingerprint/lib-rustc_codegen_trust_cg.json"),
        dependency.to_string(),
    )
    .unwrap();
    let library = library_unit
        .join("out")
        .join(expected_library().file_name().unwrap());
    std::fs::write(&library, b"selected fixture; not a real backend").unwrap();
    (unit.join("out/fixture-1111111111111111"), library, package)
}

#[test]
fn cargo_unit_layout_selects_the_exact_library_dependency() {
    let (test, library, package) = cargo_unit_case("unit-positive");
    // A tempting profile-level library and a different current-looking unit
    // must never replace the test's actual dependency edge.
    std::fs::write(
        package
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join(library.file_name().unwrap()),
        b"stale profile",
    )
    .unwrap();
    let other = package.join("3333333333333333");
    std::fs::create_dir_all(other.join("out")).unwrap();
    std::fs::create_dir(other.join("fingerprint")).unwrap();
    std::fs::write(
        other.join("out").join(library.file_name().unwrap()),
        b"other unit",
    )
    .unwrap();
    std::fs::write(
        other.join("fingerprint/lib-rustc_codegen_trust_cg"),
        "0700000000000000",
    )
    .unwrap();
    assert_eq!(artifact::backend_for_test_executable(&test), Ok(library));
}

#[test]
fn cargo_unit_layout_refuses_missing_ambiguous_or_malformed_dependencies() {
    for (label, deps) in [
        ("missing", serde_json::json!([])),
        (
            "duplicate",
            serde_json::json!([
                [17, "rustc_codegen_trust_cg", false, 6],
                [17, "rustc_codegen_trust_cg", false, 6]
            ]),
        ),
        (
            "wrong-name",
            serde_json::json!([[17, "other_backend", false, 6]]),
        ),
        (
            "wrong-hash",
            serde_json::json!([[17, "rustc_codegen_trust_cg", false, 7]]),
        ),
        (
            "wrong-shape",
            serde_json::json!([[17, "rustc_codegen_trust_cg", false, 6, 0]]),
        ),
        (
            "wrong-type",
            serde_json::json!([[17, "rustc_codegen_trust_cg", false, "6"]]),
        ),
    ] {
        let (test, _, _) = cargo_unit_case(label);
        let descriptor = test
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("fingerprint/test-integration-test-fixture.json");
        let mut value: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&descriptor).unwrap()).unwrap();
        value["deps"] = deps;
        std::fs::write(descriptor, value.to_string()).unwrap();
        assert!(
            artifact::backend_for_test_executable(&test).is_err(),
            "{label}"
        );
    }
}

#[test]
fn cargo_unit_layout_refuses_identity_drift_and_duplicate_library_units() {
    for key in ["rustc", "config", "compile_kind"] {
        let (test, library, _) = cargo_unit_case(key);
        let descriptor = library
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("fingerprint/lib-rustc_codegen_trust_cg.json");
        let mut value: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&descriptor).unwrap()).unwrap();
        value[key] = serde_json::json!(100);
        std::fs::write(descriptor, value.to_string()).unwrap();
        assert!(
            artifact::backend_for_test_executable(&test).is_err(),
            "{key}"
        );
    }
    let (test, library, package) = cargo_unit_case("duplicate-library");
    let duplicate = package.join("3333333333333333");
    std::fs::create_dir_all(duplicate.join("out")).unwrap();
    std::fs::create_dir(duplicate.join("fingerprint")).unwrap();
    for name in [
        "lib-rustc_codegen_trust_cg",
        "lib-rustc_codegen_trust_cg.json",
    ] {
        std::fs::copy(
            library
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("fingerprint")
                .join(name),
            duplicate.join("fingerprint").join(name),
        )
        .unwrap();
    }
    std::fs::copy(
        &library,
        duplicate.join("out").join(library.file_name().unwrap()),
    )
    .unwrap();
    assert!(artifact::backend_for_test_executable(&test).is_err());
}

#[test]
fn cargo_unit_layout_refuses_corrupt_metadata_and_invalid_artifacts() {
    for case in [
        "malformed-json",
        "bad-fingerprint",
        "empty-library",
        "directory-library",
    ] {
        let (test, library, _) = cargo_unit_case(case);
        let fingerprint = library
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("fingerprint");
        match case {
            "malformed-json" => std::fs::write(
                fingerprint.join("lib-rustc_codegen_trust_cg.json"),
                b"{bad json",
            )
            .unwrap(),
            "bad-fingerprint" => std::fs::write(
                fingerprint.join("lib-rustc_codegen_trust_cg"),
                b"not a hash",
            )
            .unwrap(),
            "empty-library" => std::fs::write(&library, b"").unwrap(),
            "directory-library" => {
                std::fs::rename(&library, library.with_extension("retained-control")).unwrap();
                std::fs::create_dir(&library).unwrap();
            }
            _ => unreachable!(),
        }
        assert!(
            artifact::backend_for_test_executable(&test).is_err(),
            "{case}"
        );
    }
}
