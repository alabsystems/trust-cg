// Regression tests for layout-sensitive kernel fixture selection.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[path = "../fixture_toolchain.rs"]
mod fixture_toolchain;

use fixture_toolchain::{
    FixtureToolchain, classify_fixture_toolchain, has_ae9_linux_kernel_fixtures,
    kernel_fixture_layout_cfg, qualifies_current_kernel_fixtures,
};

#[test]
fn linux_kernel_fixtures_require_their_exact_compiler_and_target() {
    let version = "rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)";
    assert!(has_ae9_linux_kernel_fixtures(
        &format!("{version}\n"),
        "aarch64-unknown-linux-gnu"
    ));
    for target in ["aarch64-apple-darwin", "x86_64-unknown-linux-gnu", ""] {
        assert!(!has_ae9_linux_kernel_fixtures(version, target));
    }
    for version in [
        "rustc 1.99.0-dev (012345678 2026-09-21) (trustc 0.1.0)",
        "rustc 1.99.0-dev (ae9c2c1da 2026-09-21)",
        "rustc 1.97.1 (8bab26f4f 2026-07-14)",
        "",
    ] {
        assert!(!has_ae9_linux_kernel_fixtures(
            version,
            "aarch64-unknown-linux-gnu"
        ));
    }
}

#[test]
fn linux_qualification_does_not_change_legacy_layout_selection() {
    assert_eq!(
        classify_fixture_toolchain("rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)"),
        FixtureToolchain::Unsupported
    );
}

#[test]
fn current_corpus_qualification_requires_its_exact_compiler_and_target() {
    let version = "rustc 1.99.0-dev (450403669 2026-09-24) (trustc 0.10.0+g450403669)";
    assert!(qualifies_current_kernel_fixtures(
        &format!("{version}\n"),
        "aarch64-apple-darwin"
    ));
    for target in ["aarch64-unknown-linux-gnu", "x86_64-apple-darwin", ""] {
        assert!(!qualifies_current_kernel_fixtures(version, target));
    }
    for version in [
        "rustc 1.99.0-dev (450403669 2026-09-24)",
        "rustc 1.99.0-dev (450403669 2026-09-24) (trustc 0.10.0)",
        "rustc 1.99.0-dev (012345678 2026-09-24) (trustc 0.10.0+g450403669)",
        "rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)",
        "rustc 1.97.1 (8bab26f4f 2026-07-14)",
        "",
    ] {
        assert!(
            !qualifies_current_kernel_fixtures(version, "aarch64-apple-darwin"),
            "qualified {version:?}"
        );
    }
    // The qualification selects the current corpus beside the legacy
    // selector; it does not change what that selector returns.
    assert_eq!(
        classify_fixture_toolchain(version),
        FixtureToolchain::Unsupported
    );
}

#[test]
fn qualified_current_layout_selection_requires_the_exact_build_and_darwin_host() {
    for version in [
        "rustc 1.101.0-dev (c6d3ebc20 2026-10-27) (trustc 0.11.0+gc6d3ebc20)",
        "rustc 1.101.0-dev (d460ce139 2026-10-28) (trustc 0.12.0+gd460ce139)",
        "rustc 1.101.0-dev (29ebb403d 2026-10-28) (trustc 0.12.0+g29ebb403d)",
    ] {
        for lint_driver in [false, true] {
            assert_eq!(
                kernel_fixture_layout_cfg(version, "aarch64-apple-darwin", lint_driver),
                "kernel_fixture_layout_current"
            );
        }
        for target in ["aarch64-unknown-linux-gnu", "x86_64-apple-darwin", ""] {
            assert!(!qualifies_current_kernel_fixtures(version, target));
            assert_eq!(
                kernel_fixture_layout_cfg(version, target, false),
                "kernel_fixture_layout_unknown"
            );
        }
        let (compiler, _) = version.split_once(" (trustc ").unwrap();
        let (trust_version, _) = version.split_once("+g").unwrap();
        let commit = version.split_whitespace().nth(2).unwrap();
        for changed in [
            compiler.to_owned(),
            format!("{trust_version})"),
            version.replace(" (trustc ", " (rustc "),
            version.replacen(commit, "(012345678", 1),
            version.replace("2026-10-", "2026-11-"),
            format!("{version}x"),
        ] {
            assert!(!qualifies_current_kernel_fixtures(
                &changed,
                "aarch64-apple-darwin"
            ));
            assert_eq!(
                kernel_fixture_layout_cfg(&changed, "aarch64-apple-darwin", false),
                "kernel_fixture_layout_unknown"
            );
        }
        assert_eq!(
            classify_fixture_toolchain(version),
            FixtureToolchain::Unsupported
        );
    }
}

/// `build.rs` emits exactly this cfg. A lint driver in front of a certified
/// or exactly qualified compiler must not demote it to the lint-only cfg,
/// and only an uncertified compiler under a lint driver gets that cfg.
#[test]
fn build_script_cfg_keeps_a_qualified_compiler_ahead_of_the_lint_only_arm() {
    let qualified = "rustc 1.99.0-dev (450403669 2026-09-24) (trustc 0.10.0+g450403669)";
    for lint_driver in [false, true] {
        assert_eq!(
            kernel_fixture_layout_cfg(qualified, "aarch64-apple-darwin", lint_driver),
            "kernel_fixture_layout_current",
            "lint_driver={lint_driver}"
        );
        assert_eq!(
            kernel_fixture_layout_cfg(
                "rustc 1.95.0 (59807616e 2026-04-14)",
                "aarch64-apple-darwin",
                lint_driver
            ),
            "kernel_fixture_layout_matches"
        );
        for certified in [
            "rustc 1.97.1 (8bab26f4f 2026-07-14)",
            "rustc 1.96.0-dev (94d61d9b6 2026-06-15)",
            "rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc 0.1.0)",
        ] {
            assert_eq!(
                kernel_fixture_layout_cfg(certified, "aarch64-apple-darwin", lint_driver),
                "kernel_fixture_layout_current",
                "{certified} lint_driver={lint_driver}"
            );
        }
    }
    // The same compiler on a target it did not qualify is uncertified there.
    assert_eq!(
        kernel_fixture_layout_cfg(qualified, "aarch64-unknown-linux-gnu", false),
        "kernel_fixture_layout_unknown"
    );
    assert_eq!(
        kernel_fixture_layout_cfg(qualified, "aarch64-unknown-linux-gnu", true),
        "kernel_fixture_layout_lint_only"
    );
    let uncertified = "rustc 1.99.0-dev (012345678 2026-09-24) (trustc 0.10.0+g012345678)";
    assert_eq!(
        kernel_fixture_layout_cfg(uncertified, "aarch64-apple-darwin", false),
        "kernel_fixture_layout_unknown"
    );
    assert_eq!(
        kernel_fixture_layout_cfg(uncertified, "aarch64-apple-darwin", true),
        "kernel_fixture_layout_lint_only"
    );
}

#[test]
fn exact_rust_1_95_identity_selects_frozen_fixture() {
    assert_eq!(
        classify_fixture_toolchain("rustc 1.95.0 (59807616e 2026-04-14)\n"),
        FixtureToolchain::Rust195
    );
}

#[test]
fn pinned_rust_1_97_selects_regenerated_fixture() {
    assert_eq!(
        classify_fixture_toolchain("rustc 1.97.1 (8bab26f4f 2026-07-14)\n"),
        FixtureToolchain::Current
    );
}

#[test]
fn exact_trust_compiler_selects_regenerated_fixture() {
    assert_eq!(
        classify_fixture_toolchain("rustc 1.96.0-dev (94d61d9b6 2026-06-15)"),
        FixtureToolchain::Current
    );
}

#[test]
fn installed_trust_compiler_selects_the_qualified_current_fixture() {
    assert_eq!(
        classify_fixture_toolchain("rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc 0.1.0)\n"),
        FixtureToolchain::Current
    );
    // Only that exact build: another commit or a missing Trust suffix is not it.
    for version in [
        "rustc 1.99.0-dev (321aaeda8 2026-09-17) (trustc 0.1.0)",
        "rustc 1.99.0-dev (321aaeda7 2026-09-17)",
        "rustc 1.99.0-dev (321aaeda7 2026-09-18) (trustc 0.1.0)",
    ] {
        assert_eq!(
            classify_fixture_toolchain(version),
            FixtureToolchain::Unsupported,
            "accepted {version}"
        );
    }
}

#[test]
fn uncertified_compilers_are_unsupported() {
    for version in [
        "rustc 1.99.0-nightly (012345678 2026-07-22)",
        "rustc 1.99.0-dev (012345678 2026-07-22)",
        "rustc 1.98.0 (012345678 2026-08-01)",
    ] {
        assert_eq!(
            classify_fixture_toolchain(version),
            FixtureToolchain::Unsupported,
            "accepted {version}"
        );
    }
}

#[test]
fn missing_or_malformed_compiler_output_fails_closed() {
    for version in ["", "rustc", "1.95.0", "rustc 1.95.0"] {
        assert_eq!(
            classify_fixture_toolchain(version),
            FixtureToolchain::Unsupported,
            "accepted {version:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Lint-driver detection
//
// `build.rs` relaxes the layout-fixture guard to a LINT-ONLY cfg when a lint
// driver is in front of an uncertified compiler, because such a driver
// type-checks and links no test binary. That relaxation is only as sound as
// this predicate: a false positive would compile the layout-sensitive targets
// on a compiler that can actually run them.
// ---------------------------------------------------------------------------

use fixture_toolchain::lint_driver_from;

#[test]
fn a_lint_driver_is_recognised_by_file_stem() {
    for wrapper in [
        "$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/tippy-driver",
        "$HOME/.rustup/toolchains/1.97.1-aarch64-apple-darwin/bin/clippy-driver",
        "clippy-driver",
        "tippy-driver",
    ] {
        assert!(
            lint_driver_from([Some(wrapper.to_string())]),
            "did not recognise {wrapper}"
        );
    }
}

/// The ordinary build path sets NEITHER wrapper — measured on this machine for
/// `targo check` and `cargo build`. That absence is what keeps a real build
/// fail-closed, so it is pinned rather than assumed.
#[test]
fn an_ordinary_build_sets_no_lint_driver() {
    assert!(!lint_driver_from([None, None]));
    assert!(!lint_driver_from([]));
}

/// A FALSE POSITIVE here would compile a frozen `repr(Rust)` layout fixture on
/// a compiler that can execute it. The predicate matches the executable's file
/// stem, so neither a checkout that merely lives under a directory of that
/// name, nor an unrelated wrapper (sccache and friends), is mistaken for one.
#[test]
fn nothing_but_a_lint_driver_counts() {
    for wrapper in [
        "/home/ci/clippy-driver/bin/rustc",
        "/opt/tippy-driver/wrapper",
        "/usr/local/bin/sccache",
        "/usr/bin/rustc",
        "clippy-driver-wrapper",
        "my-clippy-driver",
        "",
    ] {
        assert!(
            !lint_driver_from([Some(wrapper.to_string())]),
            "wrongly treated {wrapper:?} as a lint driver"
        );
    }
}

/// Either wrapper variable can carry the driver, and one set alongside an
/// empty other must still be seen.
#[test]
fn either_wrapper_variable_carries_the_driver() {
    assert!(lint_driver_from([
        Some("/x/bin/tippy-driver".to_string()),
        None
    ]));
    assert!(lint_driver_from([
        None,
        Some("/x/bin/clippy-driver".to_string())
    ]));
}
