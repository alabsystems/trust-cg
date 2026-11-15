// Tests for the AY identity rule (`ay_identity.rs`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;

/// Measured `--version` output of the Trust 9178 bundle's `bin/ay`
/// (`aterm/pkg/store/trust/9178/bin/ay`, 2026-09-17).
const BUNDLE_9178_BANNER: &str =
    "ay 0.26.0+build.9624.075a482aec84e441918d935743957876bd24afdb@2026-09-16T06:27:30Z
build.version=0.26.0
build.increment=9624
build.commit=075a482aec84e441918d935743957876bd24afdb
build.datetime_utc=2026-09-16T06:27:30Z
build.stamp=0.26.0+build.9624.075a482aec84e441918d935743957876bd24afdb@2026-09-16T06:27:30Z
";

/// Measured `--version` output of aterm's managed `store/ay/8256/bin/ay` — the
/// binary the plugin's solver-coupled tests actually ran before this rule.
const MANAGED_8256_BANNER: &str =
    "ay 0.13.0+build.8256.dd4de9e94e0bb94a458641c7e5aa814c8aeadf59@2026-08-21T02:14:15Z
build.version=0.13.0
build.increment=8256
build.commit=dd4de9e94e0bb94a458641c7e5aa814c8aeadf59
build.datetime_utc=2026-08-21T02:14:15Z
build.stamp=0.13.0+build.8256.dd4de9e94e0bb94a458641c7e5aa814c8aeadf59@2026-08-21T02:14:15Z
";

fn pinned_build() -> AyBuildIdentity {
    parse_ay_version_banner(BUNDLE_9178_BANNER).unwrap()
}

fn managed_build() -> AyBuildIdentity {
    parse_ay_version_banner(MANAGED_8256_BANNER).unwrap()
}

fn exe(name: &str) -> String {
    format!("{name}{}", std::env::consts::EXE_SUFFIX)
}

#[test]
fn banner_parses_the_measured_bundle_and_managed_banners() {
    let bundle = pinned_build();
    assert_eq!(bundle.commit(), "075a482aec84e441918d935743957876bd24afdb");
    assert_eq!(bundle.version(), "0.26.0");
    assert_eq!(bundle.increment(), "9624");
    let managed = managed_build();
    assert_eq!(managed.commit(), "dd4de9e94e0bb94a458641c7e5aa814c8aeadf59");
    assert_ne!(bundle, managed);
    // Same commit built at another time parses to the same build LABEL. The
    // label is not what admission compares: the bytes are (see below).
    let restamped = BUNDLE_9178_BANNER.replace("2026-09-16T06:27:30Z", "2026-09-14T17:34:33Z");
    assert_eq!(parse_ay_version_banner(&restamped).unwrap(), bundle);
}

#[test]
fn banner_without_a_complete_clean_self_consistent_identity_is_refused() {
    let cases = [
        ("empty output", String::new()),
        ("a non-AY tool", "clean 1.2.3\n".to_owned()),
        ("the old fixture banner", "ay fixture\n".to_owned()),
        (
            "missing commit",
            BUNDLE_9178_BANNER.replace(
                "build.commit=075a482aec84e441918d935743957876bd24afdb\n",
                "",
            ),
        ),
        (
            "duplicated commit",
            format!("{BUNDLE_9178_BANNER}build.commit=075a482aec84e441918d935743957876bd24afdb\n"),
        ),
        (
            "dirty commit",
            BUNDLE_9178_BANNER.replace(
                "build.commit=075a482aec84e441918d935743957876bd24afdb",
                "build.commit=075a482aec84e441918d935743957876bd24afdb-dirty",
            ),
        ),
        (
            "short commit",
            BUNDLE_9178_BANNER.replace(
                "build.commit=075a482aec84e441918d935743957876bd24afdb",
                "build.commit=075a482ae",
            ),
        ),
        (
            "stamp from another build",
            BUNDLE_9178_BANNER.replace(
                "build.stamp=0.26.0+build.9624.075a482aec84e441918d935743957876bd24afdb@",
                "build.stamp=0.13.0+build.8256.dd4de9e94e0bb94a458641c7e5aa814c8aeadf59@",
            ),
        ),
        (
            "non-numeric increment",
            BUNDLE_9178_BANNER
                .replace("build.increment=9624", "build.increment=x")
                .replace("+build.9624.", "+build.x."),
        ),
        (
            // Measured: AY built from a `git archive` export with
            // AY_SOURCE_GIT_COMMIT set reports build 0 and that commit.
            "unnumbered build",
            BUNDLE_9178_BANNER
                .replace("build.increment=9624", "build.increment=0")
                .replace("+build.9624.", "+build.0."),
        ),
        (
            "unnumbered build with padding",
            BUNDLE_9178_BANNER
                .replace("build.increment=9624", "build.increment=00")
                .replace("+build.9624.", "+build.00."),
        ),
    ];
    for (name, banner) in cases {
        assert!(
            parse_ay_version_banner(&banner).is_err(),
            "{name} must not identify an AY build"
        );
    }
}

#[test]
fn a_recorded_identity_needs_a_well_formed_digest() {
    for digest in ["", "075a482ae", &"A".repeat(64), &"g".repeat(64)] {
        assert!(
            AyIdentity::recorded(
                digest,
                pinned_build().commit(),
                pinned_build().version(),
                pinned_build().increment(),
            )
            .is_err(),
            "{digest:?} is not a SHA-256"
        );
    }
}

/// `<root>/<name>` laid out as a Rust sysroot: `bin/trustc` and `lib/rustlib`.
fn sysroot_layout(root: &Path, name: &str) -> PathBuf {
    let sysroot = root.join(name);
    std::fs::create_dir_all(sysroot.join("bin")).unwrap();
    std::fs::create_dir_all(sysroot.join("lib").join("rustlib")).unwrap();
    std::fs::write(sysroot.join("bin").join(exe("trustc")), b"compiler").unwrap();
    sysroot
}

#[test]
fn only_the_compiler_driver_of_a_rust_sysroot_hosts_the_toolchain() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let sysroot = sysroot_layout(root, "sysroot");
    let bin = sysroot.join("bin");
    std::fs::write(bin.join(exe("rustc")), b"compiler alias").unwrap();
    assert_eq!(
        hosting_compiler_sysroot(&bin.join(exe("trustc"))),
        Some(sysroot.clone())
    );
    assert_eq!(
        hosting_compiler_sysroot(&bin.join(exe("rustc"))),
        Some(sysroot.clone())
    );
    assert_eq!(
        hosting_compiler_sysroot(&bin.join(exe("targo-trust"))),
        None,
        "a tool that is not the compiler driver is not hosted by the compiler"
    );
    assert_eq!(
        hosting_compiler_sysroot(&bin.join(exe("ay"))),
        None,
        "AY is never its own host"
    );
    // The measured round-4 hole: any `bin/` holding a file named `rustc`
    // counted, so a program copied next to a fake `rustc` and a fake `ay` was
    // "hosted". Without `lib/rustlib` there is no sysroot, whatever the names.
    let fake = root.join("hostlayout").join("bin");
    std::fs::create_dir_all(&fake).unwrap();
    std::fs::write(fake.join(exe("rustc")), b"#!/bin/sh\n").unwrap();
    std::fs::write(fake.join(exe("ay")), b"#!/bin/sh\n").unwrap();
    assert_eq!(
        hosting_compiler_sysroot(&fake.join(exe("ayid-probe"))),
        None
    );
    assert_eq!(hosting_compiler_sysroot(&fake.join(exe("rustc"))), None);
    // A cargo test harness is not in a sysroot.
    let deps = root.join("target/debug/deps");
    std::fs::create_dir_all(&deps).unwrap();
    std::fs::write(deps.join(exe("trustc")), b"not a sysroot").unwrap();
    assert_eq!(hosting_compiler_sysroot(&deps.join(exe("harness"))), None);
    assert_eq!(hosting_compiler_sysroot(&deps.join(exe("trustc"))), None);
}

#[cfg(unix)]
mod executable_fixtures {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    /// A distinct executable per `label`. Running it (any argument) records a
    /// marker next to it and fails, so a test can prove it was never started.
    pub(super) fn write_ay(path: &Path, label: &str) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(
            path,
            test_fixtures::bind_self(
                path,
                &format!("#!/bin/sh\n# {label}\n: > \"$0.executed\"\nexit 70\n"),
            ),
        )
        .unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    /// A script that prints `banner` for `--version`: the round-4 decoy.
    fn write_banner_script(path: &Path, banner: &str) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(
            path,
            test_fixtures::bind_self(
                path,
                &format!(
                    "#!/bin/sh\n: > \"$0.executed\"\nif [ \"$1\" = --version ]; then cat <<'EOF'\n{banner}EOF\nexit 0; fi\nexit 70\n"
                ),
            ),
        )
        .unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    fn executed(path: &Path) -> bool {
        let mut marker = path.as_os_str().to_owned();
        marker.push(".executed");
        Path::new(&marker).exists()
    }

    fn digest(path: &Path) -> String {
        digest_file(path).unwrap().0
    }

    /// The pinned AY: `label`'s bytes, labelled with the 9178 build banner.
    fn pinned_identity(path: &Path) -> AyIdentity {
        AyIdentity {
            sha256: digest(path),
            build: Some(pinned_build()),
            overlay: None,
        }
    }

    /// `<root>/<name>` as a Rust sysroot whose `bin/ay` has `label`'s bytes
    /// (no `bin/ay` when `label` is `None`).
    fn toolchain(root: &Path, name: &str, label: Option<&str>) -> PathBuf {
        let sysroot = sysroot_layout(root, name);
        if let Some(label) = label {
            write_ay(&sysroot.join("bin").join(exe("ay")), label);
        }
        sysroot
    }

    fn ay_of(sysroot: &Path) -> PathBuf {
        sysroot.join("bin").join(exe("ay"))
    }

    fn harness(root: &Path) -> PathBuf {
        root.join("target/debug/deps").join(exe("harness"))
    }

    fn resolve_process(
        running_exe: Option<&Path>,
        record: &ToolchainAyRecord,
        override_value: Option<&OsStr>,
    ) -> Result<PinnedAy, AyIdentityRefusal> {
        resolve(ResolutionInputs {
            running_exe,
            record,
            naming: Naming::Process(override_value),
        })
    }

    fn resolve_explicit(
        record: &ToolchainAyRecord,
        value: &OsStr,
    ) -> Result<PinnedAy, AyIdentityRefusal> {
        resolve(ResolutionInputs {
            running_exe: None,
            record,
            naming: Naming::Explicit(value),
        })
    }

    #[test]
    fn toolchain_ay_with_the_recorded_bytes_is_admitted_without_being_run() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "bundle", Some("pinned ay bytes"));
        let expected = pinned_identity(&ay_of(&sysroot));
        let record = ToolchainAyRecord::new(sysroot.clone(), Ok(expected.clone()));
        let admitted = resolve_process(Some(&harness(root)), &record, None).unwrap();
        assert_eq!(admitted.path(), ay_of(&sysroot));
        assert_eq!(admitted.route(), AyRoute::ToolchainSysroot);
        assert_eq!(admitted.sysroot(), Some(sysroot.as_path()));
        assert_eq!(
            admitted.sysroot_source(),
            Some(SysrootSource::BuildCompiler)
        );
        assert_eq!(admitted.identity(), &expected);
        assert_eq!(admitted.sha256(), digest(&ay_of(&sysroot)));
        let described = admitted.describe();
        assert!(
            described.contains("route=toolchain-pinned-ay"),
            "{described}"
        );
        assert!(described.contains(expected.sha256()), "{described}");
        assert!(described.contains(pinned_build().commit()), "{described}");
        assert!(
            !executed(&ay_of(&sysroot)),
            "admission compares bytes; it must not execute the candidate"
        );
    }

    fn overlay_fixture() -> ToolchainOverlay {
        ToolchainOverlay::new(&"1".repeat(64), &"2".repeat(64), &"3".repeat(40)).unwrap()
    }

    /// An overlay build admits by the same digest rule and route, and names
    /// the overlay manifest, its Clean digest and Clean commit wherever the
    /// AY identity is described (verdict provenance, reports).
    #[test]
    fn an_overlay_record_admits_by_digest_and_names_the_overlay_in_provenance() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "overlay", Some("overlay ay bytes"));
        let overlay = overlay_fixture();
        let record = ToolchainAyRecord::new_overlay(
            sysroot.clone(),
            Ok(pinned_identity(&ay_of(&sysroot))),
            Some(overlay.clone()),
        );
        assert_eq!(record.overlay(), Some(&overlay));
        assert_eq!(record.pinned_clean_sha256(), Some("2".repeat(64).as_str()));
        let admitted = resolve_process(Some(&harness(root)), &record, None).unwrap();
        assert_eq!(admitted.route(), AyRoute::ToolchainSysroot);
        assert_eq!(admitted.identity().overlay(), Some(&overlay));
        let described = admitted.describe();
        assert!(
            described.contains("route=toolchain-pinned-ay"),
            "{described}"
        );
        for needle in [
            format!("manifest-sha256 {}", "1".repeat(64)),
            format!("clean-sha256 {}", "2".repeat(64)),
            format!("clean-commit {}", "3".repeat(40)),
        ] {
            assert!(described.contains(&needle), "{described}");
        }
        // An installed toolchain's record names no overlay and pins no checker.
        let plain = ToolchainAyRecord::new(sysroot.clone(), Ok(pinned_identity(&ay_of(&sysroot))));
        assert_eq!(plain.overlay(), None);
        assert_eq!(plain.pinned_clean_sha256(), None);
        assert!(!plain.expected().unwrap().describe().contains("overlay"));
    }

    /// A refused overlay manifest records no AY and pins the empty checker
    /// digest, which no file has.
    #[test]
    fn a_refused_overlay_admits_no_ay_and_no_checker() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "overlay", Some("overlay ay bytes"));
        let record = ToolchainAyRecord::new_overlay(
            sysroot.clone(),
            Ok(pinned_identity(&ay_of(&sysroot))),
            None,
        );
        assert!(record.expected().is_err());
        assert_eq!(record.pinned_clean_sha256(), Some(""));
        let refusal = resolve_process(Some(&harness(root)), &record, None).unwrap_err();
        assert_eq!(refusal.code(), "TCG-AY-IDENTITY-UNRECORDED");
        // Malformed recorded overlay fields are refused the same way.
        assert_eq!(
            overlay_record("valid", "short", &"2".repeat(64), &"3".repeat(40)),
            OverlayRecord::Invalid
        );
        assert_eq!(
            overlay_record("invalid", "", "", ""),
            OverlayRecord::Invalid
        );
        assert_eq!(overlay_record("", "", "", ""), OverlayRecord::None);
    }

    /// The round-4 residual, measured in `trustc`: a shell script at the
    /// candidate path that prints the pinned `--version` banner was admitted.
    /// Its bytes are not the recorded AY, so it is refused — and never run.
    #[test]
    fn a_script_printing_the_pinned_banner_is_refused_and_never_run() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let real = root.join("real").join(exe("ay"));
        write_ay(&real, "the real pinned ay");
        let record = ToolchainAyRecord::new(root.join("unused"), Ok(pinned_identity(&real)));

        let decoy_sysroot = sysroot_layout(root, "decoy-toolchain");
        let decoy = ay_of(&decoy_sysroot);
        write_banner_script(&decoy, BUNDLE_9178_BANNER);
        let override_decoy = root.join("override").join(exe("ay"));
        write_banner_script(&override_decoy, BUNDLE_9178_BANNER);

        for (route, result) in [
            (
                AyRoute::ToolchainSysroot,
                resolve_process(
                    Some(&decoy_sysroot.join("bin").join(exe("trustc"))),
                    &record,
                    None,
                ),
            ),
            (
                AyRoute::EnvironmentOverride,
                resolve_process(None, &record, Some(override_decoy.as_os_str())),
            ),
            (
                AyRoute::ExplicitPath,
                resolve_explicit(&record, override_decoy.as_os_str()),
            ),
        ] {
            let refusal = result.unwrap_err();
            assert!(
                matches!(&refusal, AyIdentityRefusal::Mismatch { route: found_route, found_sha256, .. }
                    if *found_route == route && found_sha256 != record.expected().unwrap().sha256()),
                "{route:?}: {refusal}"
            );
            assert_eq!(refusal.code(), "TCG-AY-IDENTITY-MISMATCH");
        }
        assert!(!executed(&decoy), "a refused candidate is never started");
        assert!(
            !executed(&override_decoy),
            "a refused candidate is never started"
        );
    }

    /// The original defect: the managed 8256 AY where the toolchain's AY is
    /// recorded. Refused by name, with both digests and the recorded build.
    #[test]
    fn different_ay_bytes_are_refused_naming_both_digests() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let real = root.join("real").join(exe("ay"));
        write_ay(&real, "the real pinned ay");
        let expected = pinned_identity(&real);
        let sysroot = toolchain(root, "bundle", Some("managed 8256 ay"));
        let record = ToolchainAyRecord::new(sysroot.clone(), Ok(expected.clone()));
        let refusal = resolve_process(Some(&harness(root)), &record, None).unwrap_err();
        assert_eq!(
            refusal,
            AyIdentityRefusal::Mismatch {
                route: AyRoute::ToolchainSysroot,
                path: ay_of(&sysroot),
                expected: Box::new(expected.clone()),
                found_sha256: digest(&ay_of(&sysroot)),
            }
        );
        let message = refusal.to_string();
        assert!(
            message.starts_with("[TCG-AY-IDENTITY-MISMATCH]"),
            "{message}"
        );
        assert!(message.contains(expected.sha256()), "{message}");
        assert!(message.contains(&digest(&ay_of(&sysroot))), "{message}");
        assert!(message.contains(pinned_build().commit()), "{message}");
    }

    /// The compiler hosting the process wins over the one that built the
    /// crate. The control is the SAME record resolved without a hosting
    /// compiler, which must reach the other (different-bytes) toolchain.
    #[test]
    fn hosting_compiler_toolchain_is_used_instead_of_the_build_toolchain() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let host = toolchain(root, "host", Some("pinned ay bytes"));
        let build = toolchain(root, "build", Some("another ay build"));
        let record = ToolchainAyRecord::new(build.clone(), Ok(pinned_identity(&ay_of(&host))));
        let trustc = host.join("bin").join(exe("trustc"));

        let admitted = resolve_process(Some(&trustc), &record, None).unwrap();
        assert_eq!(admitted.sysroot(), Some(host.as_path()));
        assert_eq!(
            admitted.sysroot_source(),
            Some(SysrootSource::HostingCompiler)
        );
        assert_eq!(admitted.path(), ay_of(&host));

        let control = resolve_process(None, &record, None).unwrap_err();
        assert!(
            matches!(&control, AyIdentityRefusal::Mismatch { path, .. } if path == &ay_of(&build)),
            "control must reach the build toolchain: {control}"
        );
    }

    /// A hosting toolchain whose AY has other bytes is refused; the build
    /// toolchain's matching AY is NOT substituted.
    #[test]
    fn hosting_toolchain_mismatch_does_not_fall_back_to_the_build_toolchain() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let host = toolchain(root, "host", Some("another ay build"));
        let build = toolchain(root, "build", Some("pinned ay bytes"));
        let record = ToolchainAyRecord::new(build.clone(), Ok(pinned_identity(&ay_of(&build))));
        let refusal = resolve_process(Some(&host.join("bin").join(exe("trustc"))), &record, None)
            .unwrap_err();
        assert!(
            matches!(&refusal, AyIdentityRefusal::Mismatch { path, .. } if path == &ay_of(&host)),
            "{refusal}"
        );
    }

    /// The round-4 host-layout hole, end to end: a program copied into a `bin/`
    /// next to a fake `rustc` and an `ay` holding the PINNED bytes is not hosted
    /// there, so the rule still names the build toolchain's AY.
    #[test]
    fn a_program_next_to_a_file_named_rustc_is_not_hosted_by_it() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let build = toolchain(root, "build", Some("pinned ay bytes"));
        let record = ToolchainAyRecord::new(build.clone(), Ok(pinned_identity(&ay_of(&build))));
        let layout = root.join("hostlayout").join("bin");
        std::fs::create_dir_all(&layout).unwrap();
        std::fs::write(layout.join(exe("rustc")), b"#!/bin/sh\n").unwrap();
        std::fs::copy(ay_of(&build), layout.join(exe("ay"))).unwrap();
        for running in [layout.join(exe("ayid-probe")), layout.join(exe("rustc"))] {
            let admitted = resolve_process(Some(&running), &record, None).unwrap();
            assert_eq!(admitted.path(), ay_of(&build), "{}", running.display());
            assert_eq!(
                admitted.sysroot_source(),
                Some(SysrootSource::BuildCompiler)
            );
        }
    }

    #[test]
    fn toolchain_without_ay_is_refused_and_nothing_else_is_searched() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "bundle", None);
        let pinned_source = root.join("pinned").join(exe("ay"));
        write_ay(&pinned_source, "pinned ay bytes");
        // The PINNED bytes everywhere the old discovery looked. They can only
        // matter if the rule searches the disk.
        for decoy in [
            "home/Library/Application Support/aterm/pkg/store/ay/current/bin/ay",
            "path-bin/ay",
            "home/trust/build/aarch64-apple-darwin/stage2/bin/ay",
            "home/ay/target/release/ay",
            "target/debug/deps/ay",
        ] {
            let path = root.join(decoy);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::copy(&pinned_source, &path).unwrap();
        }
        let record = ToolchainAyRecord::new(sysroot.clone(), Ok(pinned_identity(&pinned_source)));
        let refusal = resolve_process(Some(&harness(root)), &record, None).unwrap_err();
        assert_eq!(
            refusal,
            AyIdentityRefusal::ToolchainAyMissing {
                sysroot: sysroot.clone(),
                sysroot_source: SysrootSource::BuildCompiler,
                path: ay_of(&sysroot),
            }
        );
    }

    #[test]
    fn unreadable_ay_is_refused_as_unidentified() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "bundle", Some("pinned ay bytes"));
        let expected = pinned_identity(&ay_of(&sysroot));
        // Execute-only: a name the OS would run but whose bytes cannot be read.
        std::fs::set_permissions(ay_of(&sysroot), std::fs::Permissions::from_mode(0o111)).unwrap();
        let record = ToolchainAyRecord::new(sysroot.clone(), Ok(expected));
        let refusal = resolve_process(Some(&harness(root)), &record, None).unwrap_err();
        std::fs::set_permissions(ay_of(&sysroot), std::fs::Permissions::from_mode(0o755)).unwrap();
        assert!(
            matches!(&refusal, AyIdentityRefusal::Unidentified { path, .. } if path == &ay_of(&sysroot)),
            "{refusal}"
        );
        assert_eq!(refusal.code(), "TCG-AY-IDENTITY-UNIDENTIFIED");
    }

    #[test]
    fn unrecorded_identity_admits_nothing_on_any_route() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "bundle", Some("pinned ay bytes"));
        let record = ToolchainAyRecord::new(
            sysroot.clone(),
            Err("the build compiler's sysroot ships no AY".to_owned()),
        );
        trust_cg_process_env::with_env_overrides_removed(
            &[test_fixtures::FIXTURE_DIGESTS_ENV],
            || {
                for override_value in [None, Some(ay_of(&sysroot).into_os_string())] {
                    let refusal =
                        resolve_process(Some(&harness(root)), &record, override_value.as_deref())
                            .unwrap_err();
                    assert_eq!(refusal.code(), "TCG-AY-IDENTITY-UNRECORDED", "{refusal}");
                }
                let refusal = resolve_explicit(&record, ay_of(&sysroot).as_os_str()).unwrap_err();
                assert_eq!(refusal.code(), "TCG-AY-IDENTITY-UNRECORDED", "{refusal}");
            },
        );
    }

    #[test]
    fn a_copy_of_the_recorded_bytes_elsewhere_is_admitted_on_its_route() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "bundle", Some("pinned ay bytes"));
        let record = ToolchainAyRecord::new(sysroot.clone(), Ok(pinned_identity(&ay_of(&sysroot))));
        let copy = root.join("elsewhere").join(exe("ay"));
        std::fs::create_dir_all(copy.parent().unwrap()).unwrap();
        std::fs::copy(ay_of(&sysroot), &copy).unwrap();

        let by_override =
            resolve_process(Some(&harness(root)), &record, Some(copy.as_os_str())).unwrap();
        assert_eq!(by_override.path(), copy);
        assert_eq!(by_override.route(), AyRoute::EnvironmentOverride);
        assert!(by_override.describe().contains("route=override-pinned-ay"));

        let explicit = resolve_explicit(&record, copy.as_os_str()).unwrap();
        assert_eq!(explicit.path(), copy);
        assert_eq!(explicit.route(), AyRoute::ExplicitPath);
        assert!(explicit.describe().contains("route=explicit-pinned-ay"));
    }

    /// `AY_SOLVER_PATH=<other bytes>` (and an explicit path to them) is refused
    /// even though the toolchain AY would have been admitted: never a fallback.
    #[test]
    fn named_path_with_other_bytes_is_refused_without_fallback() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "bundle", Some("pinned ay bytes"));
        let expected = pinned_identity(&ay_of(&sysroot));
        let managed = root.join("aterm/pkg/store/ay/8256/bin").join(exe("ay"));
        write_ay(&managed, "managed 8256 ay");
        let record = ToolchainAyRecord::new(sysroot, Ok(expected.clone()));
        assert_eq!(
            resolve_process(Some(&harness(root)), &record, Some(managed.as_os_str())).unwrap_err(),
            AyIdentityRefusal::Mismatch {
                route: AyRoute::EnvironmentOverride,
                path: managed.clone(),
                expected: Box::new(expected.clone()),
                found_sha256: digest(&managed),
            }
        );
        assert_eq!(
            resolve_explicit(&record, managed.as_os_str()).unwrap_err(),
            AyIdentityRefusal::Mismatch {
                route: AyRoute::ExplicitPath,
                path: managed.clone(),
                expected: Box::new(expected),
                found_sha256: digest(&managed),
            }
        );
    }

    #[test]
    fn named_paths_must_be_existing_absolute_files_and_are_never_searched() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let sysroot = toolchain(root, "bundle", Some("pinned ay bytes"));
        let record = ToolchainAyRecord::new(sysroot.clone(), Ok(pinned_identity(&ay_of(&sysroot))));
        // The PINNED bytes on the process PATH must not make a bare name work.
        let path_bin = root.join("path-bin");
        std::fs::create_dir_all(&path_bin).unwrap();
        std::fs::copy(ay_of(&sysroot), path_bin.join(exe("ay"))).unwrap();
        trust_cg_process_env::with_env_overrides(&[("PATH", path_bin.to_str().unwrap())], || {
            for value in ["", "ay", "path-bin/ay"] {
                assert_eq!(
                    resolve_process(Some(&harness(root)), &record, Some(OsStr::new(value)))
                        .unwrap_err(),
                    AyIdentityRefusal::OverrideNotAbsolute {
                        route: AyRoute::EnvironmentOverride,
                        value: OsString::from(value)
                    }
                );
                assert_eq!(
                    resolve_explicit(&record, OsStr::new(value)).unwrap_err(),
                    AyIdentityRefusal::OverrideNotAbsolute {
                        route: AyRoute::ExplicitPath,
                        value: OsString::from(value)
                    }
                );
            }
        });
        let missing = root.join("missing").join(exe("ay"));
        assert_eq!(
            resolve_process(Some(&harness(root)), &record, Some(missing.as_os_str())).unwrap_err(),
            AyIdentityRefusal::OverrideMissing {
                route: AyRoute::EnvironmentOverride,
                path: missing.clone()
            }
        );
        assert_eq!(
            resolve_explicit(&record, missing.as_os_str()).unwrap_err(),
            AyIdentityRefusal::OverrideMissing {
                route: AyRoute::ExplicitPath,
                path: missing
            }
        );
    }

    /// The process-level rule in THIS test harness: no compiler hosts it, so
    /// it must resolve the building toolchain's AY, compared by the recorded
    /// SHA-256 — whatever `PATH` or `HOME` say.
    #[test]
    fn this_test_harness_resolves_the_recorded_build_toolchain_ay() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        write_ay(&root.join("path-bin").join(exe("ay")), "path decoy");
        write_ay(
            &root.join("home/Library/Application Support/aterm/pkg/store/ay/current/bin/ay"),
            "package store decoy",
        );
        let resolved = trust_cg_process_env::with_env_overrides_removed(
            &[AY_OVERRIDE_ENV, test_fixtures::FIXTURE_DIGESTS_ENV],
            || {
                trust_cg_process_env::with_env_overrides(
                    &[
                        ("PATH", root.join("path-bin").to_str().unwrap()),
                        ("HOME", root.join("home").to_str().unwrap()),
                    ],
                    resolve_for_process,
                )
            },
        );
        let record = ToolchainAyRecord::recorded();
        match record.expected() {
            Err(reason) => assert_eq!(
                resolved,
                Err(AyIdentityRefusal::Unrecorded {
                    build_sysroot: record.build_sysroot().to_path_buf(),
                    reason: reason.to_owned(),
                })
            ),
            Ok(expected) => {
                let toolchain_ay = record.build_sysroot().join("bin").join(exe("ay"));
                match resolved {
                    Ok(admitted) => {
                        assert_eq!(admitted.path(), toolchain_ay);
                        assert_eq!(admitted.route(), AyRoute::ToolchainSysroot);
                        assert_eq!(
                            admitted.sysroot_source(),
                            Some(SysrootSource::BuildCompiler)
                        );
                        assert_eq!(admitted.identity(), expected);
                        assert_eq!(admitted.sha256(), digest(&toolchain_ay));
                    }
                    // The toolchain may have changed under a built harness;
                    // that must be named, and still never replaced.
                    Err(refusal) => assert!(
                        matches!(
                            &refusal,
                            AyIdentityRefusal::Mismatch { path, .. }
                                | AyIdentityRefusal::ToolchainAyMissing { path, .. }
                                if path == &toolchain_ay
                        ),
                        "{refusal}"
                    ),
                }
            }
        }
    }

    /// Unit-test fixture declarations admit exactly the declared bytes, on the
    /// same route checks, and nothing without a declaration.
    #[test]
    fn fixture_declarations_admit_only_the_declared_bytes() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let declared = root.join("declared").join(exe("ay"));
        write_ay(&declared, "declared fixture");
        let undeclared = root.join("undeclared").join(exe("ay"));
        write_ay(&undeclared, "undeclared fixture");
        let with_override = |value: &Path, digests: Option<&str>| {
            trust_cg_process_env::with_env_edits(|environment| {
                environment.set(AY_OVERRIDE_ENV, value.as_os_str());
                match digests {
                    Some(digests) => environment.set(test_fixtures::FIXTURE_DIGESTS_ENV, digests),
                    None => environment.remove(test_fixtures::FIXTURE_DIGESTS_ENV),
                }
                resolve_for_process()
            })
        };
        let declaration = test_fixtures::declare(&[&declared]);
        let admitted = with_override(&declared, Some(&declaration)).unwrap();
        assert_eq!(admitted.path(), declared);
        assert_eq!(admitted.identity().build(), None);
        assert!(admitted.describe().contains("unit-test fixture sha256"));

        let refusal = with_override(&undeclared, Some(&declaration)).unwrap_err();
        assert!(
            matches!(
                refusal,
                AyIdentityRefusal::Mismatch { .. } | AyIdentityRefusal::Unrecorded { .. }
            ),
            "{refusal}"
        );
        let refusal = with_override(&declared, None).unwrap_err();
        assert!(
            matches!(
                refusal,
                AyIdentityRefusal::Mismatch { .. } | AyIdentityRefusal::Unrecorded { .. }
            ),
            "without a declaration the fixture is not the recorded AY: {refusal}"
        );
    }

    /// An admission is bound to the file state it digested: replacing the
    /// executable is re-digested (and refused), and the old admission can no
    /// longer start anything — including after an in-place rewrite.
    #[test]
    fn replaced_or_rewritten_executables_are_redigested_and_not_started() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        write_ay(&fixture, "fixture A");
        let declaration = test_fixtures::declare(&[&fixture]);
        let resolve_override = || {
            trust_cg_process_env::with_env_edits(|environment| {
                environment.set(AY_OVERRIDE_ENV, fixture.as_os_str());
                environment.set(test_fixtures::FIXTURE_DIGESTS_ENV, &declaration);
                resolve_for_process()
            })
        };
        let first = resolve_override().unwrap();
        assert_eq!(first.route(), AyRoute::EnvironmentOverride);
        assert_eq!(resolve_override().unwrap(), first, "memoized admission");
        assert!(first.command().is_ok());

        // Remove then recreate with other bytes: a different file.
        std::fs::remove_file(&fixture).unwrap();
        write_ay(&fixture, "fixture B, a different build");
        let refusal = resolve_override().unwrap_err();
        assert!(
            matches!(&refusal, AyIdentityRefusal::Mismatch { found_sha256, .. } if *found_sha256 == digest(&fixture)),
            "a replaced executable must be re-digested, got {refusal}"
        );
        assert_eq!(
            first.command().unwrap_err(),
            AyIdentityRefusal::Changed {
                route: AyRoute::EnvironmentOverride,
                path: fixture.clone()
            }
        );

        // Same inode, rewritten in place with the ORIGINAL bytes: the file
        // state still differs from the admitted one, so the old admission
        // refuses and a fresh resolution digests the file again.
        std::fs::remove_file(&fixture).unwrap();
        write_ay(&fixture, "fixture A");
        let second = resolve_override().unwrap();
        std::fs::write(
            &fixture,
            test_fixtures::bind_self(
                &fixture,
                "#!/bin/sh\n# fixture A\n: > \"$0.executed\"\nexit 70\n",
            ),
        )
        .unwrap();
        assert_eq!(
            second.command().unwrap_err().code(),
            "TCG-AY-IDENTITY-CHANGED"
        );
        assert!(!executed(&fixture));
    }
}

#[test]
fn user_cache_base_uses_only_absolute_locations() {
    use std::ffi::OsStr;
    let base = trust_cg_process_env::private_fs::user_cache_base;
    assert_eq!(
        base(Some(OsStr::new("/x/cache")), Some(OsStr::new("/home/u"))).unwrap(),
        PathBuf::from("/x/cache")
    );
    assert_eq!(
        base(Some(OsStr::new("relative")), Some(OsStr::new("/home/u"))).unwrap(),
        PathBuf::from("/home/u/.cache")
    );
    assert_eq!(
        base(None, Some(OsStr::new("/home/u"))).unwrap(),
        PathBuf::from("/home/u/.cache")
    );
    assert!(base(None, Some(OsStr::new("home"))).is_err());
    assert!(base(Some(OsStr::new("")), None).is_err());
}

/// The post-admission swap (measured on 288ac2d2c): AY re-executes ITSELF by
/// its own path at startup, so replacing the admitted file after spawn ran a
/// decoy 6 of 9 times through `trustc` and inside the gate's replay. An
/// admitted AY now starts from a private copy of its admitted bytes.
#[cfg(unix)]
mod private_copy {
    use super::*;
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    use std::process::Stdio;

    /// Behaves like AY at startup: sleeps, then re-executes `$0` (its own
    /// path, deliberately NOT bound to the admitted file) and answers.
    ///
    /// `owner` names the test and goes into the script's bytes. The private
    /// copy is content-addressed, so two tests writing byte-identical fixtures
    /// would share one copy in this process's exec root, and a test that
    /// tampers with its copy would pull it out from under the other test's
    /// spawn (measured: `admitted_bytes_...` printed nothing in 2 of 3 runs
    /// beside `a_changed_private_copy_...`).
    fn self_reexecuting_ay(path: &Path, delay: &str, owner: &str) {
        std::fs::write(
            path,
            format!(
                "#!/bin/sh\n# self re-exec fixture for {owner}\n\
                 if [ -z \"$FIXTURE_REEXECED\" ]; then sleep {delay}; \
                 FIXTURE_REEXECED=1 exec \"$0\" \"$@\"; fi\n\
                 printf 'admitted %s\\n' \"$*\"\n"
            ),
        )
        .unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    fn decoy(path: &Path, log: &Path) {
        let staged = path.with_extension("decoy");
        std::fs::write(
            &staged,
            format!(
                "#!/bin/sh\nprintf 'DECOY %s\\n' \"$*\" >> '{}'\nprintf 'decoy\\n'\n",
                log.display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&staged, std::fs::Permissions::from_mode(0o755)).unwrap();
        std::fs::rename(&staged, path).unwrap();
    }

    /// Every start of an admitted AY goes through `PinnedAy`'s launcher, which
    /// records it for the gate's identity record: the ADMITTED file and digest
    /// (not the private copy that runs them), with the identity line, once per
    /// process. Without the variable nothing is written.
    #[test]
    fn the_launcher_records_the_admitted_ay_it_starts() {
        use crate::proof_tool_record::{PROOF_IDENTITY_OUT_ENV, SCHEMA};
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(
            &fixture,
            "0",
            "the_launcher_records_the_admitted_ay_it_starts",
        );
        let out = directory.path().join("identity.jsonl");
        let pinned = test_fixtures::pin(&fixture);
        trust_cg_process_env::with_env_overrides_removed(&[PROOF_IDENTITY_OUT_ENV], || {
            pinned.command().unwrap();
        });
        assert!(!out.exists(), "nothing is recorded without the variable");
        trust_cg_process_env::with_env_overrides(
            &[(PROOF_IDENTITY_OUT_ENV, out.to_str().unwrap())],
            || {
                for _ in 0..2 {
                    let output = pinned.command().unwrap().arg("probe").output().unwrap();
                    assert_eq!(String::from_utf8_lossy(&output.stdout), "admitted probe\n");
                }
            },
        );
        let text = std::fs::read_to_string(&out).unwrap();
        let rows: Vec<serde_json::Value> = text
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(rows.len(), 1, "one line per distinct tool: {text}");
        let row = &rows[0];
        assert_eq!(row["schema"], SCHEMA);
        assert_eq!(row["role"], "ay");
        assert_eq!(row["path"], pinned.path().display().to_string());
        assert_ne!(row["path"], pinned.exec_path().display().to_string());
        assert_eq!(row["sha256"], pinned.sha256());
        assert_eq!(row["identity"], pinned.identity().describe());
    }

    #[test]
    fn admitted_bytes_are_started_from_a_private_content_addressed_copy() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(
            &fixture,
            "0",
            "admitted_bytes_are_started_from_a_private_content_addressed_copy",
        );
        let pinned = test_fixtures::pin(&fixture);
        let copy = pinned.exec_path().to_path_buf();
        assert_ne!(copy, fixture);
        assert_eq!(copy.file_name(), fixture.file_name());
        assert_eq!(
            copy.parent().unwrap().file_name().unwrap(),
            OsStr::new(pinned.sha256()),
            "the copy is addressed by the admitted digest"
        );
        assert_eq!(digest_file(&copy).unwrap().0, pinned.sha256());
        let file = std::fs::symlink_metadata(&copy).unwrap();
        assert!(file.file_type().is_file());
        assert_eq!(file.mode() & 0o7777, 0o500);
        assert_eq!(file.nlink(), 1);
        for directory in [
            copy.parent().unwrap(),
            copy.parent().unwrap().parent().unwrap(),
        ] {
            assert_eq!(
                std::fs::symlink_metadata(directory).unwrap().mode() & 0o7777,
                0o700,
                "{}",
                directory.display()
            );
        }
        let output = pinned.command().unwrap().arg("probe").output().unwrap();
        assert_eq!(String::from_utf8_lossy(&output.stdout), "admitted probe\n");
        // Same bytes, same copy: a second admission reuses it.
        assert_eq!(test_fixtures::pin(&fixture).exec_path(), copy);
    }

    #[test]
    fn replacing_the_admitted_file_after_spawn_never_runs_the_replacement() {
        for (index, swap_after_ms) in [0u64, 20, 80, 200, 400].into_iter().enumerate() {
            let directory = tempfile::tempdir().unwrap();
            let fixture = directory.path().join(exe("ay"));
            // A distinct delay per case keeps each fixture's bytes (and copy)
            // its own.
            self_reexecuting_ay(
                &fixture,
                &format!("0.{}", 3 + index),
                "replacing_the_admitted_file_after_spawn_never_runs_the_replacement",
            );
            let log = directory.path().join("decoy.log");
            let pinned = test_fixtures::pin(&fixture);
            let child = pinned
                .command()
                .unwrap()
                .arg("query")
                .stdout(Stdio::piped())
                .spawn()
                .unwrap();
            std::thread::sleep(std::time::Duration::from_millis(swap_after_ms));
            decoy(&fixture, &log);
            let output = child.wait_with_output().unwrap();
            assert_eq!(
                String::from_utf8_lossy(&output.stdout),
                "admitted query\n",
                "swap after {swap_after_ms} ms"
            );
            assert!(
                !log.exists(),
                "swap after {swap_after_ms} ms ran the decoy: {}",
                std::fs::read_to_string(&log).unwrap_or_default()
            );
            // The admission still refuses to start anything once its admitted
            // file has changed, and the decoy is never admitted.
            assert_eq!(
                pinned.command().unwrap_err().code(),
                "TCG-AY-IDENTITY-CHANGED"
            );
            assert!(!log.exists());
        }
    }

    #[test]
    fn a_changed_private_copy_is_refused_and_rebuilt_from_admitted_bytes() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(
            &fixture,
            "0",
            "a_changed_private_copy_is_refused_and_rebuilt_from_admitted_bytes",
        );
        let log = directory.path().join("decoy.log");
        let pinned = test_fixtures::pin(&fixture);
        let copy = pinned.exec_path().to_path_buf();

        // Replaced by rename (what the owner of the directory could do).
        decoy(&copy, &log);
        let refusal = pinned.command().unwrap_err();
        assert_eq!(refusal.code(), "TCG-AY-IDENTITY-COPY-CHANGED", "{refusal}");
        // A fresh admission discards the invalid copy and writes the admitted
        // bytes again.
        let again = test_fixtures::pin(&fixture);
        assert_eq!(again.exec_path(), copy);
        assert_eq!(digest_file(&copy).unwrap().0, again.sha256());
        let output = again.command().unwrap().arg("x").output().unwrap();
        assert_eq!(String::from_utf8_lossy(&output.stdout), "admitted x\n");

        // Made writable: no longer the private 0500 file.
        std::fs::set_permissions(&copy, std::fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(
            again.command().unwrap_err().code(),
            "TCG-AY-IDENTITY-COPY-CHANGED"
        );
        // Its directory opened to the group.
        let again = test_fixtures::pin(&fixture);
        let parent = copy.parent().unwrap();
        std::fs::set_permissions(parent, std::fs::Permissions::from_mode(0o750)).unwrap();
        assert_eq!(
            again.command().unwrap_err().code(),
            "TCG-AY-IDENTITY-COPY-CHANGED"
        );
        // A directory that is not private is not repaired silently: admission
        // refuses to materialize into it.
        let refusal = std::panic::catch_unwind(|| test_fixtures::pin(&fixture)).unwrap_err();
        let message = refusal
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_default();
        assert!(
            message.contains("TCG-AY-IDENTITY-UNMATERIALIZED"),
            "{message}"
        );
        std::fs::set_permissions(parent, std::fs::Permissions::from_mode(0o700)).unwrap();
        assert!(test_fixtures::pin(&fixture).command().is_ok());
        assert!(!log.exists(), "no decoy may ever run");
    }

    /// Umask 0002 (Ubuntu's default for a user with a user-private group):
    /// `std::fs::create_dir_all` made `<cache>/trust-cg` `0775`, and the
    /// ancestor rule then refused every AY (measured 2026-09-26). Every
    /// directory of the tree trust-cg creates is now `0700`. A directory that
    /// already exists group-writable is still refused, never changed, and the
    /// refusal names it, its mode and the remedy. Runs in a child test process
    /// (its own umask and its own exec root), started by `sh` under the umask.
    #[test]
    fn under_umask_0002_the_cache_tree_is_private_and_an_open_root_is_refused_with_its_remedy() {
        const CHILD: &str = "PRIVATE_COPY_UMASK_CHILD";
        const NAME: &str = "ay_identity::tests::private_copy::\
            under_umask_0002_the_cache_tree_is_private_and_an_open_root_is_refused_with_its_remedy";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new("/bin/sh")
                .arg("-c")
                .arg("umask 0002 && exec \"$0\" \"$@\"")
                .arg(std::env::current_exe().unwrap())
                .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
                .env(CHILD, "1")
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                output.status.success() && stdout.contains("1 passed"),
                "umask 0002 child: {}\n{stdout}\n{stderr}",
                output.status
            );
            return;
        }
        let directory = tempfile::tempdir().unwrap();
        let mode = |path: &Path| std::fs::symlink_metadata(path).unwrap().mode() & 0o7777;
        let control = directory.path().join("control");
        std::fs::create_dir_all(&control).unwrap();
        assert_eq!(mode(&control), 0o775, "the child must run under umask 0002");

        let first = directory.path().join(exe("ay"));
        self_reexecuting_ay(&first, "0", "umask 0002 first fixture");
        let copy = test_fixtures::pin(&first).exec_path().to_path_buf();
        let digest_dir = copy.parent().unwrap();
        let exec_dir = digest_dir.parent().unwrap();
        let trust_cg = exec_dir.parent().unwrap();
        assert_eq!(trust_cg.file_name().unwrap(), OsStr::new("trust-cg"));
        for created in [trust_cg, exec_dir, digest_dir] {
            assert_eq!(mode(created), 0o700, "{}", created.display());
        }

        // An existing `trust-cg` opened to the group, as `create_dir_all`
        // left it under this umask before.
        std::fs::set_permissions(trust_cg, std::fs::Permissions::from_mode(0o775)).unwrap();
        let second = directory.path().join(exe("ay-second"));
        self_reexecuting_ay(&second, "0", "umask 0002 second fixture");
        let record = ToolchainAyRecord::new(
            PathBuf::from("/nonexistent-fixture-sysroot"),
            Ok(AyIdentity {
                sha256: test_fixtures::sha256_of(&second),
                build: None,
                overlay: None,
            }),
        );
        let refusal = resolve(ResolutionInputs {
            running_exe: None,
            record: &record,
            naming: Naming::Explicit(second.as_os_str()),
        })
        .unwrap_err();
        assert_eq!(
            refusal.code(),
            "TCG-AY-IDENTITY-UNMATERIALIZED",
            "{refusal}"
        );
        let message = refusal.to_string();
        let shown = trust_cg.display();
        for needed in [
            format!("{shown} has mode 0775"),
            format!("`chmod go-w {shown}`"),
            "XDG_CACHE_HOME".to_owned(),
        ] {
            assert!(
                message.contains(&needed),
                "{needed:?} missing from {message}"
            );
        }
        assert_eq!(
            mode(trust_cg),
            0o775,
            "an existing directory is never changed"
        );

        // The owner's remedy admits it.
        std::fs::set_permissions(trust_cg, std::fs::Permissions::from_mode(0o755)).unwrap();
        assert!(test_fixtures::pin(&second).command().is_ok());
        println!("AY_PRIVATE_COPY_UMASK_0002 created=0700 open_root_refused=0775");
    }

    /// X-HOST-P13 third closure audit. A cache base reached through a symlink
    /// in a directory others can write is resolved once and the root is named
    /// from the RESOLVED base, so the copy is started where the checks looked,
    /// whatever the symlink points to later; the same base as a real
    /// directory inside that open directory is refused. Each directory is
    /// judged before anything is created in it: a `trust-cg` that already
    /// exists open to the group, or as a symlink, gains no `ay-exec`, and a
    /// base below an open directory gains no `trust-cg`, before the refusal.
    #[test]
    fn the_root_is_named_from_the_resolved_base_and_nothing_is_created_before_a_refusal() {
        let directory = tempfile::tempdir().unwrap();
        let top = std::fs::canonicalize(directory.path()).unwrap();
        // `tempdir` follows the umask (0775 under 0002); the cases below need
        // a private top.
        std::fs::set_permissions(&top, std::fs::Permissions::from_mode(0o700)).unwrap();
        let mode = |path: &Path| std::fs::symlink_metadata(path).unwrap().mode() & 0o7777;
        let make = |path: &Path, mode: u32| {
            std::fs::create_dir(path).unwrap();
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).unwrap();
        };
        let exec_root = |base: &Path| base.join("trust-cg").join("ay-exec");

        // A base reached through `<shared 0777>/link`: named from where the
        // link led when it was resolved.
        let real = top.join("real");
        make(&real, 0o700);
        let shared = top.join("shared");
        make(&shared, 0o777);
        let link = shared.join("link");
        std::os::unix::fs::symlink(&real, &link).unwrap();
        let root = ay_private_copy::private_root_at(&exec_root(&link)).unwrap();
        assert_eq!(root, exec_root(&real), "named from the resolved base");
        assert_eq!(mode(&real.join("trust-cg")), 0o700);
        assert_eq!(mode(&root), 0o700);
        // The control: a real base inside the open directory is refused, and
        // gains nothing first.
        let direct = shared.join("direct");
        make(&direct, 0o700);
        let refusal = ay_private_copy::private_root_at(&exec_root(&direct)).unwrap_err();
        assert!(
            refusal.contains(&format!("{} has mode 0777", shared.display())),
            "{refusal}"
        );
        assert!(!direct.join("trust-cg").exists(), "nothing created first");

        // An existing `trust-cg` open to the group: refused, unchanged, and
        // no `ay-exec` inside it.
        let open = top.join("open");
        make(&open, 0o700);
        make(&open.join("trust-cg"), 0o775);
        let refusal = ay_private_copy::private_root_at(&exec_root(&open)).unwrap_err();
        assert!(
            refusal.contains(&format!(
                "{} has mode 0775",
                open.join("trust-cg").display()
            )),
            "{refusal}"
        );
        assert!(
            !exec_root(&open).exists(),
            "no ay-exec inside an open trust-cg"
        );
        assert_eq!(mode(&open.join("trust-cg")), 0o775, "never changed");

        // A symlinked `trust-cg`: refused, and its target gains no `ay-exec`.
        let linked = top.join("linked");
        make(&linked, 0o700);
        let target = top.join("target");
        make(&target, 0o700);
        std::os::unix::fs::symlink(&target, linked.join("trust-cg")).unwrap();
        let refusal = ay_private_copy::private_root_at(&exec_root(&linked)).unwrap_err();
        assert!(
            refusal.contains("is not a directory (a symlink is not followed)"),
            "{refusal}"
        );
        assert!(
            !target.join("ay-exec").exists(),
            "nothing created through the symlink"
        );
    }

    /// Re-run test `name` in a child test process with `CHILD`=`mode`,
    /// returning its success and stdout.
    fn run_child(name: &str, child: &str, mode: &str) -> (bool, String) {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", name, "--nocapture", "--test-threads=1"])
            .env(child, mode)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr);
        (output.status.success(), format!("{stdout}\n{stderr}"))
    }

    fn printed<'a>(transcript: &'a str, key: &str) -> &'a str {
        transcript
            .lines()
            .find_map(|line| line.split_once(key).map(|(_, value)| value.trim()))
            .unwrap_or_else(|| panic!("{key} missing from {transcript}"))
    }

    /// A fixture's private root belongs to its test process and is removed
    /// when that process exits, also after a failing (panicking) test, so
    /// repeated test runs leave nothing in the temporary directory.
    #[test]
    fn a_test_process_removes_its_fixture_root_when_it_exits_even_after_a_panic() {
        const CHILD: &str = "PRIVATE_COPY_ROOT_CHILD";
        const NAME: &str = "ay_identity::tests::private_copy::\
            a_test_process_removes_its_fixture_root_when_it_exits_even_after_a_panic";
        if let Some(mode) = std::env::var_os(CHILD) {
            let directory = tempfile::tempdir().unwrap();
            let fixture = directory.path().join(exe("ay"));
            self_reexecuting_ay(
                &fixture,
                "0",
                &format!("root lifetime {}", std::process::id()),
            );
            let copy = test_fixtures::pin(&fixture).exec_path().to_path_buf();
            let base = copy.ancestors().nth(4).unwrap().to_path_buf();
            let inert = test_fixtures::inert();
            // Both paths in their RESOLVED spelling: the fixture root is
            // already canonical (`private_root_at` canonicalizes it), and the
            // parent cannot canonicalize a directory that no longer exists.
            println!("FIXTURE_ROOT_BASE {}", base.display());
            println!(
                "INERT_FIXTURE_DIR {}",
                std::fs::canonicalize(inert.path().parent().unwrap())
                    .unwrap()
                    .display()
            );
            assert!(base.is_dir() && inert.path().is_file());
            assert!(mode != "panic", "deliberate failure after materializing");
            return;
        }
        // Compare resolved spellings: on macOS `$TMPDIR` is under `/var`, a
        // symlink to `/private/var`, and `Path::starts_with` compares
        // components as text.
        let temp = std::fs::canonicalize(std::env::temp_dir()).unwrap();
        for mode in ["pass", "panic"] {
            let (success, transcript) = run_child(NAME, CHILD, mode);
            assert_eq!(success, mode == "pass", "{mode}: {transcript}");
            for key in ["FIXTURE_ROOT_BASE", "INERT_FIXTURE_DIR"] {
                let path = PathBuf::from(printed(&transcript, key));
                assert!(
                    path.starts_with(&temp),
                    "{mode}: {} is not under the temp dir {}",
                    path.display(),
                    temp.display()
                );
                assert!(
                    !path.exists(),
                    "{mode}: {} outlived its test process",
                    path.display()
                );
            }
        }
    }

    /// The AY this build records is copied once per user and reused by every
    /// later test process: two processes admit it and start the same file
    /// (same inode, not rewritten) under the shared root. (A stock build
    /// records no AY and only checks the root's location.)
    #[test]
    fn the_recorded_toolchain_ay_is_copied_once_and_reused_across_test_processes() {
        const CHILD: &str = "PRIVATE_COPY_SHARED_CHILD";
        const NAME: &str = "ay_identity::tests::private_copy::\
            the_recorded_toolchain_ay_is_copied_once_and_reused_across_test_processes";
        let shared = ay_private_copy::shared_test_root();
        assert!(shared.starts_with(std::env::temp_dir()));
        assert!(shared.ends_with("trust-cg/ay-exec"));
        let record = ToolchainAyRecord::recorded();
        let Ok(expected) = record.expected() else {
            println!("SKIP no toolchain AY recorded by this build: nothing to copy");
            return;
        };
        let toolchain_ay = record.build_sysroot().join("bin").join(exe("ay"));
        if std::env::var_os(CHILD).is_some() {
            let admitted = resolve_explicit_path(&toolchain_ay).unwrap();
            let metadata = std::fs::symlink_metadata(admitted.exec_path()).unwrap();
            println!("SHARED_COPY {}", admitted.exec_path().display());
            println!(
                "SHARED_COPY_STATE {} {}",
                metadata.ino(),
                metadata.ctime_nsec()
            );
            return;
        }
        let (first_ok, first) = run_child(NAME, CHILD, "1");
        let (second_ok, second) = run_child(NAME, CHILD, "2");
        assert!(first_ok && second_ok, "{first}\n{second}");
        let copy = PathBuf::from(printed(&first, "SHARED_COPY "));
        assert_eq!(copy, PathBuf::from(printed(&second, "SHARED_COPY ")));
        assert_eq!(
            printed(&first, "SHARED_COPY_STATE"),
            printed(&second, "SHARED_COPY_STATE"),
            "the second process must reuse the first copy, not write another"
        );
        assert!(
            copy.starts_with(
                std::fs::canonicalize(shared.parent().unwrap().parent().unwrap()).unwrap()
            ),
            "{}",
            copy.display()
        );
        assert_eq!(
            copy.parent().unwrap().file_name().unwrap(),
            OsStr::new(expected.sha256())
        );
        assert_eq!(digest_file(&copy).unwrap().0, expected.sha256());
    }

    /// A writer killed mid-copy (SIGKILL) leaves its `.ay-copy-*` temporary in
    /// the shared `<sha256>` directory. A later materialization removes it
    /// once its writer is provably gone: its lock is free (the kernel drops a
    /// killed process's lock) and it is older than the create-to-lock window.
    /// A temporary a live process holds, a young one, the published `ay` and a
    /// symlink (never followed) are kept.
    #[test]
    fn stale_temporaries_of_dead_writers_are_removed_and_live_ones_kept() {
        use std::io::{BufRead, Write};
        use std::time::{Duration, SystemTime};
        const CHILD: &str = "PRIVATE_COPY_TEMPORARY_HOLDER";
        const NAME: &str = "ay_identity::tests::private_copy::\
            stale_temporaries_of_dead_writers_are_removed_and_live_ones_kept";
        if let Some(path) = std::env::var_os(CHILD) {
            // A live writer: holds the temporary's lock until it is killed.
            let file = std::fs::OpenOptions::new().read(true).open(&path).unwrap();
            file.lock().unwrap();
            println!("TEMPORARY_LOCKED");
            std::io::stdout().flush().unwrap();
            std::thread::sleep(Duration::from_secs(120));
            return;
        }
        struct Holder(std::process::Child);
        impl Drop for Holder {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }

        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let old = SystemTime::now() - Duration::from_secs(3600);
        let plant = |name: &str, modified: SystemTime| {
            let path = dir.join(name);
            let mut file = std::fs::File::create(&path).unwrap();
            file.write_all(b"partial copy").unwrap();
            file.set_modified(modified).unwrap();
            path
        };
        let dead = plant(".ay-copy-dead", old);
        let young = plant(".ay-copy-young", SystemTime::now());
        let live = plant(".ay-copy-live", old);
        let published = plant(&exe("ay"), old);
        let target = plant("link-target", old);
        let link = dir.join(".ay-copy-link");
        std::os::unix::fs::symlink(&target, &link).unwrap();

        let mut holder = Holder(
            std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
                .env(CHILD, &live)
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .spawn()
                .unwrap(),
        );
        let mut lines = std::io::BufReader::new(holder.0.stdout.take().unwrap()).lines();
        assert!(
            lines.any(|line| line.unwrap().contains("TEMPORARY_LOCKED")),
            "the holder never locked the temporary"
        );

        ay_private_copy::remove_stale_temporaries(dir);
        assert!(!dead.exists(), "a dead writer's old temporary is removed");
        assert!(
            young.exists(),
            "a young temporary may be between create and lock"
        );
        assert!(live.exists(), "a temporary a live process holds is kept");
        assert!(published.exists(), "the published copy is never touched");
        assert!(std::fs::symlink_metadata(&link).is_ok() && target.exists());

        // The live writer is killed; the kernel releases its lock with it.
        drop(holder);
        ay_private_copy::remove_stale_temporaries(dir);
        assert!(!live.exists(), "the killed writer's temporary is removed");
        assert!(young.exists() && published.exists() && target.exists());
        assert!(std::fs::symlink_metadata(&link).is_ok());
    }

    /// Materializing an admitted AY removes a dead writer's temporary from its
    /// `<sha256>` directory and keeps the published copy.
    #[test]
    fn materializing_removes_a_dead_writers_temporary_beside_the_copy() {
        use std::time::{Duration, SystemTime};
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(&fixture, "0", "dead writer temporary cleanup");
        let copy = test_fixtures::pin(&fixture).exec_path().to_path_buf();
        let planted = copy.parent().unwrap().join(".ay-copy-killed-writer");
        std::fs::write(&planted, b"partial").unwrap();
        std::fs::File::options()
            .write(true)
            .open(&planted)
            .unwrap()
            .set_modified(SystemTime::now() - Duration::from_secs(3600))
            .unwrap();
        let again = test_fixtures::pin(&fixture);
        assert_eq!(again.exec_path(), copy);
        assert!(!planted.exists());
        assert!(again.command().is_ok());
    }

    /// A fixture that logs `<path it was started as>|<arguments>` to `log`
    /// on every start. `$0` is deliberately not bound to the fixture's own
    /// path: the log shows WHICH file ran. `owner` goes into the bytes, so each
    /// test's fixture has its own private copy.
    fn start_logging_ay(path: &Path, log: &Path, owner: &str) {
        std::fs::write(
            path,
            format!(
                "#!/bin/sh\n# start-logging fixture for {owner}\n\
                 printf '%s|%s\\n' \"$0\" \"$*\" >> '{}'\n",
                log.display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    fn starts(log: &Path) -> Vec<String> {
        std::fs::read_to_string(log)
            .unwrap_or_default()
            .lines()
            .map(str::to_owned)
            .collect()
    }

    /// The marker recording, for later processes, that a first start of a
    /// copy's file state has completed.
    fn first_start_marker(pinned: &PinnedAy) -> PathBuf {
        pinned.exec_path().with_file_name("ay.first-start")
    }

    /// The starts a host that assesses new executables makes before the
    /// first command of a copy: one `--version` of that copy; none elsewhere.
    fn first_start_of(copy: &str) -> Vec<String> {
        if ay_private_copy::HOST_ASSESSES_FIRST_START {
            vec![format!("{copy}|--version")]
        } else {
            Vec::new()
        }
    }

    /// A new private copy's first start is slow on macOS (up to 32.2 s
    /// measured for the 158 MB toolchain AY; see `first_start`), so it must
    /// never be the start a solver deadline is running for. Admission starts
    /// nothing; the first command handed out for an AY build's copy is
    /// preceded by one `--version` start of that copy, once per copy per
    /// process, and that completed start is recorded beside the copy. A
    /// fixture without an AY build is never started for it.
    #[test]
    fn the_first_start_of_an_ay_build_copy_precedes_its_first_command() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        let log = directory.path().join("starts.log");
        start_logging_ay(&fixture, &log, "first start precedes the first command");

        let pinned = test_fixtures::pin_as_build(&fixture);
        assert!(starts(&log).is_empty(), "admission starts nothing");
        assert!(!first_start::made(&pinned));
        let copy = pinned.exec_path().display().to_string();

        let mut command = pinned.command().unwrap();
        assert_eq!(
            starts(&log),
            first_start_of(&copy),
            "the copy's first start precedes the first command handed out"
        );
        assert_eq!(
            first_start::made(&pinned),
            ay_private_copy::HOST_ASSESSES_FIRST_START
        );
        assert_eq!(
            first_start_marker(&pinned).exists(),
            ay_private_copy::HOST_ASSESSES_FIRST_START,
            "a completed first start is recorded for other processes"
        );
        assert!(command.arg("query").status().unwrap().success());
        assert!(pinned.command().is_ok());
        assert!(test_fixtures::pin_as_build(&fixture).command().is_ok());
        let mut expected = first_start_of(&copy);
        expected.push(format!("{copy}|query"));
        assert_eq!(starts(&log), expected, "one first start per copy");

        let plain_fixture = directory.path().join("plain").join(exe("ay"));
        std::fs::create_dir_all(plain_fixture.parent().unwrap()).unwrap();
        let plain_log = directory.path().join("plain-starts.log");
        start_logging_ay(&plain_fixture, &plain_log, "a fixture without an AY build");
        let plain = test_fixtures::pin(&plain_fixture);
        assert!(plain.command().is_ok());
        assert!(
            starts(&plain_log).is_empty(),
            "a fixture without an AY build is started only by its test"
        );
    }

    /// One registry decides every first start. The identity-warm thread's
    /// prime (`ay_bridge::prime_published_solver_copy`) makes it only for a
    /// copy published during this process, and a later command does not
    /// repeat it. A copy found published WITHOUT a record of a completed
    /// first start (another process published it and never started it, or
    /// is starting it now) is not primed, but its first command still makes
    /// the start before any deadline; a copy found WITH that record (a warm
    /// cache) starts nothing extra, not even for its first command.
    #[test]
    fn the_prime_takes_a_copy_published_here_and_a_command_any_unrecorded_one() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        let log = directory.path().join("starts.log");
        start_logging_ay(&fixture, &log, "prime and command share one registry");
        let pinned = test_fixtures::pin_as_build(&fixture);
        let copy = pinned.exec_path().display().to_string();

        pinned.prime_published_copy();
        assert_eq!(starts(&log), first_start_of(&copy), "published here");
        pinned.prime_published_copy();
        assert!(
            pinned
                .command()
                .unwrap()
                .arg("after-prime")
                .status()
                .unwrap()
                .success()
        );
        let mut expected = first_start_of(&copy);
        expected.push(format!("{copy}|after-prime"));
        assert_eq!(starts(&log), expected, "the prime was the first start");

        // A new process finding the copy with its completed first start
        // recorded: a warm cache starts nothing extra.
        first_start::forget(&pinned);
        let warm = test_fixtures::pin_as_build(&fixture);
        warm.prime_published_copy();
        assert!(
            warm.command()
                .unwrap()
                .arg("warm")
                .status()
                .unwrap()
                .success()
        );
        expected.push(format!("{copy}|warm"));
        assert_eq!(
            starts(&log),
            expected,
            "a recorded first start is not repeated"
        );

        // A new process finding the copy with no completed first start
        // recorded (its publisher never started it): the prime leaves it
        // alone, the first command makes it.
        first_start::forget(&pinned);
        let _ = std::fs::remove_file(first_start_marker(&pinned));
        let found = test_fixtures::pin_as_build(&fixture);
        found.prime_published_copy();
        assert_eq!(
            starts(&log),
            expected,
            "a copy published elsewhere is not primed"
        );
        assert!(
            found
                .command()
                .unwrap()
                .arg("found")
                .status()
                .unwrap()
                .success()
        );
        expected.extend(first_start_of(&copy));
        expected.push(format!("{copy}|found"));
        assert_eq!(starts(&log), expected);

        // A stale record (another file state) records nothing.
        first_start::forget(&pinned);
        std::fs::write(first_start_marker(&pinned), "0 0 0 0 0\n").unwrap();
        assert!(
            test_fixtures::pin_as_build(&fixture)
                .command()
                .unwrap()
                .arg("stale")
                .status()
                .unwrap()
                .success()
        );
        expected.extend(first_start_of(&copy));
        expected.push(format!("{copy}|stale"));
        assert_eq!(starts(&log), expected);
    }

    /// A command needed while another thread makes the first start (the
    /// identity-warm thread's prime, in a compile) waits for that start to
    /// finish instead of starting the copy itself: the one start is made
    /// once, and no part of it falls inside the waiting caller's deadline.
    #[test]
    fn a_command_needed_during_the_prime_waits_for_it_and_starts_nothing_extra() {
        if !ay_private_copy::HOST_ASSESSES_FIRST_START {
            println!("SKIP this host makes no first start on its own");
            return;
        }
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        let log = directory.path().join("starts.log");
        let release = directory.path().join("release");
        std::fs::write(
            &fixture,
            format!(
                "#!/bin/sh\n# slow-first-start fixture\n\
                 printf 'begin %s\\n' \"$*\" >> '{log}'\n\
                 if [ \"$1\" = --version ]; then\n\
                 while [ ! -e '{release}' ]; do sleep 0.05; done\n\
                 fi\n\
                 printf 'end %s\\n' \"$*\" >> '{log}'\n",
                log = log.display(),
                release = release.display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&fixture, std::fs::Permissions::from_mode(0o755)).unwrap();
        let pinned = test_fixtures::pin_as_build(&fixture);

        let prime = {
            let pinned = pinned.clone();
            std::thread::spawn(move || pinned.prime_published_copy())
        };
        let armed = std::time::Instant::now();
        while !first_start::in_progress(&pinned) {
            assert!(
                armed.elapsed() < std::time::Duration::from_secs(60),
                "the prime never started"
            );
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        let waiter = {
            let pinned = pinned.clone();
            std::thread::spawn(move || {
                let command = pinned.command();
                (command.is_ok(), first_start::made(&pinned))
            })
        };
        // Release the first start only once the waiter is waiting for it.
        let armed = std::time::Instant::now();
        while first_start::waits(&pinned) == 0 {
            assert!(
                !waiter.is_finished(),
                "a command was handed out while the first start ran"
            );
            assert!(
                armed.elapsed() < std::time::Duration::from_secs(60),
                "the command never waited for the first start"
            );
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        assert!(
            !waiter.is_finished(),
            "a command was handed out mid first start"
        );
        std::fs::write(&release, "").unwrap();
        prime.join().unwrap();
        let (got_command, made_before) = waiter.join().unwrap();
        assert!(got_command);
        assert!(
            made_before,
            "the command was handed out only after the first start"
        );
        assert_eq!(
            starts(&log),
            ["begin --version", "end --version"],
            "one first start, made by the prime"
        );
    }

    /// A first start that never finishes is stopped at its allowance: a
    /// thread needing a command waits for it, so an unbounded start would
    /// hold every AY user of the process. A stopped start counts as made in
    /// this process (the next command is handed out at once and never repeats
    /// it) but is not recorded for other processes, which make it again.
    ///
    /// The bound is asserted against the fixture's two-minute `--version`,
    /// not against the 500 ms allowance: a new fixture file may itself be held
    /// for assessment past the allowance, so whether its `--version` got to
    /// log is not asserted either.
    #[test]
    fn a_first_start_that_never_finishes_is_stopped_at_its_allowance() {
        if !ay_private_copy::HOST_ASSESSES_FIRST_START {
            println!("SKIP this host makes no first start on its own");
            return;
        }
        const WEDGED: std::time::Duration = std::time::Duration::from_secs(120);
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        let log = directory.path().join("starts.log");
        std::fs::write(
            &fixture,
            format!(
                "#!/bin/sh\n# wedged-first-start fixture {}\nprintf '%s\\n' \"$*\" >> '{}'\n\
                 if [ \"$1\" = --version ]; then exec sleep {}; fi\n",
                fixture.display(),
                log.display(),
                WEDGED.as_secs()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&fixture, std::fs::Permissions::from_mode(0o755)).unwrap();

        let pinned = test_fixtures::pin_as_build(&fixture);
        let begun = std::time::Instant::now();
        first_start::ensure_within(&pinned, std::time::Duration::from_millis(500));
        let took = begun.elapsed();
        assert!(
            took < WEDGED / 2,
            "a first start that never finishes must be stopped at its allowance, took {took:?}"
        );
        assert!(first_start::made(&pinned), "a stopped first start is made");
        assert!(
            !first_start_marker(&pinned).exists(),
            "a stopped first start is not recorded for other processes"
        );

        let begun = std::time::Instant::now();
        let mut command = pinned.command().unwrap();
        assert!(
            begun.elapsed() < WEDGED / 2,
            "the next command must not repeat the stopped first start"
        );
        assert!(command.arg("query").status().unwrap().success());
        let starts = starts(&log);
        assert_eq!(
            starts.last().map(String::as_str),
            Some("query"),
            "{starts:?}"
        );
        assert!(
            starts.iter().filter(|start| *start == "--version").count() <= 1,
            "{starts:?}"
        );
    }

    /// The copy is streamed in bounded chunks (not read whole into memory),
    /// digested over exactly the bytes written, and never published when the
    /// source no longer has the admitted digest.
    #[test]
    fn a_streamed_copy_is_published_only_with_the_admitted_digest() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path().join("exec");
        std::fs::create_dir(&root).unwrap();
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700)).unwrap();
        // Several chunks and a partial last one.
        let source = directory.path().join("source");
        let bytes: Vec<u8> = (0..(ay_private_copy::COPY_CHUNK_BYTES * 5 / 2))
            .map(|index| (index % 251) as u8)
            .collect();
        std::fs::write(&source, &bytes).unwrap();
        let sha256 = digest_file(&source).unwrap().0;

        let published = root.join("copy");
        ay_private_copy::write_copy(&source, &sha256, &root, &published).unwrap();
        assert_eq!(std::fs::read(&published).unwrap(), bytes);
        assert_eq!(
            std::fs::symlink_metadata(&published).unwrap().mode() & 0o7777,
            0o500
        );

        let refused = root.join("refused");
        let other = "0".repeat(64);
        let reason = ay_private_copy::write_copy(&source, &other, &root, &refused).unwrap_err();
        assert!(reason.contains("changed after admission"), "{reason}");
        assert!(
            !refused.exists(),
            "a copy of other bytes is never published"
        );
        assert_eq!(
            std::fs::read_dir(&root).unwrap().count(),
            1,
            "the refused temporary is removed"
        );
    }

    /// Fixed-cost bound (L14-P5): threads of one process that resolve the
    /// same AY into a fresh cache root write its private copy once, and read
    /// the source and the published copy once each. In a compile these are
    /// the identity-warm thread and the first proof query; each used to
    /// stream its own copy of the whole AY.
    #[test]
    fn concurrent_resolutions_in_one_process_write_one_copy() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(&fixture, "0", "concurrent resolutions write one copy");
        let start = std::sync::Barrier::new(8);
        let pinned: Vec<PinnedAy> = std::thread::scope(|scope| {
            let resolvers: Vec<_> = (0..8)
                .map(|_| {
                    scope.spawn(|| {
                        start.wait();
                        test_fixtures::pin(&fixture)
                    })
                })
                .collect();
            resolvers
                .into_iter()
                .map(|resolver| resolver.join().unwrap())
                .collect()
        });
        let copy = pinned[0].exec_path().to_path_buf();
        assert!(pinned.iter().all(|each| each.exec_path() == copy));
        assert_eq!(
            ay_private_copy::copies_written_into(copy.parent().unwrap()),
            1,
            "one copy streamed for eight resolutions"
        );
        assert_eq!(digest_computation_count(&fixture), 1);
        assert_eq!(digest_computation_count(&copy), 1);
        for each in &pinned {
            each.revalidate().unwrap();
        }
    }

    /// A record admitting exactly `sha256`, taken WITHOUT the digest memo, so
    /// a resolution against it is the first digest of the fixture's state.
    fn record_of_bytes(bytes: &[u8]) -> (String, ToolchainAyRecord) {
        let sha256 = format!("{:x}", <sha2::Sha256 as sha2::Digest>::digest(bytes));
        let record = ToolchainAyRecord::new(
            PathBuf::from("/nonexistent-fixture-sysroot"),
            Ok(AyIdentity {
                sha256: sha256.clone(),
                build: None,
                overlay: None,
            }),
        );
        (sha256, record)
    }

    fn resolve_named(
        record: &ToolchainAyRecord,
        path: &Path,
    ) -> Result<PinnedAy, AyIdentityRefusal> {
        resolve(ResolutionInputs {
            running_exe: None,
            record,
            naming: Naming::Explicit(path.as_os_str()),
        })
    }

    /// Fixed-cost bound (L14-P5): admitting an AY whose file state this
    /// process has not digested, into a cache root with no copy, reads the
    /// source ONCE. The digest streamed while the copy is written is the
    /// admission digest (a later admission of the same state reads nothing),
    /// and the published copy is still digested before it is used.
    #[test]
    fn a_fresh_admission_reads_the_source_once_and_still_verifies_the_copy() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(&fixture, "0", "a fresh admission reads the source once");
        let bytes = std::fs::read(&fixture).unwrap();
        let (sha256, record) = record_of_bytes(&bytes);

        let pinned = resolve_named(&record, &fixture).unwrap();
        assert_eq!(pinned.sha256(), sha256);
        let copy = pinned.exec_path().to_path_buf();
        assert_eq!(
            copy.parent(),
            Some(ay_private_copy::copy_directory(&sha256).unwrap().as_path())
        );
        assert_eq!(std::fs::read(&copy).unwrap(), bytes);
        assert_eq!(
            ay_private_copy::copies_written_into(copy.parent().unwrap()),
            1
        );
        assert_eq!(
            digest_computation_count(&fixture),
            1,
            "the streamed digest is the admission digest"
        );
        assert_eq!(
            digest_computation_count(&copy),
            1,
            "the published copy is digested before it is used"
        );

        let again = resolve_named(&record, &fixture).unwrap();
        assert_eq!(again.exec_path(), copy);
        assert_eq!(digest_computation_count(&fixture), 1);
        assert_eq!(digest_computation_count(&copy), 1);
        pinned.revalidate().unwrap();
        let mut command = pinned.command().unwrap();
        let output = command.arg("probe").output().unwrap();
        assert_eq!(String::from_utf8_lossy(&output.stdout), "admitted probe\n");
    }

    /// The one-read admission never publishes bytes that are not the admitted
    /// identity: the record names other bytes, nothing appears in that
    /// digest's directory, no temporary is left, and the refusal is the one
    /// the separate admission digest gives, naming the fixture's digest. The
    /// refusal comes from that one read: the source is not read again.
    #[test]
    fn a_fresh_admission_of_other_bytes_publishes_nothing_and_is_refused_as_before() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(&fixture, "0", "a fresh admission of other bytes");
        let bytes = std::fs::read(&fixture).unwrap();
        let (actual, _) = record_of_bytes(&bytes);
        // A well-formed digest of different bytes.
        let (other, record) = record_of_bytes(b"other bytes than the fixture's");

        let refusal = resolve_named(&record, &fixture).unwrap_err();
        let AyIdentityRefusal::Mismatch {
            expected,
            found_sha256,
            ..
        } = &refusal
        else {
            panic!("expected a mismatch refusal, got {refusal}");
        };
        assert_eq!(expected.sha256(), other);
        assert_eq!(found_sha256, &actual);
        let other_directory = ay_private_copy::copy_directory(&other).unwrap();
        let left: Vec<_> = std::fs::read_dir(&other_directory)
            .map(|entries| {
                entries
                    .filter_map(Result::ok)
                    .map(|entry| entry.file_name())
                    .collect()
            })
            .unwrap_or_default();
        assert!(
            left.is_empty(),
            "nothing published or left behind: {left:?}"
        );
        assert_eq!(
            ay_private_copy::copies_written_into(&other_directory),
            1,
            "the one read streamed the source once"
        );
        assert_eq!(
            digest_computation_count(&fixture),
            1,
            "the mismatch is refused from the one read"
        );
    }

    /// The one-read admission's source stamp is checked after the read, and
    /// before the streamed digest is compared: a source rewritten while it is
    /// read is not admitted from the bytes read. The separate admission digest
    /// then reads the new bytes and refuses them, and nothing is published.
    #[test]
    fn a_source_rewritten_while_the_one_read_streams_it_is_not_admitted() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(&fixture, "0", "a source rewritten during the one read");
        let bytes = std::fs::read(&fixture).unwrap();
        let (sha256, record) = record_of_bytes(&bytes);
        let rewritten = b"#!/bin/sh\n# rewritten while it was read\nexit 70\n".to_vec();
        let (rewritten_sha256, _) = record_of_bytes(&rewritten);
        let replacement = rewritten.clone();
        on_next_whole_read(move |path| std::fs::write(path, replacement).unwrap());

        let refusal = resolve_named(&record, &fixture).unwrap_err();
        let AyIdentityRefusal::Mismatch {
            expected,
            found_sha256,
            ..
        } = &refusal
        else {
            panic!("expected a mismatch refusal, got {refusal}");
        };
        assert_eq!(expected.sha256(), sha256);
        assert_eq!(found_sha256, &rewritten_sha256);
        let copy_directory = ay_private_copy::copy_directory(&sha256).unwrap();
        assert_eq!(
            ay_private_copy::copies_written_into(&copy_directory),
            1,
            "the admitted bytes were streamed once"
        );
        let left: Vec<_> = std::fs::read_dir(&copy_directory)
            .map(|entries| {
                entries
                    .filter_map(Result::ok)
                    .map(|entry| entry.file_name())
                    .collect()
            })
            .unwrap_or_default();
        assert!(left.is_empty(), "nothing published: {left:?}");
    }

    /// A source no longer in the stamp the one-read admission was given is
    /// refused before it is read: nothing is streamed, nothing is admitted and
    /// nothing is published.
    #[test]
    fn the_one_read_refuses_a_stale_stamp_before_reading() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(&fixture, "0", "a stale stamp before the one read");
        let bytes = std::fs::read(&fixture).unwrap();
        let (sha256, _) = record_of_bytes(&bytes);
        let stale = file_stamp(&fixture).unwrap();
        // The same bytes in a new file state.
        std::fs::File::options()
            .write(true)
            .open(&fixture)
            .unwrap()
            .set_modified(std::time::UNIX_EPOCH + std::time::Duration::from_secs(1))
            .unwrap();
        assert_ne!(file_stamp(&fixture).as_ref(), Some(&stale));

        let mut admitted = false;
        let outcome =
            ay_private_copy::materialize_admitting(&fixture, &stale, &sha256, || admitted = true);
        assert!(matches!(outcome, ay_private_copy::OneRead::Undecided));
        assert!(!admitted);
        let copy_directory = ay_private_copy::copy_directory(&sha256).unwrap();
        assert_eq!(
            ay_private_copy::copies_written_into(&copy_directory),
            0,
            "refused before the read"
        );
        assert!(
            std::fs::read_dir(&copy_directory)
                .map(|mut entries| entries.next().is_none())
                .unwrap_or(true),
            "nothing published"
        );
    }

    /// The separate admission digest refuses a file that changed while it
    /// was being read, and records no digest for either file state.
    #[test]
    fn a_file_changed_while_it_is_digested_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = directory.path().join(exe("ay"));
        self_reexecuting_ay(&fixture, "0", "a file changed while it is digested");
        let before = file_stamp(&fixture).unwrap();
        on_next_whole_read(|path| std::fs::write(path, b"other bytes").unwrap());
        let refusal = digest_file(&fixture).unwrap_err();
        assert_eq!(
            refusal,
            "the executable changed while it was being digested"
        );
        assert!(
            digest_memo_slot(&fixture, &before)
                .lock()
                .unwrap()
                .is_none()
        );
    }

    /// Beginning the host's first-start assessment starts the file suspended
    /// and kills it before it runs. The spawn is held before the check that
    /// its child has not run, for three times as long as an unsuspended start
    /// of a like fixture took to write its marker (the control below; at
    /// least 500 ms, at most 5 s). A child that was not started suspended is
    /// not stopped when checked, and has written its marker by then, so both
    /// the check and the absent marker fail for it.
    #[cfg(target_os = "macos")]
    #[test]
    fn beginning_the_host_assessment_never_runs_the_file() {
        let directory = tempfile::tempdir().unwrap();
        let marker_of = |path: &Path| {
            let mut marker = path.as_os_str().to_owned();
            marker.push(".executed");
            PathBuf::from(marker)
        };

        // Control: the fixture marks a start made the way the spawn makes
        // one (argument `--version`, empty environment) within the hold.
        let control = directory.path().join(exe("run"));
        super::executable_fixtures::write_ay(&control, "begin the host assessment (control)");
        let began = std::time::Instant::now();
        let status = std::process::Command::new(&control)
            .arg("--version")
            .env_clear()
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(70));
        assert!(marker_of(&control).exists(), "the control marks its start");
        let marked_in = began.elapsed();
        let hold = (marked_in * 3).clamp(
            std::time::Duration::from_millis(500),
            std::time::Duration::from_secs(5),
        );
        eprintln!("an unsuspended start marked in {marked_in:?}; holding the spawn {hold:?}");

        let fixture = directory.path().join(exe("never-run"));
        super::executable_fixtures::write_ay(&fixture, "begin the host assessment");
        ay_private_copy::hold_next_spawned_child(hold);
        assert!(
            ay_private_copy::begin_host_assessment(&fixture),
            "the child was seen stopped, with no user time, before it was killed and reaped"
        );
        assert!(
            !marker_of(&fixture).exists(),
            "the file was run by the assessment spawn"
        );

        // A Mach-O executable (the AY copy's kind, not an interpreted
        // script) passes the same check: a fresh copy of `/usr/bin/true`.
        let mach_o = directory.path().join(exe("true-copy"));
        std::fs::copy("/usr/bin/true", &mach_o).unwrap();
        assert!(
            ay_private_copy::begin_host_assessment(&mach_o),
            "a suspended Mach-O child was seen stopped, with no user time"
        );
    }
}

/// Fixed-cost bound (L14-P5): concurrent digests of one file state read the
/// file once. The identity-warm thread and the first proof query both resolve
/// the AY and verify its private copy; each must not read a whole executable
/// the other is already reading. Every caller gets the one digest.
#[test]
fn concurrent_digests_of_one_file_state_read_it_once() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("concurrent-digest");
    // Large enough (8 MiB) that the readers overlap.
    let bytes: Vec<u8> = (0..(8usize << 20))
        .map(|index| (index % 253) as u8)
        .collect();
    std::fs::write(&file, &bytes).unwrap();
    let expected = format!("{:x}", <sha2::Sha256 as sha2::Digest>::digest(&bytes));

    let start = std::sync::Barrier::new(8);
    let digests: Vec<String> = std::thread::scope(|scope| {
        let readers: Vec<_> = (0..8)
            .map(|_| {
                scope.spawn(|| {
                    start.wait();
                    digest_file(&file).unwrap().0
                })
            })
            .collect();
        readers
            .into_iter()
            .map(|reader| reader.join().unwrap())
            .collect()
    });
    assert!(
        digests.iter().all(|digest| *digest == expected),
        "{digests:?}"
    );
    assert_eq!(
        digest_computation_count(&file),
        1,
        "one read for eight callers"
    );

    // A new file state is a new identity: it is read again, once.
    std::fs::write(&file, b"replaced").unwrap();
    assert_eq!(
        digest_file(&file).unwrap().0,
        format!("{:x}", <sha2::Sha256 as sha2::Digest>::digest(b"replaced"))
    );
    assert_eq!(digest_file(&file).unwrap().0.len(), 64);
    assert_eq!(digest_computation_count(&file), 2);
}
