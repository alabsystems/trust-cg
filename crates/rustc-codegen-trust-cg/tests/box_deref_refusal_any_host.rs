//! Host-independent twin of `current_private_api.rs`
//! `actual_box_deref_mir_refuses_before_object_emission`, which is compiled
//! only on aarch64-apple-darwin.
//!
//! The refusal under test is target-independent: `refuse_unmodeled_body`
//! walks MIR before any lowering, so it must hold on every host the bridge
//! builds on. This file has no OS or architecture gate; it compiles a library
//! for the host target and needs no linker, C compiler or native prerequisite.
//!
//! The bridge emits `Inst::BoxDeref` only when the compiler it was built
//! against exports the Box fact query (`cfg(rustc_box_deref_facts)`, probed in
//! `build.rs`) AND that compiler admits the site. Both build-capability arms
//! are pinned here: without the query the cast is unconditionally refused;
//! with it, the default floor still refuses and the explicit named-premise
//! diagnostic lane emits an object plus both disclosure lines.
//! Author: Andrew Yates | Copyright 2026 | License: Apache-2.0
#![cfg(rustc_session_split)]

use std::process::Command;

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

/// Preserve, but never create, the native owner's GNU jobserver descriptors
/// across this test's direct compiler children.
///
/// Targo deliberately gives a libtest no compiler authority of its own.  The
/// canonical bridge runner executes the already-built test under the admitted
/// GNU owner; Rust's Darwin `Command` path otherwise closes the inherited
/// descriptors even though their exact locators remain in `MAKEFLAGS`.  Force
/// the fork path and clear only `FD_CLOEXEC` on descriptors that are both
/// advertised and live.  A missing, malformed, or closed advertisement stays
/// a hard refusal; this helper never opens a pipe or grants scheduler credit.
#[cfg(unix)]
fn retain_inherited_compiler_custody(command: &mut Command) {
    use std::collections::BTreeSet;
    use std::os::unix::process::CommandExt;

    const F_GETFD: i32 = 1;
    const F_SETFD: i32 = 2;
    const FD_CLOEXEC: i32 = 1;

    unsafe extern "C" {
        fn fcntl(fd: i32, command: i32, ...) -> i32;
    }

    let mut descriptors = BTreeSet::new();
    let mut advertised = false;
    for name in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
        let Some(value) = std::env::var_os(name) else {
            continue;
        };
        let value = value
            .to_str()
            .unwrap_or_else(|| panic!("{name} is not Unicode"));
        let mut selected = None;
        for word in value.split_ascii_whitespace() {
            for prefix in ["--jobserver-auth=", "--jobserver-fds="] {
                if let Some(raw) = word.strip_prefix(prefix) {
                    selected = Some(raw);
                }
            }
        }
        let Some(raw) = selected else {
            continue;
        };
        advertised = true;
        if raw.starts_with("fifo:") {
            continue;
        }
        let Some((read, write)) = raw.split_once(',') else {
            panic!("malformed {name} jobserver advertisement: {raw:?}");
        };
        for text in [read, write] {
            let descriptor: i32 = text
                .parse()
                .unwrap_or_else(|_| panic!("malformed {name} jobserver descriptor: {text:?}"));
            assert!(
                descriptor >= 3,
                "invalid {name} jobserver descriptor: {descriptor}"
            );
            let flags = unsafe { fcntl(descriptor, F_GETFD) };
            assert!(
                flags >= 0,
                "{name} advertises closed jobserver descriptor {descriptor}: {}",
                std::io::Error::last_os_error()
            );
            descriptors.insert(descriptor);
        }
    }
    assert!(
        advertised,
        "actual compiler fixture requires an inherited GNU scheduler advertisement"
    );

    let descriptors: Vec<_> = descriptors.into_iter().collect();
    // SAFETY: the closure performs only async-signal-safe `fcntl` calls and
    // constructs an `io::Error` from errno.  Every fd was authenticated as a
    // live advertised jobserver endpoint in the parent immediately above.
    unsafe {
        command.pre_exec(move || {
            for descriptor in &descriptors {
                let flags = fcntl(*descriptor, F_GETFD);
                if flags < 0 || fcntl(*descriptor, F_SETFD, flags & !FD_CLOEXEC) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
}

#[cfg(not(unix))]
fn retain_inherited_compiler_custody(_command: &mut Command) {
    panic!("actual Trust compiler fixtures require Unix jobserver custody");
}

fn oracle_command() -> Command {
    let mut command = toolchain_support::rustc_command();
    retain_inherited_compiler_custody(&mut command);
    command
}

#[cfg(rustc_box_deref_facts)]
fn driver_command() -> Command {
    let mut command = toolchain_support::rustc_driver_command();
    retain_inherited_compiler_custody(&mut command);
    command
}

/// Sources that reach `BoxDerefTransmute` in unoptimized MIR, by name.
const FIXTURES: [(&str, &str); 2] = [
    (
        "shared_reference_to_box",
        r#"
#[unsafe(no_mangle)]
#[inline(never)]
pub fn dereference_box(value: &Box<u8>) -> u8 { **value }
"#,
    ),
    (
        "box_by_value",
        r#"
#[unsafe(no_mangle)]
#[inline(never)]
pub fn read_box(value: Box<u64>) -> u64 { *value }
"#,
    ),
];

#[cfg(not(rustc_box_deref_facts))]
#[test]
fn capability_absent_refuses_before_object_emission_on_this_host() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "tcg-box-deref-any-host-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).expect("create owned fixture directory");
    let dylib = backend_artifact_support::current_test_backend();
    for (name, text) in FIXTURES {
        let source = directory.join(format!("{name}.rs"));
        std::fs::write(&source, text).expect("write actual Rust fixture");
        let oracle_mir = directory.join(format!("{name}.mir"));
        let oracle = oracle_command()
            .args(["--crate-type=lib", "-Zmir-opt-level=0", "--emit=mir"])
            .arg(&source)
            .arg("-o")
            .arg(&oracle_mir)
            .output()
            .expect("run actual compiler oracle");
        assert!(
            oracle.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&oracle.stderr)
        );
        let mir = std::fs::read_to_string(&oracle_mir).expect("read actual emitted MIR");
        // The control: without the operation in MIR the refusal below would
        // be some other construct's.
        assert!(
            mir.contains("BoxDerefTransmute"),
            "{name}: fixture did not exercise the current operation: {mir}"
        );
        let object = directory.join(format!("{name}.o"));
        let output = oracle_command()
            .arg(format!("-Zcodegen-backend={}", dylib.display()))
            .args([
                "--crate-type=lib",
                "-Cpanic=abort",
                "-Zmir-opt-level=0",
                "--emit=obj",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .output()
            .expect("run current backend");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{name}: an unmodeled Box validity obligation was admitted: {stderr}"
        );
        assert!(
            stderr.contains("[TCG-BOX-DEREF]"),
            "{name}: wrong refusal: {stderr}"
        );
        assert!(
            !object.exists(),
            "{name}: refused program emitted an object at {}",
            object.display()
        );
        println!(
            "[box_deref_refusal_any_host] {name}: refused with [TCG-BOX-DEREF] on {}-{}",
            std::env::consts::ARCH,
            std::env::consts::OS
        );
    }
    let _ = std::fs::remove_dir_all(&directory);
}

#[cfg(rustc_box_deref_facts)]
#[test]
fn capability_present_keeps_default_refusal_and_enables_only_the_disclosed_opt_in() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "tcg-box-deref-capability-present-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).expect("create owned fixture directory");
    let source = directory.join("box_by_value.rs");
    std::fs::write(&source, FIXTURES[1].1).expect("write actual Rust fixture");
    let dylib = backend_artifact_support::current_test_backend();

    let compile = |name: &str, knobs: &[&str]| {
        let object = directory.join(format!("{name}.o"));
        let output = driver_command()
            .arg("--edition=2021")
            .arg(format!("-Zcodegen-backend={}", dylib.display()))
            .arg(toolchain_support::backend_knobs_arg(knobs))
            .args([
                "--crate-type=lib",
                "-Cpanic=abort",
                "-Coverflow-checks=off",
                "-Zmir-opt-level=0",
                "--emit=obj",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .output()
            .expect("run fact-capable compiler");
        (object, output)
    };

    let (default_object, default_output) = compile("default", &["no-proof-certs"]);
    let default_stderr = String::from_utf8_lossy(&default_output.stderr);
    assert!(
        !default_output.status.success(),
        "the default consumer floor admitted a Box fact: {default_stderr}"
    );
    assert!(
        default_stderr.contains("[TCG-BOX-DEREF]"),
        "{default_stderr}"
    );
    assert!(!default_object.exists());

    let (opted_object, opted_output) = compile(
        "named-premise",
        &["no-proof-certs", "box-deref-named-premise"],
    );
    let opted_stderr = String::from_utf8_lossy(&opted_output.stderr);
    assert!(
        opted_output.status.success(),
        "the compiler admitted the site but the explicit consumer failed: {opted_stderr}"
    );
    assert!(
        opted_object.is_file(),
        "the admitted compile emitted no object"
    );
    assert!(
        opted_stderr.contains("[TCG-BOX-DEREF-FACT]")
            && opted_stderr.contains("root param_by_value"),
        "the producer fact was not disclosed: {opted_stderr}"
    );
    assert!(
        opted_stderr.contains("[TCG-BOX-DEREF-ASSUMED]")
            && opted_stderr.contains("admitted for compilation under named assumptions"),
        "the consumer assumption was not disclosed accurately: {opted_stderr}"
    );
    let _ = std::fs::remove_dir_all(&directory);
}
