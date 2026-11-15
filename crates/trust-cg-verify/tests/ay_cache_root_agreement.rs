// trust-cg-verify/tests/ay_cache_root_agreement.rs - one AY cache root for every reader
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// AY is started only from its private copy under `<user cache>/trust-cg/
// ay-exec` (`ay_private_copy`). Process-level admission (`trust-cg
// --print-ay-identity`, which the Linux floor's `--require-proof-tools`
// preflight runs, and `ay_bridge::solver_refusal_note`) and each
// function-verification request (`FunctionVerificationRequest::capture`,
// whose `ay_refusal_note` every proof-promotion refusal over its evidence
// carries) must resolve that root, and so admit or refuse AY, identically,
// in one file-system state. X-HOST-P13's second audit measured them
// disagreeing: a request froze an empty or relative `XDG_CACHE_HOME` (or an
// empty `HOME`) anchored to its working directory, so under a group-writable
// checkout (umask 0002) AY was refused inside every request with no
// `TCG-AY-IDENTITY` note while the preflight and the note reported it
// admitted (`jit_cert_cache_identity_aarch64` 0/9), and under a private one a
// second 655 MB copy of AY was written into the working directory.
//
// Each case runs this binary as a child, with the case's `XDG_CACHE_HOME`,
// `HOME`, working directory and umask, where it reports what each reader
// resolved. The parent requires: the request and the process admit the same
// private copy, or refuse with the same refusal, which the note carries as
// `TCG-AY-IDENTITY-UNMATERIALIZED`; an empty or relative `XDG_CACHE_HOME` is
// ignored (XDG Base Directory specification), a relative `HOME` names no
// cache; and nothing is ever written into the working directory. Requires
// the build's recorded toolchain AY: without one this target fails, it does
// not pass. Test rung: cache-root agreement, not a proof.

#![cfg(unix)]

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::{Value, json};
use trust_cg_verify::FunctionVerificationRequest;
use trust_cg_verify::ay_identity::{
    AyIdentityRefusal, PinnedAy, recorded_toolchain_ay_identity, resolve_for_process,
};
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;

const CHILD: &str = "AY_CACHE_ROOT_AGREEMENT_CHILD";
const NAME: &str = "every_reader_resolves_one_ay_cache_root_whatever_the_working_directory";
const REPORT: &str = "AY_CACHE_ROOT_REPORT ";

fn outcome(resolved: Result<&PinnedAy, &AyIdentityRefusal>) -> Value {
    match resolved {
        Ok(pinned) => json!({ "exec_path": pinned.exec_path().display().to_string() }),
        Err(refusal) => json!({ "code": refusal.code(), "refusal": refusal.to_string() }),
    }
}

/// The child: what each reader resolves in this process's environment.
fn report() -> Value {
    let process = resolve_for_process();
    let request = FunctionVerificationRequest::capture(
        VerificationConfig::default(),
        ProvenanceXCheckMode::Enforce,
    );
    let note = request.ay_refusal_note();
    let request = match (request.ay_solver(), request.ay_refusal()) {
        (Some(pinned), _) => outcome(Ok(pinned)),
        (None, Some(refusal)) => outcome(Err(refusal)),
        (None, None) => json!({ "code": "none" }),
    };
    json!({
        "process": outcome(process.as_ref()),
        "request": request,
        "note": note,
        "process_note": trust_cg_verify::ay_bridge::solver_refusal_note(),
        "base": trust_cg_process_env::private_fs::current_user_cache_base()
            .map(|base| base.display().to_string())
            .unwrap_or_else(|error| format!("refused: {error}")),
    })
}

fn private_dir(path: &Path, mode: u32) -> PathBuf {
    std::fs::create_dir_all(path).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).unwrap();
    path.to_path_buf()
}

fn entries(path: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(path)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

/// Every `ay-exec/<digest>/ay` copy below `root`.
fn copies(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let Ok(read) = std::fs::read_dir(&directory) else {
            continue;
        };
        for entry in read.flatten() {
            let path = entry.path();
            let kind = entry.file_type().unwrap();
            if kind.is_dir() {
                pending.push(path);
            } else if path.file_name().is_some_and(|name| name == "ay")
                && path
                    .ancestors()
                    .nth(2)
                    .is_some_and(|exec| exec.ends_with("ay-exec"))
            {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

/// Both readers refused with the same `TCG-AY-IDENTITY-UNMATERIALIZED`
/// refusal, which names each of `needed`, and the refusal note carries it.
fn unmaterialized(report: &Value, needed: &[String]) {
    for reader in ["process", "request"] {
        assert_eq!(
            report[reader]["code"], "TCG-AY-IDENTITY-UNMATERIALIZED",
            "{reader}: {report}"
        );
    }
    let refusal = report["process"]["refusal"].as_str().unwrap();
    for needed in needed {
        assert!(
            refusal.contains(needed.as_str()),
            "{needed:?} missing: {report}"
        );
    }
    for key in ["note", "process_note"] {
        let note = report[key].as_str().unwrap_or_default();
        assert!(
            note.contains("[TCG-AY-IDENTITY-UNMATERIALIZED]") && note.contains(refusal),
            "the {key} carries the request's refusal: {report}"
        );
    }
    assert!(
        report["note"]
            .as_str()
            .unwrap_or_default()
            .starts_with(trust_cg_verify::ay_bridge::REQUEST_REFUSAL_NOTE_HEAD),
        "the note a proof-promotion refusal carries is the request's own: {report}"
    );
}

struct Case<'a> {
    name: &'a str,
    umask: &'a str,
    xdg: Option<&'a str>,
    home: &'a str,
    cwd: &'a Path,
}

fn run_case(case: &Case<'_>) -> Value {
    let mut command = Command::new("/bin/sh");
    command
        .arg("-c")
        .arg("umask \"$1\" && shift && exec \"$0\" \"$@\"")
        .arg(std::env::current_exe().unwrap())
        .arg(case.umask)
        .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
        .current_dir(case.cwd)
        .env(CHILD, "1")
        .env("HOME", case.home)
        // The toolchain route, as a compile's own solver calls take it.
        .env_remove("AY_SOLVER_PATH")
        .env_remove("TCG_PROOF_CACHE_DIR")
        .env_remove("TCG_PROOF_CERT_STORE");
    match case.xdg {
        Some(xdg) => command.env("XDG_CACHE_HOME", xdg),
        None => command.env_remove("XDG_CACHE_HOME"),
    };
    let output = command.output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "{}: child {}\n{stdout}\n{stderr}",
        case.name,
        output.status
    );
    let line = stdout
        .lines()
        .find_map(|line| line.find(REPORT).map(|at| &line[at + REPORT.len()..]))
        .unwrap_or_else(|| panic!("{}: no report\n{stdout}", case.name));
    serde_json::from_str(line).unwrap()
}

#[test]
fn every_reader_resolves_one_ay_cache_root_whatever_the_working_directory() {
    if std::env::var_os(CHILD).is_some() {
        println!("{REPORT}{}", report());
        return;
    }
    let identity = recorded_toolchain_ay_identity().unwrap_or_else(|refusal| {
        panic!(
            "this target compares the readers of the recorded toolchain AY's cache root; a \
             build that records none is a failure here, not a pass: {refusal}"
        )
    });

    let scratch = tempfile::Builder::new()
        .prefix("ay-cache-root-agreement-")
        .tempdir()
        .unwrap();
    let root = private_dir(&scratch.path().canonicalize().unwrap(), 0o700);
    let home = private_dir(&root.join("home"), 0o700);
    let home_text = home.to_str().unwrap();
    // What `mkdir` gives a checkout under umask 0002, and a private one.
    let open_cwd = private_dir(&root.join("checkout-0775"), 0o775);
    let private_cwd = private_dir(&root.join("checkout-0700"), 0o700);
    // An absolute XDG_CACHE_HOME beneath a directory others may write.
    let loose = private_dir(&root.join("shared-0775"), 0o775);
    let loose_xdg = private_dir(&loose.join("xdg"), 0o700);
    let home_cache = home.join(".cache");
    let home_cache_text = home_cache.to_str().unwrap();
    let admitted = home_cache
        .join("trust-cg/ay-exec")
        .join(identity.sha256())
        .join("ay");

    let cases: [(Option<&str>, &str, &PathBuf, &str); 7] = [
        (None, home_text, &open_cwd, "0002"),
        (Some(""), home_text, &open_cwd, "0002"),
        (Some("relcache"), home_text, &open_cwd, "0002"),
        (Some(home_cache_text), home_text, &open_cwd, "0002"),
        (Some(""), home_text, &private_cwd, "0002"),
        (Some("relcache"), home_text, &private_cwd, "0022"),
        (Some(""), home_text, &open_cwd, "0077"),
    ];
    for (xdg, home, cwd, umask) in cases {
        let name = format!(
            "XDG_CACHE_HOME={xdg:?} HOME={home} cwd={} umask {umask}",
            cwd.display()
        );
        let report = run_case(&Case {
            name: &name,
            umask,
            xdg,
            home,
            cwd,
        });
        assert_eq!(report["base"], home_cache_text, "{name}: {report}");
        for reader in ["process", "request"] {
            assert_eq!(
                report[reader]["exec_path"],
                admitted.to_str().unwrap(),
                "{name}: {reader} admits the one private copy: {report}"
            );
        }
        assert_eq!(report["note"], Value::Null, "{name}: {report}");
        assert_eq!(report["process_note"], Value::Null, "{name}: {report}");
        assert_eq!(
            entries(cwd),
            Vec::<String>::new(),
            "{name}: the working directory"
        );
    }
    assert_eq!(
        copies(&root),
        vec![admitted.clone()],
        "exactly one private copy"
    );
    assert_eq!(
        std::fs::symlink_metadata(&admitted)
            .unwrap()
            .permissions()
            .mode()
            & 0o7777,
        0o500
    );
    for directory in [
        home_cache.clone(),
        home_cache.join("trust-cg"),
        home_cache.join("trust-cg/ay-exec"),
    ] {
        assert_eq!(
            std::fs::symlink_metadata(&directory)
                .unwrap()
                .permissions()
                .mode()
                & 0o7777,
            0o700,
            "{}",
            directory.display()
        );
    }

    // No absolute cache base: refused by every reader alike, never the CWD.
    for (xdg, home) in [
        (None, ""),
        (Some("relcache"), "relative-home"),
        (Some(""), ""),
    ] {
        let name = format!("XDG_CACHE_HOME={xdg:?} HOME={home:?}");
        let report = run_case(&Case {
            name: &name,
            umask: "0002",
            xdg,
            home,
            cwd: &open_cwd,
        });
        assert_eq!(report["process"], report["request"], "{name}: {report}");
        unmaterialized(&report, &[format!("HOME={home} is not absolute")]);
        assert_eq!(
            entries(&open_cwd),
            Vec::<String>::new(),
            "{name}: the working directory"
        );
    }

    // An absolute XDG_CACHE_HOME beneath a group-writable directory: refused
    // alike, naming the directory, its mode and the remedy; never changed.
    let name = format!("XDG_CACHE_HOME={}", loose_xdg.display());
    let report = run_case(&Case {
        name: &name,
        umask: "0002",
        xdg: loose_xdg.to_str(),
        home: home_text,
        cwd: &open_cwd,
    });
    assert_eq!(report["process"], report["request"], "{name}: {report}");
    unmaterialized(
        &report,
        &[
            format!("{} has mode 0775", loose.display()),
            format!("`chmod go-w {}`", loose.display()),
        ],
    );
    assert_eq!(
        std::fs::symlink_metadata(&loose)
            .unwrap()
            .permissions()
            .mode()
            & 0o7777,
        0o775
    );
    assert_eq!(copies(&loose), Vec::<PathBuf>::new(), "no copy beneath it");
    assert_eq!(entries(&open_cwd), Vec::<String>::new());
    assert_eq!(
        copies(&root),
        vec![admitted],
        "still exactly one private copy"
    );
}
