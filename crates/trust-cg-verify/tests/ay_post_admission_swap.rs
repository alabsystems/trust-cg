// trust-cg-verify/tests/ay_post_admission_swap.rs - the real AY, swapped after admission
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Measured on 288ac2d2c: the admitted AY (0.26.0 build 9624) re-executes
// ITSELF by the path it was started from (`ay_sys::govern::arm`, its kernel
// memory governor), so replacing the admitted file after spawn ran a decoy 6
// of 9 times through `trustc` and inside the gate replay, and a verdict named
// the admitted AY while another program produced it.
//
// This test uses the REAL recorded AY bytes: a byte copy is admitted as an
// explicit path, started through `PinnedAy::command` (the only launcher), and
// replaced by a decoy at several delays after spawn. The decoy must never run
// and AY must answer. A control starts the same copy BY ITS PATH with the same
// swap, to show the attack is live on this host; without that the first half
// would prove nothing.
//
// A build that recorded no AY admits nothing; that is asserted, not skipped.

#![cfg(unix)]

use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;

use trust_cg_verify::ay_identity::{recorded_toolchain_ay_identity, resolve_explicit_path};

const SWAP_DELAYS_MS: [u64; 5] = [0, 5, 20, 50, 150];

fn decoy_over(path: &Path, log: &Path) {
    let staged = path.with_extension("decoy");
    std::fs::write(
        &staged,
        format!(
            "#!/bin/sh\nprintf 'DECOY %s\\n' \"$*\" >> '{}'\nprintf 'unsat\\n'\n",
            log.display()
        ),
    )
    .unwrap();
    std::fs::set_permissions(&staged, std::fs::Permissions::from_mode(0o755)).unwrap();
    std::fs::rename(&staged, path).unwrap();
}

/// Start `command` on a satisfiable query, replace `admitted` after `delay`,
/// and return (stdout, whether the decoy ran).
fn swap_during_start(
    mut command: Command,
    admitted: &Path,
    query: &Path,
    log: &Path,
    delay: u64,
) -> (String, bool) {
    let child = command
        .arg(query)
        .env("GOVERN_AY_MB", "2048")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    std::thread::sleep(Duration::from_millis(delay));
    decoy_over(admitted, log);
    let output = child.wait_with_output().unwrap();
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        log.exists(),
    )
}

#[test]
fn the_real_ay_swapped_after_admission_never_runs_the_replacement() {
    let directory = tempfile::tempdir().unwrap();
    let recorded = match recorded_toolchain_ay_identity() {
        Ok(identity) => identity,
        Err(refusal) => {
            let probe = directory.path().join("ay");
            std::fs::write(&probe, b"#!/bin/sh\nexit 0\n").unwrap();
            std::fs::set_permissions(&probe, std::fs::Permissions::from_mode(0o755)).unwrap();
            assert_eq!(
                resolve_explicit_path(&probe).unwrap_err().code(),
                refusal.code()
            );
            return;
        }
    };
    // The toolchain AY is the file the recorded digest names.
    let toolchain = trust_cg_verify::ay_identity::resolve_for_process()
        .expect("the recorded toolchain AY is admitted");
    assert_eq!(toolchain.sha256(), recorded.sha256());
    let bytes = std::fs::read(toolchain.path()).unwrap();
    let query = directory.path().join("sat.smt2");
    std::fs::write(
        &query,
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= x #x2a))\n(check-sat)\n",
    )
    .unwrap();

    let mut control_hits = 0;
    for delay in SWAP_DELAYS_MS {
        let case = directory.path().join(format!("case-{delay}"));
        std::fs::create_dir(&case).unwrap();
        let admitted = case.join("ay");
        let log = case.join("decoy.log");

        // Through the launcher: the admitted bytes answer, whatever the path
        // holds after admission.
        std::fs::write(&admitted, &bytes).unwrap();
        std::fs::set_permissions(&admitted, std::fs::Permissions::from_mode(0o755)).unwrap();
        let pinned = resolve_explicit_path(&admitted).unwrap();
        assert_eq!(pinned.sha256(), recorded.sha256());
        assert_ne!(pinned.exec_path(), admitted.as_path());
        let (stdout, decoy_ran) =
            swap_during_start(pinned.command().unwrap(), &admitted, &query, &log, delay);
        assert!(
            !decoy_ran,
            "swap {delay} ms after spawn ran the decoy through PinnedAy::command: {}",
            std::fs::read_to_string(&log).unwrap_or_default()
        );
        assert_eq!(
            stdout.lines().next(),
            Some("sat"),
            "swap {delay} ms: the admitted AY must answer"
        );
        assert_eq!(
            pinned.command().unwrap_err().code(),
            "TCG-AY-IDENTITY-CHANGED"
        );

        // Control: the same bytes started by the admitted PATH.
        std::fs::remove_file(&admitted).unwrap();
        std::fs::remove_file(&log).ok();
        std::fs::write(&admitted, &bytes).unwrap();
        std::fs::set_permissions(&admitted, std::fs::Permissions::from_mode(0o755)).unwrap();
        let (_, decoy_ran) =
            swap_during_start(Command::new(&admitted), &admitted, &query, &log, delay);
        control_hits += usize::from(decoy_ran);
    }
    eprintln!(
        "control: the decoy ran in {control_hits} of {} path-started runs",
        SWAP_DELAYS_MS.len()
    );
    assert!(
        control_hits > 0,
        "the control never ran the decoy, so this host did not exercise AY's self re-exec"
    );
}
