use super::*;
use std::os::unix::fs::PermissionsExt;

/// A new Lean process control, started once before any deadline
/// (`test_fixtures::warm`), so the deadlines below bound what it does, not the
/// host's first-exec assessment of a new file.
fn script(body: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    use crate::ay_identity::test_fixtures::{warm, warm_guard};
    let dir = tempfile::tempdir().expect("owned Lean process control");
    let path = dir.path().join("lean-control");
    std::fs::write(&path, format!("#!/bin/sh\n{}\n{body}\n", warm_guard()))
        .expect("write Lean process control");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
        .expect("chmod Lean control");
    warm(&path);
    (dir, path)
}

#[test]
fn subprocess_lean_deadline_includes_inherited_output_pipes() {
    let (_dir, path) = script("(sleep 3; printf 'late output\\n') &\nexit 0");
    let start = Instant::now();
    let result = run_command_with_timeout(path.to_str().expect("script path"), &["check"], 1000);
    assert!(
        matches!(result, LeanCommandOutcome::Timeout),
        "unclosed output must not turn a deadline into successful replay"
    );
    assert!(start.elapsed() < Duration::from_secs(2));
}

#[test]
fn subprocess_lean_retains_late_sorry_before_accepting_a_complete_transcript() {
    assert!(output_contains_explicit_sorry(
        "",
        "warning: declaration uses explicit sorry\n"
    ));
    let (_dir, path) =
        script("(sleep 0.1; printf 'warning: declaration uses explicit sorry\\n' >&2) &\nexit 0");
    let result = run_command_with_timeout(path.to_str().expect("script path"), &["check"], 5000);
    let LeanCommandOutcome::Completed {
        status,
        stdout,
        stderr,
    } = result
    else {
        panic!("finite child output should complete within the deadline: {result:?}");
    };
    assert!(status.success());
    assert!(
        output_contains_explicit_sorry(&stdout, &stderr),
        "a direct-child exit is not permission to discard a descendant's sorry report"
    );
}
