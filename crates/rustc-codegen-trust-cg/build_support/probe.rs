// Throwaway compiler capability probes; never compiler verification authority.
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

use serde_json::Value;
use std::env;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

pub(super) const PROBE_TIMEOUT: Duration = Duration::from_secs(60);
const STREAM_LIMIT: u64 = 1024 * 1024;

#[derive(Debug)]
pub(super) struct Captured {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

fn stop(child: &mut Child) {
    if !matches!(child.try_wait(), Ok(None)) {
        return;
    }
    let _ = child.kill();
    let until = Instant::now() + Duration::from_millis(100);
    while Instant::now() < until {
        if !matches!(child.try_wait(), Ok(None)) {
            break;
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}

/// Bound child execution AND complete pipe capture, including inherited pipes.
/// Cleanup targets the direct child and does not claim escaped-descendant or
/// uninterruptible-process termination. Reader threads are never joined on an
/// incomplete stream; an error aborts this build instead of authorizing absence.
///
/// Preserve the inherited GNU advertisements and native scheduler handoff
/// together. Trust authenticates that transport and can recover the original
/// scheduler when an unaware descendant closes the advertised descriptors.
/// Removing only the GNU advertisements leaves an unusable native handoff.
/// These children also include real metadata compilations, whose scheduler
/// custody must survive; this helper neither grants nor replaces it.
pub(super) fn capture(command: &mut Command, timeout: Duration) -> Result<Captured, String> {
    let start = Instant::now();
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("cannot start {command:?}: {error}"))?;
    let (sender, receiver) = mpsc::channel();
    let streams: Vec<Box<dyn Read + Send>> = vec![
        Box::new(child.stdout.take().expect("piped stdout")),
        Box::new(child.stderr.take().expect("piped stderr")),
    ];
    for (index, stream) in streams.into_iter().enumerate() {
        let sender = sender.clone();
        std::thread::spawn(move || {
            let mut data = Vec::new();
            let result = stream
                .take(STREAM_LIMIT + 1)
                .read_to_end(&mut data)
                .map_err(|error| format!("pipe read failed: {error}"))
                .and_then(|_| {
                    if data.len() as u64 > STREAM_LIMIT {
                        Err("compiler output exceeded the 1 MiB stream limit".to_owned())
                    } else {
                        Ok(data)
                    }
                });
            let _ = sender.send((index, result));
        });
    }
    drop(sender);
    let mut output: [Option<Vec<u8>>; 2] = [None, None];
    let mut status = None;
    loop {
        while let Ok((index, result)) = receiver.try_recv() {
            match result {
                Ok(data) => output[index] = Some(data),
                Err(error) => {
                    stop(&mut child);
                    return Err(error);
                }
            }
        }
        if status.is_none() {
            match child.try_wait() {
                Ok(result) => status = result,
                Err(error) => {
                    stop(&mut child);
                    return Err(format!("cannot wait for compiler: {error}"));
                }
            }
        }
        if start.elapsed() >= timeout {
            stop(&mut child);
            return Err(format!(
                "compiler probe deadline {timeout:?} expired before complete exit/stdout/stderr"
            ));
        }
        if let Some(status) = status {
            if output.iter().all(Option::is_some) {
                return Ok(Captured {
                    status,
                    stdout: output[0].take().unwrap(),
                    stderr: output[1].take().unwrap(),
                });
            }
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}

pub(super) struct ProbeOptions {
    pub flags: Vec<&'static str>,
    pub tracked_arguments: bool,
}

pub(super) fn probe_options(compiler: &Path) -> ProbeOptions {
    let output = capture(Command::new(compiler).arg("-Zhelp"), PROBE_TIMEOUT)
        .unwrap_or_else(|error| panic!("cannot inspect build compiler options: {error}"));
    assert!(
        output.status.success() && output.stderr.is_empty(),
        "build compiler option listing failed or was ambiguous: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let listing = String::from_utf8(output.stdout).expect("UTF-8 compiler option listing");
    let mut lines = listing.lines().filter(|line| !line.trim().is_empty());
    assert!(
        matches!(
            lines.next().map(str::trim),
            Some("Available options:" | "Available unstable options:")
        ),
        "unrecognized compiler option-list header"
    );
    let mut names = std::collections::BTreeSet::new();
    for raw_line in lines {
        let line = raw_line.trim();
        if !line.starts_with("-Z") {
            // Current rustc/Trust help includes indented continuation lines
            // for options such as autodiff and unpretty. They describe the
            // preceding option and cannot advertise additional capabilities.
            assert!(
                !names.is_empty()
                    && raw_line.starts_with("        ")
                    && !line.starts_with("error:")
                    && !line.starts_with("error[")
                    && !line.starts_with("warning:"),
                "malformed compiler option continuation: {line}"
            );
            continue;
        }
        let (name, description) = line
            .strip_prefix("-Z ")
            .and_then(|row| row.trim_start().split_once('='))
            .unwrap_or_else(|| panic!("malformed compiler option row: {line}"));
        assert!(
            !name.is_empty()
                && name
                    .bytes()
                    .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
                && description.starts_with("val")
                && description.contains(" -- "),
            "malformed compiler option row: {line}"
        );
        assert!(names.insert(name), "duplicated compiler option row: {name}");
    }
    assert!(
        names.contains("codegen-backend"),
        "build compiler returned an unrecognized or incomplete -Zhelp listing"
    );
    ProbeOptions {
        flags: if names.contains("trust-verify") {
            vec!["-Ztrust-verify=off"]
        } else {
            Vec::new()
        },
        tracked_arguments: names.contains("trust-ir-cg-args"),
    }
}

#[derive(Clone, Copy)]
pub(super) enum MissingApi {
    EarlySession,
    TrackedArguments,
    MirMono,
    HirLangItem,
    MemoryLangItem,
    HirAttributes,
    CommonLinkage,
    CompiledModuleCacheLinks,
    SessionCrateType,
    UnstableSampleProfile,
    TupleScalarPair,
    BooleanCastPadding,
    BooleanIndirectStack,
    BfloatPrimitive,
    PpcF128Register,
    ScalarPointerResult,
    TerminatorAttributes,
    GotoLoopHints,
    BackendLaneCount,
    BoundFnArgs,
    GenericArgsRef,
    SuperClausesQuery,
    OwnClausesQuery,
    BoxDerefFacts,
}

fn primary_span_matches(diagnostic: &Value, path: &Path, source: &str, token: &str) -> bool {
    let Some(spans) = diagnostic["spans"].as_array() else {
        return false;
    };
    let primary: Vec<_> = spans
        .iter()
        .filter(|span| span["is_primary"] == true)
        .collect();
    if primary.len() != 1 {
        return false;
    }
    let span = primary[0];
    if span["file_name"].as_str() != path.to_str() || !span["expansion"].is_null() {
        return false;
    }
    let Some(line) = span["line_start"]
        .as_u64()
        .and_then(|line| usize::try_from(line).ok())
    else {
        return false;
    };
    if line == 0 || span["line_end"].as_u64() != Some(line as u64) {
        return false;
    }
    let Some(text) = source.lines().nth(line - 1) else {
        return false;
    };
    let Some(start) = span["column_start"]
        .as_u64()
        .and_then(|x| usize::try_from(x).ok())
    else {
        return false;
    };
    let Some(end) = span["column_end"]
        .as_u64()
        .and_then(|x| usize::try_from(x).ok())
    else {
        return false;
    };
    let Some(rows) = span["text"].as_array() else {
        return false;
    };
    start > 0
        && end > start
        && end <= text.chars().count() + 1
        && text
            .chars()
            .skip(start - 1)
            .take(end - start)
            .collect::<String>()
            == token
        && rows.len() == 1
        && rows[0]["text"].as_str() == Some(text)
        && rows[0]["highlight_start"].as_u64() == Some(start as u64)
        && rows[0]["highlight_end"].as_u64() == Some(end as u64)
}

fn exact_absence(diagnostics: &[Value], api: MissingApi, path: &Path, source: &str) -> bool {
    let mut errors = Vec::new();
    let mut summaries = 0;
    let mut notes = 0;
    // Trust brands the help command while preserving the diagnostic code.
    // Accept only these exact notes; unrelated failures still abort the build.
    let explanations = match api {
        MissingApi::TrackedArguments
        | MissingApi::CompiledModuleCacheLinks
        | MissingApi::UnstableSampleProfile
        | MissingApi::TerminatorAttributes => [
            "For more information about this error, try `rustc --explain E0609`.",
            "For more information about this error, try `trustc --explain E0609`.",
        ],
        MissingApi::EarlySession
        | MissingApi::MirMono
        | MissingApi::HirLangItem
        | MissingApi::HirAttributes => [
            "For more information about this error, try `rustc --explain E0432`.",
            "For more information about this error, try `trustc --explain E0432`.",
        ],
        MissingApi::MemoryLangItem
        | MissingApi::CommonLinkage
        | MissingApi::BfloatPrimitive
        | MissingApi::PpcF128Register
        | MissingApi::ScalarPointerResult
        | MissingApi::BackendLaneCount
        | MissingApi::BoundFnArgs
        | MissingApi::SuperClausesQuery
        | MissingApi::OwnClausesQuery
        | MissingApi::BoxDerefFacts => [
            "For more information about this error, try `rustc --explain E0599`.",
            "For more information about this error, try `trustc --explain E0599`.",
        ],
        MissingApi::SessionCrateType => [
            "For more information about this error, try `rustc --explain E0603`.",
            "For more information about this error, try `trustc --explain E0603`.",
        ],
        MissingApi::TupleScalarPair => [
            "For more information about this error, try `rustc --explain E0164`.",
            "For more information about this error, try `trustc --explain E0164`.",
        ],
        MissingApi::GenericArgsRef => [
            "For more information about this error, try `rustc --explain E0425`.",
            "For more information about this error, try `trustc --explain E0425`.",
        ],
        MissingApi::BooleanCastPadding
        | MissingApi::BooleanIndirectStack
        | MissingApi::GotoLoopHints => [
            "For more information about this error, try `rustc --explain E0026`.",
            "For more information about this error, try `trustc --explain E0026`.",
        ],
    };
    for diagnostic in diagnostics {
        let level = diagnostic["level"].as_str();
        if level == Some("error")
            && diagnostic["code"].is_null()
            && diagnostic["message"] == "aborting due to 1 previous error"
            && diagnostic["spans"].as_array().is_some_and(Vec::is_empty)
            && diagnostic["children"].as_array().is_some_and(Vec::is_empty)
        {
            summaries += 1;
        } else if level == Some("error") {
            errors.push(diagnostic);
        } else if level == Some("failure-note")
            && diagnostic["message"]
                .as_str()
                .is_some_and(|message| explanations.contains(&message))
            && diagnostic["code"].is_null()
            && diagnostic["spans"].as_array().is_some_and(Vec::is_empty)
            && diagnostic["children"].as_array().is_some_and(Vec::is_empty)
        {
            notes += 1;
        } else {
            return false;
        }
    }
    if errors.len() != 1 || summaries != 1 || notes > 1 {
        return false;
    }
    let diagnostic = errors[0];
    let Some(children) = diagnostic["children"].as_array() else {
        return false;
    };
    if children
        .iter()
        .any(|child| !matches!(child["level"].as_str(), Some("note" | "help")))
    {
        return false;
    }
    let code = diagnostic["code"]["code"].as_str();
    let message = diagnostic["message"].as_str().unwrap_or("");
    match api {
        MissingApi::EarlySession => {
            code == Some("E0432")
                && message == "unresolved import `rustc_session::EarlySession`"
                && primary_span_matches(diagnostic, path, source, "rustc_session::EarlySession")
        }
        MissingApi::TrackedArguments => {
            code == Some("E0609")
                && message.starts_with("no field `trust_ir_cg_args` on type `")
                && primary_span_matches(diagnostic, path, source, "trust_ir_cg_args")
        }
        MissingApi::MirMono => {
            code == Some("E0432")
                && ((message == "unresolved import `rustc_middle::mir::mono`"
                    && primary_span_matches(diagnostic, path, source, "mono"))
                    || (message == "unresolved import `rustc_middle::mir::mono::MonoItem`"
                        && primary_span_matches(diagnostic, path, source, "MonoItem")))
        }
        MissingApi::HirLangItem => {
            code == Some("E0432")
                && message == "unresolved import `rustc_hir::LangItem`"
                && primary_span_matches(diagnostic, path, source, "rustc_hir::LangItem")
        }
        MissingApi::MemoryLangItem => {
            code == Some("E0599")
                && message
                    == "no variant, associated function, or constant named `MemCpy` found for enum `LangItem` in the current scope"
                && primary_span_matches(diagnostic, path, source, "MemCpy")
        }
        MissingApi::HirAttributes => {
            code == Some("E0432")
                && message == "unresolved import `rustc_hir::attrs`"
                && primary_span_matches(diagnostic, path, source, "attrs")
        }
        MissingApi::CommonLinkage => {
            code == Some("E0599")
                && ["Linkage", "rustc_hir::attrs::Linkage", "rustc_attr_ir::Linkage"]
                    .into_iter()
                    .any(|name| message == format!(
                        "no variant, associated function, or constant named `Common` found for enum `{name}` in the current scope"
                    ))
                && primary_span_matches(diagnostic, path, source, "Common")
        }
        MissingApi::CompiledModuleCacheLinks => {
            code == Some("E0609")
                && message == "no field `links_from_incr_cache` on type `CompiledModule`"
                && primary_span_matches(diagnostic, path, source, "links_from_incr_cache")
        }
        MissingApi::SessionCrateType => {
            code == Some("E0603")
                && message == "enum `CrateType` is private"
                && primary_span_matches(diagnostic, path, source, "CrateType")
        }
        MissingApi::UnstableSampleProfile => {
            code == Some("E0609")
                && ["UnstableOptions", "rustc_session::config::UnstableOptions"]
                    .into_iter()
                    .any(|ty| message == format!("no field `profile_sample_use` on type `{ty}`"))
                && primary_span_matches(diagnostic, path, source, "profile_sample_use")
        }
        MissingApi::TupleScalarPair => {
            code == Some("E0164")
                && message == "expected tuple struct or tuple variant, found struct variant `rustc_abi::BackendRepr::ScalarPair`"
                && primary_span_matches(diagnostic, path, source, "rustc_abi::BackendRepr::ScalarPair(a, b)")
        }
        MissingApi::BooleanIndirectStack => {
            code == Some("E0026")
                && message == "variant `Indirect` does not have a field named `on_stack`"
                && primary_span_matches(diagnostic, path, source, "on_stack")
        }
        MissingApi::BfloatPrimitive => {
            code == Some("E0599")
                && message == "no variant, associated function, or constant named `F16B` found for enum `rustc_abi::Float` in the current scope"
                && primary_span_matches(diagnostic, path, source, "F16B")
        }
        MissingApi::PpcF128Register => {
            code == Some("E0599")
                && message == "no variant, associated function, or constant named `PpcF128` found for enum `RegKind` in the current scope"
                && primary_span_matches(diagnostic, path, source, "PpcF128")
        }
        MissingApi::ScalarPointerResult => {
            code == Some("E0599")
                && message == "no method named `discard_err` found for struct `rustc_middle::mir::interpret::Pointer<Prov>` in the current scope"
                && primary_span_matches(diagnostic, path, source, "discard_err")
        }
        MissingApi::TerminatorAttributes => {
            code == Some("E0609")
                && message == "no field `attributes` on type `&mut Terminator<'_>`"
                && primary_span_matches(diagnostic, path, source, "attributes")
        }
        MissingApi::GotoLoopHints => {
            code == Some("E0026")
                && message == "variant `Goto` does not have a field named `loop_hint_attrs`"
                && primary_span_matches(diagnostic, path, source, "loop_hint_attrs")
        }
        MissingApi::BackendLaneCount => {
            code == Some("E0599")
                && message == "no method named `as_u64` found for type `u64` in the current scope"
                && primary_span_matches(diagnostic, path, source, "as_u64")
        }
        MissingApi::BoundFnArgs => {
            code == Some("E0599")
                && message == "no method named `no_bound_vars` found for reference `&'tcx ty::list::RawList<(), rustc_middle::ty::GenericArg<'tcx>>` in the current scope"
                && primary_span_matches(diagnostic, path, source, "no_bound_vars")
        }
        MissingApi::GenericArgsRef => {
            code == Some("E0425")
                && message == "cannot find type `GenericArgsRef` in module `ty`"
                && primary_span_matches(diagnostic, path, source, "GenericArgsRef")
        }
        MissingApi::SuperClausesQuery => {
            code == Some("E0599")
                && message == "no method named `explicit_super_clauses_of` found for struct `TyCtxt<'tcx>` in the current scope"
                && primary_span_matches(diagnostic, path, source, "explicit_super_clauses_of")
        }
        MissingApi::OwnClausesQuery => {
            code == Some("E0599")
                && message == "no method named `clauses_of` found for struct `TyCtxt<'tcx>` in the current scope"
                && primary_span_matches(diagnostic, path, source, "clauses_of")
        }
        MissingApi::BoxDerefFacts => {
            code == Some("E0599")
                && message == "no method named `trust_box_deref_facts` found for struct `TyCtxt<'tcx>` in the current scope"
                && primary_span_matches(diagnostic, path, source, "trust_box_deref_facts")
        }
        MissingApi::BooleanCastPadding => {
            code == Some("E0026")
                && message == "variant `Cast` does not have a field named `pad_i32`"
                && primary_span_matches(diagnostic, path, source, "pad_i32")
        }
    }
}

/// The sysroot the REAL compile uses (`<RUSTC> --print sysroot --target $TARGET`; see
/// `target_compile_sysroot` in build.rs for why the target matters).
///
/// The probes run the resolved `<sysroot>/bin/<binary>` directly, not the selected
/// `RUSTC` — which under bootstrap is a shim that appends `--sysroot`. A compiler run
/// by path computes its DEFAULT sysroot from where its own driver library lives, and
/// for a stage0 that is the toolchain it was copied from, not the sysroot the real
/// build compiles against. Measured 2026-09-15: the snapshot stage0 ships rustc-dev
/// rmetas of an older generation (`librustc_middle-a198cdfc…`), while bootstrap's
/// stage0-sysroot and the rustc-private tool sysroot it adds with `-Lall` carry the
/// current one (`…-888712a9…`), so every `extern crate rustc_middle` probe failed
/// E0464 "multiple candidates" — a failure the real compile, which does get
/// `--sysroot`, never has. Passing the reported sysroot makes the probe see exactly
/// the crates the build will.
static PROBE_SYSROOT: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();

pub(super) fn set_probe_sysroot(sysroot: PathBuf) {
    assert!(
        PROBE_SYSROOT.set(sysroot).is_ok(),
        "probe sysroot recorded twice"
    );
}

/// Whether the ambient rustflags already choose a sysroot (`--sysroot X` or
/// `--sysroot=X`); an explicit choice there wins over the reported one.
fn flags_choose_sysroot<'a>(flags: impl IntoIterator<Item = &'a str>) -> bool {
    flags
        .into_iter()
        .any(|flag| flag == "--sysroot" || flag.starts_with("--sysroot="))
}

fn add_rustflags(command: &mut Command) {
    let flags: Vec<String> = if let Some(encoded) = env::var_os("CARGO_ENCODED_RUSTFLAGS") {
        let encoded = encoded
            .into_string()
            .expect("CARGO_ENCODED_RUSTFLAGS must be UTF-8");
        encoded
            .split('\x1f')
            .filter(|flag| !flag.is_empty())
            .map(str::to_owned)
            .collect()
    } else if let Some(flags) = env::var_os("RUSTFLAGS") {
        let flags = flags.into_string().expect("RUSTFLAGS must be UTF-8");
        flags.split_whitespace().map(str::to_owned).collect()
    } else {
        Vec::new()
    };
    // Nested, not a let-chain: this build script compiles as edition 2021.
    if !flags_choose_sysroot(flags.iter().map(String::as_str)) {
        if let Some(sysroot) = PROBE_SYSROOT.get() {
            command.arg("--sysroot").arg(sysroot);
        }
    }
    command.args(&flags);
}

pub(super) fn compile_probe(
    compiler: &Path,
    flags: &[&str],
    name: &str,
    source: &str,
    absent: Option<MissingApi>,
) -> bool {
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is set by cargo"));
    let path = out.join(format!("probe_{name}.rs"));
    let metadata = out.join(format!("probe_{name}.rmeta"));
    fs::write(&path, source).expect("write capability probe");
    // A previous successful build must not satisfy this invocation's output check.
    match fs::remove_file(&metadata) {
        Ok(()) => (),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => (),
        Err(error) => panic!("remove stale probe metadata: {error}"),
    }
    let mut command = Command::new(compiler);
    add_rustflags(&mut command);
    // This overrides ambient verification ONLY for discarded type-check probes,
    // never by emitting rustflags or mutating the actual bridge build environment.
    command
        .args(flags)
        .args([
            "--crate-name",
            &format!("rustc_codegen_trust_cg_probe_{name}"),
            "--crate-type=rlib",
            "--emit=metadata",
            "--error-format=json",
        ])
        .arg(&path)
        .arg("-o")
        .arg(&metadata);
    fs::write(
        out.join(format!("probe_{name}.command")),
        format!("{command:?}\n"),
    )
    .expect("record probe command");
    let output = capture(&mut command, PROBE_TIMEOUT)
        .unwrap_or_else(|error| panic!("capability probe {name} failed: {error}"));
    fs::write(out.join(format!("probe_{name}.stdout")), &output.stdout)
        .expect("record probe stdout");
    fs::write(out.join(format!("probe_{name}.stderr")), &output.stderr)
        .expect("record probe stderr");
    fs::write(
        out.join(format!("probe_{name}.status")),
        format!("{}\n", output.status),
    )
    .expect("record probe status");
    assert!(
        output.stdout.is_empty(),
        "capability probe {name} produced unexpected stdout"
    );
    let stderr = std::str::from_utf8(&output.stderr).expect("UTF-8 compiler diagnostics");
    let diagnostics: Vec<Value> = stderr
        .lines()
        .map(|line| {
            let value: Value = serde_json::from_str(line).unwrap_or_else(|error| {
                panic!("capability probe {name} returned non-JSON diagnostics: {error}: {stderr}")
            });
            assert_eq!(
                value["$message_type"], "diagnostic",
                "unexpected compiler diagnostic record: {value}"
            );
            value
        })
        .collect();
    if output.status.success() {
        assert!(
            diagnostics
                .iter()
                .all(|value| matches!(value["level"].as_str(), Some("warning" | "note" | "help"))),
            "successful probe {name} carried error diagnostics: {stderr}"
        );
        assert!(
            metadata
                .metadata()
                .is_ok_and(|meta| meta.is_file() && meta.len() > 0),
            "successful probe {name} produced no fresh metadata"
        );
        return true;
    }
    if output.status.code() == Some(1)
        && absent.is_some_and(|api| exact_absence(&diagnostics, api, &path, source))
    {
        return false;
    }
    panic!(
        "capability probe {name} failed for a reason other than its exact missing API ({}): {stderr}",
        output.status
    );
}

#[cfg(all(test, unix))]
mod tests {
    #[test]
    fn an_explicit_rustflags_sysroot_wins_over_the_reported_one() {
        assert!(super::flags_choose_sysroot(["-Lall=/x", "--sysroot", "/s"]));
        assert!(super::flags_choose_sysroot(["--sysroot=/s"]));
        assert!(!super::flags_choose_sysroot([
            "-Lall=/x",
            "-Ztrust-verify=off"
        ]));
        assert!(!super::flags_choose_sysroot(["--sysroot-ish"]));
    }

    use super::*;

    #[test]
    fn capture_requires_complete_streams_and_bounds_execution() {
        let result = capture(
            Command::new("sh").args(["-c", "printf done; printf note >&2"]),
            Duration::from_secs(2),
        )
        .unwrap();
        assert!(result.status.success());
        assert_eq!(result.stdout, b"done");
        assert_eq!(result.stderr, b"note");
        assert!(
            capture(
                Command::new("sh").args(["-c", "printf late"]),
                Duration::ZERO
            )
            .is_err()
        );
        let start = Instant::now();
        assert!(
            capture(
                Command::new("sh").args(["-c", "exec sleep 2"]),
                Duration::from_millis(30)
            )
            .unwrap_err()
            .contains("deadline")
        );
        assert!(start.elapsed() < Duration::from_secs(1));
        assert!(
            capture(
                Command::new("sh").args(["-c", "sleep 0.2 & exit 0"]),
                Duration::from_millis(30)
            )
            .unwrap_err()
            .contains("complete exit/stdout/stderr")
        );
    }

    #[test]
    fn capture_preserves_the_complete_scheduler_advertisement() {
        let mut command = Command::new("sh");
        command
            .args(["-c", "printf '%s|%s|%s|%s' \"${CARGO_MAKEFLAGS-unset}\" \"${MAKEFLAGS-unset}\" \"${MFLAGS-unset}\" \"${CARGO_JOBSERVER_HANDOFF-unset}\""])
            .env("CARGO_MAKEFLAGS", "-j --jobserver-auth=3,5")
            .env("MAKEFLAGS", "--jobserver-fds=3,5")
            .env("MFLAGS", "-j")
            .env("CARGO_JOBSERVER_HANDOFF", "opaque-advertisement-not-authority");
        let result = capture(&mut command, Duration::from_secs(2)).unwrap();
        assert!(result.status.success());
        assert_eq!(
            result.stdout,
            b"-j --jobserver-auth=3,5|--jobserver-fds=3,5|-j|opaque-advertisement-not-authority"
        );
        assert!(result.stderr.is_empty());
    }

    #[test]
    fn capture_refuses_missing_tools_and_unbounded_output() {
        assert!(
            capture(
                &mut Command::new("/nonexistent/bridge-probe-compiler"),
                Duration::from_secs(1)
            )
            .is_err()
        );
        assert!(
            capture(
                Command::new("sh").args(["-c", "exec head -c 1048577 /dev/zero"]),
                Duration::from_secs(2)
            )
            .unwrap_err()
            .contains("stream limit")
        );
    }
}
