//! The harness shared by the Linux AArch64 runtime twins of Darwin bridge
//! fixtures: `static_data_linux`, `drop_heap_linux` and
//! `coroutine_generator_linux`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0
//!
//! MANDATORY ON ITS HOST. Each twin is a required target of
//! `scripts/check_linux_aarch64_bridge.py`. A missing prerequisite fails the
//! test by name, never skips it: the backend-knob option (`require_knobs`),
//! the host triple (`require_host`), and every tool a step spawns (`cc`,
//! `readelf`, `objdump`, `timeout`, `sha256sum`, `mktemp`), whose spawn
//! failure panics. The runner binds a freshly built backend by path and
//! SHA-256 (`TCG_TEST_BACKEND_PATH`/`TCG_TEST_BACKEND_SHA256`); a standalone
//! invocation instead loads, and hashes, the library Cargo built for this
//! test build. Nothing here builds into the shared target directory or
//! selects a cached library.
//!
//! EVIDENCE BOUNDARY. Every compile, CG and LLVM alike, starts from the shared
//! build-compiler constructor (`toolchain_support::rustc_command`: edition
//! 2021 and `-Ztrust-verify=off`), and every bridge compile passes the
//! backend's `no-proof-certs` knob. No object carries a certificate: a pass is
//! native TESTING evidence for the exercised shapes, not proof, certificate or
//! exact-object-binding evidence. GNU cc/ld, binutils, glibc and the
//! LLVM-compiled drivers are trusted.

#![allow(dead_code)]

use super::{backend_artifact_support, toolchain_support};
use std::collections::{BTreeMap, BTreeSet};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

pub const TARGET: &str = "aarch64-unknown-linux-gnu";
pub const OPT_LEVELS: [u32; 4] = [0, 1, 2, 3];
/// The only backend knob a twin's positive lanes pass.
pub const NO_PROOF_CERTS: &[&str] = &["no-proof-certs"];
/// Process-environment controls a qualification run must not inherit: the
/// compiler refuses the `TCG_*`/`TRUST_CG_*` family anyway, and a test that
/// read one would no longer be the lane the runner records.
pub const REJECTED_ENVIRONMENT: [&str; 7] = [
    "TCG_NO_PROOF_CERTS",
    "TCG_JIT_UNCHECKED",
    "TCG_OPT_LEVEL",
    "TCG_DISABLE_UNWIND",
    "TRUST_CG_DISABLE_PASSES",
    "TRUST_CG_DISABLE_CFGSIMPLIFY_SUBPASSES",
    "TCG_DATAFLOW_INTEGRITY",
];

/// Fail, by name, when the build compiler cannot express the backend knob
/// every bridge compile here passes, or when an ambient control is set.
/// (`toolchain_support::skip_without_backend_knobs` would skip instead: a
/// skip of a required target is a pass that never ran.)
pub fn require_knobs(test: &str) {
    assert!(
        toolchain_support::backend_knobs_supported(),
        "{test}: this build compiler has no `{}`, so the `no-proof-certs` knob every bridge \
         compile of this required target passes cannot be expressed; this is a defect of the \
         host or package, not a skip",
        toolchain_support::BACKEND_KNOBS_OPTION
    );
    for name in REJECTED_ENVIRONMENT {
        assert!(
            std::env::var_os(name).is_none(),
            "{test}: qualification rejects {name}"
        );
    }
}

/// The artifacts directory of one test run, created by `mktemp -d -t`. It is
/// removed by [`Artifacts::finish`] after a passing run unless `keep` is set
/// to `1`; a failing run panics first, so its artifacts stay for inspection.
pub struct Artifacts {
    pub root: PathBuf,
    keep: &'static str,
}

impl Artifacts {
    pub fn new(prefix: &str, keep: &'static str) -> Artifacts {
        let temp = Command::new("mktemp")
            .args(["-d", "-t", &format!("{prefix}.XXXXXX")])
            .output()
            .expect("mktemp artifacts");
        assert!(temp.status.success(), "mktemp failed");
        let root = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
        eprintln!("native bridge artifacts: {}", root.display());
        Artifacts { root, keep }
    }

    pub fn finish(self) {
        if std::env::var_os(self.keep).is_some_and(|value| value == "1") {
            eprintln!("retained artifacts: {}", self.root.display());
        } else {
            std::fs::remove_dir_all(&self.root).expect("remove the artifacts of a passing run");
        }
    }
}

/// The build compiler must be the Linux AArch64 host compiler.
pub fn require_host(artifacts: &Path) {
    let host = checked(
        toolchain_support::rustc_driver_command().arg("-vV"),
        30,
        &artifacts.join("rustc.log"),
    );
    assert!(
        String::from_utf8_lossy(&host.stdout)
            .lines()
            .any(|line| line == format!("host: {TARGET}")),
        "the build compiler's host is not {TARGET}"
    );
}

// Every compile of a twin, CG and LLVM alike, starts from the shared
// build-compiler constructor (edition 2021, `-Ztrust-verify=off` on Trust).
// Test-only backend selection never enters a compiler environment.
pub fn rustc_command() -> Command {
    let mut command = toolchain_support::rustc_command();
    command
        .env_remove("TCG_TEST_BACKEND_PATH")
        .env_remove("TCG_TEST_BACKEND_SHA256");
    command
}

/// Run `command` under GNU `timeout` (which bounds the complete child process
/// group and kills it when the bound fires), retain the complete transcript in
/// `log`, and return the output with the transcript.
pub fn run_bounded(command: &mut Command, seconds: u32, log: &Path) -> (Output, String) {
    let mut bounded = Command::new("timeout");
    bounded.args(["--kill-after=5", &seconds.to_string()]);
    bounded.arg(command.get_program()).args(command.get_args());
    if let Some(dir) = command.get_current_dir() {
        bounded.current_dir(dir);
    }
    for (key, value) in command.get_envs() {
        if let Some(value) = value {
            bounded.env(key, value);
        } else {
            bounded.env_remove(key);
        }
    }
    // output() drains both pipes concurrently, including a verbose failed
    // compiler diagnostic.
    let output = bounded.output().expect("execute bounded native step");
    let transcript = format!(
        "command: {command:?}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::write(log, &transcript).expect("retain complete step log");
    (output, transcript)
}

pub fn checked(command: &mut Command, seconds: u32, log: &Path) -> Output {
    let (output, transcript) = run_bounded(command, seconds, log);
    assert!(
        output.status.success(),
        "{transcript}\nartifacts: {}",
        log.display()
    );
    output
}

pub fn sha256(path: &Path) -> String {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .expect("sha256sum");
    assert!(output.status.success(), "hash {}", path.display());
    let text = String::from_utf8(output.stdout).expect("SHA256 output");
    let hash = text.split_whitespace().next().expect("SHA256 digest");
    assert!(hash.len() == 64 && hash.bytes().all(|b| b.is_ascii_hexdigit()));
    hash.to_owned()
}

/// The SHA-256 of `bytes`, through a file beside `scratch`.
pub fn sha256_of(bytes: &[u8], scratch: &Path) -> String {
    std::fs::write(scratch, bytes).expect("write bytes to hash");
    sha256(scratch)
}

pub fn backend() -> (PathBuf, String) {
    let path = std::env::var_os("TCG_TEST_BACKEND_PATH");
    let hash = std::env::var("TCG_TEST_BACKEND_SHA256").ok();
    match (path, hash) {
        (Some(path), Some(expected)) => {
            let path = PathBuf::from(path);
            assert!(
                path.is_absolute() && path.is_file(),
                "exact backend path required"
            );
            let actual = sha256(&path);
            assert_eq!(actual, expected, "runner's fresh backend identity changed");
            (path, actual)
        }
        (None, None) => {
            // No runner binding: the library Cargo built for this test build,
            // never a nested build into the shared target directory.
            let path = backend_artifact_support::current_test_backend();
            let hash = sha256(&path);
            (path, hash)
        }
        _ => panic!("backend path and SHA256 must be supplied together"),
    }
}

/// A bridge compile's backend: its exact path, and the knobs it passes.
#[derive(Clone, Copy)]
pub struct Bridge<'a> {
    pub path: &'a Path,
    pub knobs: &'a [&'a str],
}

/// Add the backend selection of a bridge compile to `command`; an LLVM
/// compile (`None`) gets nothing.
pub fn select_backend(command: &mut Command, bridge: Option<Bridge<'_>>) {
    if let Some(bridge) = bridge {
        command.arg(format!("-Zcodegen-backend={}", bridge.path.display()));
        command.arg(toolchain_support::backend_knobs_arg(bridge.knobs));
    }
}

pub fn compiler_name(bridge: Option<Bridge<'_>>) -> &'static str {
    if bridge.is_some() { "cg" } else { "llvm" }
}

/// One `readelf -sW` row. The name is the last field and the section index the
/// one before it, so an `st_other` annotation such as `[VARIANT_PCS]` after the
/// visibility cannot shift them. A section symbol has no name field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElfSymbol {
    pub index: u64,
    pub value: u64,
    pub size: u64,
    pub kind: String,
    pub bind: String,
    pub section: String,
    pub name: String,
}

pub fn parse_symbols(text: &str) -> Vec<ElfSymbol> {
    text.lines()
        .filter_map(|line| {
            let fields: Vec<&str> = line.split_whitespace().collect();
            let index = fields.first()?.strip_suffix(':')?.parse::<u64>().ok()?;
            if fields.len() < 7 {
                return None;
            }
            // `Num: Value Size Type Bind Vis [st_other] Ndx [Name]`.
            let index_field = fields[fields.len() - 2];
            let named = fields.len() >= 8
                && (index_field.parse::<u64>().is_ok()
                    || index_field == "UND"
                    || index_field == "ABS"
                    || index_field == "COM");
            let (section, name) = if named {
                (fields[fields.len() - 2], fields[fields.len() - 1])
            } else {
                (fields[fields.len() - 1], "")
            };
            Some(ElfSymbol {
                index,
                value: u64::from_str_radix(fields[1], 16).ok()?,
                size: fields[2].parse().ok()?,
                kind: fields[3].to_owned(),
                bind: fields[4].to_owned(),
                section: section.to_owned(),
                name: name.to_owned(),
            })
        })
        .collect()
}

/// One `readelf -SW` row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElfSection {
    pub name: String,
    pub kind: String,
    pub offset: u64,
    pub size: u64,
    pub flags: String,
    pub align: u64,
}

/// `readelf -SW` rows keyed by section index. Rows without flags have one
/// field fewer; the unnamed null section is skipped.
pub fn parse_sections(text: &str) -> BTreeMap<u64, ElfSection> {
    let mut sections = BTreeMap::new();
    for line in text.lines() {
        let Some(rest) = line.trim_start().strip_prefix('[') else {
            continue;
        };
        let Some((index, fields)) = rest.split_once(']') else {
            continue;
        };
        let Ok(index) = index.trim().parse::<u64>() else {
            continue;
        };
        let fields: Vec<&str> = fields.split_whitespace().collect();
        // Name Type Address Off Size ES [Flg] Lk Inf Al
        let flags = match fields.len() {
            10 => fields[6].to_owned(),
            9 => String::new(),
            _ => continue,
        };
        let (Ok(offset), Ok(size), Ok(align)) = (
            u64::from_str_radix(fields[3], 16),
            u64::from_str_radix(fields[4], 16),
            fields[fields.len() - 1].parse::<u64>(),
        ) else {
            continue;
        };
        sections.insert(
            index,
            ElfSection {
                name: fields[0].to_owned(),
                kind: fields[1].to_owned(),
                offset,
                size,
                flags,
                align,
            },
        );
    }
    sections
}

/// One `readelf -rW` row of an `.rela.<section>` table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElfRelocation {
    pub section: String,
    pub offset: u64,
    pub symbol_index: u64,
    pub kind: String,
}

pub fn parse_relocations(text: &str) -> Vec<ElfRelocation> {
    let mut section = String::new();
    let mut rows = Vec::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("Relocation section '") {
            section = rest
                .split('\'')
                .next()
                .unwrap_or_default()
                .trim_start_matches(".rela")
                .to_owned();
            continue;
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.len() < 3 || !fields[2].starts_with("R_AARCH64_") {
            continue;
        }
        let (Ok(offset), Ok(info)) = (
            u64::from_str_radix(fields[0], 16),
            u64::from_str_radix(fields[1], 16),
        ) else {
            continue;
        };
        rows.push(ElfRelocation {
            section: section.clone(),
            offset,
            symbol_index: info >> 32,
            kind: fields[2].to_owned(),
        });
    }
    rows
}

/// The symbols, sections and relocations of one emitted object.
pub struct ObjectFacts {
    pub path: PathBuf,
    pub symbols: Vec<ElfSymbol>,
    pub sections: BTreeMap<u64, ElfSection>,
    pub relocations: Vec<ElfRelocation>,
}

impl ObjectFacts {
    pub fn defined(&self, name: &str) -> Option<&ElfSymbol> {
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name && symbol.section != "UND")
    }

    pub fn imports(&self, name: &str) -> bool {
        self.symbols
            .iter()
            .any(|symbol| symbol.name == name && symbol.section == "UND")
    }

    pub fn symbol(&self, index: u64) -> &ElfSymbol {
        self.symbols
            .iter()
            .find(|symbol| symbol.index == index)
            .unwrap_or_else(|| panic!("symbol {index} missing in {}", self.path.display()))
    }

    /// The section a defined symbol lives in.
    pub fn section_of(&self, symbol: &ElfSymbol) -> &ElfSection {
        let index: u64 = symbol.section.parse().unwrap_or_else(|_| {
            panic!(
                "`{}` has no section index in {}",
                symbol.name,
                self.path.display()
            )
        });
        self.sections.get(&index).unwrap_or_else(|| {
            panic!(
                "section {index} of `{}` missing in {}",
                symbol.name,
                self.path.display()
            )
        })
    }

    /// The relocations whose site lies in `symbol`'s bytes, in its section.
    pub fn relocations_in(&self, symbol: &ElfSymbol) -> Vec<&ElfRelocation> {
        let section = &self.section_of(symbol).name;
        self.relocations
            .iter()
            .filter(|row| {
                &row.section == section
                    && symbol.value <= row.offset
                    && row.offset < symbol.value + symbol.size.max(1)
            })
            .collect()
    }

    /// The allocator shim rustc emits for a staticlib (a driver brings its
    /// own), recognized by its `__rust_alloc` definition.
    pub fn is_allocator_shim(&self) -> bool {
        self.symbols.iter().any(|symbol| {
            symbol.section != "UND"
                && (symbol.name == "__rust_alloc" || symbol.name.ends_with("___rust_alloc"))
        })
    }

    pub fn file_name(&self) -> String {
        self.path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .into_owned()
    }
}

pub fn readelf(flag: &str, object: &Path, log: &Path) -> String {
    let output = checked(Command::new("readelf").arg(flag).arg(object), 30, log);
    String::from_utf8(output.stdout).expect("readelf output")
}

/// Inspect every freshly emitted object in `object_dir`, retaining the symbol,
/// section and relocation dumps beside it.
pub fn inspect_objects(object_dir: &Path) -> Vec<ObjectFacts> {
    let mut objects = std::fs::read_dir(object_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect::<Vec<_>>();
    objects.sort();
    objects
        .into_iter()
        .map(|path| {
            let dump = |kind: &str| PathBuf::from(format!("{}.{kind}.txt", path.display()));
            let symbols = parse_symbols(&readelf("-sW", &path, &dump("symbols")));
            let sections = parse_sections(&readelf("-SW", &path, &dump("sections")));
            let relocations = parse_relocations(&readelf("-rW", &path, &dump("relocations")));
            ObjectFacts {
                path,
                symbols,
                sections,
                relocations,
            }
        })
        .collect()
}

/// The one object of `objects` that defines `name`.
pub fn definer<'a>(objects: &[&'a ObjectFacts], name: &str) -> &'a ObjectFacts {
    let definers: Vec<&&ObjectFacts> = objects
        .iter()
        .filter(|facts| facts.defined(name).is_some())
        .collect();
    assert_eq!(
        definers.len(),
        1,
        "`{name}` must be defined in exactly one linked object"
    );
    definers[0]
}

/// The line an aborting stub writes to stderr, followed by its symbol, before
/// it calls `abort()`.
pub const ABORT_STUB_LINE: &str = "TCG_ABORT_STUB ";

/// Write `<dir>/abort_stubs.c`, one aborting definition of each undefined
/// core diverging helper (`toolchain_support::is_abort_stub_symbol`: the
/// unoptimized overflow/alignment/bounds checks' panic entries) that the
/// linked `objects` reference and none of them defines, as the other bridge
/// differentials do: a reached stub aborts the run, which fails the lane
/// unless the lane models that `SIGABRT`. Each stub first writes
/// [`ABORT_STUB_LINE`] and its own symbol to stderr, so a lane that models an
/// abort can name the panic entry that fired ([`model_runs`] records it and
/// [`assert_twins_agree`] compares it between CG and LLVM).
/// Returns the stub file (when any is needed) and the number of stubs.
pub fn abort_stubs(dir: &Path, objects: &[&ObjectFacts]) -> (Option<PathBuf>, usize) {
    let defined: BTreeSet<&str> = objects
        .iter()
        .flat_map(|facts| facts.symbols.iter())
        .filter(|symbol| symbol.section != "UND")
        .map(|symbol| symbol.name.as_str())
        .collect();
    let stubs: BTreeSet<&str> = objects
        .iter()
        .flat_map(|facts| facts.symbols.iter())
        .filter(|symbol| symbol.section == "UND" && !defined.contains(symbol.name.as_str()))
        .map(|symbol| symbol.name.as_str())
        .filter(|name| toolchain_support::is_abort_stub_symbol(name))
        .collect();
    if stubs.is_empty() {
        return (None, 0);
    }
    let mut source = String::from("#include <stdlib.h>\n#include <unistd.h>\n");
    for (index, symbol) in stubs.iter().enumerate() {
        // Symbols are `[A-Za-z0-9_.$]`, already spelled inside `__asm__("")`.
        source.push_str(&format!(
            "void tcg_abort_stub_{index}(void) __asm__(\"{symbol}\");\n\
             void tcg_abort_stub_{index}(void) {{\n\
             \x20   static const char line[] = \"{ABORT_STUB_LINE}{symbol}\\n\";\n\
             \x20   if (write(2, line, sizeof line - 1) < 0) {{}}\n\
             \x20   abort();\n\
             }}\n"
        ));
    }
    let path = dir.join("abort_stubs.c");
    std::fs::write(&path, source).unwrap();
    (Some(path), stubs.len())
}

/// How one native execution ended: an exit code or a terminating signal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ending {
    Exit(i32),
    Signal(i32),
}

impl Ending {
    pub fn of(output: &Output) -> Ending {
        match (output.status.code(), output.status.signal()) {
            (Some(code), _) => Ending::Exit(code),
            (None, Some(signal)) => Ending::Signal(signal),
            (None, None) => panic!("execution ended with neither exit code nor signal"),
        }
    }

    /// The marker spelling: `exit:N` or `signal:N`.
    pub fn label(self) -> String {
        match self {
            Ending::Exit(code) => format!("exit:{code}"),
            Ending::Signal(signal) => format!("signal:{signal}"),
        }
    }
}

/// GNU `timeout`'s exit status when its bound fired (`--kill-after` adds 137).
pub const TIMEOUT_EXITS: [i32; 2] = [124, 137];

/// Run `executable` once under a bound; a timeout fails the test.
pub fn run_native(lane: &Path, executable: &Path, args: &[&str], log_name: &str) -> Output {
    let mut command = Command::new(executable);
    command.args(args);
    let (output, transcript) = run_bounded(&mut command, 30, &lane.join(format!("{log_name}.log")));
    if let Some(code) = output.status.code() {
        assert!(
            !TIMEOUT_EXITS.contains(&code),
            "{} timed out and was killed: {transcript}",
            executable.display()
        );
    }
    output
}

/// One native lane: a fixture built by one compiler at one level, linked and
/// run `runs` times; every run's ending and stdout must equal the model.
pub struct LaneRow {
    pub fixture: &'static str,
    pub compiler: &'static str,
    pub opt: u32,
    pub runs: usize,
    pub ending: Ending,
    pub stdout_sha256: String,
    /// The aborting stub every run of a `SIGABRT` lane fired (its symbol, from
    /// [`ABORT_STUB_LINE`]); `None` for every other ending.
    pub abort_stub: Option<String>,
}

impl LaneRow {
    /// A `SIGABRT` lane aborted through the core panic entry `entry` (the
    /// symbol's last path component), not through some other stub.
    pub fn assert_aborted_through(&self, entry: &str) {
        let stub = self.abort_stub.as_deref().unwrap_or_else(|| {
            panic!(
                "{} {} O{}: no aborting stub fired",
                self.fixture, self.compiler, self.opt
            )
        });
        assert!(
            stub.ends_with(entry),
            "{} {} O{}: aborted through `{stub}`, not `{entry}`",
            self.fixture,
            self.compiler,
            self.opt
        );
    }

    pub fn json(&self) -> serde_json::Value {
        serde_json::json!({
            "fixture": self.fixture,
            "compiler": self.compiler,
            "opt_level": self.opt,
            "runs": self.runs,
            "passes": self.runs,
            "ending": self.ending.label(),
            "stdout_sha256": self.stdout_sha256,
        })
    }
}

/// Run `executable` `runs` times; each run must end as `expected` with
/// exactly `model` on stdout and nothing on stderr, except that a run ending
/// in `SIGABRT` must name exactly one fired aborting stub there (the same one
/// in every run), and no other ending may fire one. Returns the lane row.
#[allow(clippy::too_many_arguments)]
pub fn model_runs(
    lane: &Path,
    executable: &Path,
    fixture: &'static str,
    compiler: &'static str,
    opt: u32,
    runs: usize,
    expected: Ending,
    model: &str,
) -> LaneRow {
    assert!(runs >= 1, "a lane runs at least once");
    let mut observed = None;
    for run in 0..runs {
        let output = run_native(lane, executable, &[], &format!("run{run}"));
        let what = format!("{fixture} {compiler} O{opt} run {run}");
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            model,
            "{what}: stdout differs from the model (ended {:?}); stderr: {}",
            Ending::of(&output),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            Ending::of(&output),
            expected,
            "{what}: ended differently from the model; stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        if expected == Ending::Exit(0) {
            assert!(
                output.stderr.is_empty(),
                "{what}: unexpected stderr: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        let stderr = String::from_utf8_lossy(&output.stderr);
        let fired: Vec<&str> = stderr
            .lines()
            .filter_map(|line| line.strip_prefix(ABORT_STUB_LINE))
            .collect();
        let stub = if expected == Ending::Signal(SIGABRT) {
            assert_eq!(
                fired.len(),
                1,
                "{what}: a modelled SIGABRT must fire exactly one aborting stub; stderr: {stderr}"
            );
            Some(fired[0].to_owned())
        } else {
            assert!(
                fired.is_empty(),
                "{what}: an aborting stub fired in a lane that does not model SIGABRT: {stderr}"
            );
            None
        };
        let (_, _, first_stub) =
            observed.get_or_insert((Ending::of(&output), output.stdout, stub.clone()));
        assert_eq!(
            *first_stub, stub,
            "{what}: aborted through a different stub than run 0"
        );
    }
    // The row records what ran (every run equal to the model above), hashed
    // from the observed bytes, so the runner can compare it with the model's
    // digest independently.
    let (ending, stdout, abort_stub) = observed.unwrap();
    LaneRow {
        fixture,
        compiler,
        opt,
        runs,
        ending,
        stdout_sha256: sha256_of(&stdout, &lane.join("observed.stdout")),
        abort_stub,
    }
}

/// `SIGABRT`, the ending of a lane that reaches an aborting panic stub.
pub const SIGABRT: i32 = 6;

/// Every `twinned` fixture has exactly one CG and one LLVM row at every level,
/// and the two agree exactly.
pub fn assert_twins_agree(rows: &[LaneRow], twinned: &[&str]) {
    for fixture in twinned {
        for opt in OPT_LEVELS {
            let lane = |compiler: &str| -> &LaneRow {
                let found: Vec<&LaneRow> = rows
                    .iter()
                    .filter(|row| {
                        row.compiler == compiler && row.fixture == *fixture && row.opt == opt
                    })
                    .collect();
                assert_eq!(
                    found.len(),
                    1,
                    "{fixture} O{opt}: exactly one {compiler} lane"
                );
                found[0]
            };
            let (cg, llvm) = (lane("cg"), lane("llvm"));
            assert_eq!(
                (cg.ending, &cg.stdout_sha256, &cg.abort_stub),
                (llvm.ending, &llvm.stdout_sha256, &llvm.abort_stub),
                "{fixture} O{opt}: the CG and LLVM executables differ"
            );
        }
    }
}

/// The marker line a twin prints for the runner: `<marker> <json>`, binding
/// the backend hash and the verification-off scope of every compile.
pub fn print_marker(marker: &str, mut execution: serde_json::Value, digest: &str) {
    let object = execution.as_object_mut().expect("marker object");
    object.insert("schema".into(), serde_json::json!(1));
    object.insert("target".into(), serde_json::json!(TARGET));
    object.insert("opt_levels".into(), serde_json::json!(OPT_LEVELS));
    object.insert("certificates".into(), serde_json::json!("off"));
    object.insert("frontend_verify".into(), serde_json::json!("off"));
    object.insert("backend_sha256".into(), serde_json::json!(digest));
    println!("\n{marker} {}", serde_json::to_string(&execution).unwrap());
}

#[test]
fn readelf_rows_parse_symbols_sections_and_relocations() {
    let symbols = parse_symbols(
        "Symbol table '.symtab' contains 5 entries:\n   Num:    Value          Size Type    Bind   Vis      Ndx Name\n     \
         0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND \n     \
         2: 0000000000000000     0 SECTION LOCAL  DEFAULT    2 \n     \
         3: 0000000000000010     4 OBJECT  GLOBAL DEFAULT    4 AY_STATIC_N\n     \
         6: 0000000000000000     0 NOTYPE  GLOBAL DEFAULT  UND ay_record\n     \
         7: 0000000000000000    24 FUNC    GLOBAL DEFAULT [VARIANT_PCS]     1 f\n",
    );
    assert_eq!(symbols.len(), 5, "{symbols:?}");
    assert_eq!(
        (
            symbols[1].kind.as_str(),
            symbols[1].section.as_str(),
            symbols[1].name.as_str()
        ),
        ("SECTION", "2", "")
    );
    assert_eq!(
        symbols[2],
        ElfSymbol {
            index: 3,
            value: 0x10,
            size: 4,
            kind: "OBJECT".into(),
            bind: "GLOBAL".into(),
            section: "4".into(),
            name: "AY_STATIC_N".into(),
        }
    );
    assert_eq!(
        (symbols[3].section.as_str(), symbols[3].name.as_str()),
        ("UND", "ay_record")
    );
    assert_eq!(
        (symbols[4].section.as_str(), symbols[4].name.as_str()),
        ("1", "f")
    );
    let sections = parse_sections(
        "  [Nr] Name              Type            Address          Off    Size   ES Flg Lk Inf Al\n  \
         [ 0]                   NULL            0000000000000000 000000 000000 00      0   0  0\n  \
         [ 1] .text             PROGBITS        0000000000000000 000040 0000a0 00  AX  0   0  4\n  \
         [ 4] .rodata.AY_STATIC_N PROGBITS      0000000000000000 0000e0 000004 00   A  0   0  4\n  \
         [ 6] .bss.AY_ZERO      NOBITS          0000000000000000 000100 000040 00  WA  0   0 16\n  \
         [ 7] .note.GNU-stack   PROGBITS        0000000000000000 000148 000000 00      0   0  1\n",
    );
    assert_eq!(
        sections.get(&4),
        Some(&ElfSection {
            name: ".rodata.AY_STATIC_N".into(),
            kind: "PROGBITS".into(),
            offset: 0xe0,
            size: 4,
            flags: "A".into(),
            align: 4,
        })
    );
    assert_eq!(
        sections
            .get(&6)
            .map(|s| (s.kind.as_str(), s.flags.as_str(), s.align)),
        Some(("NOBITS", "WA", 16))
    );
    assert_eq!(sections.get(&7).map(|s| s.flags.as_str()), Some(""));
    assert!(!sections.contains_key(&0));
    let relocations = parse_relocations(
        "Relocation section '.rela.data.rel.ro.AY_OPS' at offset 0x148 contains 1 entry:\n    \
         Offset             Info             Type               Symbol's Value  Symbol's Name + Addend\n\
         0000000000000008  0000000700000101 R_AARCH64_ABS64        0000000000000000 ay_square + 0\n",
    );
    assert_eq!(
        relocations,
        vec![ElfRelocation {
            section: ".data.rel.ro.AY_OPS".into(),
            offset: 8,
            symbol_index: 7,
            kind: "R_AARCH64_ABS64".into(),
        }]
    );
    assert_eq!(Ending::Exit(0).label(), "exit:0");
    assert_eq!(Ending::Signal(11).label(), "signal:11");
}
