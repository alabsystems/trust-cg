//! Thin Box entry/cell pointers through real Rust ABI metadata, not a C Box ABI.
//! This is a certificates-off native diagnostic, not allocation-origin proof.

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::collections::{HashMap, HashSet};
use std::ffi::OsString;
use std::fs::{self, File};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const TARGET: &str = "aarch64-apple-darwin";
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];
const PROVIDER: &str = include_str!("support/box_pointer_entry/provider.rs");
const CALLEE: &str = include_str!("support/box_pointer_entry/callee.rs");
const DRIVER: &str = include_str!("support/box_pointer_entry/driver.rs");

struct Temporary(PathBuf);

impl Temporary {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-box-pointer-entry-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).expect("create unique fixture directory");
        Self(fs::canonicalize(path).expect("canonical fixture directory"))
    }
}

impl Drop for Temporary {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!(
                "retained thin-Box differential artifacts: {}",
                self.0.display()
            );
        } else {
            fs::remove_dir_all(&self.0).expect("remove only this fixture's owned directory");
        }
    }
}

struct Run {
    status: ExitStatus,
    stdout: String,
    stderr: String,
}

fn checked(command: &mut Command, seconds: u64, log: &Path) -> Run {
    let display = format!("{command:?}");
    let stdout = log.with_extension("stdout");
    let stderr = log.with_extension("stderr");
    command
        .stdin(Stdio::null())
        .stdout(Stdio::from(File::create(&stdout).unwrap()))
        .stderr(Stdio::from(File::create(&stderr).unwrap()))
        .process_group(0);
    let mut child = command.spawn().unwrap_or_else(|error| {
        panic!("could not start mandatory command {display}: {error}; artifacts at {log:?}")
    });
    let start = Instant::now();
    let (status, timed_out) = loop {
        if let Some(status) = child.try_wait().expect("poll mandatory command") {
            break (status, false);
        }
        if start.elapsed() >= Duration::from_secs(seconds) {
            // Reap the compiler/linker process group, not just its parent.
            unsafe extern "C" {
                fn kill(pid: i32, signal: i32) -> i32;
            }
            unsafe { kill(-(child.id() as i32), 9) };
            let _ = child.kill();
            break (child.wait().expect("reap timed-out command"), true);
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let result = Run {
        status,
        stdout: fs::read_to_string(stdout).expect("read command stdout"),
        stderr: fs::read_to_string(stderr).expect("read command stderr"),
    };
    fs::write(
        log,
        format!(
            "COMMAND {display}\nSTATUS {}\nTIMEOUT {timed_out}\nSTDOUT\n{}\nSTDERR\n{}",
            result.status, result.stdout, result.stderr
        ),
    )
    .expect("preserve mandatory command transcript");
    assert!(
        !timed_out && result.status.success(),
        "mandatory command failed (timeout={timed_out}): {display}\n{}\n{}\ntranscript: {}",
        result.stdout,
        result.stderr,
        log.display()
    );
    result
}

fn compiler_command() -> Command {
    let mut command = toolchain_support::rustc_command();
    for (name, _) in std::env::vars_os() {
        let text = name.to_string_lossy();
        if text.starts_with("TRUST_CG_")
            || text.starts_with("TCG_")
            || text.starts_with("AY_")
            || text.starts_with("TRUST_IR_CG_")
            || text == "CARGO_MAKEFLAGS"
        {
            command.env_remove(name);
        }
    }
    command
}

fn sha256(path: &Path, log: &Path) -> String {
    let metadata = fs::symlink_metadata(path).expect("artifact to authenticate exists");
    assert!(
        metadata.file_type().is_file() && metadata.len() != 0,
        "{path:?}"
    );
    let output = checked(
        Command::new("shasum").args(["-a", "256"]).arg(path),
        30,
        log,
    );
    let digest = output
        .stdout
        .split_whitespace()
        .next()
        .expect("SHA256 digest");
    assert_eq!(digest.len(), 64);
    assert!(digest.bytes().all(|byte| byte.is_ascii_hexdigit()));
    digest.to_owned()
}

struct Identities(Vec<(PathBuf, String)>);

impl Identities {
    fn capture(paths: &[PathBuf], dir: &Path) -> Self {
        Self(
            paths
                .iter()
                .enumerate()
                .map(|(index, path)| {
                    let digest = sha256(path, &dir.join(format!("identity-{index}.log")));
                    println!("BOX_POINTER_ENTRY_ARTIFACT path={path:?} sha256={digest}");
                    (path.clone(), digest)
                })
                .collect(),
        )
    }

    fn require_unchanged(&self, dir: &Path, phase: &str) {
        for (index, (path, expected)) in self.0.iter().enumerate() {
            let actual = sha256(path, &dir.join(format!("{phase}-identity-{index}.log")));
            assert_eq!(&actual, expected, "frozen artifact changed: {path:?}");
        }
    }
}

fn mir_function<'a>(mir: &'a str, name: &str) -> &'a str {
    let start = mir
        .find(&format!("fn {name}("))
        .unwrap_or_else(|| panic!("actual emitted MIR has no mandatory root {name}"));
    let function = &mir[start..];
    let end = function.find("\nfn ").unwrap_or(function.len());
    &function[..end]
}

fn mir_local(text: &str) -> Option<usize> {
    let digits = text.trim().strip_prefix('_')?;
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

fn whole_box_type(ty: &str) -> bool {
    ty.trim().strip_prefix("std::boxed::").unwrap_or(ty.trim()) == "Box<i64>"
}

fn box_transfer(text: &str) -> Option<(usize, bool)> {
    let text = text.trim();
    let (operand, moved) = if let Some(operand) = text.strip_prefix("copy ") {
        (operand, false)
    } else {
        (text.strip_prefix("move ")?, true)
    };
    Some((mir_local(operand)?, moved))
}

#[derive(Clone)]
struct BoxSource {
    root: usize,
    epoch: usize,
    path: Vec<usize>,
}

/// Authenticate only the two fixture roots' whole Box routes. This is a
/// bounded reader of the actual emitted MIR, not a generic MIR optimizer.
/// Follow the sole normal successor from bb0 to the unsize, recording exact
/// Copy/Move assignments of typed Box<i64> locals. A retarget invalidates the
/// epoch of all previously copied pointers; only a later read of the actual
/// formal's cell can supply the source. Projected transfers never qualify.
fn trace_box_unsize(function: &str, retargeted: bool) -> Result<Vec<usize>, String> {
    let invalid = |why: &str| format!("whole-Box MIR route: {why}");
    let header = function
        .lines()
        .next()
        .ok_or_else(|| invalid("missing header"))?;
    let parameters = header
        .split_once('(')
        .and_then(|(_, rest)| rest.split_once(") ->"))
        .ok_or_else(|| invalid("unexpected header"))?
        .0;
    let mut types = HashMap::new();
    for declaration in parameters
        .split(',')
        .chain(function.lines().filter_map(|line| {
            line.trim().strip_prefix("let ").map(|rest| {
                rest.strip_prefix("mut ")
                    .unwrap_or(rest)
                    .trim_end_matches(';')
            })
        }))
    {
        if let Some((local, ty)) = declaration.split_once(':') {
            if let Some(local) = mir_local(local) {
                if types.insert(local, ty.trim()).is_some() {
                    return Err(invalid("duplicate local type declaration"));
                }
            }
        }
    }
    if !types.get(&1).is_some_and(|ty| whole_box_type(ty))
        || (retargeted && !types.get(&2).is_some_and(|ty| whole_box_type(ty)))
    {
        return Err(invalid("actual Box formals are missing or mistyped"));
    }
    let mut blocks: HashMap<usize, Vec<&str>> = HashMap::new();
    let mut current = None;
    for line in function.lines().map(str::trim) {
        if let Some(label) = line
            .strip_prefix("bb")
            .and_then(|rest| rest.strip_suffix(": {"))
        {
            let id: usize = label
                .parse()
                .map_err(|_| invalid("unmodeled block label"))?;
            if blocks.insert(id, Vec::new()).is_some() {
                return Err(invalid("duplicate basic block"));
            }
            current = Some(id);
        } else if line == "}" {
            current = None;
        } else if let Some(id) = current {
            if !line.is_empty() {
                blocks.get_mut(&id).unwrap().push(line);
            }
        }
    }
    let mut sources = HashMap::from([(
        1,
        BoxSource {
            root: 1,
            epoch: 0,
            path: vec![1],
        },
    )]);
    if retargeted {
        sources.insert(
            2,
            BoxSource {
                root: 2,
                epoch: 0,
                path: vec![2],
            },
        );
    }
    let mut borrows = HashSet::new();
    let mut visited = HashSet::new();
    let mut block = 0;
    let mut epoch = 0;
    let mut statements = 0;
    for _ in 0..16 {
        if !visited.insert(block) {
            return Err(invalid("cycle before the unsize"));
        }
        let body = blocks
            .get(&block)
            .ok_or_else(|| invalid("missing normal successor"))?;
        let mut successor = None;
        'statements: for (index, statement) in body.iter().enumerate() {
            statements += 1;
            if statements > 128 {
                return Err(invalid("statement budget exceeded"));
            }
            if statement.contains("PointerCoercion(Unsize") {
                let rhs = statement
                    .split_once(" = ")
                    .ok_or_else(|| invalid("unsize is not an assignment"))?
                    .1;
                let operand = rhs
                    .split_once(" as ")
                    .ok_or_else(|| invalid("unsize has no source"))?
                    .0;
                let (local, _) = box_transfer(operand)
                    .ok_or_else(|| invalid("unsize source is not a whole Copy/Move local"))?;
                if !types.get(&local).is_some_and(|ty| whole_box_type(ty)) {
                    return Err(invalid("unsize source is not typed Box<i64>"));
                }
                let source = sources.get(&local).ok_or_else(|| {
                    invalid("unsize source has no current whole-local definition")
                })?;
                if source.root != 1 {
                    return Err(invalid("unsize source is a wrong root"));
                }
                if source.epoch != epoch {
                    return Err(invalid("unsize source is a stale temporary"));
                }
                if epoch != usize::from(retargeted) {
                    return Err(invalid("unsize is missing the actual retarget"));
                }
                return Ok(source.path.clone());
            }
            if let Some(destination) = statement
                .strip_prefix("goto -> bb")
                .and_then(|rest| rest.strip_suffix(';'))
            {
                if index + 1 != body.len() {
                    return Err(invalid("statement after a terminator"));
                }
                successor = Some(destination.parse().map_err(|_| invalid("unmodeled goto"))?);
                break;
            }
            if *statement == "return;" || *statement == "unreachable;" {
                return Err(invalid("unsize is not reached on the sole normal route"));
            }
            for prefix in ["StorageLive(", "StorageDead(", "Deinit("] {
                if let Some(operand) = statement.strip_prefix(prefix) {
                    let local =
                        operand
                            .strip_suffix(");")
                            .and_then(mir_local)
                            .ok_or_else(|| {
                                invalid("malformed whole-local storage or deinit statement")
                            })?;
                    if !types.contains_key(&local) {
                        return Err(invalid("storage/deinit local has no actual declaration"));
                    }
                    sources.remove(&local);
                    borrows.remove(&local);
                    continue 'statements;
                }
            }
            let Some((lhs, rhs)) = statement.split_once(" = ") else {
                return Err(invalid("unmodeled statement before the unsize"));
            };
            let destination =
                mir_local(lhs).ok_or_else(|| invalid("projected assignment before the unsize"))?;
            let rhs = rhs.trim_end_matches(';');
            if let Some(arguments) = rhs
                .strip_prefix("replace_box(")
                .and_then(|rest| rest.split_once(") -> [return: bb"))
            {
                if !retargeted
                    || epoch != 0
                    || index + 1 != body.len()
                    || !rhs.ends_with(", unwind unreachable]")
                {
                    return Err(invalid("unmodeled retarget count or edge"));
                }
                let arguments: Vec<_> = arguments.0.split(',').collect();
                if arguments.len() != 2 {
                    return Err(invalid("retarget call lost its two actual arguments"));
                }
                let borrow = box_transfer(arguments[0])
                    .ok_or_else(|| invalid("retarget address is not a whole borrow local"))?
                    .0;
                let replacement = box_transfer(arguments[1])
                    .ok_or_else(|| invalid("replacement is not a whole Box local"))?
                    .0;
                if !borrows.contains(&borrow)
                    || !sources
                        .get(&1)
                        .is_some_and(|source| source.root == 1 && source.epoch == 0)
                    || !sources
                        .get(&replacement)
                        .is_some_and(|source| source.root == 2 && source.epoch == 0)
                {
                    return Err(invalid(
                        "retarget arguments are not the authenticated formal address and replacement",
                    ));
                }
                epoch = 1;
                sources.insert(
                    1,
                    BoxSource {
                        root: 1,
                        epoch,
                        path: vec![1],
                    },
                );
                successor = Some(
                    rhs.split_once(") -> [return: bb")
                        .unwrap()
                        .1
                        .split(',')
                        .next()
                        .unwrap()
                        .parse()
                        .map_err(|_| invalid("unmodeled retarget successor"))?,
                );
                break;
            }
            if rhs.contains(" -> ") {
                return Err(invalid("unmodeled call before the unsize"));
            }
            borrows.remove(&destination);
            if rhs == "&mut _1"
                && types
                    .get(&destination)
                    .is_some_and(|ty| ty.strip_prefix("&mut ").is_some_and(whole_box_type))
            {
                borrows.insert(destination);
            }
            if types.get(&destination).is_some_and(|ty| whole_box_type(ty)) {
                sources.remove(&destination);
                if let Some((input, moved)) = box_transfer(rhs) {
                    if !types.get(&input).is_some_and(|ty| whole_box_type(ty)) {
                        return Err(invalid("whole-local transfer has a non-Box source"));
                    }
                    if let Some(mut source) = sources.get(&input).cloned() {
                        if source.path.len() >= 16 {
                            return Err(invalid("whole-local transfer budget exceeded"));
                        }
                        source.path.push(destination);
                        if moved {
                            sources.remove(&input);
                        }
                        sources.insert(destination, source);
                    }
                } else if rhs.starts_with("copy ") || rhs.starts_with("move ") {
                    return Err(invalid("projected or malformed whole-Box transfer"));
                }
            }
        }
        block =
            successor.ok_or_else(|| invalid("unsize is not reached on the sole normal route"))?;
    }
    Err(invalid("basic-block budget exceeded"))
}

fn require_trace_reader_controls() {
    let mir = |before: &str, after: &str, operand: &str| {
        format!(
            "fn consume_retargeted(_1: Box<i64>, _2: Box<i64>) -> i64 {{\nlet mut _4: &mut std::boxed::Box<i64>;\nlet _5: std::boxed::Box<dyn Read>;\nlet mut _6: std::boxed::Box<i64>;\nbb0: {{\n{before}\n_4 = &mut _1;\n_3 = replace_box(copy _4, copy _2) -> [return: bb1, unwind unreachable];\n}}\nbb1: {{\n{after}\n_5 = {operand} as std::boxed::Box<dyn Read> (PointerCoercion(Unsize, Implicit));\nreturn;\n}}\n}}"
        )
    };
    assert_eq!(
        trace_box_unsize(&mir("", "", "copy _1"), true).unwrap(),
        [1]
    );
    assert_eq!(
        trace_box_unsize(&mir("", "_6 = move _1;", "move _6"), true).unwrap(),
        [1, 6]
    );
    let untouched_storage = "fn consume_untouched(_1: Box<i64>) -> i64 {\nlet _2: std::boxed::Box<dyn Read>;\nbb0: {\nStorageLive(_2);\n_2 = copy _1 as std::boxed::Box<dyn Read> (PointerCoercion(Unsize, Implicit));\nreturn;\n}\n}";
    assert_eq!(trace_box_unsize(untouched_storage, false).unwrap(), [1]);
    let unreached = mir("", "_6 = copy _1;", "copy _6").replace("return: bb1", "return: bb2");
    let unreached = unreached.strip_suffix('}').unwrap().to_owned() + "bb2: {\nreturn;\n}\n}";
    for (label, detail, source) in [
        (
            "wrong root",
            "wrong root",
            mir("", "_6 = copy _2;", "copy _6"),
        ),
        (
            "projected source",
            "projected or malformed whole-Box transfer",
            mir("", "_6 = copy (*_1);", "copy _6"),
        ),
        (
            "stale temporary",
            "stale temporary",
            mir("_6 = copy _1;", "", "copy _6"),
        ),
        (
            "overwritten temporary",
            "wrong root",
            mir("", "_6 = copy _1;\n_6 = copy _2;", "copy _6"),
        ),
        (
            "non-Box temporary",
            "unsize source is not typed Box<i64>",
            mir("", "_6 = copy _1;", "copy _6")
                .replace("let mut _6: std::boxed::Box<i64>;", "let mut _6: i64;"),
        ),
        (
            "unreached unsize",
            "unsize is not reached on the sole normal route",
            unreached,
        ),
        (
            "storage-live cleared source",
            "unsize source has no current whole-local definition",
            mir("", "_6 = copy _1;\nStorageLive(_6);", "copy _6"),
        ),
        (
            "storage-dead cleared source",
            "unsize source has no current whole-local definition",
            mir("", "_6 = copy _1;\nStorageDead(_6);", "copy _6"),
        ),
        (
            "deinit cleared source",
            "unsize source has no current whole-local definition",
            mir("", "_6 = copy _1;\nDeinit(_6);", "copy _6"),
        ),
        (
            "projected storage",
            "malformed whole-local storage or deinit statement",
            mir("", "StorageLive(_6.0);\n_6 = copy _1;", "copy _6"),
        ),
        (
            "undeclared storage",
            "storage/deinit local has no actual declaration",
            mir("", "StorageDead(_99);\n_6 = copy _1;", "copy _6"),
        ),
    ] {
        let error = trace_box_unsize(&source, true)
            .err()
            .unwrap_or_else(|| panic!("reader admitted {label}"));
        assert!(
            error.contains(detail),
            "{label} failed at an unrelated reader gate: {error}"
        );
    }
    println!("BOX_POINTER_ENTRY_MIR_TRACE_CONTROLS cases=14 accepted=3 refused=11");
}

fn require_mir_inventory(path: &Path, lane: &str, opt: &str) -> String {
    let mir = fs::read_to_string(path).expect("actual emitted consumer MIR");
    for name in ["consume_untouched", "consume_retargeted"] {
        let function = mir_function(&mir, name);
        let header = function.lines().next().unwrap();
        assert!(header.contains("_1: Box<i64>"), "{lane}/O{opt}: {header}");
        let unsizes: Vec<_> = function
            .lines()
            .filter(|line| {
                line.contains("PointerCoercion(Unsize") && line.contains("Box<dyn Read>")
            })
            .collect();
        assert_eq!(
            unsizes.len(),
            1,
            "{lane}/O{opt}: {name} lost its source Box unsize\n{function}"
        );
        let path = trace_box_unsize(function, name == "consume_retargeted")
            .unwrap_or_else(|why| panic!("{lane}/O{opt}: {name}: {why}\n{function}"));
        println!("BOX_POINTER_ENTRY_MIR_SOURCE lane={lane} opt={opt} root={name} locals={path:?}");
        assert!(
            function.contains("<dyn Read as Read>::read("),
            "{lane}/O{opt}: {name} lost actual dynamic dispatch\n{function}"
        );
        assert!(
            function.contains("drop(") || function.contains("std::mem::drop::<Box<dyn Read>>"),
            "{lane}/O{opt}: {name} lost the source Box Drop\n{function}"
        );
        if name == "consume_untouched" {
            assert!(!function.contains("replace_box("), "{function}");
            assert!(
                !function.contains("&mut _1"),
                "untouched source root acquired a mutable cell\n{function}"
            );
        } else {
            assert!(header.contains("_2: Box<i64>"), "{header}");
        }
    }
    println!("BOX_POINTER_ENTRY_MIR lane={lane} opt={opt} roots=2 untouched=1 retargeted=1");
    mir
}

fn common_compile(root: &Path, opt: &str) -> Command {
    let mut command = compiler_command();
    command
        .current_dir(root)
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Ccodegen-units=1",
            "-Coverflow-checks=off",
            "-Cdebug-assertions=no",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("-L")
        .arg(format!("dependency={}", root.display()));
    command
}

fn compile_cell(
    root: &Path,
    dir: &Path,
    opt: &str,
    backend: Option<&Path>,
    provider: &Path,
) -> (PathBuf, PathBuf, String) {
    fs::create_dir(dir).expect("fresh compiler cell directory");
    let mut compile = common_compile(root, opt);
    compile
        .args([
            "--crate-name=box_pointer_entry_callee",
            "--crate-type=rlib",
            "--emit=link,mir",
        ])
        .arg(root.join("callee.rs"))
        .arg("--extern")
        .arg(format!("box_pointer_entry_provider={}", provider.display()))
        .arg("--out-dir")
        .arg(dir);
    if let Some(backend) = backend {
        let mut argument = OsString::from("-Zcodegen-backend=");
        argument.push(backend);
        compile
            .arg(argument)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    checked(&mut compile, 240, &dir.join("compile.log"));
    let lane = if backend.is_some() { "cg" } else { "llvm" };
    let mir = require_mir_inventory(&dir.join("box_pointer_entry_callee.mir"), lane, opt);
    let rlib = dir.join("libbox_pointer_entry_callee.rlib");
    let executable = dir.join("driver");
    let mut link = common_compile(root, "2");
    link.arg("--crate-name=box_pointer_entry_driver")
        .arg(root.join("driver.rs"))
        .arg("--extern")
        .arg(format!("box_pointer_entry_provider={}", provider.display()))
        .arg("--extern")
        .arg(format!("box_pointer_entry_callee={}", rlib.display()))
        .arg("-L")
        .arg(format!("dependency={}", dir.display()))
        .arg("-o")
        .arg(&executable);
    // This normal LLVM link reads both real rlib metadata records. No Rust
    // Box, function-pointer, hidden-location or panic ABI is hand-declared.
    checked(&mut link, 240, &dir.join("link.log"));
    (rlib, executable, mir)
}

#[test]
fn ordinary_box_entry_and_retargeted_cell_match_llvm() {
    darwin_native::require("ordinary_box_entry_and_retargeted_cell_match_llvm", &[]);
    require_trace_reader_controls();
    let temporary = Temporary::new();
    let root = &temporary.0;
    let provider_source = root.join("provider.rs");
    let callee_source = root.join("callee.rs");
    let driver_source = root.join("driver.rs");
    for (path, source) in [
        (&provider_source, PROVIDER),
        (&callee_source, CALLEE),
        (&driver_source, DRIVER),
    ] {
        fs::write(path, source).expect("write immutable physical fixture source");
    }
    let backend = backend_artifact_support::current_test_backend();
    let compiler = fs::canonicalize(toolchain_support::rustc_driver_command().get_program())
        .expect("actual selected build compiler");
    let identities = Identities::capture(
        &[
            compiler,
            backend.clone(),
            provider_source,
            callee_source,
            driver_source,
        ],
        root,
    );
    let provider = root.join("libbox_pointer_entry_provider.rlib");
    checked(
        common_compile(root, "0")
            .args([
                "--crate-name=box_pointer_entry_provider",
                "--crate-type=rlib",
            ])
            .arg(root.join("provider.rs"))
            .arg("-o")
            .arg(&provider),
        240,
        &root.join("provider-compile.log"),
    );
    let provider_identity = Identities::capture(std::slice::from_ref(&provider), root);
    let mut native_runs = 0;
    let mut llvm_runs = 0;
    let mut cg_runs = 0;
    let mut drop_frees = 0;
    let mut reads = 0;
    let mut retargets = 0;
    let mut mir_routes = 0;
    for (index, opt) in OPT_LEVELS.iter().enumerate() {
        let mut oracle_mir = None;
        for (lane, backend_option) in [("llvm", None), ("cg", Some(backend.as_path()))] {
            let dir = root.join(format!("{lane}-O{opt}"));
            let (rlib, executable, mir) = compile_cell(root, &dir, opt, backend_option, &provider);
            identities.require_unchanged(&dir, "post-link");
            provider_identity.require_unchanged(&dir, "post-link-provider");
            let cell_identity = Identities::capture(&[rlib, executable.clone()], &dir);
            if lane == "llvm" {
                oracle_mir = Some(mir);
            } else {
                assert_eq!(
                    Some(&mir),
                    oracle_mir.as_ref(),
                    "O{opt}: paired compiler frontend MIR differs"
                );
            }
            mir_routes += 2;
            let old_payload = 17_000_i64 + index as i64;
            let new_payload = -93_000_i64 - index as i64;
            for (kind, payload, frees, callback_count, event_count) in [
                ("untouched", old_payload, 1, 0, 2),
                ("retargeted", new_payload, 2, 1, 5),
            ] {
                let output = checked(
                    Command::new(&executable)
                        .args([kind, &old_payload.to_string(), &new_payload.to_string()])
                        .env("MallocScribble", "1")
                        .env("MallocGuardEdges", "1")
                        .env("MallocErrorAbort", "1"),
                    30,
                    &dir.join(format!("run-{kind}.log")),
                );
                let expected = format!(
                    "BOX_POINTER_ENTRY_CASE kind={kind} payload={payload} address_match=1 reads=1 retargets={callback_count} drop_frees={frees} bad_layout=0 events={event_count}"
                );
                assert_eq!(
                    output
                        .stdout
                        .lines()
                        .filter(|line| *line == expected)
                        .count(),
                    1,
                    "{lane}/O{opt}/{kind} did not establish its full ledger\n{}",
                    output.stdout
                );
                assert_eq!(
                    output.stdout.lines().count(),
                    2,
                    "unexpected native output: {}",
                    output.stdout
                );
                assert!(output.stdout.lines().next().unwrap().starts_with(&format!(
                    "BOX_POINTER_ENTRY_ADDRESS kind={kind} expected=0x"
                )));
                // Darwin's malloc debugging switches may print their own
                // startup diagnostics. Preserve stderr in the transcript;
                // success, exact stdout, address/payload and the full allocator
                // ledger are mandatory, as in the existing heap differential.
                println!("BOX_POINTER_ENTRY_RUN lane={lane} opt={opt} case={kind}");
                print!("{}", output.stdout);
                if !output.stderr.is_empty() {
                    eprintln!("BOX_POINTER_ENTRY_MALLOC_DIAGNOSTIC\n{}", output.stderr);
                }
                identities.require_unchanged(&dir, &format!("post-{kind}"));
                provider_identity.require_unchanged(&dir, &format!("post-{kind}-provider"));
                cell_identity.require_unchanged(&dir, &format!("post-{kind}-cell"));
                native_runs += 1;
                llvm_runs += usize::from(lane == "llvm");
                cg_runs += usize::from(lane == "cg");
                drop_frees += frees;
                reads += 1;
                retargets += callback_count;
            }
        }
    }
    assert_eq!(
        (native_runs, llvm_runs, cg_runs, mir_routes),
        (16, 8, 8, 16)
    );
    assert_eq!((drop_frees, reads, retargets), (24, 16, 8));
    println!(
        "BOX_POINTER_ENTRY_DIFFERENTIAL cells=8 cases=2 native_runs=16 llvm_runs=8 cg_runs=8 mir_routes=16 box_drop_frees=24 reads=16 retargets=8 bad_layout=0 provider=LLVM oracle=LLVM certs=off"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
