//! Native Linux ELF twin of `unwind_cleanup_aarch64.rs`: a real Rust panic
//! unwinds through frames the rustc bridge compiled for
//! `aarch64-unknown-linux-gnu`, their cleanup landing pads drop a `Box` and
//! user `Drop` values mid-unwind, and `std::panic::catch_unwind` in an
//! LLVM-compiled driver catches it. Every lane has an LLVM twin.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0
//!
//! This target is mandatory on its named host, not a portable skip. The
//! separate bridge runner binds a freshly built backend by path and SHA-256
//! (`TCG_TEST_BACKEND_PATH`/`TCG_TEST_BACKEND_SHA256`); a standalone invocation
//! instead loads, and hashes, the library Cargo built for this test build. It
//! never builds into the shared target directory or selects a cached library.
//!
//! FIXTURE. The Darwin twin's crate and panicker are kept byte-identical
//! (`box_across_unwind` holds a `Box<i32>` across `panicker::ay_may_unwind`,
//! which panics with a `&str`). Two functions are appended: in
//! `guards_across_unwind(n)` a user-`Drop` `Guard` and a `Box<Guard>` are live
//! across `panicker::ay_unwind_if(n)`, which panics with a typed payload when
//! `n != 0`; `nested_unwind(n)` holds a `Guard` and a `Box<i64>` across a call
//! to `guards_across_unwind`, so a panic crosses two bridge frames and the
//! inner frame's `Resume` reaches the outer frame's landing pad. `Guard::drop`
//! appends its id to a drop log in the panicker rlib.
//!
//! WHAT IS CHECKED, AT O0-O3. The O0 MIR of each fixture function carries a
//! real `UnwindAction::Cleanup` edge. The bridge objects are selected by
//! defined symbol (`readelf -sW`); only the allocator shim is excluded. Since
//! the multi-object publication (`ld -r`, 2026-10-23) one published object
//! defines all three fixture functions, so every fact is read per function:
//! the object defining it carries `.gcc_except_table`, exactly one `.eh_frame`
//! FDE starting at the function whose LSDA pointer names the function's own
//! LSDA in that table (its extent read from its header, followed by nothing
//! but alignment padding), `DW.ref.rust_eh_personality` resolving to
//! `rust_eh_personality`, and, inside the function, a call to
//! `_Unwind_Resume`. Its LSDA
//! call-site rows cover the function contiguously. Cleanup user-Drop calls
//! whose MIR says `unwind terminate(cleanup)` may add a strictly checked,
//! terminal empty Rust filter; typed catches remain excluded. Exactly one row covers
//! the call to the panicking callee, with a cleanup landing pad. The linked
//! driver's definition of each fixture function has the selected object's
//! size. The driver makes five calls (three panics, two normal returns) and
//! prints, per call, the outcome and payload, the ordered drop log, the
//! `Box<i32>`/`Box<i64>` allocation and free counts and the panic-hook count;
//! every run of a bridge executable must print exactly the model. The LLVM
//! twin must print the same, except that it may remove the allocation of the
//! two boxes that are never read (Rust permits it; LLVM does at O1-O3).
//!
//! CONTROLS. For each fixture function and level, a copy of its bridge object
//! whose protecting row has its landing pad set to zero (same length, the
//! row still covers the call) is linked instead: the panic is still caught
//! with the same payload, and exactly that frame's drops and frees are
//! missing, as the model predicts. With the `disable-unwind` knob the bridge
//! refuses each fixture function by name ("TerminatorKind::Call with cleanup
//! unwind") and leaves no object defining one.
//!
//! EVIDENCE BOUNDARY. The frontend runs with `-Ztrust-verify=off` and the
//! backend with the `no-proof-certs` knob, so the EH objects carry no
//! certificate. The LSDA rows, FDEs and personality references are unproven
//! object-side facts checked with GNU `readelf`/`objdump`. The Rust unwind
//! runtime (`rust_eh_personality`, libgcc's unwinder), the LLVM-compiled
//! driver and panicker, and GNU `ld` are trusted. The catch is in the driver:
//! `catch_unwind` inside a bridge frame is refused by the bridge (not
//! exercised here). This is native testing evidence for these shapes only.
//!
//! The artifacts directory is removed when the test passes; setting
//! `UNWIND_CLEANUP_LINUX_KEEP_ARTIFACTS=1` retains it.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TARGET: &str = "aarch64-unknown-linux-gnu";
const OPT_LEVELS: [u32; 4] = [0, 1, 2, 3];
/// Native executions of each linked CG/LLVM executable.
const RUNS_PER_LANE: usize = 3;
const PERSONALITY: &str = "rust_eh_personality";
const PERSONALITY_SLOT: &str = "DW.ref.rust_eh_personality";
const RESUME: &str = "_Unwind_Resume";
const DISABLE_UNWIND_REFUSAL: &str = "TerminatorKind::Call with cleanup unwind";
const KEEP_ARTIFACTS: &str = "UNWIND_CLEANUP_LINUX_KEEP_ARTIFACTS";
/// (bridge function, the callee whose call its landing pad protects).
const FIXTURES: [(&str, &str); 3] = [
    ("box_across_unwind", "ay_may_unwind"),
    ("guards_across_unwind", "ay_unwind_if"),
    ("nested_unwind", "guards_across_unwind"),
];

/// Byte-identical to `UNWIND_CRATE` in `unwind_cleanup_aarch64.rs` (the script
/// test `test_unwind_target_keeps_the_darwin_crates` pins this).
const DARWIN_UNWIND_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
extern crate panicker;\n\
#[no_mangle]\n\
pub extern \"C-unwind\" fn box_across_unwind() -> i32 {\n\
    let _b = Box::new(7i32);\n\
    panicker::ay_may_unwind()\n\
}\n";

/// Byte-identical to `PANICKER_CRATE` in `unwind_cleanup_aarch64.rs`.
const DARWIN_PANICKER_CRATE: &str = "\
#![crate_type = \"rlib\"]\n\
#[no_mangle]\n\
pub extern \"C-unwind\" fn ay_may_unwind() -> i32 { panic!(\"boom from panicker\"); }\n";

/// Appended to [`DARWIN_UNWIND_CRATE`]: user `Drop` values, a `Box<Guard>`,
/// a typed payload and a second bridge frame.
const UNWIND_EXTENSION: &str = r#"
pub struct Guard {
    id: i32,
}
impl Drop for Guard {
    fn drop(&mut self) {
        panicker::ay_record_drop(self.id);
    }
}
#[no_mangle]
#[inline(never)]
pub extern "C-unwind" fn guards_across_unwind(n: i32) -> i32 {
    let _a = Guard { id: 1 };
    let _b = Box::new(Guard { id: 2 });
    panicker::ay_unwind_if(n) + 1
}
#[no_mangle]
pub extern "C-unwind" fn nested_unwind(n: i32) -> i32 {
    let _g = Guard { id: 10 };
    let _h = Box::new(11i64);
    guards_across_unwind(n) * 2
}
"#;

/// Appended to [`DARWIN_PANICKER_CRATE`] (compiled by LLVM, like the rest of
/// the panicker): the drop log and the typed-payload raise.
const PANICKER_EXTENSION: &str = r#"
use std::sync::atomic::{AtomicI32, AtomicUsize, Ordering};
static DROP_LOG: [AtomicI32; 16] = [const { AtomicI32::new(0) }; 16];
static DROP_LEN: AtomicUsize = AtomicUsize::new(0);
/// 24 bytes, align 4: its box is in neither counted allocation class.
pub struct Payload {
    pub code: i32,
    pub tag: [u8; 20],
}
#[no_mangle]
pub extern "C" fn ay_record_drop(id: i32) {
    let at = DROP_LEN.fetch_add(1, Ordering::SeqCst);
    if at < DROP_LOG.len() {
        DROP_LOG[at].store(id, Ordering::SeqCst);
    }
}
/// The ids logged since the last call, without allocating: a `Vec<i32>` of
/// one id would fall in the driver's counted `Box<i32>` class.
pub fn take_drop_log() -> ([i32; 16], usize) {
    let len = DROP_LEN.swap(0, Ordering::SeqCst);
    assert!(len <= DROP_LOG.len(), "drop log overflow");
    let mut log = [0; 16];
    for (value, slot) in log.iter_mut().zip(&DROP_LOG[..len]) {
        *value = slot.load(Ordering::SeqCst);
    }
    (log, len)
}
#[no_mangle]
pub extern "C-unwind" fn ay_unwind_if(n: i32) -> i32 {
    if n != 0 {
        std::panic::panic_any(Payload { code: n * 7, tag: *b"ay_unwind_if payload" });
    }
    40
}
"#;

/// The LLVM-compiled driver. It catches every call with `catch_unwind` and
/// prints one line per call; a silent counting hook replaces the default
/// panic message. The counting allocator tracks only the `Box<i32>`/
/// `Box<Guard>` (4 bytes, align 4) and `Box<i64>` (8, 8) classes; the panic
/// payload boxes (`&str`: 16/8, `Payload`: 24/4) fall in neither. `late`
/// counts tracked allocations and frees while the payload is inspected and
/// dropped, after the call's counts are taken; the model requires zero.
const DRIVER: &str = r#"
extern crate panicker;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
static COUNTS: [AtomicUsize; 4] = [const { AtomicUsize::new(0) }; 4];
static HOOKS: AtomicUsize = AtomicUsize::new(0);
fn class(layout: Layout) -> Option<usize> {
    match (layout.size(), layout.align()) {
        (4, 4) => Some(0),
        (8, 8) => Some(2),
        _ => None,
    }
}
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if let Some(index) = class(layout) {
            COUNTS[index].fetch_add(1, Ordering::SeqCst);
        }
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        if let Some(index) = class(layout) {
            COUNTS[index + 1].fetch_add(1, Ordering::SeqCst);
        }
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOCATOR: Counting = Counting;
extern "C-unwind" {
    fn box_across_unwind() -> i32;
    fn guards_across_unwind(n: i32) -> i32;
    fn nested_unwind(n: i32) -> i32;
}
fn take_counts() -> [usize; 4] {
    [0, 1, 2, 3].map(|index| COUNTS[index].swap(0, Ordering::SeqCst))
}
fn report(label: &str, call: &dyn Fn() -> i32) {
    let _ = take_counts();
    let _ = panicker::take_drop_log();
    HOOKS.store(0, Ordering::SeqCst);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| call()));
    let counts = take_counts();
    let (log, len) = panicker::take_drop_log();
    let drops = &log[..len];
    let hooks = HOOKS.swap(0, Ordering::SeqCst);
    let outcome = match result {
        Ok(value) => format!("returned {value}"),
        Err(payload) => match payload.downcast::<panicker::Payload>() {
            Ok(typed) => format!("caught payload:{}:{}", typed.code, String::from_utf8_lossy(&typed.tag)),
            Err(payload) => match payload.downcast::<&'static str>() {
                Ok(text) => format!("caught str:{text}"),
                Err(_) => "caught unknown".to_string(),
            },
        },
    };
    let late = take_counts();
    println!(
        "{label} {outcome} drops={drops:?} box_i32={}/{} box_i64={}/{} hooks={hooks} late={}",
        counts[0], counts[1], counts[2], counts[3], late.iter().sum::<usize>()
    );
}
fn main() {
    std::panic::set_hook(Box::new(|_| {
        HOOKS.fetch_add(1, Ordering::SeqCst);
    }));
    report("box_across_unwind()", &|| unsafe { box_across_unwind() });
    report("guards_across_unwind(0)", &|| unsafe { guards_across_unwind(0) });
    report("guards_across_unwind(3)", &|| unsafe { guards_across_unwind(3) });
    report("nested_unwind(0)", &|| unsafe { nested_unwind(0) });
    report("nested_unwind(-2)", &|| unsafe { nested_unwind(-2) });
}
"#;

/// Per-run totals of the driver's reference behavior.
const CALLS_PER_RUN: usize = 5;
const PANICS_PER_RUN: usize = 3;
const DROP_EVENTS_PER_RUN: usize = 10;
const BOX_FREES_PER_RUN: usize = 7;

/// One modelled driver line.
struct ModelCall {
    label: &'static str,
    outcome: &'static str,
    drops: Vec<i32>,
    box_i32: (usize, usize),
    box_i64: (usize, usize),
    hooks: usize,
}

/// The driver's exact output, either with every landing pad intact
/// (`mutated == None`) or with the landing pad protecting `mutated`'s call to
/// its callee removed: that frame then runs none of its cleanups while the
/// panic still reaches the driver's `catch_unwind`.
fn model(mutated: Option<&str>) -> Vec<ModelCall> {
    let lost = |function: &str| mutated == Some(function);
    let mut calls = vec![
        ModelCall {
            label: "box_across_unwind()",
            outcome: "caught str:boom from panicker",
            drops: vec![],
            box_i32: (1, if lost("box_across_unwind") { 0 } else { 1 }),
            box_i64: (0, 0),
            hooks: 1,
        },
        ModelCall {
            label: "guards_across_unwind(0)",
            outcome: "returned 41",
            drops: vec![2, 1],
            box_i32: (1, 1),
            box_i64: (0, 0),
            hooks: 0,
        },
        ModelCall {
            label: "guards_across_unwind(3)",
            outcome: "caught payload:21:ay_unwind_if payload",
            drops: vec![2, 1],
            box_i32: (1, 1),
            box_i64: (0, 0),
            hooks: 1,
        },
        ModelCall {
            label: "nested_unwind(0)",
            outcome: "returned 82",
            drops: vec![2, 1, 10],
            box_i32: (1, 1),
            box_i64: (1, 1),
            hooks: 0,
        },
        ModelCall {
            label: "nested_unwind(-2)",
            outcome: "caught payload:-14:ay_unwind_if payload",
            drops: vec![2, 1, 10],
            box_i32: (1, 1),
            box_i64: (1, 1),
            hooks: 1,
        },
    ];
    if lost("guards_across_unwind") {
        for index in [2, 4] {
            calls[index].drops.retain(|id| *id != 1 && *id != 2);
            calls[index].box_i32.1 = 0;
        }
    }
    if lost("nested_unwind") {
        calls[4].drops.retain(|id| *id != 10);
        calls[4].box_i64.1 = 0;
    }
    calls
}

/// `box_across_unwind`'s `Box<i32>` (line 0) and `nested_unwind`'s `Box<i64>`
/// (lines 3 and 4) are never read, so Rust permits removing their allocation;
/// LLVM does at O1-O3. The bridge lanes must show every allocation and free.
fn with_elided_boxes(mut calls: Vec<ModelCall>, box_i32: bool, box_i64: bool) -> Vec<ModelCall> {
    if box_i32 {
        calls[0].box_i32 = (0, 0);
    }
    if box_i64 {
        for index in [3, 4] {
            calls[index].box_i64 = (0, 0);
        }
    }
    calls
}

fn render(calls: &[ModelCall]) -> String {
    calls
        .iter()
        .map(|call| {
            format!(
                "{} {} drops={:?} box_i32={}/{} box_i64={}/{} hooks={} late=0\n",
                call.label,
                call.outcome,
                call.drops,
                call.box_i32.0,
                call.box_i32.1,
                call.box_i64.0,
                call.box_i64.1,
                call.hooks
            )
        })
        .collect()
}

/// (drop events, box frees) of one modelled run.
fn totals(calls: &[ModelCall]) -> (usize, usize) {
    let drops = calls.iter().map(|call| call.drops.len()).sum();
    let frees = calls
        .iter()
        .map(|call| call.box_i32.1 + call.box_i64.1)
        .sum();
    (drops, frees)
}

// Every compile of this target, CG and LLVM alike, starts from the shared
// build-compiler constructor (edition 2021, `-Ztrust-verify=off` on Trust).
// Test-only backend selection never enters a compiler environment.
fn rustc_command() -> Command {
    let mut command = toolchain_support::rustc_command();
    command
        .env_remove("TCG_TEST_BACKEND_PATH")
        .env_remove("TCG_TEST_BACKEND_SHA256");
    command
}

fn run_bounded(command: &mut Command, seconds: u32, log: &Path) -> (Output, String) {
    // GNU timeout bounds the complete child process group. output() drains both
    // pipes concurrently, including a verbose failed compiler diagnostic.
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
    let output = bounded
        .output()
        .expect("execute bounded native unwind step");
    let transcript = format!(
        "command: {command:?}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::write(log, &transcript).expect("retain complete step log");
    (output, transcript)
}

fn checked(command: &mut Command, seconds: u32, log: &Path) -> Output {
    let (output, transcript) = run_bounded(command, seconds, log);
    assert!(
        output.status.success(),
        "{transcript}\nartifacts: {}",
        log.display()
    );
    output
}

fn sha256(path: &Path) -> String {
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

fn backend() -> (PathBuf, String) {
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

/// One `readelf -sW` row. The name is the last field and the section index the
/// one before it, so an `st_other` annotation such as `[VARIANT_PCS]` after the
/// visibility cannot shift them. A section symbol has no name field.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ElfSymbol {
    index: u64,
    value: u64,
    size: u64,
    kind: String,
    bind: String,
    section: String,
    name: String,
}

fn parse_symbols(text: &str) -> Vec<ElfSymbol> {
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
                    || index_field == "ABS");
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
struct ElfSection {
    name: String,
    offset: u64,
    size: u64,
}

/// `readelf -SW` rows keyed by section index. Rows without flags have one
/// field fewer; the unnamed null section is skipped.
fn parse_sections(text: &str) -> BTreeMap<u64, ElfSection> {
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
        if fields.len() != 9 && fields.len() != 10 {
            continue;
        }
        let (Ok(offset), Ok(size)) = (
            u64::from_str_radix(fields[3], 16),
            u64::from_str_radix(fields[4], 16),
        ) else {
            continue;
        };
        sections.insert(
            index,
            ElfSection {
                name: fields[0].to_owned(),
                offset,
                size,
            },
        );
    }
    sections
}

/// One `readelf -rW` row of an `.rela.<section>` table.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ElfRelocation {
    section: String,
    offset: u64,
    symbol_index: u64,
    kind: String,
    /// The explicit RELA addend (`... + <hex>` or `... - <hex>`).
    addend: i64,
}

fn parse_relocations(text: &str) -> Vec<ElfRelocation> {
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
        // `... <symbol value> [<name>] +|- <hex addend>`: the addend is the
        // last field and its sign the one before it.
        let magnitude = i64::from_str_radix(fields[fields.len() - 1], 16)
            .unwrap_or_else(|_| panic!("relocation row without a hex addend: {line}"));
        let addend = match fields[fields.len() - 2] {
            "+" => magnitude,
            "-" => -magnitude,
            other => panic!("relocation row without an addend sign ({other}): {line}"),
        };
        rows.push(ElfRelocation {
            section: section.clone(),
            offset,
            symbol_index: info >> 32,
            kind: fields[2].to_owned(),
            addend,
        });
    }
    rows
}

fn read_uleb128(bytes: &[u8], at: &mut usize) -> u64 {
    let mut value = 0u64;
    let mut shift = 0;
    loop {
        let byte = *bytes.get(*at).expect("truncated ULEB128");
        *at += 1;
        assert!(shift < 64, "ULEB128 overflows u64");
        value |= u64::from(byte & 0x7f) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return value;
        }
    }
}

/// One LSDA call-site row, with the byte range of its landing-pad field.
#[derive(Debug, Clone, PartialEq, Eq)]
struct LsdaRow {
    start: u64,
    length: u64,
    landing_pad: u64,
    action: u64,
    landing_pad_field: std::ops::Range<usize>,
}

/// A signed action-table value, bounded by the TType base.
fn read_sleb128(bytes: &[u8], at: &mut usize, end: usize) -> i64 {
    let mut value = 0i128;
    let mut shift = 0;
    loop {
        assert!(*at < end, "truncated action-table SLEB128");
        let byte = bytes[*at];
        *at += 1;
        assert!(shift < 64, "SLEB128 overflows i64");
        value |= i128::from(byte & 0x7f) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            if byte & 0x40 != 0 {
                value |= (!0i128) << shift;
            }
            return i64::try_from(value).expect("SLEB128 overflows i64");
        }
    }
}

/// Parse this fixture's cleanup rows and genuine Rust terminate empty filters.
/// Positive catch types, chained/nonempty filters, typeinfo slots/relocations
/// and unreferenced action data remain outside the admitted test shape.
fn parse_unwind_lsda(bytes: &[u8]) -> Vec<LsdaRow> {
    assert!(bytes.len() >= 4, "LSDA header truncated: {bytes:02x?}");
    assert_eq!(bytes[0], 0xff, "LPStart must be omitted (function start)");
    let mut at = 2;
    let type_base = match bytes[1] {
        0xff => None,
        0x9b => {
            let offset = usize::try_from(read_uleb128(bytes, &mut at))
                .expect("TType offset overflows usize");
            let base = at.checked_add(offset).expect("TType base overflows usize");
            assert!(base < bytes.len(), "TType base escapes its LSDA");
            assert_eq!(
                base + 1,
                bytes.len(),
                "only one empty filter byte follows TType"
            );
            assert_eq!(base % 4, 0, "TType base must be four-byte aligned");
            assert_eq!(bytes[base], 0, "Rust terminate filter must allow no types");
            Some(base)
        }
        other => panic!("unsupported fixture TType encoding {other:#x}"),
    };
    assert_eq!(bytes[at], 0x01, "call sites must be ULEB128-encoded");
    at += 1;
    let table_length =
        usize::try_from(read_uleb128(bytes, &mut at)).expect("call-site length overflows usize");
    let end = at
        .checked_add(table_length)
        .expect("call-site table overflows usize");
    assert!(end <= bytes.len(), "call-site table escapes its LSDA");
    if let Some(base) = type_base {
        assert!(end <= base, "call-site table overlaps TType");
    }
    let mut rows = Vec::new();
    while at < end {
        let start = read_uleb128(bytes, &mut at);
        let length = read_uleb128(bytes, &mut at);
        let field = at;
        let landing_pad = read_uleb128(bytes, &mut at);
        let landing_pad_field = field..at;
        let action = read_uleb128(bytes, &mut at);
        rows.push(LsdaRow {
            start,
            length,
            landing_pad,
            action,
            landing_pad_field,
        });
    }
    assert_eq!(at, end, "call-site rows overrun the declared table length");
    if let Some(base) = type_base {
        let actions: BTreeMap<u64, ()> = rows
            .iter()
            .filter_map(|row| {
                if row.action == 0 {
                    return None;
                }
                assert_ne!(row.landing_pad, 0, "terminate action needs a landing pad");
                Some((row.action, ()))
            })
            .collect();
        assert!(
            !actions.is_empty(),
            "TType must bind a real terminate action"
        );
        let mut cursor = end;
        for action in actions.into_keys() {
            let offset = usize::try_from(action - 1).expect("action offset overflows usize");
            let record = end
                .checked_add(offset)
                .expect("action address overflows usize");
            assert_eq!(record, cursor, "unreferenced/overlapping action data");
            let filter = read_sleb128(bytes, &mut cursor, base);
            let next = read_sleb128(bytes, &mut cursor, base);
            assert_eq!(filter, -1, "only the bound empty Rust filter is allowed");
            assert_eq!(next, 0, "Rust empty filter must be terminal");
            assert_eq!(
                &bytes[record..cursor],
                &[0x7f, 0],
                "canonical terminal empty filter"
            );
        }
        assert!(base - cursor <= 3, "typeinfo slots or excess action data");
        assert!(
            bytes[cursor..base].iter().all(|byte| *byte == 0),
            "nonzero action padding"
        );
    } else {
        assert!(
            rows.iter().all(|row| row.action == 0),
            "cleanup-only rows must have no action"
        );
        assert!(
            bytes[end..].iter().all(|byte| *byte == 0),
            "cleanup-only action data"
        );
    }
    rows
}

/// The length of the LSDA at the start of `bytes`, read from its header: the
/// TType form ends one byte past its TType base (the single empty Rust filter
/// [`parse_unwind_lsda`] admits there), the cleanup-only form at the end of
/// its call-site table. [`parse_unwind_lsda`] then checks the whole LSDA
/// against that exact extent.
fn lsda_length(bytes: &[u8]) -> usize {
    assert!(bytes.len() >= 4, "LSDA header truncated: {bytes:02x?}");
    assert_eq!(bytes[0], 0xff, "LPStart must be omitted (function start)");
    let mut at = 2;
    match bytes[1] {
        0x9b => {
            let offset = usize::try_from(read_uleb128(bytes, &mut at))
                .expect("TType offset overflows usize");
            at.checked_add(offset)
                .and_then(|base| base.checked_add(1))
                .expect("TType base overflows usize")
        }
        0xff => {
            assert_eq!(bytes[at], 0x01, "call sites must be ULEB128-encoded");
            at += 1;
            let table_length = usize::try_from(read_uleb128(bytes, &mut at))
                .expect("call-site length overflows usize");
            at.checked_add(table_length)
                .expect("call-site table overflows usize")
        }
        other => panic!("unsupported fixture TType encoding {other:#x}"),
    }
}

/// The section-relative byte range of `function`'s LSDA in `facts`'
/// `.gcc_except_table` (section `lsda_index`).
///
/// An object can hold several functions' LSDAs: the bridge's published
/// `--emit=obj` object is its per-item objects partial-linked by `ld -r`
/// (2026-10-23), which concatenates their tables, each input aligned to its
/// four bytes. The function's FDE is the one `.eh_frame` record whose
/// initial-location relocation names the function (directly or as its
/// `.text` offset); its LSDA pointer is the one `.gcc_except_table`
/// relocation between that field and the next FDE's. The LSDA's extent is
/// its own header's ([`lsda_length`]); what follows it up to the next LSDA
/// must be exactly the zero alignment padding a partial link inserts, and
/// the last LSDA must end the section. A trailing zero byte of the LSDA
/// itself inside that padding cannot be told apart from padding; such a byte
/// is referenced by no call-site or action record.
fn function_lsda(
    facts: &ObjectFacts,
    symbol: &ElfSymbol,
    text_index: u64,
    lsda_index: u64,
    lsda_section: &ElfSection,
    bytes: &[u8],
) -> std::ops::Range<usize> {
    let name = facts.file_name();
    let mut eh_frame: Vec<&ElfRelocation> = facts
        .relocations
        .iter()
        .filter(|row| row.section == ".eh_frame" && row.kind == "R_AARCH64_PREL32")
        .collect();
    eh_frame.sort_by_key(|row| row.offset);
    fn target_address(facts: &ObjectFacts, row: &ElfRelocation) -> u64 {
        let target = facts.symbol(row.symbol_index);
        u64::try_from(i128::from(target.value) + i128::from(row.addend))
            .unwrap_or_else(|_| panic!("negative relocation target {row:?}"))
    }
    let initial_locations: Vec<&&ElfRelocation> = eh_frame
        .iter()
        .filter(|row| facts.symbol(row.symbol_index).section == text_index.to_string())
        .collect();
    let own: Vec<&&&ElfRelocation> = initial_locations
        .iter()
        .filter(|row| {
            let target = facts.symbol(row.symbol_index);
            (target.name == symbol.name && row.addend == 0)
                || (target.kind == "SECTION" && target_address(facts, row) == symbol.value)
        })
        .collect();
    assert_eq!(
        own.len(),
        1,
        "{name}: exactly one FDE must start at {}",
        symbol.name
    );
    let fde = own[0].offset;
    let next_fde = initial_locations
        .iter()
        .map(|row| row.offset)
        .filter(|offset| *offset > fde)
        .min()
        .unwrap_or(u64::MAX);
    let lsda_pointers: Vec<&&ElfRelocation> = eh_frame
        .iter()
        .filter(|row| facts.symbol(row.symbol_index).section == lsda_index.to_string())
        .collect();
    let own_lsda: Vec<u64> = lsda_pointers
        .iter()
        .filter(|row| fde < row.offset && row.offset < next_fde)
        .map(|row| target_address(facts, row))
        .collect();
    assert_eq!(
        own_lsda.len(),
        1,
        "{name}: {}'s FDE must point at exactly one LSDA",
        symbol.name
    );
    let start = own_lsda[0];
    let bound = lsda_pointers
        .iter()
        .map(|row| target_address(facts, row))
        .filter(|address| *address > start)
        .min()
        .unwrap_or(lsda_section.size);
    assert!(
        bound <= lsda_section.size,
        "{name}: an LSDA escapes its table"
    );
    let section = lsda_section.offset as usize;
    let (start, bound) = (start as usize, bound as usize);
    let length = lsda_length(&bytes[section + start..section + bound]);
    let end = start + length;
    assert!(
        end <= bound,
        "{name}: {}'s LSDA overlaps the next",
        symbol.name
    );
    let padding = if bound == lsda_section.size as usize {
        0
    } else {
        (4 - end % 4) % 4
    };
    assert_eq!(
        bound - end,
        padding,
        "{name}: {}'s LSDA is followed by more than its alignment padding",
        symbol.name
    );
    assert!(
        bytes[section + end..section + bound]
            .iter()
            .all(|byte| *byte == 0),
        "{name}: nonzero padding after {}'s LSDA",
        symbol.name
    );
    start..end
}

/// A ULEB128 zero of exactly `width` bytes (`80 .. 80 00`).
fn padded_uleb128_zero(width: usize) -> Vec<u8> {
    assert!(width >= 1);
    let mut bytes = vec![0x80; width];
    bytes[width - 1] = 0;
    bytes
}

struct ObjectFacts {
    path: PathBuf,
    symbols: Vec<ElfSymbol>,
    sections: BTreeMap<u64, ElfSection>,
    relocations: Vec<ElfRelocation>,
}

impl ObjectFacts {
    fn defined(&self, name: &str) -> Option<&ElfSymbol> {
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name && symbol.section != "UND")
    }

    fn imports(&self, name: &str) -> bool {
        self.symbols
            .iter()
            .any(|symbol| symbol.name == name && symbol.section == "UND")
    }

    fn symbol(&self, index: u64) -> &ElfSymbol {
        self.symbols
            .iter()
            .find(|symbol| symbol.index == index)
            .unwrap_or_else(|| panic!("symbol {index} missing in {}", self.path.display()))
    }

    fn section_named(&self, name: &str) -> Option<(u64, &ElfSection)> {
        let mut matches = self
            .sections
            .iter()
            .filter(|(_, section)| section.name == name);
        let first = matches.next().map(|(index, section)| (*index, section));
        assert!(
            matches.next().is_none(),
            "{} has several {name} sections",
            self.path.display()
        );
        first
    }

    /// The allocator shim rustc emits for the staticlib (the driver brings
    /// its own), recognized by its `__rust_alloc` definition.
    fn is_allocator_shim(&self) -> bool {
        self.symbols.iter().any(|symbol| {
            symbol.section != "UND"
                && (symbol.name == "__rust_alloc" || symbol.name.ends_with("___rust_alloc"))
        })
    }

    fn defines_fixture(&self) -> bool {
        FIXTURES
            .iter()
            .any(|(function, _)| self.defined(function).is_some())
    }

    fn file_name(&self) -> String {
        self.path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .into_owned()
    }
}

fn readelf(flag: &str, object: &Path, log: &Path) -> String {
    let output = checked(Command::new("readelf").arg(flag).arg(object), 30, log);
    String::from_utf8(output.stdout).expect("readelf output")
}

/// Inspect every freshly emitted object in `object_dir`, retaining the symbol,
/// section and relocation dumps beside it.
fn inspect_objects(object_dir: &Path) -> Vec<ObjectFacts> {
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

/// Build the panicker rlib (normal toolchain, LLVM) once per artifacts tree.
fn build_panicker(artifacts: &Path) -> PathBuf {
    let source = artifacts.join("panicker.rs");
    std::fs::write(
        &source,
        format!("{DARWIN_PANICKER_CRATE}{PANICKER_EXTENSION}"),
    )
    .unwrap();
    let rlib = artifacts.join("libpanicker.rlib");
    checked(
        rustc_command()
            .args(["--crate-name", "panicker", "--crate-type", "rlib"])
            .args(["--target", TARGET, "-Cpanic=unwind", "-Copt-level=0"])
            .arg("--emit=link")
            .arg("-o")
            .arg(&rlib)
            .arg(&source),
        180,
        &artifacts.join("panicker-build.log"),
    );
    rlib
}

fn extern_panicker(rlib: &Path) -> String {
    format!("panicker={}", rlib.display())
}

/// The O0 MIR of every fixture function must carry a real cleanup edge: an
/// `unwind: bbN` into a `(cleanup)` block. Returns the number of functions.
fn assert_mir_cleanup_edges(artifacts: &Path, source: &Path, rlib: &Path) -> usize {
    let mir = artifacts.join("unwind.mir");
    checked(
        rustc_command()
            .args(["--crate-type", "lib", "--target", TARGET])
            .args(["-Cpanic=unwind", "-Zmir-opt-level=0"])
            .arg("--extern")
            .arg(extern_panicker(rlib))
            .arg("--emit=mir")
            .arg("-o")
            .arg(&mir)
            .arg(source),
        180,
        &artifacts.join("mir.log"),
    );
    let text = std::fs::read_to_string(&mir).unwrap();
    for (function, _) in FIXTURES {
        let header = format!("fn {function}(");
        let start = text
            .find(&header)
            .unwrap_or_else(|| panic!("MIR dump lacks {function}"));
        let body = &text[start..];
        let body = &body[..body.find("\n}\n").expect("MIR body end")];
        assert!(
            body.contains("unwind: bb") && body.contains("(cleanup)"),
            "{function}'s MIR must carry an UnwindAction::Cleanup edge:\n{body}"
        );
    }
    FIXTURES.len()
}

fn compile(
    source: &Path,
    rlib: &Path,
    object_dir: &Path,
    opt: u32,
    backend_knobs: Option<(&Path, &[&str])>,
    log: &Path,
) -> (Output, String) {
    std::fs::create_dir(object_dir).unwrap();
    let mut command = rustc_command();
    command.args(["--crate-type", "staticlib"]);
    if let Some((backend, knobs)) = backend_knobs {
        command.arg(format!("-Zcodegen-backend={}", backend.display()));
        command.arg(toolchain_support::backend_knobs_arg(knobs));
    }
    // One CGU keeps the per-MonoItem objects predictable, as in the TLS twin.
    command
        .args([
            "-Ccodegen-units=1",
            "-Cpanic=unwind",
            "-Cforce-unwind-tables=yes",
        ])
        .args(["--target", TARGET])
        .arg(format!("-Copt-level={opt}"))
        .arg("--extern")
        .arg(extern_panicker(rlib))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(object_dir)
        .arg(source);
    run_bounded(&mut command, 180, log)
}

/// Archive `objects` and link them with the driver through the build
/// compiler, so the Rust runtime (`rust_eh_personality`, `_Unwind_Resume`, the
/// allocator shim) resolves as in any Rust binary.
fn link(lane: &Path, name: &str, objects: &[&Path], rlib: &Path, driver: &Path) -> PathBuf {
    let library = lane.join(format!("lib{name}.a"));
    let mut archive = Command::new("ar");
    archive.arg("crs").arg(&library).args(objects);
    checked(&mut archive, 60, &lane.join(format!("{name}-ar.log")));
    let executable = lane.join(format!("{name}.elf"));
    checked(
        rustc_command()
            .args(["--target", TARGET, "-Cpanic=unwind", "-Copt-level=0"])
            .arg("-L")
            .arg(lane)
            .args(["-l", &format!("static={name}")])
            .arg("--extern")
            .arg(extern_panicker(rlib))
            .arg("-o")
            .arg(&executable)
            .arg(driver),
        180,
        &lane.join(format!("{name}-link.log")),
    );
    executable
}

/// Each fixture function is defined once in `executable`, with the size of
/// its definition in the selected objects.
fn assert_linked_definitions(lane: &Path, executable: &Path, linked: &[&ObjectFacts]) {
    let dump = readelf("-sW", executable, &lane.join("executable-symbols.txt"));
    let symbols = parse_symbols(&dump);
    for (function, _) in FIXTURES {
        let definitions: Vec<&ElfSymbol> = symbols
            .iter()
            .filter(|symbol| symbol.name == function && symbol.section != "UND")
            .collect();
        assert_eq!(
            definitions.len(),
            1,
            "{function} must be defined once in the executable"
        );
        let object = linked
            .iter()
            .find_map(|facts| facts.defined(function))
            .unwrap_or_else(|| panic!("no selected object defines {function}"));
        assert_eq!(
            (definitions[0].kind.as_str(), definitions[0].size),
            ("FUNC", object.size),
            "the executable's {function} is not the selected object's"
        );
    }
}

fn run_executable(lane: &Path, executable: &Path, log_name: &str) -> Output {
    let (output, transcript) = run_bounded(
        &mut Command::new(executable),
        20,
        &lane.join(format!("{log_name}.log")),
    );
    assert!(
        output.status.code().is_some(),
        "killed by a signal: {transcript}"
    );
    output
}

/// Run `executable`, which must exit 0 with an empty stderr; returns stdout.
fn run_driver(lane: &Path, executable: &Path, log_name: &str, what: &str) -> String {
    let output = run_executable(lane, executable, log_name);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{what}: driver exited abnormally: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{what}: unexpected stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("driver output")
}

/// Run `executable` and require the exact modelled output.
fn assert_model_run(lane: &Path, executable: &Path, log_name: &str, expected: &str, what: &str) {
    let stdout = run_driver(lane, executable, log_name, what);
    assert_eq!(
        stdout, expected,
        "{what}: driver output differs from the model"
    );
}

/// Object-level EH facts of one fixture function in a CG lane.
struct EhFunctionFacts {
    function: &'static str,
    callee: &'static str,
    object: PathBuf,
    lsda: std::ops::Range<usize>,
    lsda_rows: Vec<LsdaRow>,
    protecting_row: usize,
    resume_calls: usize,
}

fn eh_function_facts(
    linked: &[&ObjectFacts],
    function: &'static str,
    callee: &'static str,
) -> EhFunctionFacts {
    let facts = linked
        .iter()
        .find(|facts| facts.defined(function).is_some())
        .unwrap_or_else(|| panic!("no selected object defines {function}"));
    let name = facts.file_name();
    let symbol = facts.defined(function).unwrap();
    assert_eq!(
        (symbol.kind.as_str(), symbol.bind.as_str()),
        ("FUNC", "GLOBAL"),
        "{function} in {name}"
    );
    let (text_index, _) = facts
        .section_named(".text")
        .unwrap_or_else(|| panic!("{name} has no .text"));
    assert_eq!(
        symbol.section,
        text_index.to_string(),
        "{function} must be in {name}'s .text"
    );
    let (lsda_index, lsda_section) = facts
        .section_named(".gcc_except_table")
        .unwrap_or_else(|| panic!("{function}'s object {name} has no LSDA"));
    assert!(
        facts.section_named(".eh_frame").is_some(),
        "{name} has no .eh_frame"
    );
    // The FDE's LSDA pointer and the CIE's personality slot.
    let eh_frame_targets: Vec<&ElfSymbol> = facts
        .relocations
        .iter()
        .filter(|row| row.section == ".eh_frame" && row.kind == "R_AARCH64_PREL32")
        .map(|row| facts.symbol(row.symbol_index))
        .collect();
    assert!(
        eh_frame_targets
            .iter()
            .any(|target| target.section == lsda_index.to_string()),
        "{name}: no .eh_frame FDE points at .gcc_except_table"
    );
    assert!(
        eh_frame_targets
            .iter()
            .any(|target| target.name == PERSONALITY_SLOT),
        "{name}: the CIE must name {PERSONALITY_SLOT}"
    );
    let slot_targets: Vec<&str> = facts
        .relocations
        .iter()
        .filter(|row| {
            row.section == format!(".data.{PERSONALITY_SLOT}") && row.kind == "R_AARCH64_ABS64"
        })
        .map(|row| facts.symbol(row.symbol_index).name.as_str())
        .collect();
    assert_eq!(
        slot_targets,
        vec![PERSONALITY],
        "{name}: the personality slot must hold {PERSONALITY}"
    );
    assert!(
        facts.imports(PERSONALITY) && facts.imports(RESUME),
        "{name} must import {PERSONALITY} and {RESUME}"
    );
    // Calls made BY this function: an object may define several functions
    // (the published object partial-links every item's object).
    let body = symbol.value..symbol.value + symbol.size;
    let text_calls = |target: &str| -> Vec<u64> {
        facts
            .relocations
            .iter()
            .filter(|row| {
                row.section == ".text"
                    && row.kind == "R_AARCH64_CALL26"
                    && body.contains(&row.offset)
                    && facts.symbol(row.symbol_index).name == target
            })
            .map(|row| row.offset)
            .collect()
    };
    let resume_calls = text_calls(RESUME).len();
    assert!(resume_calls >= 1, "{name} never calls {RESUME}");
    let callee_calls = text_calls(callee);
    assert_eq!(
        callee_calls.len(),
        1,
        "{function} must call {callee} exactly once"
    );
    let call = callee_calls[0] - symbol.value;

    let bytes = std::fs::read(&facts.path).unwrap();
    let own = function_lsda(facts, symbol, text_index, lsda_index, lsda_section, &bytes);
    let lsda = lsda_section.offset as usize + own.start..lsda_section.offset as usize + own.end;
    assert!(
        !facts
            .relocations
            .iter()
            .any(|row| row.section == ".gcc_except_table"),
        "{name}: cleanup/empty Rust filters have no typeinfo relocations"
    );
    let lsda_rows = parse_unwind_lsda(&bytes[lsda.clone()]);
    // The rows cover [0, size) contiguously, so no PC of the function reaches
    // the personality's missing-row (terminate) case.
    let mut cursor = 0;
    for row in &lsda_rows {
        assert_eq!(row.start, cursor, "{name}: LSDA rows are not contiguous");
        cursor += row.length;
    }
    assert_eq!(
        cursor, symbol.size,
        "{name}: LSDA rows do not end at the function end"
    );
    let protecting: Vec<usize> = lsda_rows
        .iter()
        .enumerate()
        .filter(|(_, row)| row.start <= call && call < row.start + row.length)
        .map(|(index, _)| index)
        .collect();
    assert_eq!(protecting.len(), 1, "{name}: one row must cover the call");
    let row = &lsda_rows[protecting[0]];
    assert!(
        (row.start, row.length) == (call, 4)
            && row.landing_pad != 0
            && row.landing_pad < symbol.size
            && row.action == 0,
        "{name}: the call to {callee} must have its own cleanup row: {row:?}"
    );
    EhFunctionFacts {
        function,
        callee,
        object: facts.path.clone(),
        lsda,
        lsda_rows,
        protecting_row: protecting[0],
        resume_calls,
    }
}

/// Selected objects: everything but the allocator shim, which must be the
/// only one excluded when present.
fn select(objects: &[ObjectFacts]) -> (Vec<&ObjectFacts>, usize) {
    let linked: Vec<&ObjectFacts> = objects.iter().filter(|o| !o.is_allocator_shim()).collect();
    let excluded = objects.len() - linked.len();
    assert!(excluded <= 1, "more than one allocator shim");
    for (function, _) in FIXTURES {
        let definers = linked
            .iter()
            .filter(|o| o.defined(function).is_some())
            .count();
        assert_eq!(definers, 1, "`{function}` must be defined exactly once");
    }
    (linked, excluded)
}

/// Compile, inspect, link and run the fixture with one compiler at one level,
/// plus (CG) the missing-landing-pad controls. Returns the lane's marker row
/// and the control rows.
fn unwind_lane(
    artifacts: &Path,
    source: &Path,
    rlib: &Path,
    driver: &Path,
    opt: u32,
    backend: Option<(&Path, &str)>,
) -> (String, Vec<String>) {
    let compiler = if backend.is_some() { "cg" } else { "llvm" };
    let lane = artifacts.join(format!("unwind_{compiler}_O{opt}"));
    let object_dir = lane.join("objects");
    std::fs::create_dir(&lane).unwrap();
    let knobs: &[&str] = &["no-proof-certs"];
    let (output, transcript) = compile(
        source,
        rlib,
        &object_dir,
        opt,
        backend.map(|(path, _)| (path, knobs)),
        &lane.join("compile.log"),
    );
    assert!(
        output.status.success(),
        "{compiler} O{opt} unwind compile failed: {transcript}"
    );
    let objects = inspect_objects(&object_dir);
    let (linked, excluded) = select(&objects);
    let eh: Vec<EhFunctionFacts> = if backend.is_some() {
        FIXTURES
            .iter()
            .map(|(function, callee)| eh_function_facts(&linked, function, callee))
            .collect()
    } else {
        Vec::new()
    };
    let paths: Vec<&Path> = linked.iter().map(|facts| facts.path.as_path()).collect();
    let executable = link(&lane, "bridgeunwind", &paths, rlib, driver);
    assert_linked_definitions(&lane, &executable, &linked);
    // A bridge lane must show every allocation and free; LLVM may remove the
    // two never-read boxes (see `with_elided_boxes`), and every run of one
    // executable must print the same output.
    let variants: Vec<(usize, String)> = if backend.is_some() {
        vec![(0, render(&model(None)))]
    } else {
        [(false, false), (true, false), (false, true), (true, true)]
            .into_iter()
            .map(|(box_i32, box_i64)| {
                let calls = with_elided_boxes(model(None), box_i32, box_i64);
                (BOX_FREES_PER_RUN - totals(&calls).1, render(&calls))
            })
            .collect()
    };
    let mut observed = None;
    for run in 0..RUNS_PER_LANE {
        let what = format!("{compiler} O{opt} run {run}");
        let stdout = run_driver(&lane, &executable, &format!("run{run}"), &what);
        let Some(variant) = variants.iter().position(|(_, text)| *text == stdout) else {
            assert_eq!(
                stdout, variants[0].1,
                "{what}: driver output differs from the model"
            );
            unreachable!();
        };
        assert!(
            observed.is_none_or(|previous| previous == variant),
            "{what}: runs of one executable printed different outputs"
        );
        observed = Some(variant);
    }
    let elided_box_frees = variants[observed.unwrap()].0;
    let (drops, frees) = totals(&model(None));
    assert_eq!((drops, frees), (DROP_EVENTS_PER_RUN, BOX_FREES_PER_RUN));

    let mut controls = Vec::new();
    for facts in &eh {
        controls.push(missing_landing_pad_control(
            &lane, facts, &linked, rlib, driver, opt,
        ));
    }
    if let Some((path, digest)) = backend {
        assert_eq!(sha256(path), digest, "backend changed during unwind lane");
    }
    let common = format!(
        "\"compiler\":\"{compiler}\",\"opt_level\":{opt},\"runs\":{RUNS_PER_LANE},\
         \"passes\":{RUNS_PER_LANE},\"calls\":{},\"panics\":{},\"caught\":{},\
         \"drop_events\":{},\"box_frees\":{},\"elided_box_frees\":{elided_box_frees},\
         \"linked_objects\":{},\"excluded_objects\":{excluded}",
        CALLS_PER_RUN * RUNS_PER_LANE,
        PANICS_PER_RUN * RUNS_PER_LANE,
        PANICS_PER_RUN * RUNS_PER_LANE,
        DROP_EVENTS_PER_RUN * RUNS_PER_LANE,
        (BOX_FREES_PER_RUN - elided_box_frees) * RUNS_PER_LANE,
        linked.len()
    );
    let row = if backend.is_some() {
        format!(
            "{{{common},\"eh_functions\":{},\"personality\":\"{PERSONALITY}\",\"resume_calls\":{}}}",
            eh.len(),
            eh.iter().map(|facts| facts.resume_calls).sum::<usize>()
        )
    } else {
        format!("{{{common}}}")
    };
    println!(
        "{compiler} O{opt}: {} objects linked, {excluded} excluded; {RUNS_PER_LANE} runs match the model \
         ({elided_box_frees} never-read box allocations removed per run)",
        linked.len()
    );
    (row, controls)
}

/// Link a copy of `facts.object` whose row protecting the call to the callee
/// has landing pad zero, and require the model of that missing pad.
fn missing_landing_pad_control(
    lane: &Path,
    facts: &EhFunctionFacts,
    linked: &[&ObjectFacts],
    rlib: &Path,
    driver: &Path,
    opt: u32,
) -> String {
    let control = lane.join(format!("no_pad_{}", facts.function));
    std::fs::create_dir(&control).unwrap();
    let mut bytes = std::fs::read(&facts.object).unwrap();
    let row = &facts.lsda_rows[facts.protecting_row];
    let field = facts.lsda.start + row.landing_pad_field.start
        ..facts.lsda.start + row.landing_pad_field.end;
    bytes[field.clone()].copy_from_slice(&padded_uleb128_zero(field.len()));
    let mutated_rows = parse_unwind_lsda(&bytes[facts.lsda.clone()]);
    let changed: Vec<usize> = mutated_rows
        .iter()
        .zip(&facts.lsda_rows)
        .enumerate()
        .filter(|(_, (after, before))| after != before)
        .map(|(index, _)| index)
        .collect();
    assert_eq!(changed, vec![facts.protecting_row]);
    assert_eq!(mutated_rows[facts.protecting_row].landing_pad, 0);
    let mutant = control.join(facts.object.file_name().unwrap());
    std::fs::write(&mutant, &bytes).unwrap();
    let objects: Vec<&Path> = linked
        .iter()
        .map(|other| {
            if other.path == facts.object {
                mutant.as_path()
            } else {
                other.path.as_path()
            }
        })
        .collect();
    let executable = link(&control, "bridgeunwind", &objects, rlib, driver);
    let mutated = model(Some(facts.function));
    assert_model_run(
        &control,
        &executable,
        "run0",
        &render(&mutated),
        &format!("CG O{opt} without {}'s landing pad", facts.function),
    );
    let (reference_drops, reference_frees) = totals(&model(None));
    let (drops, frees) = totals(&mutated);
    println!(
        "CG O{opt}: without {}'s landing pad at {:#x}, {} drops and {} frees are missing, as modelled",
        facts.function,
        row.landing_pad,
        reference_drops - drops,
        reference_frees - frees
    );
    format!(
        "{{\"function\":\"{}\",\"callee\":\"{}\",\"opt_level\":{opt},\"lsda_rows\":{},\
         \"landing_pad\":{},\"mutated_rows\":1,\"exit_code\":0,\"lost_drops\":{},\"lost_frees\":{}}}",
        facts.function,
        facts.callee,
        facts.lsda_rows.len(),
        row.landing_pad,
        reference_drops - drops,
        reference_frees - frees
    )
}

/// The `disable-unwind` opt-out: the bridge must refuse every fixture
/// function by name and leave no object defining one.
fn disable_unwind_refusal(
    artifacts: &Path,
    source: &Path,
    rlib: &Path,
    opt: u32,
    backend: &Path,
) -> String {
    let lane = artifacts.join(format!("disable_unwind_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let knobs: &[&str] = &["no-proof-certs", "disable-unwind"];
    let (output, transcript) = compile(
        source,
        rlib,
        &lane.join("objects"),
        opt,
        Some((backend, knobs)),
        &lane.join("compile.log"),
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected compiler refusal, not success, timeout or crash: {transcript}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("[TCG-MIR-UNSUPPORTED]"),
        "wrong refusal boundary: {transcript}"
    );
    let rows: Vec<&str> = stderr.lines().map(str::trim).collect();
    for (function, _) in FIXTURES {
        let row = format!("- {function}: {DISABLE_UNWIND_REFUSAL}");
        assert_eq!(
            rows.iter().filter(|line| **line == row).count(),
            1,
            "refusal must name `{function}` exactly once: {transcript}"
        );
    }
    let leftover = inspect_objects(&lane.join("objects"));
    let definitions = leftover.iter().filter(|o| o.defines_fixture()).count();
    assert_eq!(
        definitions, 0,
        "a refused compile left an object defining a fixture function"
    );
    format!(
        "{{\"name\":\"disable_unwind\",\"opt_level\":{opt},\"cg_refusals\":1,\
         \"refused_functions\":{},\"fixture_definitions\":{definitions}}}",
        FIXTURES.len()
    )
}

#[test]
fn readelf_rows_lsda_rows_and_the_model_parse() {
    let symbols = parse_symbols(
        "Symbol table '.symtab' contains 5 entries:\n   Num:    Value          Size Type    Bind   Vis      Ndx Name\n     \
         0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND \n     \
         2: 0000000000000000     0 SECTION LOCAL  DEFAULT    2 \n     \
         3: 0000000000000010   160 FUNC    GLOBAL DEFAULT    1 box_across_unwind\n     \
         6: 0000000000000000     0 NOTYPE  GLOBAL DEFAULT  UND _Unwind_Resume\n     \
         7: 0000000000000000    24 FUNC    GLOBAL DEFAULT [VARIANT_PCS]     1 f\n",
    );
    assert_eq!(symbols.len(), 5, "{symbols:?}");
    assert_eq!(
        (
            symbols[1].index,
            symbols[1].kind.as_str(),
            symbols[1].section.as_str(),
            symbols[1].name.as_str()
        ),
        (2, "SECTION", "2", "")
    );
    assert_eq!(
        symbols[2],
        ElfSymbol {
            index: 3,
            value: 0x10,
            size: 160,
            kind: "FUNC".into(),
            bind: "GLOBAL".into(),
            section: "1".into(),
            name: "box_across_unwind".into(),
        }
    );
    assert_eq!(
        (symbols[3].section.as_str(), symbols[3].name.as_str()),
        ("UND", "_Unwind_Resume")
    );
    assert_eq!(
        (symbols[4].section.as_str(), symbols[4].name.as_str()),
        ("1", "f")
    );
    let sections = parse_sections(
        "  [Nr] Name              Type            Address          Off    Size   ES Flg Lk Inf Al\n  \
         [ 0]                   NULL            0000000000000000 000000 000000 00      0   0  0\n  \
         [ 1] .text             PROGBITS        0000000000000000 000040 0000a0 00  AX  0   0  4\n  \
         [ 2] .gcc_except_table PROGBITS        0000000000000000 0000e0 000010 00   A  0   0  4\n  \
         [ 5] .note.GNU-stack   PROGBITS        0000000000000000 000148 000000 00      0   0  1\n",
    );
    assert_eq!(
        sections.get(&2),
        Some(&ElfSection {
            name: ".gcc_except_table".into(),
            offset: 0xe0,
            size: 0x10
        })
    );
    assert_eq!(
        sections.get(&5).map(|s| s.name.as_str()),
        Some(".note.GNU-stack")
    );
    assert!(!sections.contains_key(&0));
    let relocations = parse_relocations(
        "Relocation section '.rela.text' at offset 0x148 contains 1 entry:\n    \
         Offset             Info             Type               Symbol's Value  Symbol's Name + Addend\n\
         0000000000000034  000000070000011b R_AARCH64_CALL26       0000000000000000 ay_may_unwind + 0\n\
         \n\
         Relocation section '.rela.eh_frame' at offset 0x1c0 contains 1 entry:\n    \
         Offset             Info             Type               Symbol's Value  Symbol's Name + Addend\n\
         0000000000000031  0000000200000105 R_AARCH64_PREL32       0000000000000000  + 0\n\
         0000000000000041  0000000500000105 R_AARCH64_PREL32       0000000000000000 .gcc_except_table + 20\n\
         0000000000000051  0000000500000105 R_AARCH64_PREL32       0000000000000000 .gcc_except_table - 4\n",
    );
    assert_eq!(
        relocations,
        vec![
            ElfRelocation {
                section: ".text".into(),
                offset: 0x34,
                symbol_index: 7,
                kind: "R_AARCH64_CALL26".into(),
                addend: 0,
            },
            ElfRelocation {
                section: ".eh_frame".into(),
                offset: 0x31,
                symbol_index: 2,
                kind: "R_AARCH64_PREL32".into(),
                addend: 0,
            },
            ElfRelocation {
                section: ".eh_frame".into(),
                offset: 0x41,
                symbol_index: 5,
                kind: "R_AARCH64_PREL32".into(),
                addend: 0x20,
            },
            ElfRelocation {
                section: ".eh_frame".into(),
                offset: 0x51,
                symbol_index: 5,
                kind: "R_AARCH64_PREL32".into(),
                addend: -4,
            },
        ]
    );
    // An LSDA's own extent, read from its header: the TType form ends one
    // empty-filter byte past its TType base, the cleanup-only form at the end
    // of its call-site table.
    assert_eq!(
        lsda_length(&[0xff, 0x9b, 0x19, 0x01, 0x14, 0x00, 0x2c, 0x00, 0x00, 0x2c]),
        29
    );
    assert_eq!(
        lsda_length(&[
            0xff, 0xff, 0x01, 0x05, 0x44, 0x04, 0xa4, 0x02, 0x00, 0x00, 0x00, 0x00
        ]),
        9
    );
    // The bridge's O0 `box_across_unwind` table: filler, the protected call
    // with its cleanup pad, filler; a two-byte landing pad in a second table.
    let rows = parse_unwind_lsda(&[
        0xff, 0xff, 0x01, 0x0c, 0x00, 0x34, 0x00, 0x00, 0x34, 0x04, 0x40, 0x00, 0x38, 0x68, 0x00,
        0x00,
    ]);
    assert_eq!(
        rows.iter()
            .map(|row| (row.start, row.length, row.landing_pad, row.action))
            .collect::<Vec<_>>(),
        vec![(0, 0x34, 0, 0), (0x34, 4, 0x40, 0), (0x38, 0x68, 0, 0)]
    );
    assert_eq!(rows[1].landing_pad_field, 10..11);
    let rows = parse_unwind_lsda(&[0xff, 0xff, 0x01, 0x05, 0x44, 0x04, 0xa4, 0x02, 0x00, 0x00]);
    assert_eq!(
        (rows[0].landing_pad, rows[0].landing_pad_field.clone()),
        (0x124, 6..8)
    );
    assert_eq!(padded_uleb128_zero(1), vec![0]);
    assert_eq!(padded_uleb128_zero(2), vec![0x80, 0]);
    let mut at = 0;
    assert_eq!(read_uleb128(&[0x80, 0x80, 0x00], &mut at), 0);
    assert_eq!(at, 3);
    // The model: every missing pad loses something, and only in its frame.
    let reference = model(None);
    assert_eq!(reference.len(), CALLS_PER_RUN);
    assert_eq!(
        reference.iter().filter(|call| call.hooks == 1).count(),
        PANICS_PER_RUN
    );
    assert_eq!(totals(&reference), (DROP_EVENTS_PER_RUN, BOX_FREES_PER_RUN));
    for (function, lost) in [
        ("box_across_unwind", (0, 1)),
        ("guards_across_unwind", (4, 2)),
        ("nested_unwind", (1, 1)),
    ] {
        let (drops, frees) = totals(&model(Some(function)));
        assert_eq!(
            (DROP_EVENTS_PER_RUN - drops, BOX_FREES_PER_RUN - frees),
            lost,
            "{function}"
        );
        assert_ne!(render(&model(Some(function))), render(&reference));
    }
    // Removing the never-read boxes changes only their allocation counts.
    let elided = with_elided_boxes(model(None), true, true);
    assert_eq!(
        totals(&elided),
        (DROP_EVENTS_PER_RUN, BOX_FREES_PER_RUN - 3)
    );
    assert_eq!(
        render(&elided)
            .lines()
            .zip(render(&reference).lines())
            .filter(|(a, b)| a != b)
            .count(),
        3
    );
}

#[test]
fn rust_panic_unwinds_through_bridge_cleanup_pads_linux() {
    // The bridge compiles pass backend knobs on `-Ztrust-ir-cg-args`; their
    // former `TCG_*` environment spelling is refused outright, so a compiler
    // without that option cannot express this test at all.
    if toolchain_support::skip_without_backend_knobs("unwind_cleanup_linux") {
        return;
    }
    for name in [
        "TCG_NO_PROOF_CERTS",
        "TCG_JIT_UNCHECKED",
        "TCG_OPT_LEVEL",
        "TCG_DISABLE_UNWIND",
        "TRUST_CG_DISABLE_PASSES",
        "TRUST_CG_DISABLE_CFGSIMPLIFY_SUBPASSES",
        "TCG_DATAFLOW_INTEGRITY",
    ] {
        assert!(
            std::env::var_os(name).is_none(),
            "qualification rejects {name}"
        );
    }
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-unwind-linux.XXXXXX"])
        .output()
        .expect("mktemp artifacts");
    assert!(temp.status.success());
    let artifacts = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("native bridge unwind artifacts: {}", artifacts.display());
    let host = checked(
        toolchain_support::rustc_driver_command().arg("-vV"),
        30,
        &artifacts.join("rustc.log"),
    );
    assert!(
        String::from_utf8_lossy(&host.stdout)
            .lines()
            .any(|line| line == format!("host: {TARGET}"))
    );
    let (backend, digest) = backend();

    let rlib = build_panicker(&artifacts);
    let source = artifacts.join("unwind.rs");
    let driver = artifacts.join("driver.rs");
    std::fs::write(&source, format!("{DARWIN_UNWIND_CRATE}{UNWIND_EXTENSION}")).unwrap();
    std::fs::write(&driver, DRIVER).unwrap();
    let mir_functions = assert_mir_cleanup_edges(&artifacts, &source, &rlib);

    let mut lanes = Vec::new();
    let mut controls = Vec::new();
    let mut unsupported = Vec::new();
    for opt in OPT_LEVELS {
        let (row, missing_pads) = unwind_lane(
            &artifacts,
            &source,
            &rlib,
            &driver,
            opt,
            Some((&backend, &digest)),
        );
        lanes.push(row);
        controls.extend(missing_pads);
        let (row, none) = unwind_lane(&artifacts, &source, &rlib, &driver, opt, None);
        assert!(none.is_empty());
        lanes.push(row);
        unsupported.push(disable_unwind_refusal(
            &artifacts, &source, &rlib, opt, &backend,
        ));
    }
    assert_eq!(
        sha256(&backend),
        digest,
        "backend changed during unwind qualification"
    );
    println!(
        "\nTCG_BRIDGE_UNWIND_EXECUTION {{\"schema\":1,\"target\":\"{TARGET}\",\"opt_levels\":[0,1,2,3],\
         \"runs_per_lane\":{RUNS_PER_LANE},\"mir_cleanup_functions\":{mir_functions},\
         \"lanes\":[{}],\"missing_landing_pad_controls\":[{}],\"unsupported\":[{}],\
         \"backend_sha256\":\"{digest}\"}}",
        lanes.join(","),
        controls.join(","),
        unsupported.join(",")
    );
    if std::env::var_os(KEEP_ARTIFACTS).is_some_and(|value| value == "1") {
        eprintln!("retained artifacts: {}", artifacts.display());
    } else {
        std::fs::remove_dir_all(&artifacts).expect("remove the artifacts of a passing run");
    }
}

#[test]
fn lsda_parser_binds_real_cleanup_terminate_filters_and_rejects_wrong_actions() {
    // Exact O0 LSDA bytes from the retained sealed16 objects. These functions
    // have MIR cleanup user-Drop calls with unwind terminate(cleanup).
    let guards = [
        0xff, 0x9b, 0x41, 0x01, 0x3a, 0x00, 0x50, 0x00, 0x00, 0x50, 0x04, 0xac, 0x02, 0x00, 0x54,
        0x4c, 0x00, 0x00, 0xa0, 0x01, 0x04, 0xa8, 0x01, 0x00, 0xa4, 0x01, 0x80, 0x01, 0x00, 0x00,
        0xa4, 0x02, 0x04, 0xac, 0x02, 0x00, 0xa8, 0x02, 0x1c, 0x00, 0x00, 0xc4, 0x02, 0x04, 0xcc,
        0x02, 0x00, 0xc8, 0x02, 0x40, 0x00, 0x00, 0x88, 0x03, 0x04, 0x90, 0x03, 0x01, 0x8c, 0x03,
        0x2c, 0x00, 0x00, 0x7f, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    let nested = [
        0xff, 0x9b, 0x29, 0x01, 0x24, 0x00, 0x50, 0x00, 0x00, 0x50, 0x04, 0xfc, 0x01, 0x00, 0x54,
        0xa0, 0x01, 0x00, 0x00, 0xf4, 0x01, 0x04, 0xfc, 0x01, 0x00, 0xf8, 0x01, 0x2c, 0x00, 0x00,
        0xa4, 0x02, 0x04, 0xac, 0x02, 0x01, 0xa8, 0x02, 0x2c, 0x00, 0x00, 0x7f, 0x00, 0x00, 0x00,
    ];
    let guard_rows = parse_unwind_lsda(&guards);
    assert_eq!(guard_rows.len(), 11);
    assert_eq!(
        guard_rows
            .iter()
            .filter(|r| r.action != 0)
            .map(|r| (r.start, r.length, r.landing_pad, r.action))
            .collect::<Vec<_>>(),
        [(0x188, 4, 0x190, 1)]
    );
    let ordinary = guard_rows.iter().find(|row| row.start == 0x50).unwrap();
    assert_eq!(
        (ordinary.length, ordinary.landing_pad, ordinary.action),
        (4, 0x12c, 0)
    );
    let nested_rows = parse_unwind_lsda(&nested);
    assert_eq!(nested_rows.len(), 7);
    assert_eq!(
        nested_rows
            .iter()
            .filter(|r| r.action != 0)
            .map(|r| (r.start, r.length, r.landing_pad, r.action))
            .collect::<Vec<_>>(),
        [(0x124, 4, 0x12c, 1)]
    );

    // Reject semantic changes, not just a byte-count mismatch: a catch instead
    // of an empty filter, an action successor, an allowed type, an unbound
    // action, nonzero padding and unsupported header encodings.
    for (label, index, byte) in [
        ("positive catch filter", 63, 1),
        ("nonterminal action", 64, 1),
        ("nonempty allowed-type list", 68, 1),
        ("wrong TType base", 2, 0x40),
        ("wrong call-site encoding", 3, 2),
        ("nonzero padding", 65, 1),
        ("unsupported TType encoding", 1, 0),
        ("unbound action offset", 57, 2),
    ] {
        let mut mutant = guards;
        mutant[index] = byte;
        assert!(
            std::panic::catch_unwind(|| parse_unwind_lsda(&mutant)).is_err(),
            "{label}"
        );
    }
    let mut no_terminate_pad = guards;
    no_terminate_pad[55..57].copy_from_slice(&padded_uleb128_zero(2));
    assert!(std::panic::catch_unwind(|| parse_unwind_lsda(&no_terminate_pad)).is_err());

    // The existing native lost-drop/free control removes only the ordinary
    // cleanup pad. Its action0 stays valid and the real terminate filter stays.
    let mut no_cleanup_pad = guards;
    let field = ordinary.landing_pad_field.clone();
    no_cleanup_pad[field.clone()].copy_from_slice(&padded_uleb128_zero(field.len()));
    let mutant_rows = parse_unwind_lsda(&no_cleanup_pad);
    let changed: Vec<_> = guard_rows
        .iter()
        .zip(&mutant_rows)
        .enumerate()
        .filter_map(|(index, (before, after))| (before != after).then_some(index))
        .collect();
    assert_eq!(changed, [1]);
    assert_eq!(mutant_rows[1].landing_pad, 0);
    assert_eq!(mutant_rows.iter().filter(|row| row.action != 0).count(), 1);
}
