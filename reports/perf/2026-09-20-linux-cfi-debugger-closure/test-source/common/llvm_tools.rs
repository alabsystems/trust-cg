// trust-cg-codegen/tests/common/llvm_tools.rs - external LLVM object tools
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Discovery and bounded execution of the external LLVM object inspectors
//! (`llvm-dwarfdump`, `llvm-readelf`, `llvm-objdump`) used as independent
//! readers of emitted AArch64 ELF objects.
//!
//! A missing tool is a test FAILURE, never a skip: these targets are
//! evidence for DWARF and CFI emission, and an absent reader cannot yield it.
//! Set `TRUST_CG_LLVM_BIN` to the directory holding the tools when they are
//! not on the searched paths.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

/// Directories searched after `TRUST_CG_LLVM_BIN`, before `PATH`.
const LLVM_DIRS: &[&str] = &[
    "/opt/homebrew/opt/llvm/bin",
    "/usr/local/opt/llvm/bin",
    "/usr/lib/llvm-22/bin",
    "/usr/lib/llvm-21/bin",
    "/usr/lib/llvm-20/bin",
    "/usr/lib/llvm-19/bin",
    "/usr/lib/llvm-18/bin",
    "/usr/lib/llvm-17/bin",
    "/usr/lib/llvm-16/bin",
    "/usr/lib/llvm-15/bin",
];

fn on_path(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join(name))
        .find(|candidate| candidate.is_file())
}

/// Locate LLVM tool `name` (for example `llvm-dwarfdump`), or `None`.
pub fn find_llvm_tool(name: &str) -> Option<PathBuf> {
    if let Some(dir) = std::env::var_os("TRUST_CG_LLVM_BIN") {
        let candidate = Path::new(&dir).join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    for dir in LLVM_DIRS {
        let candidate = Path::new(dir).join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    if let Some(found) = on_path(name) {
        return Some(found);
    }
    (14..=22)
        .rev()
        .find_map(|major| on_path(&format!("{name}-{major}")))
}

/// Locate LLVM tool `name` or fail the test with the discovery contract.
/// The first resolution of each tool in a process prints its path and
/// `--version` line, so a floor transcript records which reader ran.
pub fn llvm_tool(name: &str) -> PathBuf {
    use std::collections::BTreeSet;
    use std::sync::{Mutex, OnceLock};
    static REPORTED: OnceLock<Mutex<BTreeSet<String>>> = OnceLock::new();

    let path = find_llvm_tool(name).unwrap_or_else(|| {
        panic!(
            "{name} is required to inspect AArch64 ELF objects and was not found in \
             $TRUST_CG_LLVM_BIN, {LLVM_DIRS:?}, or PATH (also {name}-14..22); install LLVM \
             or point TRUST_CG_LLVM_BIN at its bin directory"
        )
    });
    let first = REPORTED
        .get_or_init(|| Mutex::new(BTreeSet::new()))
        .lock()
        .map(|mut seen| seen.insert(name.to_string()))
        .unwrap_or(false);
    if first {
        let version = Command::new(&path)
            .arg("--version")
            .output()
            .ok()
            .and_then(|out| {
                String::from_utf8_lossy(&out.stdout)
                    .lines()
                    .map(str::trim)
                    .find(|line| line.contains("version"))
                    .map(str::to_string)
            })
            .unwrap_or_default();
        eprintln!("external reader {name}: {} ({version})", path.display());
    }
    path
}

/// Run `tool args... path`, require success, and return stdout. Warnings
/// on stderr are appended so a caller can refuse them.
pub fn run_llvm(tool: &str, args: &[&str], path: &Path) -> String {
    let exe = llvm_tool(tool);
    let output = Command::new(&exe)
        .args(args)
        .arg(path)
        .output()
        .unwrap_or_else(|e| panic!("run {}: {e}", exe.display()));
    assert!(
        output.status.success(),
        "{} {} {} failed ({:?})\nstdout:\n{}\nstderr:\n{}",
        exe.display(),
        args.join(" "),
        path.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !stderr.trim().is_empty() {
        text.push_str("\n[stderr]\n");
        text.push_str(&stderr);
    }
    text
}

/// Run `tool args... path` and return (success, stdout + stderr) without
/// asserting, for mutation controls that expect a failure.
pub fn try_run_llvm(tool: &str, args: &[&str], path: &Path) -> (bool, String) {
    let exe = llvm_tool(tool);
    let output = Command::new(&exe)
        .args(args)
        .arg(path)
        .output()
        .unwrap_or_else(|e| panic!("run {}: {e}", exe.display()));
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&output.stderr));
    (output.status.success(), text)
}

/// A per-test scratch directory under the system temp directory.
pub fn scratch_dir(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_{test}_{}_{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let dir = PathBuf::from(
        dir.to_string_lossy()
            .chars()
            .map(|c| {
                if c.is_ascii_alphanumeric() || "/_-.".contains(c) {
                    c
                } else {
                    '_'
                }
            })
            .collect::<String>(),
    );
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

/// Remove a scratch directory unless `TRUST_CG_KEEP_TEST_OBJECTS` is set
/// (then its path is printed so the objects can be inspected).
pub fn cleanup(dir: &Path) {
    if std::env::var_os("TRUST_CG_KEEP_TEST_OBJECTS").is_some() {
        eprintln!("kept test objects in {}", dir.display());
    } else {
        let _ = std::fs::remove_dir_all(dir);
    }
}

/// One `FUNC` symbol row from `llvm-readelf -s`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncSymbol {
    pub name: String,
    pub value: u64,
    pub size: u64,
}

/// Every `FUNC` symbol of an ELF object, read by `llvm-readelf -s --wide`.
pub fn func_symbols(path: &Path) -> Vec<FuncSymbol> {
    let text = run_llvm("llvm-readelf", &["-s", "--wide"], path);
    text.lines()
        .filter_map(|line| {
            let fields: Vec<&str> = line.split_whitespace().collect();
            // Num: Value Size Type Bind Vis Ndx Name
            if fields.len() < 8 || fields[3] != "FUNC" {
                return None;
            }
            Some(FuncSymbol {
                name: fields[7].to_string(),
                value: u64::from_str_radix(fields[1], 16).ok()?,
                size: fields[2].parse().ok()?,
            })
        })
        .collect()
}

/// One instruction from `llvm-objdump -d`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Insn {
    pub address: u64,
    pub mnemonic: String,
    pub operands: Vec<String>,
}

/// Split an operand string at top-level commas (not inside `[...]` / `{...}`).
fn split_operands(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut current = String::new();
    for c in text.chars() {
        match c {
            '[' | '{' => depth += 1,
            ']' | '}' => depth -= 1,
            _ => {}
        }
        if c == ',' && depth == 0 {
            out.push(current.trim().to_string());
            current.clear();
        } else {
            current.push(c);
        }
    }
    if !current.trim().is_empty() {
        out.push(current.trim().to_string());
    }
    out
}

/// Disassemble the `.text` section of an AArch64 ELF object with the
/// external LLVM disassembler.
pub fn disassemble(path: &Path) -> Vec<Insn> {
    let text = run_llvm(
        "llvm-objdump",
        &["-d", "--no-show-raw-insn", "--triple=aarch64-linux-gnu"],
        path,
    );
    text.lines()
        .filter_map(|line| {
            let (address, rest) = line.split_once(':')?;
            let address = u64::from_str_radix(address.trim(), 16).ok()?;
            let rest = rest.split("//").next().unwrap_or("").trim();
            if rest.is_empty() {
                return None;
            }
            let (mnemonic, operands) = match rest.split_once(char::is_whitespace) {
                Some((m, o)) => (
                    m.to_string(),
                    split_operands(o.split('<').next().unwrap_or("")),
                ),
                None => (rest.to_string(), Vec::new()),
            };
            Some(Insn {
                address,
                mnemonic,
                operands,
            })
        })
        .collect()
}

/// DWARF register number of an AArch64 register operand (`x3`/`w3` -> 3,
/// `sp`/`wsp` -> 31, `d8`/`s8`/`q8`/`v8.16b` -> 72), or `None`.
pub fn dwarf_reg(operand: &str) -> Option<u64> {
    let op = operand.trim().trim_start_matches('[').trim_end_matches(']');
    let op = op.split('.').next().unwrap_or(op);
    if op == "sp" || op == "wsp" {
        return Some(31);
    }
    let (class, number) = op.split_at(1);
    let n: u64 = number.parse().ok()?;
    match class {
        "x" | "w" if n <= 30 => Some(n),
        "d" | "s" | "h" | "b" | "q" | "v" if n <= 31 => Some(64 + n),
        _ => None,
    }
}

/// DWARF registers an instruction writes, read off the disassembly. Stores,
/// compares and branches write no operand register; `bl`/`blr` clobber the
/// AAPCS64 caller-saved set; writeback addressing writes its base.
pub fn written_registers(insn: &Insn) -> Vec<u64> {
    let m = insn.mnemonic.as_str();
    let mut written = Vec::new();
    let writeback_base = insn.operands.iter().any(|op| op.ends_with('!'))
        || (insn.operands.len() >= 2
            && insn
                .operands
                .iter()
                .position(|op| op.starts_with('[') && op.ends_with(']'))
                .is_some_and(|i| i + 1 < insn.operands.len()));
    if writeback_base
        && let Some(base) = insn
            .operands
            .iter()
            .find(|op| op.starts_with('['))
            .and_then(|op| dwarf_reg(op.trim_start_matches('[').split(',').next().unwrap_or("")))
    {
        written.push(base);
    }
    let first = insn.operands.first().and_then(|op| dwarf_reg(op));
    let second = insn.operands.get(1).and_then(|op| dwarf_reg(op));
    match m {
        "bl" | "blr" => {
            written.extend((0..=18).chain([30]));
            written.extend((64..=71).chain(80..=95));
        }
        "b" | "br" | "ret" | "cbz" | "cbnz" | "tbz" | "tbnz" | "nop" | "cmp" | "cmn" | "tst"
        | "fcmp" | "fcmpe" | "ccmp" | "ccmn" | "fccmp" | "fccmpe" | "prfm" | "dmb" | "dsb"
        | "isb" | "brk" | "udf" | "hint" => {}
        _ if m.starts_with("b.") => {}
        "stxr" | "stlxr" | "stxrb" | "stlxrb" | "stxrh" | "stlxrh" | "stxp" | "stlxp" => {
            written.extend(first);
        }
        _ if m.starts_with("st") => {}
        "ldp" | "ldpsw" | "ldnp" | "ldxp" | "ldaxp" | "casp" | "caspa" | "caspl" | "caspal" => {
            written.extend(first);
            written.extend(second);
        }
        _ => written.extend(first),
    }
    written
}

fn le_u16(b: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(b[at..at + 2].try_into().expect("u16"))
}
fn le_u32(b: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(b[at..at + 4].try_into().expect("u32"))
}
fn le_u64(b: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(b[at..at + 8].try_into().expect("u64"))
}

/// `(file offset, size)` of the named section of an ELF64 little-endian
/// object, read from its section header table (independently of the writer).
pub fn elf_section_extent(object: &[u8], wanted: &str) -> Option<(usize, usize)> {
    let shoff = le_u64(object, 0x28) as usize;
    let shnum = le_u16(object, 0x3c) as usize;
    let shstrndx = le_u16(object, 0x3e) as usize;
    let header = |i: usize| shoff + i * 64;
    let names = le_u64(object, header(shstrndx) + 0x18) as usize;
    (0..shnum).find_map(|i| {
        let name_at = names + le_u32(object, header(i)) as usize;
        let end = object[name_at..].iter().position(|b| *b == 0)? + name_at;
        (&object[name_at..end] == wanted.as_bytes()).then(|| {
            (
                le_u64(object, header(i) + 0x18) as usize,
                le_u64(object, header(i) + 0x20) as usize,
            )
        })
    })
}
