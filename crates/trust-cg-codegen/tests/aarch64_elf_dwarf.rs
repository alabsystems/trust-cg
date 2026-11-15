// trust-cg-codegen/tests/aarch64_elf_dwarf.rs - AArch64 ELF DWARF evidence
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 ELF DWARF emission checked by independent readers.
//!
//! Real `-g` (`emit_debug`) compiles for `aarch64-unknown-linux-gnu` at O0-O3,
//! through the single-function object path and two whole-module entries
//! (`compile_module_emission_with_debug_provenance`, both functions carrying
//! their register-debug provenance, and the legacy lines-only
//! `compile_module_emission`, which describes no parameter or variable; each
//! with the fixture at text offset 0 and past the leaf), are read back by
//! LLVM's `llvm-dwarfdump`, `llvm-readelf` and `llvm-objdump`, none of which
//! share code with the emitter:
//!
//! * `llvm-dwarfdump --verify` accepts `.debug_info`, `.debug_line` and
//!   `.debug_loc`, with every cross-section and code-address field resolved
//!   through its `R_AARCH64_ABS32` / `R_AARCH64_ABS64` record;
//! * each subprogram's `[low_pc, high_pc)` equals its function symbol's start
//!   and lies inside the symbol's extent, and every line row lies inside a
//!   subprogram, on an instruction, at a fixture source line;
//! * every location-list range lies inside its subprogram and is valid
//!   against the disassembled machine code: a register location's register
//!   is not written (nor clobbered by a call) inside its range, a
//!   frame-base-relative location only covers code where X29 is the frame
//!   pointer (after the prologue sets it, before an epilogue restores it),
//!   and a spilled value's range begins right after the store to its slot
//!   with no overwrite of that slot inside it;
//! * every `.rela.debug_info` / `.rela.debug_line` record sits on a relocated
//!   field and names the section that field refers to (a relocatable-object
//!   reader resolves every section symbol to 0 and cannot tell).
//!
//! Mutation controls neutralize the relocation records and require the
//! independent reader to lose the resolved names and addresses, and show
//! the location checker refusing ranges the machine code contradicts in the
//! single-function object and in both module layouts. The Compiler/CLI
//! module path (`compiler_emit_debug_...`, one defined function) still
//! describes subprograms and line rows only; the lines-only two-function
//! module object keeps the reader, relocation-target and relocation-mutation
//! checks. The emitter-side refusal of a second function's unshifted
//! description (its entry-range parameter starts below the function) is a
//! `pipeline.rs` unit test; an unshifted range that lands inside the
//! function passes emission and is left to the location checker here and
//! the gdb module leg. The provenance entry also feeds the Mach-O writer;
//! one host-neutral test applies the
//! `llvm-dwarfdump --verify`, symbol and location checks to Mach-O module
//! objects (no debugger reads them here). This is evidence for these
//! fixtures and readers, not a proof that every location describes the
//! value its source variable holds.

#[path = "common/llvm_tools.rs"]
mod llvm_tools;

#[path = "common/elf_debug_fixture.rs"]
mod elf_debug_fixture;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use elf_debug_fixture::{
    FIXTURE, FIXTURE_FILE, LEAF, fixture_lines, lir_fixture, lir_fixture_leaf,
};
use llvm_tools::{
    FuncSymbol, Insn, cleanup, disassemble, elf_section_extent, func_symbols, run_llvm,
    scratch_dir, try_run_llvm, written_registers,
};
use trust_cg_codegen::pipeline::{
    DispatchVerifyMode, ModuleSymbolLinkage, OptLevel, Pipeline, PipelineConfig, PipelineError,
};

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn pipeline(level: OptLevel, emit_debug: bool) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: level,
        emit_debug,
        verify_dispatch: DispatchVerifyMode::Off,
        ..PipelineConfig::for_target(TRIPLE)
    })
}

fn write_object(dir: &Path, name: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.join(name);
    fs::write(&path, bytes).expect("write object");
    path
}

// ---------------------------------------------------------------------------
// llvm-dwarfdump readers
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct Subprogram {
    name: String,
    low: u64,
    high: u64,
}

#[derive(Debug, Clone)]
struct LocationRange {
    start: u64,
    end: u64,
    expr: String,
}

#[derive(Debug, Clone)]
struct DwarfVariable {
    tag: String,
    name: String,
    /// The enclosing `DW_TAG_subprogram`'s name.
    subprogram: String,
    /// `None` for a single-expression location valid over the whole scope.
    ranges: Option<Vec<LocationRange>>,
    single: Option<String>,
}

fn quoted(line: &str) -> Option<String> {
    let start = line.find("(\"")? + 2;
    let end = line[start..].find("\")")? + start;
    Some(line[start..end].to_string())
}

fn hex_after(line: &str, key: &str) -> Option<u64> {
    let at = line.find(key)? + key.len();
    let rest = line[at..].trim_start().trim_start_matches('(');
    let rest = rest.strip_prefix("0x")?;
    let digits: String = rest.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
    u64::from_str_radix(&digits, 16).ok()
}

fn parse_range(line: &str) -> Option<LocationRange> {
    let open = line.find("[0x")?;
    let rest = &line[open + 3..];
    let comma = rest.find(", 0x")?;
    let start = u64::from_str_radix(&rest[..comma], 16).ok()?;
    let rest = &rest[comma + 4..];
    let close = rest.find(')')?;
    let end = u64::from_str_radix(&rest[..close], 16).ok()?;
    let expr = rest[close + 1..]
        .trim_start_matches(':')
        .trim()
        .trim_end_matches(')')
        .to_string();
    Some(LocationRange { start, end, expr })
}

/// Subprograms and located variables from `llvm-dwarfdump --debug-info`.
fn read_debug_info(dump: &str) -> (Vec<Subprogram>, Vec<DwarfVariable>) {
    let mut subprograms = Vec::new();
    let mut variables = Vec::new();
    let mut tag = String::new();
    let mut name = String::new();
    let mut low = None;
    let mut in_location = false;
    let mut current: Option<DwarfVariable> = None;
    let flush = |current: &mut Option<DwarfVariable>, variables: &mut Vec<DwarfVariable>| {
        if let Some(var) = current.take() {
            variables.push(var);
        }
    };
    for line in dump.lines() {
        let trimmed = line.trim();
        if let Some(at) = trimmed.find("DW_TAG_") {
            flush(&mut current, &mut variables);
            in_location = false;
            tag = trimmed[at..]
                .split_whitespace()
                .next()
                .unwrap_or("")
                .to_string();
            name.clear();
            low = None;
            continue;
        }
        if trimmed.starts_with("DW_AT_") {
            in_location = false;
        }
        if trimmed.starts_with("DW_AT_name") {
            name = quoted(trimmed).unwrap_or_default();
        } else if trimmed.starts_with("DW_AT_low_pc") {
            low = hex_after(trimmed, "DW_AT_low_pc");
        } else if trimmed.starts_with("DW_AT_high_pc") && tag == "DW_TAG_subprogram" {
            let high = hex_after(trimmed, "DW_AT_high_pc").expect("subprogram high_pc");
            subprograms.push(Subprogram {
                name: name.clone(),
                low: low.expect("subprogram low_pc precedes high_pc"),
                high,
            });
        } else if trimmed.starts_with("DW_AT_location") {
            let mut var = DwarfVariable {
                tag: tag.clone(),
                name: name.clone(),
                // A subprogram is recorded at its high_pc, before its
                // children, so the last one recorded encloses this DIE.
                subprogram: subprograms
                    .last()
                    .map(|sub: &Subprogram| sub.name.clone())
                    .unwrap_or_default(),
                ranges: None,
                single: None,
            };
            if let Some(range) = parse_range(trimmed) {
                var.ranges = Some(vec![range]);
            } else if trimmed.contains("DW_OP_") {
                let expr = trimmed
                    .split_once('(')
                    .map(|(_, e)| e.trim_end_matches(')').to_string())
                    .unwrap_or_default();
                var.single = Some(expr);
            } else {
                var.ranges = Some(Vec::new());
            }
            current = Some(var);
            in_location = true;
            continue;
        }
        if in_location
            && let Some(range) = parse_range(trimmed)
            && let Some(var) = current.as_mut()
        {
            var.ranges.get_or_insert_with(Vec::new).push(range);
        }
    }
    flush(&mut current, &mut variables);
    (subprograms, variables)
}

#[derive(Debug, Clone, Copy)]
struct LineRow {
    address: u64,
    line: u64,
    end_sequence: bool,
}

fn read_line_rows(dump: &str) -> Vec<LineRow> {
    dump.lines()
        .filter_map(|line| {
            let fields: Vec<&str> = line.split_whitespace().collect();
            let address = fields.first()?.strip_prefix("0x")?;
            let address = u64::from_str_radix(address, 16).ok()?;
            let line_no = fields.get(1)?.parse().ok()?;
            Some(LineRow {
                address,
                line: line_no,
                end_sequence: line.contains("end_sequence"),
            })
        })
        .collect()
}

/// Register number of `DW_OP_regN` / `DW_OP_regx N`, if the expression is a
/// plain register location.
fn register_location(expr: &str) -> Option<u64> {
    let op = expr.split_whitespace().next()?;
    if let Some(n) = op.strip_prefix("DW_OP_reg")
        && let Ok(n) = n.parse()
    {
        return Some(n);
    }
    if op == "DW_OP_regx" {
        return expr
            .split_whitespace()
            .nth(1)?
            .trim_start_matches("0x")
            .parse()
            .ok();
    }
    None
}

/// Addresses `[start, end)` at which X29 holds this frame's frame pointer:
/// after the prologue's `mov x29, sp` / `add x29, sp, #imm`, and, within each
/// straight-line run, before an instruction that reloads X29.
fn frame_pointer_valid(insns: &[Insn], low: u64, high: u64) -> Vec<(u64, u64)> {
    let body: Vec<&Insn> = insns
        .iter()
        .filter(|insn| insn.address >= low && insn.address < high)
        .collect();
    let setup = body.iter().position(|insn| {
        matches!(insn.mnemonic.as_str(), "mov" | "add")
            && insn.operands.first().map(String::as_str) == Some("x29")
            && insn.operands.get(1).map(String::as_str) == Some("sp")
    });
    let Some(setup) = setup else {
        return Vec::new();
    };
    let mut ranges = Vec::new();
    let mut start = body[setup].address + 4;
    let mut valid = true;
    for insn in &body[setup + 1..] {
        let writes_fp = written_registers(insn).contains(&29) && insn.mnemonic != "bl";
        if valid && writes_fp {
            // The restoring instruction itself still executes with X29 valid.
            ranges.push((start, insn.address + 4));
            valid = false;
        }
        let ends_block = matches!(insn.mnemonic.as_str(), "ret" | "b" | "br");
        if !valid && ends_block {
            // Layout continues with another block entered with X29 valid.
            start = insn.address + 4;
            valid = true;
        }
    }
    if valid && start < high {
        ranges.push((start, high));
    }
    ranges
}

fn covered_by(ranges: &[(u64, u64)], start: u64, end: u64) -> bool {
    ranges.iter().any(|(lo, hi)| *lo <= start && end <= *hi)
}

fn signed_immediate(text: &str) -> Option<i64> {
    let text = text.trim().trim_start_matches('#');
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let value = match digits.strip_prefix("0x") {
        Some(hex) => i64::from_str_radix(hex, 16).ok()?,
        None => digits.parse().ok()?,
    };
    Some(if negative { -value } else { value })
}

/// `X29 - SP` once the prologue has run: the `add x29, sp, #a` immediate plus
/// every following prologue `sub sp, sp, #b` (with `lsl #12` scaling).
fn fp_minus_sp(insns: &[Insn], low: u64, high: u64) -> Option<i64> {
    let body: Vec<&Insn> = insns
        .iter()
        .filter(|insn| insn.address >= low && insn.address < high)
        .collect();
    let setup = body.iter().position(|insn| {
        insn.operands.first().map(String::as_str) == Some("x29")
            && insn.operands.get(1).map(String::as_str) == Some("sp")
    })?;
    let mut delta = match body[setup].mnemonic.as_str() {
        "mov" => 0,
        "add" => signed_immediate(body[setup].operands.get(2)?)?,
        _ => return None,
    };
    for insn in &body[setup + 1..] {
        let ops = &insn.operands;
        if insn.mnemonic != "sub" || ops.first().map(String::as_str) != Some("sp") {
            break;
        }
        let imm = signed_immediate(ops.get(2)?)?;
        delta += match ops.get(3).map(String::as_str) {
            Some("lsl #12") => imm << 12,
            _ => imm,
        };
    }
    Some(delta)
}

/// Frame-base (X29) offsets of the 8-byte slots a store writes, when its
/// address is X29- or SP-relative.
fn stored_slots(insn: &Insn, fp_minus_sp: i64) -> Vec<i64> {
    let stores = ["str", "stur", "stp"];
    if !stores.contains(&insn.mnemonic.as_str()) {
        return Vec::new();
    }
    let Some(address) = insn.operands.iter().find(|op| op.starts_with('[')) else {
        return Vec::new();
    };
    let inner = address.trim_end_matches('!').trim_start_matches('[');
    let inner = inner.trim_end_matches(']');
    let mut parts = inner.split(',').map(str::trim);
    let base = parts.next().unwrap_or("");
    let offset = parts.next().and_then(signed_immediate).unwrap_or(0);
    let from_fp = match base {
        "x29" => offset,
        "sp" => offset - fp_minus_sp,
        _ => return Vec::new(),
    };
    if insn.mnemonic == "stp" {
        vec![from_fp, from_fp + 8]
    } else {
        vec![from_fp]
    }
}

fn fbreg_offset(expr: &str) -> Option<i64> {
    expr.strip_prefix("DW_OP_fbreg")?.trim().parse().ok()
}

/// Check every variable's location ranges against the subprogram and the
/// disassembled code.
fn check_locations(
    context: &str,
    sub: &Subprogram,
    variables: &[DwarfVariable],
    insns: &[Insn],
) -> BTreeMap<String, Vec<LocationRange>> {
    let fp_valid = frame_pointer_valid(insns, sub.low, sub.high);
    let fp_minus_sp = fp_minus_sp(insns, sub.low, sub.high);
    let mut by_name = BTreeMap::new();
    for var in variables {
        let Some(ranges) = &var.ranges else {
            // Frame-base locations are always clipped to frame-pointer code,
            // so only a constant may be valid over the whole scope.
            let single = var.single.as_deref().unwrap_or("");
            assert!(
                single.contains("DW_OP_constu"),
                "{context}: {} `{}` has an unranged location {single:?}",
                var.tag,
                var.name
            );
            continue;
        };
        let mut previous_end = 0;
        for range in ranges {
            assert!(
                range.start < range.end,
                "{context}: `{}` has an empty range {range:?}",
                var.name
            );
            assert!(
                sub.low <= range.start && range.end <= sub.high,
                "{context}: `{}` range {range:?} escapes {sub:?}",
                var.name
            );
            assert!(
                range.start >= previous_end,
                "{context}: `{}` ranges overlap or are unsorted: {ranges:?}",
                var.name
            );
            assert!(
                range.start % 4 == 0 && range.end % 4 == 0,
                "{context}: `{}` range {range:?} is off the instruction grid",
                var.name
            );
            previous_end = range.end;
            if let Some(reg) = register_location(&range.expr) {
                // The value must already be in `reg` at `start` and stay there
                // until `end`: no instruction in [start, end - 4) may write
                // it (the last instruction still reads the old value).
                for insn in insns
                    .iter()
                    .filter(|insn| insn.address >= range.start && insn.address + 4 < range.end)
                {
                    assert!(
                        !written_registers(insn).contains(&reg),
                        "{context}: `{}` is claimed in DWARF register {reg} over {range:?}, \
                         but {insn:?} writes it inside the range",
                        var.name
                    );
                }
            } else if range.expr.starts_with("DW_OP_fbreg") {
                assert!(
                    covered_by(&fp_valid, range.start, range.end),
                    "{context}: `{}` uses the X29 frame base over {range:?}, outside the \
                     frame-pointer-valid code {fp_valid:?}",
                    var.name
                );
                // A range that does not begin where the frame pointer does is a
                // spilled value: the instruction just before it must store the
                // slot, and nothing inside it may overwrite that slot.
                let slot = fbreg_offset(&range.expr)
                    .unwrap_or_else(|| panic!("{context}: bad fbreg {range:?}"));
                if !fp_valid.iter().any(|(lo, _)| *lo == range.start) {
                    let delta = fp_minus_sp
                        .unwrap_or_else(|| panic!("{context}: no fixed X29-SP distance"));
                    let store = insns
                        .iter()
                        .find(|insn| insn.address + 4 == range.start)
                        .unwrap_or_else(|| panic!("{context}: nothing precedes {range:?}"));
                    assert!(
                        stored_slots(store, delta).contains(&slot),
                        "{context}: `{}` spill range {range:?} is not preceded by a store to \
                         X29{slot:+}: {store:?}",
                        var.name
                    );
                    for insn in insns
                        .iter()
                        .filter(|insn| insn.address >= range.start && insn.address + 4 < range.end)
                    {
                        assert!(
                            !stored_slots(insn, delta).contains(&slot),
                            "{context}: `{}` slot X29{slot:+} is overwritten inside {range:?} \
                             by {insn:?}",
                            var.name
                        );
                    }
                }
            } else {
                assert!(
                    range.expr.starts_with("DW_OP_constu"),
                    "{context}: `{}` has an unexpected location {:?}",
                    var.name,
                    range.expr
                );
            }
        }
        by_name.insert(var.name.clone(), ranges.clone());
    }
    by_name
}

/// Common assertions over one emitted object; returns its readers' views.
fn check_object(
    context: &str,
    path: &Path,
    expected: &[&str],
) -> (Vec<Subprogram>, Vec<DwarfVariable>, Vec<FuncSymbol>) {
    let verify = run_llvm("llvm-dwarfdump", &["--verify"], path);
    assert!(
        verify.contains("No errors."),
        "{context}: llvm-dwarfdump --verify:\n{verify}"
    );
    let info = run_llvm("llvm-dwarfdump", &["--debug-info"], path);
    let line = run_llvm("llvm-dwarfdump", &["--debug-line"], path);
    assert!(
        !info.contains("[stderr]") && !line.contains("[stderr]"),
        "{context}: llvm-dwarfdump reported warnings:\n{info}\n{line}"
    );
    assert!(
        info.contains(FIXTURE_FILE),
        "{context}: CU name missing:\n{info}"
    );
    let (subprograms, variables) = read_debug_info(&info);
    let symbols = func_symbols(path);
    for name in expected {
        let sub = subprograms
            .iter()
            .find(|s| s.name == *name)
            .unwrap_or_else(|| panic!("{context}: no subprogram `{name}`:\n{info}"));
        let sym = symbols
            .iter()
            .find(|s| s.name == *name)
            .unwrap_or_else(|| panic!("{context}: no FUNC symbol `{name}`"));
        assert_eq!(sub.low, sym.value, "{context}: `{name}` low_pc vs symbol");
        assert!(
            sub.high > sub.low && sub.high <= sym.value + sym.size,
            "{context}: `{name}` {sub:?} escapes symbol {sym:?}"
        );
    }

    let rows = read_line_rows(&line);
    assert!(!rows.is_empty(), "{context}: empty line table:\n{line}");
    let lines = fixture_lines();
    let mut seen_lines = BTreeSet::new();
    for row in &rows {
        let inside = subprograms.iter().any(|s| {
            if row.end_sequence {
                s.low < row.address && row.address <= s.high
            } else {
                s.low <= row.address && row.address < s.high
            }
        });
        assert!(
            inside,
            "{context}: line row {row:?} lies outside every subprogram {subprograms:?}"
        );
        assert_eq!(row.address % 4, 0, "{context}: row {row:?} off the grid");
        if !row.end_sequence {
            assert!(
                lines.contains(&row.line) || row.line <= 1,
                "{context}: row {row:?} names a line the fixture never carried"
            );
            seen_lines.insert(row.line);
        }
    }
    assert!(
        seen_lines.len() >= 3,
        "{context}: line table maps too few source lines: {seen_lines:?}"
    );
    (subprograms, variables, symbols)
}

fn relocation_rows(path: &Path) -> BTreeMap<String, Vec<String>> {
    let text = run_llvm("llvm-readelf", &["-r", "--wide"], path);
    let mut rows: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut section = String::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("Relocation section '") {
            section = rest.split('\'').next().unwrap_or("").to_string();
        } else if line.contains("R_AARCH64_") {
            let kind = line
                .split_whitespace()
                .find(|field| field.starts_with("R_AARCH64_"))
                .unwrap_or("")
                .to_string();
            rows.entry(section.clone()).or_default().push(kind);
        }
    }
    rows
}

// ---------------------------------------------------------------------------
// Raw ELF edits for the mutation controls
// ---------------------------------------------------------------------------

/// Turn every record of a `.rela.*` section into `R_AARCH64_NONE`.
fn neutralize_relocations(object: &mut [u8], rela: &str) {
    let (offset, size) = elf_section_extent(object, rela).unwrap_or_else(|| panic!("no {rela}"));
    assert!(size > 0 && size % 24 == 0, "{rela} size {size}");
    for entry in (offset..offset + size).step_by(24) {
        object[entry + 8..entry + 12].copy_from_slice(&0u32.to_le_bytes());
    }
}

/// Point every `.rela.*` record whose symbol is `from` at symbol `to`
/// instead, keeping its offset, type and addend.
fn retarget_relocations(object: &mut [u8], rela: &str, from: u32, to: u32) -> usize {
    let (offset, size) = elf_section_extent(object, rela).unwrap_or_else(|| panic!("no {rela}"));
    let mut patched = 0;
    for entry in (offset..offset + size).step_by(24) {
        let sym_at = entry + 12;
        let sym = u32::from_le_bytes(object[sym_at..sym_at + 4].try_into().expect("r_sym"));
        if sym == from {
            object[sym_at..sym_at + 4].copy_from_slice(&to.to_le_bytes());
            patched += 1;
        }
    }
    patched
}

/// The `.symtab` index a `.rela.*` record at `r_offset` names.
fn relocation_symbol_at(object: &[u8], rela: &str, r_offset: u64) -> u32 {
    let (offset, size) = elf_section_extent(object, rela).unwrap_or_else(|| panic!("no {rela}"));
    (offset..offset + size)
        .step_by(24)
        .find(|entry| {
            u64::from_le_bytes(object[*entry..*entry + 8].try_into().expect("r_offset")) == r_offset
        })
        .map(|entry| u32::from_le_bytes(object[entry + 12..entry + 16].try_into().expect("r_sym")))
        .unwrap_or_else(|| panic!("{rela}: no record at {r_offset:#x}"))
}

// ---------------------------------------------------------------------------
// Relocation target identity
// ---------------------------------------------------------------------------
//
// In a relocatable object every section symbol has value 0, so a DWARF
// reader resolves `section + addend` to the addend whichever section the
// record names: a strp relocated against `.debug_abbrev` reads exactly like
// one relocated against `.debug_str`, and `llvm-dwarfdump` output is
// unchanged. Only a link, which places each section at its own output
// offset, would expose it. These checks therefore derive, independently of
// the emitter, which section each relocated field refers to (from the
// `.debug_abbrev` forms and the line program's opcodes) and require the
// record `llvm-readelf` reports at that offset to name that section.

const DW_AT_LOCATION: u64 = 0x02;
const DW_AT_STMT_LIST: u64 = 0x10;
const DW_FORM_ADDR: u64 = 0x01;
const DW_FORM_STRP: u64 = 0x0e;
const DW_FORM_SEC_OFFSET: u64 = 0x17;

/// `field offset -> (relocation type, target section symbol)`.
type FieldTargets = BTreeMap<u64, (&'static str, &'static str)>;

fn section_bytes<'a>(object: &'a [u8], name: &str) -> &'a [u8] {
    let (offset, size) = elf_section_extent(object, name).unwrap_or_else(|| panic!("no {name}"));
    &object[offset..offset + size]
}

fn read_uleb(bytes: &[u8], at: &mut usize) -> u64 {
    let mut value = 0u64;
    let mut shift = 0;
    loop {
        let byte = bytes[*at];
        *at += 1;
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return value;
        }
        shift += 7;
        assert!(shift < 64, "LEB128 overflow at {:#x}", *at);
    }
}

fn skip_leb(bytes: &[u8], at: &mut usize) {
    while bytes[*at] & 0x80 != 0 {
        *at += 1;
    }
    *at += 1;
}

fn le32(bytes: &[u8], at: usize) -> usize {
    u32::from_le_bytes(bytes[at..at + 4].try_into().expect("u32")) as usize
}

/// Walk the DWARF 4 (DWARF32, 8-byte address) units of `.debug_info` with
/// the `.debug_abbrev` table and name the relocation each relocated field
/// needs. Also returns the DIE count and the per-form attribute counts, so
/// the walk can be cross-checked against `llvm-dwarfdump`.
fn debug_info_field_targets(object: &[u8]) -> (FieldTargets, usize, BTreeMap<u64, usize>) {
    let abbrev = section_bytes(object, ".debug_abbrev");
    let info = section_bytes(object, ".debug_info");
    let mut table: BTreeMap<u64, Vec<(u64, u64)>> = BTreeMap::new();
    let mut at = 0;
    loop {
        let code = read_uleb(abbrev, &mut at);
        if code == 0 {
            break;
        }
        let _tag = read_uleb(abbrev, &mut at);
        at += 1; // DW_CHILDREN_*
        let mut specs = Vec::new();
        loop {
            let attr = read_uleb(abbrev, &mut at);
            let form = read_uleb(abbrev, &mut at);
            if attr == 0 && form == 0 {
                break;
            }
            specs.push((attr, form));
        }
        assert!(table.insert(code, specs).is_none(), "abbrev {code} twice");
    }

    let mut targets = FieldTargets::new();
    let mut dies = 0;
    let mut forms: BTreeMap<u64, usize> = BTreeMap::new();
    let mut unit = 0;
    while unit < info.len() {
        let end = unit + 4 + le32(info, unit);
        assert_eq!(
            u16::from_le_bytes([info[unit + 4], info[unit + 5]]),
            4,
            "DWARF 4 unit"
        );
        // The unit header's abbreviation offset (after unit_length, version).
        targets.insert(unit as u64 + 6, ("R_AARCH64_ABS32", ".debug_abbrev"));
        assert_eq!(info[unit + 10], 8, "8-byte addresses");
        let mut at = unit + 11;
        while at < end {
            let code = read_uleb(info, &mut at);
            if code == 0 {
                continue;
            }
            dies += 1;
            let specs = table
                .get(&code)
                .unwrap_or_else(|| panic!("DIE at {at:#x} uses undefined abbrev {code}"));
            for &(attr, form) in specs {
                *forms.entry(form).or_default() += 1;
                let field = at as u64;
                match form {
                    DW_FORM_ADDR => {
                        targets.insert(field, ("R_AARCH64_ABS64", ".text"));
                        at += 8;
                    }
                    DW_FORM_STRP => {
                        targets.insert(field, ("R_AARCH64_ABS32", ".debug_str"));
                        at += 4;
                    }
                    DW_FORM_SEC_OFFSET => {
                        let section = match attr {
                            DW_AT_STMT_LIST => ".debug_line",
                            DW_AT_LOCATION => ".debug_loc",
                            other => panic!("sec_offset attribute {other:#x} at {field:#x}"),
                        };
                        targets.insert(field, ("R_AARCH64_ABS32", section));
                        at += 4;
                    }
                    0x0b | 0x0c | 0x11 => at += 1, // data1, flag, ref1
                    0x05 | 0x12 => at += 2,        // data2, ref2
                    0x06 | 0x13 => at += 4,        // data4, ref4
                    0x07 | 0x14 => at += 8,        // data8, ref8
                    0x0d | 0x0f => skip_leb(info, &mut at), // sdata, udata
                    0x18 => {
                        // exprloc
                        let len = read_uleb(info, &mut at) as usize;
                        at += len;
                    }
                    0x0a => at += 1 + usize::from(info[at]), // block1
                    0x08 => {
                        // string
                        at += info[at..].iter().position(|b| *b == 0).expect("NUL") + 1;
                    }
                    0x19 => {} // flag_present
                    other => panic!("form {other:#x} at {field:#x} is outside the walker's set"),
                }
            }
        }
        assert_eq!(at, end, "the DIE walk must end exactly at its unit's end");
        unit = end;
    }
    (targets, dies, forms)
}

/// Offsets of every `DW_LNE_set_address` operand in the DWARF 4 line
/// programs of `.debug_line`, each a code address relocated against `.text`.
fn debug_line_field_targets(object: &[u8]) -> FieldTargets {
    let line = section_bytes(object, ".debug_line");
    let mut targets = FieldTargets::new();
    let mut unit = 0;
    while unit < line.len() {
        let end = unit + 4 + le32(line, unit);
        assert_eq!(
            u16::from_le_bytes([line[unit + 4], line[unit + 5]]),
            4,
            "DWARF 4 line program"
        );
        let program = unit + 10 + le32(line, unit + 6);
        // minimum_instruction_length, maximum_operations_per_instruction,
        // default_is_stmt, line_base, line_range, then opcode_base.
        let opcode_base = line[unit + 15];
        let lengths = &line[unit + 16..unit + 16 + usize::from(opcode_base) - 1];
        let mut at = program;
        while at < end {
            let opcode = line[at];
            at += 1;
            if opcode == 0 {
                let len = read_uleb(line, &mut at) as usize;
                if line[at] == 0x02 {
                    assert_eq!(len, 9, "DW_LNE_set_address with an 8-byte operand");
                    targets.insert(at as u64 + 1, ("R_AARCH64_ABS64", ".text"));
                }
                at += len;
            } else if opcode == 0x09 {
                at += 2; // DW_LNS_fixed_advance_pc: uhalf operand
            } else if opcode < opcode_base {
                for _ in 0..lengths[usize::from(opcode) - 1] {
                    skip_leb(line, &mut at);
                }
            }
        }
        assert_eq!(
            at, end,
            "the line program must end exactly at its unit's end"
        );
        unit = end;
    }
    targets
}

/// `offset -> (type, symbol name)` of every record in one relocation
/// section, as `llvm-readelf -r` reports them.
fn readelf_relocations(path: &Path, rela: &str) -> BTreeMap<u64, (String, String)> {
    let text = run_llvm("llvm-readelf", &["-r", "--wide"], path);
    let mut rows = BTreeMap::new();
    let mut section = String::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("Relocation section '") {
            section = rest.split('\'').next().unwrap_or("").to_string();
            continue;
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        if section != rela || fields.len() < 5 || !fields[2].starts_with("R_AARCH64_") {
            continue;
        }
        let offset = u64::from_str_radix(fields[0], 16).expect("relocation offset");
        let row = (fields[2].to_string(), fields[4].to_string());
        assert!(
            rows.insert(offset, row).is_none(),
            "{rela}: two records at {offset:#x}"
        );
    }
    rows
}

/// Require exactly one record per relocated field, of the field's type and
/// naming the section the field refers to, and no other record.
fn compare_field_targets(
    rela: &str,
    expected: &FieldTargets,
    actual: &BTreeMap<u64, (String, String)>,
) -> Result<(), String> {
    for (offset, (kind, section)) in expected {
        match actual.get(offset) {
            Some((got_kind, got_section)) if got_kind == kind && got_section == section => {}
            other => {
                return Err(format!(
                    "{rela} field at {offset:#x} needs {kind} against {section}, found {other:?}"
                ));
            }
        }
    }
    if let Some((offset, row)) = actual
        .iter()
        .find(|(offset, _)| !expected.contains_key(offset))
    {
        return Err(format!(
            "{rela} record at {offset:#x} {row:?} relocates no DWARF field"
        ));
    }
    Ok(())
}

/// The relocation-target check for one object. The independent walks are
/// first cross-checked against `llvm-dwarfdump`'s own DIE, form and opcode
/// counts, so a walker defect cannot vacuously pass.
fn check_relocation_targets(context: &str, path: &Path) -> Result<usize, String> {
    let object = fs::read(path).expect("read object");
    let (info_targets, dies, forms) = debug_info_field_targets(&object);
    let line_targets = debug_line_field_targets(&object);

    let verbose = run_llvm("llvm-dwarfdump", &["--debug-info", "-v"], path);
    let dumped_dies = verbose
        .lines()
        .filter(|line| line.starts_with("0x") && line.contains("DW_TAG_"))
        .count();
    assert_eq!(dies, dumped_dies, "{context}: DIE count vs llvm-dwarfdump");
    for (form, name) in [
        (DW_FORM_ADDR, "[DW_FORM_addr]"),
        (DW_FORM_STRP, "[DW_FORM_strp]"),
        (DW_FORM_SEC_OFFSET, "[DW_FORM_sec_offset]"),
    ] {
        assert_eq!(
            forms.get(&form).copied().unwrap_or(0),
            verbose.matches(name).count(),
            "{context}: {name} count vs llvm-dwarfdump"
        );
    }
    let line_dump = run_llvm("llvm-dwarfdump", &["--debug-line", "-v"], path);
    assert_eq!(
        line_targets.len(),
        line_dump.matches("DW_LNE_set_address").count(),
        "{context}: set_address count vs llvm-dwarfdump"
    );

    compare_field_targets(
        ".rela.debug_info",
        &info_targets,
        &readelf_relocations(path, ".rela.debug_info"),
    )
    .map_err(|e| format!("{context}: {e}"))?;
    compare_field_targets(
        ".rela.debug_line",
        &line_targets,
        &readelf_relocations(path, ".rela.debug_line"),
    )
    .map_err(|e| format!("{context}: {e}"))?;
    Ok(info_targets.len() + line_targets.len())
}

/// What the fixture subprogram `sub` must describe, whichever object path
/// emitted it and wherever it sits in `.text`: `located` is
/// [`check_locations`]'s view of its checked location lists.
fn assert_fixture_locations(
    context: &str,
    level: OptLevel,
    sub: &Subprogram,
    variables: &[DwarfVariable],
    located: &BTreeMap<String, Vec<LocationRange>>,
) {
    // The parameter starts in X0 at entry.
    let x = located
        .get("x")
        .unwrap_or_else(|| panic!("{context}: parameter `x` has no location list"));
    assert!(
        x.first()
            .is_some_and(|r| r.start == sub.low && register_location(&r.expr) == Some(0)),
        "{context}: `x` must begin in X0 at entry: {x:?}"
    );
    assert!(
        variables
            .iter()
            .any(|v| v.name == "x" && v.tag == "DW_TAG_formal_parameter"),
        "{context}: `x` must be a formal parameter"
    );
    // The stack-resident accumulator is described through the frame base.
    let acc = located
        .get("acc")
        .unwrap_or_else(|| panic!("{context}: `acc` has no location list"));
    assert!(
        !acc.is_empty() && acc.iter().all(|r| r.expr.starts_with("DW_OP_fbreg")),
        "{context}: `acc` must live in its frame slot: {acc:?}"
    );
    assert!(
        variables.iter().any(|v| v.name == "tail_const"
            && v.single
                .as_deref()
                .is_some_and(|s| s.contains("DW_OP_constu"))),
        "{context}: `tail_const` must be a constant location"
    );
    for name in ["acc", "spill_probe", "reg_probe", "tail_const"] {
        assert!(
            variables
                .iter()
                .any(|v| v.name == name && v.tag == "DW_TAG_variable"),
            "{context}: `{name}` has no DW_TAG_variable DIE"
        );
    }
    // At O0 the spill probe lives in a spill slot from its store onward,
    // so the spill-slot store/overwrite checks above are exercised.
    if level == OptLevel::O0 {
        let spill = located
            .get("spill_probe")
            .unwrap_or_else(|| panic!("{context}: spill_probe has no location list"));
        assert!(
            spill
                .iter()
                .any(|r| r.expr.starts_with("DW_OP_fbreg") && r.start > sub.low),
            "{context}: spill_probe must be spill-slot backed: {spill:?}"
        );
        assert!(
            located
                .get("reg_probe")
                .is_some_and(|r| r.iter().any(|r| register_location(&r.expr).is_some())),
            "{context}: reg_probe must be register backed"
        );
    }
}

/// The location checker must accept `variables` of `sub` and refuse each
/// mutation that re-creates a defect the emitter used to have (or could
/// regress to), against the real machine code `insns`.
fn assert_checker_refuses_mutations(
    context: &str,
    sub: &Subprogram,
    variables: &[DwarfVariable],
    insns: &[Insn],
) {
    check_locations(&format!("{context} unmutated"), sub, variables, insns);

    let mutate = |name: &str, edit: &dyn Fn(&mut LocationRange)| {
        let mut mutated = variables.to_vec();
        let var = mutated
            .iter_mut()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("{context}: no {name}"));
        edit(&mut var.ranges.as_mut().expect("ranged")[0]);
        mutated
    };
    let refused = |what: &str, mutated: Vec<DwarfVariable>| {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_locations(what, sub, &mutated, insns);
        }));
        assert!(result.is_err(), "{context}: the checker accepted: {what}");
    };
    // A register range that begins at its defining instruction.
    refused(
        "register range at its definition",
        mutate("reg_probe", &|r| r.start -= 4),
    );
    // A frame-base range that covers the prologue before X29 is set.
    refused(
        "frame base in the prologue",
        mutate("acc", &|r| r.start = sub.low),
    );
    // A spill range that no longer follows its store.
    refused(
        "spill range detached from its store",
        mutate("spill_probe", &|r| r.start += 4),
    );
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn single_function_elf_dwarf_verifies_and_matches_code_at_every_level() {
    let dir = scratch_dir("aarch64_elf_dwarf_single");
    for level in LEVELS {
        let context = format!("single-function {level:?}");
        let object = pipeline(level, true)
            .compile_function(&lir_fixture())
            .unwrap_or_else(|e| panic!("{context}: {e}"));
        assert_eq!(&object[..4], b"\x7fELF", "{context}: not ELF");
        let path = write_object(&dir, &format!("single_{level:?}.o"), &object);
        let (subprograms, variables, _) = check_object(&context, &path, &[FIXTURE]);
        let sub = subprograms
            .iter()
            .find(|s| s.name == FIXTURE)
            .expect("fixture subprogram");
        let insns = disassemble(&path);
        let located = check_locations(&context, sub, &variables, &insns);
        assert_fixture_locations(&context, level, sub, &variables, &located);

        let relocs = relocation_rows(&path);
        let info = relocs.get(".rela.debug_info").cloned().unwrap_or_default();
        assert!(
            info.iter().any(|k| k == "R_AARCH64_ABS32")
                && info.iter().any(|k| k == "R_AARCH64_ABS64"),
            "{context}: .rela.debug_info rows {info:?}"
        );
        let line = relocs.get(".rela.debug_line").cloned().unwrap_or_default();
        assert!(
            !line.is_empty() && line.iter().all(|k| k == "R_AARCH64_ABS64"),
            "{context}: .rela.debug_line rows {line:?}"
        );
        assert!(
            !relocs.contains_key(".rela.debug_loc"),
            "{context}: DWARF4 .debug_loc entries are CU-base relative and unrelocated"
        );
    }
    cleanup(&dir);
}

/// The location checker's teeth: each mutation re-creates a defect the
/// emitter used to have (or could regress to) and must be refused against
/// the real O0 machine code, for the single-function object and for the
/// fixture subprogram of a whole-module object at offset 0 and past the leaf.
#[test]
fn location_checker_refuses_ranges_the_machine_code_contradicts() {
    let dir = scratch_dir("aarch64_elf_dwarf_checker");
    let object = pipeline(OptLevel::O0, true)
        .compile_function(&lir_fixture())
        .expect("compile fixture");
    let path = write_object(&dir, "checker.o", &object);
    let (subprograms, variables) =
        read_debug_info(&run_llvm("llvm-dwarfdump", &["--debug-info"], &path));
    let sub = subprograms[0].clone();
    let insns = disassemble(&path);
    assert_checker_refuses_mutations("single-function", &sub, &variables, &insns);

    for order in MODULE_ORDERS {
        let context = format!("module {order:?}");
        let path = write_object(
            &dir,
            &format!("checker_{}.o", order.label()),
            &prepared_module_in_order(OptLevel::O0, order),
        );
        let (subprograms, variables) =
            read_debug_info(&run_llvm("llvm-dwarfdump", &["--debug-info"], &path));
        let sub = subprograms
            .iter()
            .find(|s| s.name == FIXTURE)
            .unwrap_or_else(|| panic!("{context}: no fixture subprogram"))
            .clone();
        assert_eq!(
            sub.low > 0,
            order == ModuleOrder::LeafFirst,
            "{context}: fixture placement {sub:?}"
        );
        let fixture_variables = variables_of(&variables, FIXTURE);
        assert_checker_refuses_mutations(&context, &sub, &fixture_variables, &disassemble(&path));
    }
    cleanup(&dir);
}

/// The two module layouts the tests emit: the fixture at text offset 0 with
/// the leaf past it, or the leaf first so every fixture location range must
/// be moved past the leaf.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ModuleOrder {
    FixtureFirst,
    LeafFirst,
}

impl ModuleOrder {
    fn label(self) -> &'static str {
        match self {
            Self::FixtureFirst => "fixture_first",
            Self::LeafFirst => "leaf_first",
        }
    }

    fn functions(self) -> [trust_cg_lower::Function; 2] {
        match self {
            Self::FixtureFirst => [lir_fixture(), lir_fixture_leaf()],
            Self::LeafFirst => [lir_fixture_leaf(), lir_fixture()],
        }
    }
}

const MODULE_ORDERS: [ModuleOrder; 2] = [ModuleOrder::FixtureFirst, ModuleOrder::LeafFirst];

/// Which module entry emits the object, and which register-debug provenance
/// it receives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ModuleProvenance {
    /// `compile_module_emission_with_debug_provenance`, each function with
    /// its own map from its `-g` preparation.
    Prepared,
    /// `compile_module_emission_with_debug_provenance`, no map for any
    /// function (parameters need none).
    Absent,
    /// The legacy `compile_module_emission` entry, which describes
    /// subprograms and line rows only (no parameter or variable DIE, no
    /// `.debug_loc`), as the `Compiler`/CLI `-g` path's
    /// `compile_module_emission_with_symbol_linkage` does.
    LinesOnly,
}

/// Prepare the fixture and the leaf with `-g` and emit them as one module
/// object through the entry `provenance` names.
fn prepared_module_with(
    level: OptLevel,
    order: ModuleOrder,
    provenance: ModuleProvenance,
) -> Vec<u8> {
    let pipeline = pipeline(level, true);
    let mut functions = Vec::new();
    let mut metrics = Vec::new();
    for lir in order.functions() {
        let (func, prepared) = pipeline
            .prepare_function_with_metrics(&lir, None)
            .unwrap_or_else(|e| panic!("{level:?}: prepare {}: {e}", lir.name));
        assert!(
            prepared.debug_provenance.is_some(),
            "{level:?}: a -g preparation of `{}` retains its register-debug provenance",
            lir.name
        );
        functions.push(func);
        metrics.push(prepared);
    }
    let layouts: Vec<_> = metrics.iter().map(|m| m.frame_layout.clone()).collect();
    if provenance == ModuleProvenance::LinesOnly {
        return pipeline
            .compile_module_emission(&functions, &[], &layouts, &[])
            .unwrap_or_else(|e| panic!("{level:?}: lines-only module emission: {e}"))
            .object;
    }
    let maps: Vec<_> = metrics
        .iter()
        .map(|m| match provenance {
            ModuleProvenance::Prepared => m.debug_provenance.as_ref(),
            ModuleProvenance::Absent | ModuleProvenance::LinesOnly => None,
        })
        .collect();
    pipeline
        .compile_module_emission_with_debug_provenance(
            &functions,
            &[],
            &layouts,
            &ModuleSymbolLinkage::default(),
            &maps,
        )
        .unwrap_or_else(|e| panic!("{level:?}: module emission: {e}"))
        .into_emission()
        .object
}

fn prepared_module_in_order(level: OptLevel, order: ModuleOrder) -> Vec<u8> {
    prepared_module_with(level, order, ModuleProvenance::Prepared)
}

fn prepared_module(level: OptLevel) -> Vec<u8> {
    prepared_module_in_order(level, ModuleOrder::FixtureFirst)
}

/// The fixture-first module object from the legacy lines-only entry: the
/// shape the base tests inspected before the provenance entry existed.
fn lines_only_module(level: OptLevel) -> Vec<u8> {
    prepared_module_with(
        level,
        ModuleOrder::FixtureFirst,
        ModuleProvenance::LinesOnly,
    )
}

/// A lines-only module object describes no parameter or variable: no
/// `DW_TAG_formal_parameter` or `DW_TAG_variable` DIE, and no `.debug_loc`.
fn assert_lines_only(context: &str, path: &Path, variables: &[DwarfVariable]) {
    let info = run_llvm("llvm-dwarfdump", &["--debug-info"], path);
    assert!(
        variables.is_empty()
            && !info.contains("DW_TAG_formal_parameter")
            && !info.contains("DW_TAG_variable"),
        "{context}: a lines-only module must describe no parameter or variable:\n{info}"
    );
    let sections = run_llvm("llvm-readelf", &["-S", "--wide"], path);
    assert!(
        !sections.contains(".debug_loc"),
        "{context}: a lines-only module has no location lists:\n{sections}"
    );
}

fn variables_of(variables: &[DwarfVariable], subprogram: &str) -> Vec<DwarfVariable> {
    variables
        .iter()
        .filter(|v| v.subprogram == subprogram)
        .cloned()
        .collect()
}

#[test]
fn module_elf_dwarf_verifies_with_unwind_tables_at_every_level() {
    let dir = scratch_dir("aarch64_elf_dwarf_module");
    for level in LEVELS {
        for order in MODULE_ORDERS {
            let context = format!("module {level:?} {order:?}");
            let object = prepared_module_in_order(level, order);
            let path = write_object(
                &dir,
                &format!("module_{level:?}_{}.o", order.label()),
                &object,
            );
            let (subprograms, variables, symbols) = check_object(&context, &path, &[FIXTURE, LEAF]);
            let second = match order {
                ModuleOrder::FixtureFirst => LEAF,
                ModuleOrder::LeafFirst => FIXTURE,
            };
            let second = subprograms
                .iter()
                .find(|s| s.name == second)
                .expect("second subprogram");
            assert!(
                second.low > 0,
                "{context}: the second function must sit past the first"
            );
            assert!(
                symbols
                    .iter()
                    .any(|s| s.name == second.name && s.value == second.low),
                "{context}: second low_pc {second:?} vs {symbols:?}"
            );
            // The unwind tables and the debug sections coexist in one object.
            let sections = run_llvm("llvm-readelf", &["-S", "--wide"], &path);
            for name in [
                ".eh_frame",
                ".debug_info",
                ".debug_line",
                ".debug_loc",
                ".rela.eh_frame",
            ] {
                assert!(
                    sections.contains(name),
                    "{context}: missing {name}:\n{sections}"
                );
            }

            // Every DIE belongs to one of the two subprograms, and each
            // subprogram's location lists hold against the machine code at
            // its own text offset.
            assert!(
                variables
                    .iter()
                    .all(|v| v.subprogram == FIXTURE || v.subprogram == LEAF),
                "{context}: a DIE outside both subprograms: {variables:?}"
            );
            let insns = disassemble(&path);
            let fixture = subprograms
                .iter()
                .find(|s| s.name == FIXTURE)
                .expect("fixture subprogram");
            let fixture_variables = variables_of(&variables, FIXTURE);
            let located = check_locations(&context, fixture, &fixture_variables, &insns);
            assert_fixture_locations(&context, level, fixture, &fixture_variables, &located);

            // The frameless leaf's two synthesized-name parameters are
            // described in X0 and X1 from its entry until their first
            // clobber. From O1 its first instruction (`madd x0, ...`)
            // overwrites X0, so `arg0` then has no location at all.
            let leaf = subprograms
                .iter()
                .find(|s| s.name == LEAF)
                .expect("leaf subprogram");
            let leaf_variables = variables_of(&variables, LEAF);
            let located = check_locations(&context, leaf, &leaf_variables, &insns);
            for (reg, name) in ["arg0", "arg1"].into_iter().enumerate() {
                assert!(
                    leaf_variables
                        .iter()
                        .any(|v| v.name == name && v.tag == "DW_TAG_formal_parameter"),
                    "{context}: leaf parameter `{name}` has no DIE"
                );
                let ranges = located
                    .get(name)
                    .unwrap_or_else(|| panic!("{context}: `{name}` has no location list"));
                let required = name == "arg1" || level == OptLevel::O0;
                assert!(
                    (!required && ranges.is_empty())
                        || ranges.first().is_some_and(|r| r.start == leaf.low
                            && register_location(&r.expr) == Some(reg as u64)),
                    "{context}: leaf `{name}` must begin in X{reg} at {:#x}: {ranges:?}",
                    leaf.low
                );
            }
            // A provenance-derived register local of the leaf, starting after
            // its defining instruction inside the leaf.
            assert!(
                leaf_variables.iter().any(|v| v.tag == "DW_TAG_variable"
                    && v.ranges.as_ref().is_some_and(|ranges| ranges
                        .iter()
                        .any(|r| r.start > leaf.low && register_location(&r.expr).is_some()))),
                "{context}: the leaf must carry a register-located local: {leaf_variables:?}"
            );

            // The same two functions through the legacy lines-only entry
            // (the product `-g` module path's description): verified by the
            // same readers, the second function's low_pc on its symbol past
            // the first, the unwind and line sections present, and no
            // parameter, variable or location list.
            let context = format!("lines-only module {level:?} {order:?}");
            let object = prepared_module_with(level, order, ModuleProvenance::LinesOnly);
            let path = write_object(
                &dir,
                &format!("lines_only_{level:?}_{}.o", order.label()),
                &object,
            );
            let (subprograms, variables, symbols) = check_object(&context, &path, &[FIXTURE, LEAF]);
            let second = match order {
                ModuleOrder::FixtureFirst => LEAF,
                ModuleOrder::LeafFirst => FIXTURE,
            };
            let second = subprograms
                .iter()
                .find(|s| s.name == second)
                .expect("second subprogram");
            assert!(
                second.low > 0,
                "{context}: the second function must sit past the first"
            );
            assert!(
                symbols
                    .iter()
                    .any(|s| s.name == second.name && s.value == second.low),
                "{context}: second low_pc {second:?} vs {symbols:?}"
            );
            let sections = run_llvm("llvm-readelf", &["-S", "--wide"], &path);
            for name in [".eh_frame", ".debug_info", ".debug_line", ".rela.eh_frame"] {
                assert!(
                    sections.contains(name),
                    "{context}: missing {name}:\n{sections}"
                );
            }
            assert_lines_only(&context, &path, &variables);
        }
    }
    cleanup(&dir);
}

/// A function with no register-debug provenance keeps single-function
/// parity: its parameters are still located (they need none) and each
/// provenance-backed local keeps its DIE with an empty location list, rather
/// than refusing the module.
#[test]
fn module_elf_dwarf_without_provenance_keeps_empty_local_locations() {
    let dir = scratch_dir("aarch64_elf_dwarf_module_absent");
    for level in LEVELS {
        let context = format!("module without provenance {level:?}");
        let object = prepared_module_with(level, ModuleOrder::LeafFirst, ModuleProvenance::Absent);
        let path = write_object(&dir, &format!("absent_{level:?}.o"), &object);
        let (subprograms, variables, _) = check_object(&context, &path, &[FIXTURE, LEAF]);
        let fixture = subprograms
            .iter()
            .find(|s| s.name == FIXTURE)
            .expect("fixture subprogram");
        let fixture_variables = variables_of(&variables, FIXTURE);
        let located = check_locations(&context, fixture, &fixture_variables, &disassemble(&path));
        assert!(
            located
                .get("x")
                .and_then(|r| r.first())
                .is_some_and(|r| r.start == fixture.low && register_location(&r.expr) == Some(0)),
            "{context}: `x` must begin in X0 at entry: {located:?}"
        );
        for name in ["spill_probe", "reg_probe"] {
            let var = fixture_variables
                .iter()
                .find(|v| v.name == name && v.tag == "DW_TAG_variable")
                .unwrap_or_else(|| panic!("{context}: `{name}` lost its DIE"));
            assert_eq!(
                var.ranges.as_deref().map(<[LocationRange]>::len),
                Some(0),
                "{context}: `{name}` has no provenance, so no location: {var:?}"
            );
        }
    }
    cleanup(&dir);
}

/// The `Compiler` path the CLI's `-g` drives (`CompilerConfig::emit_debug`)
/// produces verified DWARF in its Linux ELF object at every level.
#[test]
fn compiler_emit_debug_produces_verified_elf_dwarf_at_every_level() {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{Compiler, CompilerConfig};
    let dir = scratch_dir("aarch64_elf_dwarf_compiler");
    let (_, module) = elf_debug_fixture::fixture();
    for level in LEVELS {
        let context = format!("compiler {level:?}");
        let compiled = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                emit_debug: true,
                ..CompilerConfig::default()
            },
            TargetSpec::parse(TRIPLE).expect("Linux target"),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .unwrap_or_else(|e| panic!("{context}: {e}"));
        let path = write_object(
            &dir,
            &format!("compiler_{level:?}.o"),
            &compiled.object_code,
        );
        check_object(&context, &path, &[FIXTURE]);
        let sections = run_llvm("llvm-readelf", &["-S", "--wide"], &path);
        assert!(
            sections.contains(".eh_frame") && sections.contains(".rela.debug_info"),
            "{context}:\n{sections}"
        );
    }
    cleanup(&dir);
}

#[test]
fn neutralized_debug_relocations_lose_names_and_addresses() {
    let dir = scratch_dir("aarch64_elf_dwarf_mutation");
    // The provenance-bearing module object and the legacy lines-only one
    // (no `.debug_loc`) depend on their relocation records alike.
    for (label, object) in [
        ("module", prepared_module(OptLevel::O2)),
        ("lines_only", lines_only_module(OptLevel::O2)),
    ] {
        let good = write_object(&dir, &format!("{label}_good.o"), &object);
        let good_info = run_llvm("llvm-dwarfdump", &["--debug-info"], &good);
        let (good_subs, _) = read_debug_info(&good_info);
        assert!(
            good_subs.iter().any(|s| s.name == LEAF && s.low > 0),
            "{label}: the leaf must sit past the fixture:\n{good_info}"
        );

        // Without the .debug_info records every strp reads offset 0 (the
        // empty string) and every DW_FORM_addr reads 0: the in-place fields
        // carry no object-local fallback.
        let mut info_cut = object.clone();
        neutralize_relocations(&mut info_cut, ".rela.debug_info");
        let info_cut = write_object(&dir, &format!("{label}_info_cut.o"), &info_cut);
        let (_, cut_text) = try_run_llvm("llvm-dwarfdump", &["--debug-info"], &info_cut);
        let (cut_subs, _) = read_debug_info(&cut_text);
        assert!(
            !cut_subs.iter().any(|s| s.name == FIXTURE || s.name == LEAF),
            "{label}: names must come from R_AARCH64_ABS32 records:\n{cut_text}"
        );
        assert!(
            cut_subs.iter().all(|s| s.low == 0),
            "{label}: code addresses must come from R_AARCH64_ABS64 records:\n{cut_text}"
        );

        // Without the .debug_line records every sequence restarts at address
        // 0, so the leaf's rows no longer lie inside its subprogram.
        let mut line_cut = object.clone();
        neutralize_relocations(&mut line_cut, ".rela.debug_line");
        let line_cut = write_object(&dir, &format!("{label}_line_cut.o"), &line_cut);
        let (_, rows_text) = try_run_llvm("llvm-dwarfdump", &["--debug-line"], &line_cut);
        let rows = read_line_rows(&rows_text);
        assert!(
            !rows.iter().any(|row| !row.end_sequence
                && row.address >= good_subs.iter().find(|s| s.name == LEAF).unwrap().low),
            "{label}: leaf rows must depend on their set_address relocations:\n{rows_text}"
        );
    }
    cleanup(&dir);
}

/// Each relocated DWARF field names the section it refers to. The mutation
/// control retargets every `DW_FORM_strp` record at the `.debug_abbrev`
/// section symbol: `llvm-dwarfdump --verify` and `--debug-info` read that
/// object exactly like the good one (every section symbol is 0 before a
/// link), so only this field-by-field check refuses it.
#[test]
fn debug_relocations_name_the_section_each_field_refers_to() {
    let dir = scratch_dir("aarch64_elf_dwarf_reloc_targets");
    for level in LEVELS {
        let single = write_object(
            &dir,
            &format!("single_{level:?}.o"),
            &pipeline(level, true)
                .compile_function(&lir_fixture())
                .unwrap_or_else(|e| panic!("{level:?}: {e}")),
        );
        let module = write_object(
            &dir,
            &format!("module_{level:?}.o"),
            &prepared_module(level),
        );
        let lines_only = write_object(
            &dir,
            &format!("lines_only_{level:?}.o"),
            &lines_only_module(level),
        );
        for (context, path) in [
            ("single", &single),
            ("module", &module),
            ("lines-only module", &lines_only),
        ] {
            let context = format!("{context} {level:?}");
            let fields = check_relocation_targets(&context, path).unwrap_or_else(|e| panic!("{e}"));
            assert!(fields > 0, "{context}: no relocated fields");
        }
    }

    let good_path = dir.join("single_O0.o");
    let good = fs::read(&good_path).expect("read good object");
    let (targets, _, _) = debug_info_field_targets(&good);
    let first_strp = targets
        .iter()
        .find(|(_, (_, section))| *section == ".debug_str")
        .map(|(offset, _)| *offset)
        .expect("a strp field");
    let str_anchor = relocation_symbol_at(&good, ".rela.debug_info", first_strp);
    let abbrev_anchor = relocation_symbol_at(&good, ".rela.debug_info", 6);
    assert_ne!(str_anchor, abbrev_anchor);
    let mut bad = good.clone();
    assert!(retarget_relocations(&mut bad, ".rela.debug_info", str_anchor, abbrev_anchor) > 0);
    let bad_path = write_object(&dir, "strp_against_abbrev.o", &bad);

    // The existing reader checks cannot see the defect ...
    let body = |path: &Path| {
        run_llvm("llvm-dwarfdump", &["--debug-info"], path)
            .lines()
            .skip(1) // the file-name banner
            .collect::<Vec<_>>()
            .join("\n")
    };
    assert_eq!(body(&good_path), body(&bad_path));
    assert!(run_llvm("llvm-dwarfdump", &["--verify"], &bad_path).contains("No errors."));
    // ... the field-by-field target check does.
    let err = check_relocation_targets("strp against .debug_abbrev", &bad_path)
        .expect_err("a strp relocated against .debug_abbrev must be refused");
    assert!(
        err.contains(".debug_str") && err.contains(".debug_abbrev"),
        "{err}"
    );
    cleanup(&dir);
}

#[test]
fn elf_debug_objects_refuse_the_certified_relocation_inventory() {
    let pipeline = pipeline(OptLevel::O2, true);
    let (func, metrics) = pipeline
        .prepare_function_with_metrics(&lir_fixture_leaf(), None)
        .expect("prepare leaf");
    let err = pipeline
        .module_relocation_inventory_report_with_object_state(
            &[func],
            &[],
            &[metrics.frame_layout],
            "debug.o",
        )
        .expect_err("DWARF rows are not enumerated by the inventory");
    assert!(
        matches!(err, PipelineError::ObjectRelocationInventoryIncomplete { ref reason, .. }
            if reason.contains("R_AARCH64_ABS32")),
        "{err}"
    );
}

#[test]
fn debug_sections_are_absent_without_emit_debug() {
    let dir = scratch_dir("aarch64_elf_dwarf_off");
    let object = pipeline(OptLevel::O2, false)
        .compile_function(&lir_fixture())
        .expect("compile without -g");
    let path = write_object(&dir, "no_debug.o", &object);
    let sections = run_llvm("llvm-readelf", &["-S", "--wide"], &path);
    assert!(!sections.contains(".debug_"), "{sections}");
    cleanup(&dir);
}

/// Function sections put each body in its own `.text.<symbol>` section, but
/// the DWARF image describes every function against one `.text` base. `-g`
/// together with function sections is refused by name on the module and
/// single-function paths, and each option alone still emits: debug sections
/// with the single `.text`, or per-function text sections without DWARF.
#[test]
fn elf_debug_with_function_sections_is_refused() {
    let dir = scratch_dir("aarch64_elf_dwarf_function_sections");
    for level in LEVELS {
        let context = format!("function sections {level:?}");
        let prepare = |pipeline: &Pipeline| {
            let mut functions = Vec::new();
            let mut metrics = Vec::new();
            for lir in [lir_fixture(), lir_fixture_leaf()] {
                let (func, prepared) = pipeline
                    .prepare_function_with_metrics(&lir, None)
                    .unwrap_or_else(|e| panic!("{context}: prepare {}: {e}", lir.name));
                functions.push(func);
                metrics.push(prepared);
            }
            let layouts: Vec<_> = metrics.iter().map(|m| m.frame_layout.clone()).collect();
            (functions, layouts, metrics)
        };
        let refused = |err: &PipelineError| {
            matches!(err, PipelineError::TargetObjectUnsupported { format, reason, .. }
                if format == "ELF"
                    && reason.contains("function sections")
                    && reason.contains("fail-closed"))
        };

        let debug_sections = pipeline(level, true).with_function_sections(true);
        let (functions, layouts, metrics) = prepare(&debug_sections);
        let err = debug_sections
            .compile_module_emission(&functions, &[], &layouts, &[])
            .expect_err("-g with function sections must be refused on the module path");
        assert!(refused(&err), "{context}: module: {err}");
        let maps: Vec<_> = metrics
            .iter()
            .map(|m| m.debug_provenance.as_ref())
            .collect();
        assert!(maps.iter().all(Option::is_some), "{context}: -g provenance");
        let err = debug_sections
            .compile_module_emission_with_debug_provenance(
                &functions,
                &[],
                &layouts,
                &ModuleSymbolLinkage::default(),
                &maps,
            )
            .expect_err("-g with function sections must be refused with variables too");
        assert!(refused(&err), "{context}: module with variables: {err}");
        let err = debug_sections
            .compile_function(&lir_fixture())
            .expect_err("-g with function sections must be refused for one function");
        assert!(refused(&err), "{context}: single function: {err}");

        let sections_only = pipeline(level, false).with_function_sections(true);
        let (functions, layouts, metrics) = prepare(&sections_only);
        assert!(
            metrics.iter().all(|m| m.debug_provenance.is_none()),
            "{context}: without -g no provenance is retained"
        );
        let object = sections_only
            .compile_module_emission(&functions, &[], &layouts, &[])
            .unwrap_or_else(|e| panic!("{context}: function sections without -g: {e}"))
            .object;
        let path = write_object(&dir, &format!("sections_{level:?}.o"), &object);
        let listing = run_llvm("llvm-readelf", &["-S", "--wide"], &path);
        assert!(
            listing.contains(&format!(".text.{FIXTURE}")) && !listing.contains(".debug_"),
            "{context}: function sections without -g:\n{listing}"
        );
        // -g alone emits debug sections with the single `.text`, through the
        // provenance entry and the legacy lines-only entry.
        for (label, object) in [
            ("debug", prepared_module(level)),
            ("debug_lines_only", lines_only_module(level)),
        ] {
            let path = write_object(&dir, &format!("{label}_{level:?}.o"), &object);
            let listing = run_llvm("llvm-readelf", &["-S", "--wide"], &path);
            assert!(
                listing.contains(".debug_info") && !listing.contains(&format!(".text.{FIXTURE}")),
                "{context}: {label}: -g without function sections:\n{listing}"
            );
        }
    }
    cleanup(&dir);
}

/// `many_args(a0..a8)`: the ninth integer argument arrives on the stack, and
/// eight arguments live across a call so the frame saves callee-saved pairs
/// below the FP/LR record (callee-saved area larger than 16 bytes).
fn lir_many_args() -> trust_cg_lower::Function {
    use trust_ir::{
        BinOp, Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst,
        InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
    };
    let mut module = TrustIrModule::new("many_args");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64; 9],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let barrier_ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "many_args", ft, BlockId::new(0));
    let mut barrier =
        TrustIrFunction::new(FuncId::new(1), "spill_barrier", barrier_ft, BlockId::new(0));
    barrier.linkage = Linkage::External;
    let mut body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(9)),
    ];
    let mut acc = ValueId::new(9);
    for (next, arg) in (10u32..).zip(1u32..9) {
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: acc,
                rhs: ValueId::new(arg),
            })
            .with_result(ValueId::new(next)),
        );
        acc = ValueId::new(next);
    }
    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: (0..9).map(|i| (ValueId::new(i), Ty::I64)).collect(),
        body,
    }];
    module
        .try_add_function(func.clone())
        .expect("Module::try_add_function: test fixture");
    module
        .try_add_function(barrier)
        .expect("Module::try_add_function: test fixture");
    let names = module
        .functions
        .iter()
        .map(|f| (f.id, f.name.clone()))
        .collect();
    let (mut lir, _) = trust_cg_lower::translate_function_with_names_and_license(
        &func,
        &module,
        &names,
        &permit_unlicensed(),
    )
    .expect("translate many_args");
    lir.debug_meta.source_file = Some(FIXTURE_FILE.to_string());
    lir.debug_meta.param_names = (0..9).map(|i| format!("a{i}")).collect();
    lir
}

/// The CFA rule `llvm-dwarfdump --eh-frame` gives for the body of the only
/// FDE: `X29 + n` once the prologue has run.
fn body_cfa_from_x29(path: &Path) -> i64 {
    let dump = run_llvm("llvm-dwarfdump", &["--eh-frame"], path);
    let last_row = dump
        .lines()
        .rfind(|line| line.trim_start().starts_with("0x") && line.contains(": CFA="))
        .unwrap_or_else(|| panic!("no unwind rows:\n{dump}"));
    let cfa = last_row
        .split("CFA=")
        .nth(1)
        .and_then(|rest| rest.split(':').next())
        .expect("CFA rule");
    cfa.strip_prefix("W29+")
        .unwrap_or_else(|| panic!("body CFA is not X29-based: {last_row}"))
        .trim()
        .parse()
        .expect("CFA offset")
}

#[test]
fn stack_passed_argument_is_described_at_its_cfa_slot_at_every_level() {
    let dir = scratch_dir("aarch64_elf_dwarf_stack_arg");
    for level in LEVELS {
        let context = format!("stack argument {level:?}");
        let object = pipeline(level, true)
            .compile_function(&lir_many_args())
            .unwrap_or_else(|e| panic!("{context}: {e}"));
        let path = write_object(&dir, &format!("many_args_{level:?}.o"), &object);
        let verify = run_llvm("llvm-dwarfdump", &["--verify"], &path);
        assert!(verify.contains("No errors."), "{context}:\n{verify}");
        let (subprograms, variables) =
            read_debug_info(&run_llvm("llvm-dwarfdump", &["--debug-info"], &path));
        let sub = &subprograms[0];
        let insns = disassemble(&path);
        check_locations(&context, sub, &variables, &insns);

        // The frame saves more than the FP/LR pair, so a CSA-relative
        // description would differ from the correct CFA-relative one.
        let saves = insns
            .iter()
            .take_while(|insn| insn.mnemonic == "stp")
            .count();
        assert!(
            saves >= 2,
            "{context}: expected callee-saved pairs below FP/LR"
        );

        // AAPCS64 places the first stack argument at the CFA (the caller's
        // SP at the call). With CFA = X29 + k from the CFI, its frame-base
        // (X29) offset must be exactly k.
        let cfa = body_cfa_from_x29(&path);
        let a8 = variables
            .iter()
            .find(|v| v.name == "a8")
            .unwrap_or_else(|| panic!("{context}: no DIE for a8"));
        let ranges = a8.ranges.as_ref().expect("a8 location list");
        assert!(!ranges.is_empty(), "{context}: a8 has no location");
        for range in ranges {
            assert_eq!(
                range.expr,
                format!("DW_OP_fbreg +{cfa}"),
                "{context}: a8 must be at X29 + {cfa} (the CFA), got {range:?}"
            );
        }
    }
    cleanup(&dir);
}

/// lldb's own DWARF consumer, loading the relocatable ELF object without
/// running it: every body line resolves to a breakpoint inside the function,
/// in source order, and an address on a body line maps back to that line
/// with the fixture's variables in scope.
#[cfg(target_os = "macos")]
#[test]
fn lldb_resolves_elf_object_lines_and_variables_at_every_level() {
    use elf_debug_fixture::{BODY_LINES, FIRST_BODY_LINE};
    let lldb = ["/usr/bin/lldb", "/opt/homebrew/opt/llvm/bin/lldb"]
        .into_iter()
        .find(|path| Path::new(path).is_file())
        .expect("lldb is required on the macOS host for the ELF object debugger check");
    let dir = scratch_dir("aarch64_elf_dwarf_lldb");
    for level in LEVELS {
        let context = format!("lldb {level:?}");
        let object = pipeline(level, true)
            .compile_function(&lir_fixture())
            .unwrap_or_else(|e| panic!("{context}: {e}"));
        let path = write_object(&dir, &format!("lldb_{level:?}.o"), &object);
        let symbol = func_symbols(&path)
            .into_iter()
            .find(|s| s.name == FIXTURE)
            .expect("fixture symbol");
        let target = format!("target create --arch aarch64 {}", path.display());
        let mut command = std::process::Command::new(lldb);
        command.arg("--batch").arg("-o").arg(&target);
        for k in 0..BODY_LINES {
            command.arg("-o").arg(format!(
                "breakpoint set -f {FIXTURE_FILE} -l {}",
                FIRST_BODY_LINE + k
            ));
        }
        let output = command.output().expect("run lldb");
        let text = String::from_utf8_lossy(&output.stdout).into_owned()
            + &String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{context}: lldb failed:\n{text}");
        let mut addresses = Vec::new();
        for k in 0..BODY_LINES {
            let line = FIRST_BODY_LINE + k;
            let needle = format!("at {FIXTURE_FILE}:{line}:");
            let row = text
                .lines()
                .find(|row| row.starts_with("Breakpoint ") && row.contains(&needle))
                .unwrap_or_else(|| panic!("{context}: line {line} did not resolve:\n{text}"));
            let address = row
                .split("address = 0x")
                .nth(1)
                .and_then(|hex| u64::from_str_radix(hex.trim(), 16).ok())
                .unwrap_or_else(|| panic!("{context}: no address in {row}"));
            assert!(
                (symbol.value..symbol.value + symbol.size).contains(&address),
                "{context}: line {line} at {address:#x} escapes {symbol:?}"
            );
            addresses.push(address);
        }
        assert!(
            addresses.windows(2).all(|pair| pair[0] < pair[1]),
            "{context}: body lines must resolve in source order: {addresses:x?}"
        );

        let probe = addresses[2];
        let lookup = std::process::Command::new(lldb)
            .arg("--batch")
            .arg("-o")
            .arg(&target)
            .arg("-o")
            .arg(format!("image lookup -v -a {probe:#x}"))
            .output()
            .expect("run lldb lookup");
        let lookup = String::from_utf8_lossy(&lookup.stdout).into_owned();
        assert!(
            lookup.contains(&format!("{FIXTURE_FILE}:{}:", FIRST_BODY_LINE + 2)),
            "{context}: {probe:#x} must map to line {}:\n{lookup}",
            FIRST_BODY_LINE + 2
        );
        // lldb lists only variables whose location covers the address; `x`
        // leaves X0 at the barrier call, before the body lines.
        for name in ["\"acc\"", "\"tail_const\""] {
            assert!(
                lookup.contains(&format!("name = {name}")),
                "{context}: {name} missing at {probe:#x}:\n{lookup}"
            );
        }
        assert!(
            lookup.contains("DW_OP_fbreg"),
            "{context}: acc must be frame-based:\n{lookup}"
        );
    }
    cleanup(&dir);
}

/// Mach-O text address of `_name`, read by `llvm-objdump --syms`.
fn macho_symbol_address(context: &str, path: &Path, name: &str) -> u64 {
    let table = run_llvm("llvm-objdump", &["--syms"], path);
    let suffix = format!(" _{name}");
    table
        .lines()
        .find(|row| row.ends_with(&suffix) && row.contains("__TEXT,__text"))
        .and_then(|row| row.split_whitespace().next())
        .and_then(|address| u64::from_str_radix(address, 16).ok())
        .unwrap_or_else(|| panic!("{context}: no __text symbol _{name}:\n{table}"))
}

/// The module entry that describes parameters and variables shares its
/// description with the Mach-O writer. Host-neutral structural control: the
/// same two functions emitted as an `aarch64-apple-darwin` module object in
/// both orders at O0-O3 pass `llvm-dwarfdump --verify`, each subprogram sits
/// at its independently read symbol address, and every location range of
/// both subprograms holds against the `llvm-objdump` disassembly. No
/// debugger reads these objects here; the Darwin debugger legs are separate.
#[test]
fn module_macho_dwarf_locations_hold_against_the_disassembly_at_every_level() {
    let dir = scratch_dir("aarch64_elf_dwarf_macho_module");
    for level in LEVELS {
        for order in MODULE_ORDERS {
            let context = format!("Mach-O module {level:?} {order:?}");
            let pipeline = Pipeline::new(PipelineConfig {
                opt_level: level,
                emit_debug: true,
                verify_dispatch: DispatchVerifyMode::Off,
                ..PipelineConfig::for_target("aarch64-apple-darwin")
            });
            let mut functions = Vec::new();
            let mut metrics = Vec::new();
            for lir in order.functions() {
                let (func, prepared) = pipeline
                    .prepare_function_with_metrics(&lir, None)
                    .unwrap_or_else(|e| panic!("{context}: prepare {}: {e}", lir.name));
                functions.push(func);
                metrics.push(prepared);
            }
            let layouts: Vec<_> = metrics.iter().map(|m| m.frame_layout.clone()).collect();
            let maps: Vec<_> = metrics
                .iter()
                .map(|m| m.debug_provenance.as_ref())
                .collect();
            assert!(maps.iter().all(Option::is_some), "{context}: -g provenance");
            let object = pipeline
                .compile_module_emission_with_debug_provenance(
                    &functions,
                    &[],
                    &layouts,
                    &ModuleSymbolLinkage::default(),
                    &maps,
                )
                .unwrap_or_else(|e| panic!("{context}: module emission: {e}"))
                .into_emission()
                .object;
            let path = write_object(
                &dir,
                &format!("macho_module_{level:?}_{}.o", order.label()),
                &object,
            );
            let verify = run_llvm("llvm-dwarfdump", &["--verify"], &path);
            assert!(
                verify.contains("No errors."),
                "{context}: llvm-dwarfdump --verify:\n{verify}"
            );
            let info = run_llvm("llvm-dwarfdump", &["--debug-info"], &path);
            assert!(
                !info.contains("[stderr]"),
                "{context}: llvm-dwarfdump reported warnings:\n{info}"
            );
            let sections = run_llvm("llvm-objdump", &["--section-headers"], &path);
            assert!(
                sections.contains("__debug_loc"),
                "{context}: no __debug_loc:\n{sections}"
            );
            let (subprograms, variables) = read_debug_info(&info);
            let insns = disassemble(&path);
            for name in [FIXTURE, LEAF] {
                let sub = subprograms
                    .iter()
                    .find(|s| s.name == name)
                    .unwrap_or_else(|| panic!("{context}: no subprogram `{name}`:\n{info}"));
                assert_eq!(
                    sub.low,
                    macho_symbol_address(&context, &path, name),
                    "{context}: `{name}` low_pc vs its symbol"
                );
                let own = variables_of(&variables, name);
                let located = check_locations(&context, sub, &own, &insns);
                assert!(
                    own.iter().any(|v| v.tag == "DW_TAG_formal_parameter"),
                    "{context}: `{name}` has no formal parameter: {own:?}"
                );
                if name == FIXTURE {
                    assert_fixture_locations(&context, level, sub, &own, &located);
                }
            }
            let second = match order {
                ModuleOrder::FixtureFirst => LEAF,
                ModuleOrder::LeafFirst => FIXTURE,
            };
            assert!(
                subprograms.iter().any(|s| s.name == second && s.low > 0),
                "{context}: `{second}` must sit past the first function: {subprograms:?}"
            );
        }
    }
    cleanup(&dir);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
