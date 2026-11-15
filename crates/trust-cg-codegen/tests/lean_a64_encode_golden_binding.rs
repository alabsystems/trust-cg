// trust-cg-codegen/tests/lean_a64_encode_golden_binding.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
//! X-LEAN-P3 — golden binding of the Lean A64 instruction-word model to the
//! production AArch64 emitter and to the ENC-5 decode-check.
//!
//! `formal/lean/Trust/A64/EncoderGolden.lean` is GENERATED from
//! `Trust.A64.corpus` and holds one row per line:
//! `⟨shape, operands, instruction, word⟩`. Lean's kernel checks that the rows
//! are exactly the corpus, that every word is the model's `encode` of the
//! instruction, that the model's `decode` maps the word back, and that the
//! instruction is valid (`lake build`). This test parses those rows and checks
//! the Rust side of the same anchor:
//!
//! * the production `encode_instruction` emits exactly the row's word for the
//!   row's `AArch64Opcode` and `MachOperand`s;
//! * where `aarch64::encoding` / `encoding_mem` have a field-level helper for
//!   the instruction class, that helper given the Lean instruction's fields
//!   emits the same word;
//! * the ENC-5 decode-check (`A64DecodeCheck`) accepts the word as the
//!   operands' intent, and refuses every single-bit corruption of it;
//! * the rows, their count, every instruction class and every bound shape are
//!   present (a row dropped on either side is a failure, not a smaller pass).
//!
//! Corruption controls run the same binding on mutated golden text and require
//! a named refusal. Evidence strength: an enumerated golden corpus checked by
//! testing on the Rust side and by kernel evaluation on the Lean side. It is
//! NOT a proof that the Rust emitter refines the Lean model for inputs outside
//! the corpus.

use std::collections::BTreeMap;
use std::path::PathBuf;

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::aarch64::{encoding, encoding_mem};
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand as Arg, PReg};

/// Rows `Trust.A64.corpus` renders; also pinned by the Lean theorem
/// `goldenRows_length` in the golden module.
const EXPECTED_ROWS: usize = 831;

/// Every `Trust.A64.Instr` constructor.
const INSTR_CLASSES: [&str; 27] = [
    "pcRel",
    "addSubImm",
    "logicalImm",
    "moveWide",
    "bitfield",
    "extract",
    "branchImm",
    "compareBranch",
    "testBranch",
    "condBranch",
    "branchReg",
    "brk",
    "nop",
    "barrier",
    "loadLiteral",
    "loadStorePair",
    "loadStoreImm9",
    "loadStoreRegOff",
    "loadStoreUImm",
    "logicalShifted",
    "addSubShifted",
    "addSubExt",
    "addSubCarry",
    "condSelect",
    "dataProc2",
    "dataProc1",
    "dataProc3",
];

/// The emitter opcodes the corpus binds (`Trust.A64.Shape`). A row's shape is
/// looked up by the opcode's `Debug` name, so the Lean and Rust spellings
/// cannot silently diverge.
const SHAPES: &[Op] = &[
    Op::AddRR,
    Op::AddRI,
    Op::AddRIShift12,
    Op::SubRR,
    Op::SubRI,
    Op::AddsRR,
    Op::AddsRI,
    Op::SubsRR,
    Op::SubsRI,
    Op::AddRRShift,
    Op::SubRRShift,
    Op::AddRRShiftLsr,
    Op::Neg,
    Op::CmpRR,
    Op::CmpRI,
    Op::CMPWrr,
    Op::CMPXrr,
    Op::CMPWri,
    Op::CMPXri,
    Op::MulRR,
    Op::Madd,
    Op::Msub,
    Op::Smull,
    Op::Umull,
    Op::Smulh,
    Op::Umulh,
    Op::SDiv,
    Op::UDiv,
    Op::Adc,
    Op::Sbc,
    Op::Adcs,
    Op::Sbcs,
    Op::AndRR,
    Op::OrrRR,
    Op::EorRR,
    Op::BicRR,
    Op::OrnRR,
    Op::EorRRShift,
    Op::EorRRLsl,
    Op::EorRRLsr,
    Op::AndRI,
    Op::OrrRI,
    Op::EorRI,
    Op::Tst,
    Op::LslRR,
    Op::LsrRR,
    Op::AsrRR,
    Op::LslRI,
    Op::LsrRI,
    Op::AsrRI,
    Op::RorRI,
    Op::Rbit,
    Op::MovR,
    Op::MOVWrr,
    Op::MOVXrr,
    Op::MovI,
    Op::Movz,
    Op::MOVZWi,
    Op::MOVZXi,
    Op::Movn,
    Op::Movk,
    Op::Csel,
    Op::Csinc,
    Op::Csinv,
    Op::Csneg,
    Op::CSet,
    Op::Ubfm,
    Op::Sbfm,
    Op::Bfm,
    Op::Sxtw,
    Op::Uxtw,
    Op::Sxtb,
    Op::Sxth,
    Op::Uxtb,
    Op::Uxth,
    Op::B,
    Op::Bl,
    Op::BL,
    Op::BCond,
    Op::Bcc,
    Op::Cbz,
    Op::Cbnz,
    Op::Tbz,
    Op::Tbnz,
    Op::Br,
    Op::Blr,
    Op::BLR,
    Op::Ret,
    Op::LdrRI,
    Op::StrRI,
    Op::LdrbRI,
    Op::LdrhRI,
    Op::LdrsbRI,
    Op::LdrshRI,
    Op::StrbRI,
    Op::StrhRI,
    Op::STRWui,
    Op::STRXui,
    Op::LdrPreIndex,
    Op::StrPreIndex,
    Op::LdrPostIndex,
    Op::StrPostIndex,
    Op::LdrLiteral,
    Op::LdpRI,
    Op::StpRI,
    Op::StpPreIndex,
    Op::LdpPostIndex,
    Op::LdrRO,
    Op::StrRO,
    Op::LdrbRO,
    Op::LdrhRO,
    Op::StrbRO,
    Op::StrhRO,
    Op::LdrswRO,
    Op::Adr,
    Op::Adrp,
    Op::Brk,
    Op::Dmb,
    Op::Dsb,
    Op::Isb,
    Op::Nop,
    Op::AlignNop,
    Op::VolatileLdrRI,
    Op::VolatileStrRI,
    Op::VolatileLdrbRI,
    Op::VolatileLdrhRI,
    Op::VolatileStrbRI,
    Op::VolatileStrhRI,
    Op::TailCall,
    Op::AddPCRel,
    Op::STRSui,
    Op::STRDui,
    Op::Crc32B,
    Op::Crc32H,
    Op::Crc32W,
    Op::Crc32X,
    Op::Crc32Cb,
    Op::Crc32Ch,
    Op::Crc32Cw,
    Op::Crc32Cx,
];

fn repo_path(relative: &str) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop(); // crates
    path.pop(); // repository root
    path.push(relative);
    path
}

fn golden_text() -> String {
    let path = repo_path("formal/lean/Trust/A64/EncoderGolden.lean");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()))
}

/// A `Trust.A64.Opnd`.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Operand {
    X(u16),
    W(u16),
    Sp,
    Wsp,
    Xzr,
    Wzr,
    Imm(i64),
    Mem(u16, i64),
    /// Scalar SIMD&FP `S n` / `D n`.
    S(u16),
    D(u16),
}

/// One parsed golden row.
#[derive(Debug, Clone)]
struct Row {
    line: usize,
    shape: String,
    operands: Vec<Operand>,
    class: String,
    fields: Vec<u32>,
    word: u32,
}

/// Split at top-level commas (outside brackets and parentheses).
fn split_top_level(text: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut current = String::new();
    for ch in text.chars() {
        match ch {
            '[' | '(' => {
                depth += 1;
                current.push(ch);
            }
            ']' | ')' => {
                depth -= 1;
                current.push(ch);
            }
            ',' if depth == 0 => parts.push(std::mem::take(&mut current)),
            _ => current.push(ch),
        }
    }
    if !current.trim().is_empty() {
        parts.push(current);
    }
    parts
        .into_iter()
        .map(|part| part.trim().to_string())
        .collect()
}

fn parse_int(token: &str) -> Result<i64, String> {
    let token = token.trim();
    let inner = token
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
        .unwrap_or(token);
    inner
        .trim()
        .parse::<i64>()
        .map_err(|error| format!("bad integer `{token}`: {error}"))
}

fn parse_operand(text: &str) -> Result<Operand, String> {
    let text = text.trim();
    let (head, rest) = text.split_once(' ').unwrap_or((text, ""));
    let register = |rest: &str| -> Result<u16, String> {
        let n: u16 = rest
            .trim()
            .parse()
            .map_err(|error| format!("bad register number in `{text}`: {error}"))?;
        if n > 30 {
            return Err(format!("register number out of range in `{text}`"));
        }
        Ok(n)
    };
    let fp_register = |rest: &str| -> Result<u16, String> {
        let n: u16 = rest
            .trim()
            .parse()
            .map_err(|error| format!("bad register number in `{text}`: {error}"))?;
        if n > 31 {
            return Err(format!("register number out of range in `{text}`"));
        }
        Ok(n)
    };
    Ok(match head {
        ".x" => Operand::X(register(rest)?),
        ".w" => Operand::W(register(rest)?),
        ".s" => Operand::S(fp_register(rest)?),
        ".d" => Operand::D(fp_register(rest)?),
        ".sp" if rest.is_empty() => Operand::Sp,
        ".wsp" if rest.is_empty() => Operand::Wsp,
        ".xzr" if rest.is_empty() => Operand::Xzr,
        ".wzr" if rest.is_empty() => Operand::Wzr,
        ".imm" => Operand::Imm(parse_int(rest)?),
        ".mem" => {
            let (base, offset) = rest
                .trim()
                .split_once(' ')
                .ok_or_else(|| format!("malformed memory operand `{text}`"))?;
            let base: u16 = base
                .parse()
                .map_err(|error| format!("bad memory base in `{text}`: {error}"))?;
            if base > 31 {
                return Err(format!("memory base out of range in `{text}`"));
            }
            Operand::Mem(base, parse_int(offset)?)
        }
        _ => return Err(format!("unknown operand `{text}`")),
    })
}

fn parse_row(line: usize, text: &str) -> Result<Row, String> {
    let body = text
        .trim()
        .strip_prefix('⟨')
        .and_then(|rest| rest.strip_suffix(',').unwrap_or(rest).strip_suffix('⟩'))
        .ok_or_else(|| format!("line {line}: not a `⟨...⟩` row"))?;
    let parts = split_top_level(body);
    let [shape, operands, instr, word] = parts.as_slice() else {
        return Err(format!(
            "line {line}: expected 4 row fields, found {}",
            parts.len()
        ));
    };
    let shape = shape
        .strip_prefix('.')
        .ok_or_else(|| format!("line {line}: shape `{shape}` is not `.Name`"))?
        .to_string();
    let operands = operands
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
        .ok_or_else(|| format!("line {line}: operands `{operands}` are not a list"))?;
    let operands = split_top_level(operands)
        .iter()
        .map(|operand| parse_operand(operand).map_err(|error| format!("line {line}: {error}")))
        .collect::<Result<Vec<_>, _>>()?;
    let mut tokens = instr.split_whitespace();
    let class = tokens
        .next()
        .and_then(|class| class.strip_prefix('.'))
        .ok_or_else(|| format!("line {line}: instruction `{instr}` is not `.class fields`"))?
        .to_string();
    let fields = tokens
        .map(|field| {
            field
                .parse::<u32>()
                .map_err(|error| format!("line {line}: bad field `{field}`: {error}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let word = word
        .strip_prefix("0x")
        .ok_or_else(|| format!("line {line}: word `{word}` is not hexadecimal"))?;
    let word = u32::from_str_radix(word, 16)
        .map_err(|error| format!("line {line}: bad word `{word}`: {error}"))?;
    Ok(Row {
        line,
        shape,
        operands,
        class,
        fields,
        word,
    })
}

/// Parse the generated rows and the row count the Lean module states.
fn parse_golden(text: &str) -> Result<(Vec<Row>, usize), Vec<String>> {
    let mut errors = Vec::new();
    let mut rows = Vec::new();
    let mut inside = false;
    let mut stated = None;
    for (index, raw) in text.lines().enumerate() {
        let line = index + 1;
        let trimmed = raw.trim();
        if trimmed.starts_with("def goldenRows : List GoldenRow := [") {
            inside = true;
            continue;
        }
        if inside {
            if trimmed == "]" {
                inside = false;
                continue;
            }
            match parse_row(line, trimmed) {
                Ok(row) => rows.push(row),
                Err(error) => errors.push(error),
            }
        } else if let Some(rest) =
            trimmed.strip_prefix("theorem goldenRows_length : goldenRows.length = ")
        {
            let count = rest.split_whitespace().next().unwrap_or_default();
            match count.parse::<usize>() {
                Ok(count) => stated = Some(count),
                Err(error) => errors.push(format!("line {line}: bad stated count: {error}")),
            }
        }
    }
    match stated {
        None => errors.push("missing `goldenRows_length` theorem".into()),
        Some(count) if count != rows.len() => errors.push(format!(
            "the module states {count} rows but {} parse",
            rows.len()
        )),
        Some(_) => {}
    }
    if rows.is_empty() {
        errors.push("no golden rows parsed".into());
    }
    if errors.is_empty() {
        Ok((rows, stated.unwrap_or_default()))
    } else {
        Err(errors)
    }
}

fn opcode_of(shape: &str) -> Option<Op> {
    SHAPES
        .iter()
        .copied()
        .find(|opcode| format!("{opcode:?}") == shape)
}

/// The `MachOperand` a golden operand spells (see `Trust.A64.Corpus`).
fn machine_operand(operand: &Operand) -> Arg {
    match operand {
        Operand::X(n) => Arg::PReg(PReg::new(*n)),
        Operand::W(n) => Arg::PReg(PReg::new(32 + *n)),
        Operand::Sp => Arg::PReg(PReg::new(31)),
        Operand::Wsp => Arg::PReg(PReg::new(63)),
        Operand::Xzr => Arg::PReg(PReg::new(160)),
        Operand::Wzr => Arg::PReg(PReg::new(161)),
        Operand::Imm(value) => Arg::Imm(*value),
        Operand::Mem(base, offset) => Arg::MemOp {
            base: PReg::new(*base),
            offset: *offset,
        },
        Operand::S(n) => Arg::PReg(PReg::new(128 + *n)),
        Operand::D(n) => Arg::PReg(PReg::new(96 + *n)),
    }
}

fn machine_inst(row: &Row) -> Result<MachInst, String> {
    let opcode = opcode_of(&row.shape).ok_or_else(|| {
        format!(
            "line {}: shape `{}` has no AArch64Opcode binding",
            row.line, row.shape
        )
    })?;
    Ok(MachInst::new(
        opcode,
        row.operands.iter().map(machine_operand).collect(),
    ))
}

/// Sign-extend the low `bits` of `value`.
fn signed(value: u32, bits: u32) -> i64 {
    let shift = 64 - bits;
    (i64::from(value) << shift) >> shift
}

/// The word the field-level `aarch64::encoding` / `encoding_mem` helper emits
/// for the Lean instruction's fields, when such a helper exists for the class.
fn helper_word(class: &str, f: &[u32]) -> Result<Option<u32>, String> {
    let need = |arity: usize| -> Result<(), String> {
        if f.len() == arity {
            Ok(())
        } else {
            Err(format!(
                "class `{class}` takes {arity} fields, found {}",
                f.len()
            ))
        }
    };
    let mem = |result: Result<u32, encoding_mem::EncodeError>| {
        result
            .map(Some)
            .map_err(|error| format!("helper refused: {error}"))
    };
    Ok(match class {
        "addSubShifted" => {
            need(8)?;
            Some(encoding::encode_add_sub_shifted_reg(
                f[0], f[1], f[2], f[3], f[4], f[5], f[6], f[7],
            ))
        }
        "logicalShifted" => {
            need(8)?;
            Some(encoding::encode_logical_shifted_reg(
                f[0], f[1], f[2], f[3], f[4], f[5], f[6], f[7],
            ))
        }
        "extract" => {
            need(6)?;
            Some(encoding::encode_extract(f[0], f[1], f[2], f[3], f[4], f[5]))
        }
        "dataProc1" if f.get(1) == Some(&0) => {
            need(4)?;
            Some(encoding::encode_bit_reverse(f[0], f[2], f[3]))
        }
        "addSubImm" => {
            need(7)?;
            Some(encoding::encode_add_sub_imm(
                f[0], f[1], f[2], f[3], f[4], f[5], f[6],
            ))
        }
        "moveWide" => {
            need(5)?;
            Some(encoding::encode_move_wide(f[0], f[1], f[2], f[3], f[4]))
        }
        "condBranch" => {
            need(2)?;
            Some(encoding::encode_cond_branch(f[0], f[1]))
        }
        "branchImm" => {
            need(2)?;
            Some(encoding::encode_uncond_branch(f[0], f[1]))
        }
        "branchReg" => {
            need(2)?;
            Some(encoding::encode_branch_reg(f[0], f[1]))
        }
        "compareBranch" => {
            need(4)?;
            Some(encoding::encode_cmp_branch(f[0], f[1], f[2], f[3]))
        }
        "loadStoreUImm" => {
            need(6)?;
            Some(encoding::encode_load_store_ui(
                f[0], f[1], f[2], f[3], f[4], f[5],
            ))
        }
        "loadStoreImm9" if f.get(4) == Some(&0) => {
            need(7)?;
            Some(encoding::encode_load_store_unscaled(
                f[0],
                f[1],
                f[2],
                signed(f[3], 9) as i32,
                f[5],
                f[6],
            ))
        }
        "loadStorePair" if f.get(2) == Some(&2) => {
            need(8)?;
            Some(encoding::encode_load_store_pair(
                f[0], f[1], f[3], f[4], f[5], f[6], f[7],
            ))
        }
        "loadStoreRegOff" => {
            need(8)?;
            let extend = match f[4] {
                0b010 => encoding_mem::RegExtend::Uxtw,
                0b011 => encoding_mem::RegExtend::Lsl,
                0b110 => encoding_mem::RegExtend::Sxtw,
                0b111 => encoding_mem::RegExtend::Sxtx,
                other => return Err(format!("register-offset option {other} has no helper")),
            };
            mem(encoding_mem::encode_ldr_str_register_fields(
                f[0],
                f[1] == 1,
                f[2],
                f[3] as u8,
                extend,
                f[5] == 1,
                f[6] as u8,
                f[7] as u8,
            ))?
        }
        "addSubExt" if f.len() == 8 && f == [1, 1, 1, f[3], 3, 0, 31, f[7]] => {
            Some(encoding::encode_subs_sp_extended(f[3], f[7]))
        }
        "pcRel" => {
            need(4)?;
            let imm21 = signed((f[2] << 2) | f[1], 21) as i32;
            if f[0] == 1 {
                mem(encoding_mem::encode_adrp(imm21, f[3] as u8))?
            } else {
                mem(encoding_mem::encode_adr(imm21, f[3] as u8))?
            }
        }
        _ => None,
    })
}

/// What the binding of a golden text established.
#[derive(Debug, Default)]
struct Binding {
    rows: usize,
    helper_bound: usize,
    enc5_match: usize,
    per_class: BTreeMap<String, usize>,
    per_shape: BTreeMap<String, usize>,
}

/// Bind every golden row to the emitter, the field-level helpers and ENC-5.
fn bind(text: &str) -> Result<Binding, Vec<String>> {
    let (rows, _) = parse_golden(text)?;
    let mut errors = Vec::new();
    let mut binding = Binding {
        rows: rows.len(),
        ..Binding::default()
    };
    for row in &rows {
        if !INSTR_CLASSES.contains(&row.class.as_str()) {
            errors.push(format!(
                "line {}: unknown instruction class `{}`",
                row.line, row.class
            ));
            continue;
        }
        *binding.per_class.entry(row.class.clone()).or_default() += 1;
        *binding.per_shape.entry(row.shape.clone()).or_default() += 1;
        let inst = match machine_inst(row) {
            Ok(inst) => inst,
            Err(error) => {
                errors.push(error);
                continue;
            }
        };
        match encode_instruction(&inst) {
            Ok(word) if word == row.word => {}
            Ok(word) => errors.push(format!(
                "line {}: ENCODER DRIFT {:?}: emitter {word:#010x}, Lean golden {:#010x}",
                row.line, inst, row.word
            )),
            Err(error) => errors.push(format!(
                "line {}: emitter refuses {:?} (Lean golden {:#010x}): {error}",
                row.line, inst, row.word
            )),
        }
        match helper_word(&row.class, &row.fields) {
            Ok(Some(word)) if word == row.word => binding.helper_bound += 1,
            Ok(Some(word)) => errors.push(format!(
                "line {}: field-level helper for `{}` {:?} emits {word:#010x}, Lean golden {:#010x}",
                row.line, row.class, row.fields, row.word
            )),
            Ok(None) => {}
            Err(error) => errors.push(format!("line {}: {error}", row.line)),
        }
        match A64DecodeCheck.check_one(&inst, &row.word.to_le_bytes(), None) {
            DecodeCheckOutcome::Match => binding.enc5_match += 1,
            other => errors.push(format!(
                "line {}: ENC-5 does not accept {:?} = {:#010x}: {other:?}",
                row.line, inst, row.word
            )),
        }
    }
    if errors.is_empty() {
        Ok(binding)
    } else {
        Err(errors)
    }
}

fn expect_bound(text: &str) -> Binding {
    match bind(text) {
        Ok(binding) => binding,
        Err(errors) => panic!(
            "{} golden binding failures:\n{}",
            errors.len(),
            errors.join("\n")
        ),
    }
}

#[test]
fn lean_a64_golden_rows_bind_to_the_emitter_helpers_and_enc5() {
    let binding = expect_bound(&golden_text());
    assert_eq!(binding.rows, EXPECTED_ROWS, "golden row count drifted");
    assert_eq!(binding.enc5_match, binding.rows);
    for class in INSTR_CLASSES {
        assert!(
            binding.per_class.contains_key(class),
            "instruction class `{class}` has no golden row"
        );
    }
    for opcode in SHAPES {
        let name = format!("{opcode:?}");
        assert!(
            binding.per_shape.contains_key(&name),
            "bound shape `{name}` has no golden row"
        );
    }
    eprintln!(
        "LEAN_A64_GOLDEN rows={} helper_bound={} enc5_match={} classes={} shapes={}",
        binding.rows,
        binding.helper_bound,
        binding.enc5_match,
        binding.per_class.len(),
        binding.per_shape.len()
    );
}

#[test]
fn enc5_refuses_every_single_bit_corruption_of_a_golden_word() {
    let (rows, _) = parse_golden(&golden_text()).unwrap_or_else(|errors| panic!("{errors:?}"));
    let mut accepted = Vec::new();
    let mut checked = 0usize;
    for row in &rows {
        let inst = machine_inst(row).unwrap_or_else(|error| panic!("{error}"));
        for bit in 0..32 {
            let corrupted = row.word ^ (1u32 << bit);
            checked += 1;
            if matches!(
                A64DecodeCheck.check_one(&inst, &corrupted.to_le_bytes(), None),
                DecodeCheckOutcome::Match
            ) {
                accepted.push(format!(
                    "line {} {:?}: bit {bit} -> {corrupted:#010x}",
                    row.line, inst
                ));
            }
        }
    }
    assert_eq!(checked, EXPECTED_ROWS * 32);
    assert!(
        accepted.is_empty(),
        "ENC-5 accepted {} corrupted words:\n{}",
        accepted.len(),
        accepted.join("\n")
    );
}

/// Replace the `n`-th golden row line (0-based) with `f(line)`.
fn mutate_row(text: &str, n: usize, f: impl Fn(&str) -> Option<String>) -> String {
    let mut seen = 0usize;
    let mut inside = false;
    let mut out = Vec::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("def goldenRows : List GoldenRow := [") {
            inside = true;
            out.push(line.to_string());
            continue;
        }
        if inside && trimmed == "]" {
            inside = false;
        }
        if inside {
            if seen == n {
                seen += 1;
                if let Some(replacement) = f(line) {
                    out.push(replacement);
                }
                continue;
            }
            seen += 1;
        }
        out.push(line.to_string());
    }
    out.join("\n")
}

#[test]
fn binding_refuses_corrupted_golden_text() {
    let text = golden_text();
    let (rows, _) = parse_golden(&text).unwrap_or_else(|errors| panic!("{errors:?}"));
    let first = &rows[0];
    let word = format!("{:#010X}", first.word).replacen("0X", "0x", 1);
    let flipped = format!("{:#010X}", first.word ^ 1).replacen("0X", "0x", 1);

    let refusal = |mutated: &str, needle: &str, what: &str| match bind(mutated) {
        Ok(_) => panic!("control `{what}` was accepted"),
        Err(errors) => assert!(
            errors.iter().any(|error| error.contains(needle)),
            "control `{what}` refused without `{needle}`: {errors:?}"
        ),
    };

    // A changed word: the emitter (and the field helper) disagree with it.
    refusal(
        &mutate_row(&text, 0, |line| Some(line.replacen(&word, &flipped, 1))),
        "ENCODER DRIFT",
        "changed word",
    );
    // A dropped row: the stated Lean row count no longer matches.
    refusal(&mutate_row(&text, 5, |_| None), "rows but", "dropped row");
    // An unknown emitter shape.
    refusal(
        &mutate_row(&text, 0, |line| {
            Some(line.replacen(".AddRR,", ".AddRRR,", 1))
        }),
        "no AArch64Opcode binding",
        "unknown shape",
    );
    // A changed operand with the instruction and word left alone.
    refusal(
        &mutate_row(&text, 0, |line| Some(line.replacen("[.x 0,", "[.x 3,", 1))),
        "ENCODER DRIFT",
        "changed operand",
    );
    // A changed instruction field with the word left alone: the field helper
    // disagrees (the Lean kernel refuses the same edit in `lake build`).
    refusal(
        &mutate_row(&text, 0, |line| {
            Some(line.replacen(
                ".addSubShifted 1 0 0 0 2 0 1 0",
                ".addSubShifted 1 0 0 0 2 0 1 1",
                1,
            ))
        }),
        "field-level helper",
        "changed instruction field",
    );
    // A malformed operand and an unknown instruction class.
    refusal(
        &mutate_row(&text, 0, |line| Some(line.replacen(".x 1", ".q 1", 1))),
        "unknown operand",
        "malformed operand",
    );
    refusal(
        &mutate_row(&text, 0, |line| {
            Some(line.replacen(".addSubShifted", ".addSubShiftedX", 1))
        }),
        "unknown instruction class",
        "unknown class",
    );
    // An ENC-5 intent mismatch: a word the emitter would not produce for the
    // operands, consistent with itself, is refused by the emitter AND ENC-5.
    let corrupted = mutate_row(&text, 0, |line| {
        Some(line.replacen("[.x 0, .x 1, .x 2]", "[.x 0, .x 1, .x 4]", 1))
    });
    match bind(&corrupted) {
        Ok(_) => panic!("control `intent mismatch` was accepted"),
        Err(errors) => assert!(
            errors
                .iter()
                .any(|error| error.contains("ENC-5 does not accept")),
            "ENC-5 did not refuse the intent mismatch: {errors:?}"
        ),
    }
}

#[test]
fn golden_module_is_built_by_the_lean_package() {
    let root = std::fs::read_to_string(repo_path("formal/lean/Trust.lean"))
        .expect("read formal/lean/Trust.lean");
    for module in [
        "Trust.A64.Encoding",
        "Trust.A64.Bitmask",
        "Trust.A64.Corpus",
        "Trust.A64.EncoderGolden",
    ] {
        assert!(
            root.lines()
                .any(|line| line.trim() == format!("import {module}")),
            "formal/lean/Trust.lean must import {module} so `lake build` checks it"
        );
    }
    let text = golden_text();
    for theorem in [
        "theorem goldenRows_are_corpus : goldenRows.map GoldenRow.golden = corpus := by decide +kernel",
        "theorem goldenRows_sound : goldenRows.all GoldenRow.sound = true := by decide +kernel",
    ] {
        assert!(
            text.lines().any(|line| line.trim() == theorem),
            "golden module lost `{theorem}`"
        );
    }
}
