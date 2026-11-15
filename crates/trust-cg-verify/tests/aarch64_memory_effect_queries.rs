// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The word-bound memory-effect decomposition (`aarch64_memory_effect`,
//! ledger L07-P2 / X-OPCODES-P1 / L04-P7) over the memory words the Darwin
//! proof-wall corpus actually emits, and the size of the queries it sends
//! against the ones it replaces.
//!
//! * `CORPUS_WORDS` are the distinct admitted memory words of the census
//!   corpus (the 18 beat-llvm programs and scale_gate's small, medium and
//!   large crates compiled for `aarch64-apple-darwin` with certificates off,
//!   read back with `objdump -d`; report
//!   `reports/2026-09-29-darwin-memory-effect-certificates/`). Each
//!   disassembly line is parsed back to the machine instruction the backend
//!   selects for it, which must re-derive exactly the corpus word, and every
//!   part of its decomposition must hold.
//! * The query census compares, per corpus word, the lane query of the
//!   obligation the walk used before (the pair obligation's McCarthy
//!   expansion, the scalar instruction-word locations) with the raw query of
//!   each part, and the registered `LDP_QF_ABV` pair theorems with both.
//! * With `MEMORY_EFFECT_SMT2_DIR` set, every query (old, new, and the parts
//!   of corrupted words that must refute) is written there with a
//!   `manifest.tsv`, as the exact bytes for the AY/Clean matrix
//!   (`reports/2026-09-29-darwin-memory-effect-certificates/commands/`).
//!
//! Testing evidence about the decomposition and a measurement of query
//! shape; nothing here runs a solver or credits a row.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;

use sha2::{Digest, Sha256};
use trust_cg_ir::regs::{PReg, SpecialReg};
use trust_cg_ir::{AArch64Opcode as O, MachInst, MachOperand};
use trust_cg_verify::aarch64_instruction_word_proofs::instruction_word_verdict;
use trust_cg_verify::aarch64_memory_effect::{
    InProcess, MemoryEffectDecomposition, decide_in_process, memory_effect, memory_effect_for_word,
    memory_effect_word,
};
use trust_cg_verify::aarch64_pair_memory_proofs::pair_memory_obligation;
use trust_cg_verify::ay_bridge::{AYConfig, generate_smt2_query_raw, lane_smt2_query};
use trust_cg_verify::lowering_proof::VerificationConfig;

/// The distinct admitted memory words of the census corpus, with objdump's
/// disassembly. Not listed: `ldrsw` (no scalar form theorem), and the
/// register-offset forms, FP/SIMD scalar `ldr q`/`str q` and the scalar
/// post-index `ldr x3, [x6], #0x8`, which this decomposition did not admit
/// when the corpus was captured (it admits them since L04-P1; their parts are
/// checked by `aarch64_memory_effect`'s unit tests and the scalar silicon
/// differential, not by this capture).
const CORPUS_WORDS: &[(u32, &str)] = &[
    (0xa9bf7bfd, "stp x29, x30, [sp, #-0x10]!"),
    (0xa8c17bfd, "ldp x29, x30, [sp], #0x10"),
    (0xf9000020, "str x0, [x1]"),
    (0xf9400001, "ldr x1, [x0]"),
    (0xa9be4ff4, "stp x20, x19, [sp, #-0x20]!"),
    (0xa9017bfd, "stp x29, x30, [sp, #0x10]"),
    (0xa9417bfd, "ldp x29, x30, [sp, #0x10]"),
    (0xa8c24ff4, "ldp x20, x19, [sp], #0x20"),
    (0xf9000041, "str x1, [x2]"),
    (0xf9400040, "ldr x0, [x2]"),
    (0xf9400020, "ldr x0, [x1]"),
    (0xf9400021, "ldr x1, [x1]"),
    (0xac810000, "stp q0, q0, [x0], #0x20"),
    (0xf90003ff, "str xzr, [sp]"),
    (0xacc10400, "ldp q0, q1, [x0], #0x20"),
    (0xacc10c02, "ldp q2, q3, [x0], #0x20"),
    (0xa9ba6ffc, "stp x28, x27, [sp, #-0x60]!"),
    (0xa90167fa, "stp x26, x25, [sp, #0x10]"),
    (0xa9025ff8, "stp x24, x23, [sp, #0x20]"),
    (0xa90357f6, "stp x22, x21, [sp, #0x30]"),
    (0xa9044ff4, "stp x20, x19, [sp, #0x40]"),
    (0xa9057bfd, "stp x29, x30, [sp, #0x50]"),
    (0xf9402ff0, "ldr x16, [sp, #0x58]"),
    (0xf9000ff0, "str x16, [sp, #0x18]"),
    (0xf90013f0, "str x16, [sp, #0x20]"),
    (0x39000013, "strb w19, [x0]"),
    (0xa9bd57f6, "stp x22, x21, [sp, #-0x30]!"),
    (0xa9014ff4, "stp x20, x19, [sp, #0x10]"),
    (0xa9027bfd, "stp x29, x30, [sp, #0x20]"),
    (0xb94047f0, "ldr w16, [sp, #0x44]"),
    (0xf9401ff0, "ldr x16, [sp, #0x38]"),
    (0x39000004, "strb w4, [x0]"),
    (0xa9bc5ff8, "stp x24, x23, [sp, #-0x40]!"),
    (0xa90157f6, "stp x22, x21, [sp, #0x10]"),
    (0xa9024ff4, "stp x20, x19, [sp, #0x20]"),
    (0xa9037bfd, "stp x29, x30, [sp, #0x30]"),
    (0xa9004ec0, "stp x0, x19, [x22]"),
    (0xa9004ee0, "stp x0, x19, [x23]"),
    (0xb90047f0, "str w16, [sp, #0x44]"),
    (0xf90027f0, "str x16, [sp, #0x48]"),
    (0xf9002bf0, "str x16, [sp, #0x50]"),
    (0xf94027f0, "ldr x16, [sp, #0x48]"),
    (0xf9402bf0, "ldr x16, [sp, #0x50]"),
    (0xf94037f0, "ldr x16, [sp, #0x68]"),
    (0xacc10801, "ldp q1, q2, [x0], #0x20"),
    (0xacc11003, "ldp q3, q4, [x0], #0x20"),
    (0xac810020, "stp q0, q0, [x1], #0x20"),
    (0xf9000adb, "str x27, [x22, #0x10]"),
    (0xa940d6c2, "ldp x2, x21, [x22, #0x8]"),
    (0xf94002c4, "ldr x4, [x22]"),
    (0xf94002c0, "ldr x0, [x22]"),
    (0xf9000ad4, "str x20, [x22, #0x10]"),
    (0xf9400ac5, "ldr x5, [x22, #0x10]"),
    (0xf94002c7, "ldr x7, [x22]"),
    (0xf9000afc, "str x28, [x23, #0x10]"),
    (0xf90002d8, "str x24, [x22]"),
    (0xa940d6e2, "ldp x2, x21, [x23, #0x8]"),
    (0xf94002e4, "ldr x4, [x23]"),
    (0xf94002e0, "ldr x0, [x23]"),
    (0xf9000af4, "str x20, [x23, #0x10]"),
    (0xf9400ae4, "ldr x4, [x23, #0x10]"),
    (0xf94002e5, "ldr x5, [x23]"),
    (0xb817c3b0, "stur w16, [x29, #-0x84]"),
    (0xf81803b0, "stur x16, [x29, #-0x80]"),
    (0xf9002ff0, "str x16, [sp, #0x58]"),
    (0xf90033f0, "str x16, [sp, #0x60]"),
    (0xf90017f0, "str x16, [sp, #0x28]"),
    (0xb90007f0, "str w16, [sp, #0x4]"),
    (0xf9001ff1, "str x17, [sp, #0x38]"),
    (0xf90007f0, "str x16, [sp, #0x8]"),
    (0xf9000bf0, "str x16, [sp, #0x10]"),
    (0xb90037f1, "str w17, [sp, #0x34]"),
    (0xf90037f1, "str x17, [sp, #0x68]"),
    (0xa94026e7, "ldp x7, x9, [x23]"),
    (0xa9412eea, "ldp x10, x11, [x23, #0x10]"),
    (0xa94236ec, "ldp x12, x13, [x23, #0x20]"),
    (0xa9433eee, "ldp x14, x15, [x23, #0x30]"),
    (0xa94452f3, "ldp x19, x20, [x23, #0x40]"),
    (0xa9455af5, "ldp x21, x22, [x23, #0x50]"),
    (0xa9450880, "ldp x0, x2, [x4, #0x50]"),
    (0xa9440880, "ldp x0, x2, [x4, #0x40]"),
    (0xa9430880, "ldp x0, x2, [x4, #0x30]"),
    (0xa9420880, "ldp x0, x2, [x4, #0x20]"),
    (0xa9410880, "ldp x0, x2, [x4, #0x10]"),
    (0xa8cc0880, "ldp x0, x2, [x4], #0xc0"),
    (0xa90026e7, "stp x7, x9, [x23]"),
    (0xa9012eea, "stp x10, x11, [x23, #0x10]"),
    (0xa90236ec, "stp x12, x13, [x23, #0x20]"),
    (0xa9033eee, "stp x14, x15, [x23, #0x30]"),
    (0xa90452f3, "stp x19, x20, [x23, #0x40]"),
    (0xa9055af5, "stp x21, x22, [x23, #0x50]"),
    (0xf90037f0, "str x16, [sp, #0x68]"),
    (0xb94037f0, "ldr w16, [sp, #0x34]"),
    (0xf9400ff0, "ldr x16, [sp, #0x18]"),
    (0xf94013f0, "ldr x16, [sp, #0x20]"),
    (0xf9001ff0, "str x16, [sp, #0x38]"),
    (0xb9000ff0, "str w16, [sp, #0xc]"),
    (0x39000033, "strb w19, [x1]"),
    (0xacc11404, "ldp q4, q5, [x0], #0x20"),
    (0xacc11c06, "ldp q6, q7, [x0], #0x20"),
    (0xac810400, "stp q0, q1, [x0], #0x20"),
    (0xac810c02, "stp q2, q3, [x0], #0x20"),
    (0x39000002, "strb w2, [x0]"),
    (0x39000020, "strb w0, [x1]"),
    (0x39000040, "strb w0, [x2]"),
];

fn register(text: &str) -> Option<MachOperand> {
    let text = text.trim();
    match text {
        "sp" => return Some(MachOperand::Special(SpecialReg::SP)),
        "xzr" => return Some(MachOperand::Special(SpecialReg::XZR)),
        "wzr" => return Some(MachOperand::Special(SpecialReg::WZR)),
        _ => {}
    }
    let (bank, number) = text.split_at(1);
    let number: u16 = number.parse().ok()?;
    let base = match bank {
        "x" if number <= 30 => 0,
        "w" if number <= 30 => 32,
        "q" if number <= 31 => 64,
        _ => return None,
    };
    Some(MachOperand::PReg(PReg::new(base + number)))
}

fn immediate(text: &str) -> Option<i64> {
    let text = text.trim().strip_prefix('#')?;
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

/// The machine instruction the backend selects for one disassembly line of
/// an admitted form, or `None` for any other form.
fn parse(line: &str) -> Option<MachInst> {
    let (mnemonic, rest) = line.split_once(' ')?;
    let (registers, rest) = rest.split_once('[')?;
    let (address, tail) = rest.split_once(']')?;
    let transfers: Vec<MachOperand> = registers
        .split(',')
        .map(str::trim)
        .filter(|text| !text.is_empty())
        .map(register)
        .collect::<Option<_>>()?;
    let mut address = address.split(',');
    let base = register(address.next()?)?;
    let offset = match address.next() {
        Some(text) => immediate(text)?,
        None => 0,
    };
    if address.next().is_some() {
        return None;
    }
    let tail = tail.trim();
    let (pre, post) = if tail == "!" {
        (true, None)
    } else if let Some(text) = tail.strip_prefix(',') {
        (false, Some(immediate(text)?))
    } else if tail.is_empty() {
        (false, None)
    } else {
        return None;
    };
    let q = transfers
        .first()
        .is_some_and(|op| matches!(op, MachOperand::PReg(p) if (64..96).contains(&p.encoding())));
    let (opcode, offset) = match (mnemonic, pre, post, q) {
        ("stp", true, None, _) => (O::StpPreIndex, offset),
        ("stp", false, None, _) => (O::StpRI, offset),
        ("stp", false, Some(step), true) => (O::NeonStpQPost, step),
        ("ldp", false, None, _) => (O::LdpRI, offset),
        ("ldp", false, Some(step), true) => (O::NeonLdpQPost, step),
        ("ldp", false, Some(step), false) => (O::LdpPostIndex, step),
        ("ldr" | "ldur", false, None, false) => (O::LdrRI, offset),
        ("str" | "stur", false, None, false) => (O::StrRI, offset),
        ("ldrb", false, None, false) => (O::LdrbRI, offset),
        ("strb", false, None, false) => (O::StrbRI, offset),
        ("ldrh", false, None, false) => (O::LdrhRI, offset),
        ("strh", false, None, false) => (O::StrhRI, offset),
        _ => return None,
    };
    let mut operands = transfers;
    operands.push(base);
    if offset != 0 {
        operands.push(MachOperand::Imm(offset));
    }
    Some(MachInst::new(opcode, operands))
}

fn control_config() -> VerificationConfig {
    VerificationConfig::with_sample_count(2048)
}

/// The query the live lane sends for a part: the raw query under the
/// source-bound replay budget (`verdict_db::live_source_bound_config`).
fn live_config() -> AYConfig {
    AYConfig {
        solver: None,
        timeout_ms: 30_000,
        produce_models: true,
    }
}

fn corpus() -> Vec<(u32, &'static str, MachInst, MemoryEffectDecomposition)> {
    CORPUS_WORDS
        .iter()
        .map(|&(word, line)| {
            let inst = parse(line).unwrap_or_else(|| panic!("unparsed corpus line `{line}`"));
            assert_eq!(
                memory_effect_word(&inst),
                Some(word),
                "`{line}` does not re-derive the corpus word {word:#010x}: {inst:?}"
            );
            let decomposition = memory_effect(&inst).expect("admitted");
            (word, line, inst, decomposition)
        })
        .collect()
}

#[test]
fn every_corpus_word_rederives_and_every_part_holds() {
    let rows = corpus();
    assert_eq!(rows.len(), CORPUS_WORDS.len());
    let mut by_opcode: BTreeMap<String, usize> = BTreeMap::new();
    let mut parts = 0;
    for (_, line, inst, decomposition) in &rows {
        *by_opcode.entry(format!("{:?}", inst.opcode)).or_default() += 1;
        for part in &decomposition.parts {
            parts += 1;
            match decide_in_process(part, &control_config()) {
                InProcess::Holds(_) => {}
                other => panic!("`{line}` {}: {other:?}", part.obligation.name),
            }
        }
    }
    let expected: BTreeMap<String, usize> = [
        ("LdpPostIndex", 3),
        ("LdpRI", 14),
        ("LdrRI", 21),
        ("NeonLdpQPost", 6),
        ("NeonStpQPost", 4),
        ("StpPreIndex", 5),
        ("StpRI", 19),
        ("StrRI", 27),
        ("StrbRI", 6),
    ]
    .into_iter()
    .map(|(name, count)| (name.to_string(), count))
    .collect();
    assert_eq!(by_opcode, expected);
    assert!(parts > 400, "{parts} parts");
}

/// One query's operator census.
#[derive(Default, Debug, Clone)]
struct Census {
    bytes: usize,
    bvadd: usize,
    ite: usize,
    equalities: usize,
    arrays: usize,
    shifts: usize,
    multiplications: usize,
    concat: usize,
    extract: usize,
    extend: usize,
    widest_input: u32,
}

fn census(query: &str) -> Census {
    let count = |needle: &str| query.matches(needle).count();
    Census {
        bytes: query.len(),
        bvadd: count("(bvadd "),
        ite: count("(ite "),
        equalities: count("(= "),
        arrays: count("(select ") + count("(store ") + count("(as const"),
        shifts: count("(bvshl ") + count("(bvlshr ") + count("(bvashr "),
        multiplications: count("(bvmul "),
        concat: count("(concat "),
        extract: count("(_ extract "),
        extend: count("(_ zero_extend ") + count("(_ sign_extend "),
        widest_input: query
            .lines()
            .filter_map(|line| line.strip_prefix("(declare-const "))
            .filter_map(|line| {
                line.split("(_ BitVec ")
                    .nth(1)?
                    .trim_end_matches(')')
                    .parse()
                    .ok()
            })
            .max()
            .unwrap_or(0),
    }
}

/// `(label, query)` of the obligation(s) the walk used for this word before
/// the decomposition: the pair obligation, or each instruction-word location.
fn old_queries(inst: &MachInst) -> Vec<(String, String)> {
    let lane = AYConfig::default();
    if let Some(obligation) = pair_memory_obligation(inst) {
        return vec![("pair".into(), lane_smt2_query(&obligation, &lane))];
    }
    instruction_word_verdict(inst, &VerificationConfig::default())
        .map(|verdict| {
            verdict
                .locations
                .iter()
                .map(|(location, obligation)| {
                    (format!("{location:?}"), lane_smt2_query(obligation, &lane))
                })
                .collect()
        })
        .unwrap_or_default()
}

fn sha(text: &str) -> String {
    Sha256::digest(text.as_bytes())
        .iter()
        .take(8)
        .fold(String::new(), |mut out, byte| {
            let _ = write!(out, "{byte:02x}");
            out
        })
}

/// Mutations every word class has: `(label, word -> corrupted word)`, applied
/// only where the field exists (pairs: Rt2 and mode; scalar: size and opc).
fn corruptions(inst: &MachInst, word: u32) -> Vec<(&'static str, u32)> {
    let pair = matches!(
        inst.opcode,
        O::StpRI | O::LdpRI | O::StpPreIndex | O::LdpPostIndex | O::NeonStpQPost | O::NeonLdpQPost
    );
    let mut out = vec![("imm-low-bit", word ^ (1 << if pair { 15 } else { 10 }))];
    if pair {
        let rt = word & 31;
        let rt2 = (word >> 10) & 31;
        if rt != rt2 {
            out.push((
                "swapped-lanes",
                (word & !(31 | (31 << 10))) | rt2 | (rt << 10),
            ));
        }
        out.push(("mode-offset", (word & !(0b11 << 23)) | (0b10 << 23)));
        out.push(("width", word ^ (1 << 31)));
    } else {
        out.push(("width", word ^ (1 << 30)));
        out.push(("extension", word ^ (1 << 23)));
    }
    // A mutation that leaves the word unchanged (an offset-form word's
    // "mode-offset") is not a corruption.
    out.retain(|(_, corrupted)| *corrupted != word);
    out
}

#[test]
fn query_census_old_obligations_against_parts() {
    let rows = corpus();
    let dump = std::env::var_os("MEMORY_EFFECT_SMT2_DIR").map(PathBuf::from);
    let mut manifest = String::from(
        "group\tfile\tword\tinstruction\tpart\tbytes\tsha256_16\tbvadd\tite\teq\tarray\tshift\tmul\tconcat\textract\textend\twidest\n",
    );
    let mut write = |group: &str, index: usize, word: u32, line: &str, part: &str, query: &str| {
        let c = census(query);
        let file = format!(
            "{group}/{index:03}-{word:08x}-{}.smt2",
            part.replace([' ', ':', '(', ')'], "_")
        );
        let _ = writeln!(
            manifest,
            "{group}\t{file}\t{word:#010x}\t{line}\t{part}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            c.bytes,
            sha(query),
            c.bvadd,
            c.ite,
            c.equalities,
            c.arrays,
            c.shifts,
            c.multiplications,
            c.concat,
            c.extract,
            c.extend,
            c.widest_input
        );
        if let Some(dir) = &dump {
            let path = dir.join(&file);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, query).unwrap();
        }
        c
    };
    let (mut old_max, mut new_max) = (Census::default(), Census::default());
    let (mut old_total, mut new_total) = (0usize, 0usize);
    let mut old_shifts = 0;
    for (index, (word, line, inst, decomposition)) in rows.iter().enumerate() {
        for (label, query) in old_queries(inst) {
            let c = write("old", index, *word, line, &label, &query);
            old_total += c.bytes;
            old_shifts += c.shifts;
            if c.bytes > old_max.bytes {
                old_max = c;
            }
        }
        for part in &decomposition.parts {
            let query = generate_smt2_query_raw(&part.obligation, &live_config());
            let c = write("new", index, *word, line, &part.part.to_string(), &query);
            assert_eq!(
                (c.arrays, c.shifts, c.multiplications),
                (0, 0, 0),
                "`{line}` {}: {query}",
                part.part
            );
            assert!(c.widest_input <= 64, "`{line}` {}", part.part);
            new_total += c.bytes;
            if c.bytes > new_max.bytes {
                new_max = c;
            }
        }
        for (label, corrupted) in corruptions(inst, *word) {
            let Some(bad) = memory_effect_for_word(inst, corrupted) else {
                continue;
            };
            for part in &bad.parts {
                let refuted = matches!(
                    decide_in_process(part, &control_config()),
                    InProcess::Refuted(_)
                );
                if refuted {
                    let query = generate_smt2_query_raw(&part.obligation, &live_config());
                    write(
                        "control",
                        index,
                        corrupted,
                        line,
                        &format!("{label} {}", part.part),
                        &query,
                    );
                }
            }
            assert!(
                bad.parts.iter().any(|part| matches!(
                    decide_in_process(part, &control_config()),
                    InProcess::Refuted(_)
                )),
                "`{line}` {label} {corrupted:#010x} refutes no part"
            );
        }
    }
    // The registered pair theorems (the representative `LDP_QF_ABV` family
    // the ledger's certificate history refers to): their lane query and the
    // array-lowered query the lane tries first.
    for (index, theorem) in trust_cg_verify::memory_proofs::all_ldp_proofs()
        .iter()
        .enumerate()
    {
        let query = lane_smt2_query(theorem, &AYConfig::default());
        write("registry", index, 0, &theorem.name, "exact", &query);
        for (sub, (lowered, _)) in
            trust_cg_verify::ay_bridge::generate_lowered_queries(theorem, &AYConfig::default())
                .iter()
                .enumerate()
        {
            write(
                "registry",
                index,
                0,
                &theorem.name,
                &format!("lowered {sub}"),
                lowered,
            );
        }
    }
    eprintln!(
        "old: {} queries worth {old_total} bytes, largest {old_max:?}; {old_shifts} shifts\n\
         new: parts worth {new_total} bytes, largest {new_max:?}",
        manifest.lines().filter(|l| l.starts_with("old\t")).count()
    );
    if let Some(dir) = &dump {
        std::fs::write(dir.join("manifest.tsv"), &manifest).unwrap();
    }
    // The pair obligation it replaces is several times the largest part.
    assert!(
        old_max.bytes > 4 * new_max.bytes,
        "old {} vs new {}",
        old_max.bytes,
        new_max.bytes
    );
    assert!(new_max.bytes < 4096, "{new_max:?}");
}
