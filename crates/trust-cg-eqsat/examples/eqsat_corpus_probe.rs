// crates/trust-cg-eqsat/examples/eqsat_corpus_probe.rs - reads interim-corpus candidates and prints their trust-ir text
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The reader half of `scripts/eqsat_corpus.py` (the interim corpus of
//! `docs/eqsat-tier-e.md` section 9).
//!
//! ```text
//! eqsat_corpus_probe --out DIR LIST
//! ```
//!
//! `LIST` holds one candidate per line, `KEY<TAB>PATH`. For every candidate,
//! in list order, the probe:
//!
//! 1. identifies the transport by its leading bytes
//!    (`trust_ir::codec::sniff_format`): the TrustIr binary codec is decoded
//!    with `trust_ir::binary::deserialize_module_with_wire_version`, text with
//!    `trust_ir::parser::parse_module`; a trust-cg `tMBC` envelope, a level-S
//!    template, JSON and anything unrecognised are refused by name (this
//!    crate's dependencies carry no JSON reader);
//! 2. validates the module with `trust_ir_build::validate_module`;
//! 3. prints it back with `trust_ir::format::text_checked` (the module as
//!    stored: its own value ids and block order, refused when the text grammar
//!    cannot carry a field), re-parses that text and requires the result to be
//!    structurally equal (`Module: PartialEq`) to the module read in step 1.
//!
//! A candidate that passes all three is written to `DIR/KEY.trust_ir` (the
//! printed text) and reported as
//! `KEY ok FORMAT FUNCTIONS BODIES INSTRUCTIONS SCALAR_OPS TEXT_BYTES`
//! (tab-separated). Any other candidate is reported as `KEY left REASON`, the
//! reason being the first refusal met. A panic inside trust-ir while reading
//! one candidate is caught and reported as that candidate's refusal, so one
//! bad input cannot hide the verdicts of the others.
//!
//! What this establishes, and what not: "ok" means the pinned trust-ir reads,
//! validates and text-round-trips the module. It says nothing about what the
//! e-graph engine does with it (it may decline every function), and nothing
//! about the module's runtime behaviour.

use std::io::Write as _;
use std::panic::{self, AssertUnwindSafe};
use std::path::PathBuf;
use std::process::ExitCode;

use trust_ir::codec::{SniffedFormat, sniff_format};
use trust_ir::{Inst, Module, Ty};

/// Longest reason written, in characters.
const MAX_REASON_CHARS: usize = 200;

/// The verdict on one candidate.
enum Verdict {
    /// Read, validated and round-tripped; the printed text and a summary.
    Ok(Box<Accepted>),
    /// Refused, with the first reason met.
    Left(String),
}

struct Accepted {
    format: String,
    text: String,
    functions: usize,
    bodies: usize,
    instructions: usize,
    scalar_ops: usize,
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("eqsat_corpus_probe: {message}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<(), String> {
    let (out, list) = arguments()?;
    let listing =
        std::fs::read_to_string(&list).map_err(|e| format!("read {}: {e}", list.display()))?;
    std::fs::create_dir_all(&out).map_err(|e| format!("create {}: {e}", out.display()))?;
    let stdout = std::io::stdout();
    let mut stdout = stdout.lock();
    let (mut ok, mut left) = (0usize, 0usize);
    for (number, line) in listing.lines().enumerate() {
        if line.is_empty() {
            continue;
        }
        let Some((key, path)) = line.split_once('\t') else {
            return Err(format!(
                "{}:{}: expected KEY<TAB>PATH",
                list.display(),
                number + 1
            ));
        };
        if key.is_empty()
            || !key
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
        {
            return Err(format!(
                "{}:{}: bad key {key:?}",
                list.display(),
                number + 1
            ));
        }
        let bytes = std::fs::read(path).map_err(|e| format!("read candidate {path}: {e}"))?;
        let row = match probe_caught(&bytes) {
            Verdict::Ok(accepted) => {
                let target = out.join(format!("{key}.trust_ir"));
                std::fs::write(&target, accepted.text.as_bytes())
                    .map_err(|e| format!("write {}: {e}", target.display()))?;
                ok += 1;
                format!(
                    "{key}\tok\t{}\t{}\t{}\t{}\t{}\t{}",
                    accepted.format,
                    accepted.functions,
                    accepted.bodies,
                    accepted.instructions,
                    accepted.scalar_ops,
                    accepted.text.len()
                )
            }
            Verdict::Left(reason) => {
                left += 1;
                format!("{key}\tleft\t{}", one_line(&reason))
            }
        };
        writeln!(stdout, "{row}").map_err(|e| format!("write stdout: {e}"))?;
    }
    writeln!(stdout, "# probed {}: ok {ok}, left {left}", ok + left)
        .map_err(|e| format!("write stdout: {e}"))?;
    Ok(())
}

fn arguments() -> Result<(PathBuf, PathBuf), String> {
    let usage = "usage: eqsat_corpus_probe --out DIR LIST";
    let mut out = None;
    let mut list = None;
    let mut args = std::env::args_os().skip(1);
    while let Some(arg) = args.next() {
        if arg == "--out" {
            out = Some(PathBuf::from(args.next().ok_or(usage)?));
        } else if list.is_none() && !arg.to_string_lossy().starts_with("--") {
            list = Some(PathBuf::from(arg));
        } else {
            return Err(format!("unexpected argument {arg:?}; {usage}"));
        }
    }
    match (out, list) {
        (Some(out), Some(list)) => Ok((out, list)),
        _ => Err(usage.to_owned()),
    }
}

/// [`probe`], with a panic inside trust-ir turned into a refusal.
fn probe_caught(bytes: &[u8]) -> Verdict {
    match panic::catch_unwind(AssertUnwindSafe(|| probe(bytes))) {
        Ok(verdict) => verdict,
        Err(payload) => {
            let message = payload
                .downcast_ref::<&str>()
                .map(|s| (*s).to_owned())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "non-string panic payload".to_owned());
            Verdict::Left(format!("trust-ir panicked while reading: {message}"))
        }
    }
}

fn probe(bytes: &[u8]) -> Verdict {
    let (module, format) = match read(bytes) {
        Ok(read) => read,
        Err(reason) => return Verdict::Left(reason),
    };
    let errors = trust_ir_build::validate_module(&module);
    if let Some(first) = errors.first() {
        let more = if errors.len() > 1 {
            format!(" (+{} more)", errors.len() - 1)
        } else {
            String::new()
        };
        return Verdict::Left(format!("does not validate: {first}{more}"));
    }
    let text = match trust_ir::format::text_checked(&module) {
        Ok(text) => text,
        Err(loss) => return Verdict::Left(format!("does not round-trip through text: {loss}")),
    };
    match trust_ir::parser::parse_module(&text) {
        Ok(reparsed) if reparsed == module => {}
        Ok(_) => {
            return Verdict::Left(
                "does not round-trip through text: the re-parsed module differs".to_owned(),
            );
        }
        Err(e) => {
            return Verdict::Left(format!(
                "does not round-trip through text: the printed text does not parse: {e}"
            ));
        }
    }
    let (instructions, scalar_ops) = census(&module);
    Verdict::Ok(Box::new(Accepted {
        format,
        text,
        functions: module.functions.len(),
        bodies: module
            .functions
            .iter()
            .filter(|f| !f.is_declaration())
            .count(),
        instructions,
        scalar_ops,
    }))
}

/// Decode `bytes` by its leading bytes; the second value names the format.
fn read(bytes: &[u8]) -> Result<(Module, String), String> {
    match sniff_format(bytes) {
        Some(SniffedFormat::Binary) => {
            match trust_ir::binary::deserialize_module_with_wire_version(bytes) {
                Ok((module, version)) => Ok((module, format!("binary-v{}", version.get()))),
                Err(e) => Err(format!("binary does not decode: {e}")),
            }
        }
        Some(SniffedFormat::TrustCgContainer) => {
            Err("tMBC envelope (trust-cg container, not a bare trust-ir module)".to_owned())
        }
        Some(SniffedFormat::TemplateBinary) => {
            Err("level-S template (TRUST_IS magic), not a module".to_owned())
        }
        Some(SniffedFormat::Json) => {
            Err("JSON module (not read: no JSON reader among this crate's dependencies)".to_owned())
        }
        Some(SniffedFormat::Text) | None => {
            let Ok(text) = std::str::from_utf8(bytes) else {
                return Err(
                    "unrecognised format (not TRUST_IR binary, JSON or UTF-8 text)".to_owned(),
                );
            };
            trust_ir::parser::parse_module(text)
                .map(|module| (module, "text".to_owned()))
                .map_err(|e| format!("does not parse: {e}"))
        }
    }
}

/// Instructions in bodies, and how many of them are integer or boolean
/// scalar operations (`BinOp`, `UnOp`, `ICmp`, `Cast`, `Select`, `Const`,
/// `Copy` at an integer or `bool` type, total or not): a rough measure of
/// what the module gives the e-graph to look at.
fn census(module: &Module) -> (usize, usize) {
    let scalar = |ty: &Ty| ty.is_integer() || *ty == Ty::Bool;
    let mut instructions = 0usize;
    let mut scalar_ops = 0usize;
    for function in &module.functions {
        for block in &function.blocks {
            for node in &block.body {
                instructions += 1;
                let counted = match &node.inst {
                    Inst::BinOp { ty, .. }
                    | Inst::UnOp { ty, .. }
                    | Inst::ICmp { ty, .. }
                    | Inst::Select { ty, .. }
                    | Inst::Const { ty, .. }
                    | Inst::Copy { ty, .. } => scalar(ty),
                    Inst::Cast { src_ty, dst_ty, .. } => scalar(src_ty) && scalar(dst_ty),
                    _ => false,
                };
                if counted {
                    scalar_ops += 1;
                }
            }
        }
    }
    (instructions, scalar_ops)
}

/// `reason` on one line: control characters become spaces, runs of spaces
/// collapse, and the result is cut at [`MAX_REASON_CHARS`] characters.
fn one_line(reason: &str) -> String {
    let mut out = String::new();
    let mut last_space = true;
    for c in reason.chars() {
        let c = if c.is_control() { ' ' } else { c };
        if c == ' ' {
            if last_space {
                continue;
            }
            last_space = true;
        } else {
            last_space = false;
        }
        out.push(c);
    }
    let trimmed = out.trim_end();
    if trimmed.chars().count() <= MAX_REASON_CHARS {
        return trimmed.to_owned();
    }
    let mut cut = String::new();
    for c in trimmed.chars().take(MAX_REASON_CHARS) {
        cut.push(c);
    }
    cut.push_str("...");
    cut
}
