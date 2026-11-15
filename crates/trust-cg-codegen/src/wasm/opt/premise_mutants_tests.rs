// trust-cg-codegen/wasm/opt/premise_mutants_tests.rs - mutants of the no-wrap premise path
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Mutation tests of the emission pass's no-wrap premise path on the lane's
//! real output: a module whose GEPs fold under the premises
//! `trust_cg_verify::wasm_nowrap_premise` re-derives, beside an integer
//! address chain (`ptrtoint`/`add`/`inttoptr`) that carries none.
//!
//! The lowering's own bodies and premises come from the [`CAPTURED`] hook
//! (the queue as `validate_pending` receives it). Each function is cleaned
//! and rewritten as the pass does, its candidate validated under the
//! premises the control validator carried, and then:
//!
//! - every POST mutant (a memarg offset, an `i32.const`, a local read or a
//!   local write changed) is validated under those premises, and every one
//!   the validator accepts must compute what the candidate computes in node;
//! - every PRE mutant (the same changes to the body the premises were
//!   derived on) is validated against the candidate: the premises are bound
//!   to the unmutated body, so an accepted pair may use none of them, and
//!   must compute the same in node.
//!
//! Inputs: pointers inside the closed module's memory, where the GEPs are
//! defined, and the pointer `0xFFFF_FFF0`, whose GEP additions wrap. There
//! the chain's function must compute the same before and after the pass
//! (its additions wrap in trust-ir too, so a fold accepted for them would
//! trap instead), while a function with a premised fold traps where its
//! lowering read wrapped addresses: the emission relation is conditional on
//! the GEPs being defined, and these inputs are outside it.
//!
//! `validate_with_premises` and `validate_control_with_premises` are
//! provisional surfaces (docs/wasm32_perf_roadmap.md, "Pending owner
//! sign-off"). Node is required to execute the modules; without it the test
//! prints a loud SKIP and executes nothing.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_verify::wasm_cfg_proofs::{Imm, decode_body};

use super::*;
use crate::pipeline::OptLevel;

/// GEPs from a pointer parameter at constant offsets of at least 16 (one
/// scaled, one result used twice), GEPs from a pointer loaded from a frame
/// slot, and an integer address chain from the parameter.
const CORPUS: &str = r#"module "premise_mutants"
target "wasm32-unknown-unknown" 4 little

type ty.0 = i64

functy.0 = (ptr, i64) -> (i64)

fn @geps(functy.0) {
bb0(%0: ptr, %1: i64):
    %2 = const usize 16
    %3 = gep u8, ptr %0, %2
    %4 = load i64, ptr %3
    %5 = const usize 24
    %6 = gep u8, ptr %0, %5
    store i64 %1, ptr %6
    %7 = const usize 4
    %8 = gep i64, ptr %0, %7
    %9 = load i64, ptr %8
    %10 = add i64 %4, %9
    %11 = const usize 40
    %12 = gep u8, ptr %0, %11
    %13 = trunc i64 %1 to u16
    store u16 %13, ptr %12
    %14 = load u16, ptr %12
    %15 = zext u16 %14 to i64
    %16 = add i64 %10, %15
    ret %16
}

fn @frame(functy.0) {
bb0(%0: ptr, %1: i64):
    %2 = alloca [ty.0 x 6]
    %3 = alloca ptr
    store ptr %2, ptr %3
    %4 = load ptr, ptr %3
    %5 = const usize 8
    %6 = gep u8, ptr %4, %5
    store i64 %1, ptr %6
    %7 = const usize 16
    %8 = gep u8, ptr %4, %7
    %9 = const i64 3
    %10 = mul i64 %1, %9
    store i64 %10, ptr %8
    %11 = const usize 8
    %12 = gep u8, ptr %4, %11
    %13 = load i64, ptr %12
    %14 = const usize 16
    %15 = gep u8, ptr %4, %14
    %16 = load i64, ptr %15
    %17 = sub i64 %13, %16
    ret %17
}

fn @chain(functy.0) {
bb0(%0: ptr, %1: i64):
    %2 = ptrtoint ptr %0 to i32
    %3 = const i32 24
    %4 = add i32 %2, %3
    %5 = inttoptr i32 %4 to ptr
    store i64 %1, ptr %5
    %6 = const i32 16
    %7 = add i32 %2, %6
    %8 = inttoptr i32 %7 to ptr
    %9 = load i64, ptr %8
    %10 = load i64, ptr %5
    %11 = add i64 %9, %10
    ret %11
}
"#;

/// The pointer whose additions of 16 and more wrap.
const HIGH: i64 = 0xFFFF_FFF0;

/// `(pointer, value)` rows inside the closed module's one page, below its
/// shadow stack.
const INSIDE: [(i64, i64); 3] = [(4096, 7), (8200, -3), (12345, 1 << 40)];

fn node() -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("node"))
        .find(|p| p.is_file())
}

/// `export(pointer, value)` for every row, each call in a fresh instance;
/// `None` is a trap.
fn run(node: &PathBuf, bytes: &[u8], export: &str, rows: &[(i64, i64)]) -> Vec<Option<String>> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "tcg-premise-mutants-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    std::fs::write(dir.join("m.wasm"), bytes).expect("write module");
    let js = "const fs = require('fs');\n\
              const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
              const rows = JSON.parse(process.argv[4]);\n\
              const out = rows.map(([p, v]) => {\n\
                const inst = new WebAssembly.Instance(m, {});\n\
                try { return String(inst.exports[process.argv[3]](Number(p), BigInt(v))); }\n\
                catch (e) { if (e instanceof WebAssembly.RuntimeError) return null; throw e; }\n\
              });\n\
              process.stdout.write(JSON.stringify(out));\n";
    std::fs::write(dir.join("run.js"), js).expect("write runner");
    let rows: Vec<(String, String)> = rows
        .iter()
        .map(|(p, v)| (p.to_string(), v.to_string()))
        .collect();
    let out = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(export)
        .arg(serde_json::to_string(&rows).expect("rows"))
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "node failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    serde_json::from_slice(&out.stdout).expect("node JSON")
}

/// `base` with function `func`'s body replaced by `body`, encoded.
fn module_with(base: &WasmModule, func: u32, body: &Body) -> Vec<u8> {
    let mut m = base.clone();
    assert!(m.replace_body(
        func,
        FuncBody {
            locals: super::super::lower::run_length_encode(&body.declared),
            code: body.code.clone(),
            relocs: body.relocs.clone(),
        },
    ));
    m.finish()
}

fn uleb(mut v: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            return out;
        }
        out.push(b | 0x80);
    }
}

fn sleb(mut v: i64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        let done = (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0);
        out.push(if done { b } else { b | 0x80 });
        if done {
            return out;
        }
    }
}

/// Every single-instruction mutant of `code` (`declared` after `params` in
/// the local index space): each memarg offset moved by 1, 4 or 8 or set to
/// 0, each `i32.const` moved by 1 or set to 0, and each local read or write
/// redirected to every other local of its type, and each two adjacent
/// local reads of one type swapped. With the instruction's index and a
/// short name of the change.
fn mutants(params: &[ValType], declared: &[ValType], code: &[u8]) -> Vec<(usize, String, Vec<u8>)> {
    let insts = decode_body(code, 0).expect("decodes");
    let ty = |l: usize| params.iter().chain(declared).nth(l).copied();
    let n = params.len() + declared.len();
    let mut out = Vec::new();
    for (k, x) in insts.iter().enumerate() {
        let mut replacements: Vec<(String, Vec<u8>)> = Vec::new();
        match (x.opcode, &x.imm) {
            (0x28..=0x3e, Imm::MemArg { align, offset }) => {
                let o = u64::from(*offset);
                for new in [o + 1, o + 4, o + 8, o.saturating_sub(1), 0] {
                    if new != o && new <= u64::from(u32::MAX) {
                        let mut r = vec![x.opcode];
                        r.extend(uleb(u64::from(*align)));
                        r.extend(uleb(new));
                        replacements.push((format!("offset {o}->{new}"), r));
                    }
                }
            }
            (0x41, Imm::Int(v)) => {
                let v = *v as i32;
                for new in [v.wrapping_add(1), v.wrapping_sub(1), 0] {
                    if new != v {
                        let mut r = vec![0x41];
                        r.extend(sleb(i64::from(new)));
                        replacements.push((format!("const {v}->{new}"), r));
                    }
                }
            }
            (0x20..=0x22, Imm::Index(l)) if (*l as usize) < n => {
                for o in 0..n {
                    if o != *l as usize && ty(o) == ty(*l as usize) {
                        let mut r = vec![x.opcode];
                        r.extend(uleb(o as u64));
                        replacements.push((format!("local 0x{:02x} {l}->{o}", x.opcode), r));
                    }
                }
            }
            _ => {}
        }
        if let (0x20, Imm::Index(a)) = (x.opcode, &x.imm)
            && let Some(y) = insts.get(k + 1)
            && let (0x20, Imm::Index(b)) = (y.opcode, &y.imm)
            && a != b
            && ty(*a as usize) == ty(*b as usize)
        {
            let mut m = code[..x.offset].to_vec();
            m.extend(&code[y.offset..y.offset + y.size]);
            m.extend(&code[x.offset..y.offset]);
            m.extend(&code[y.offset + y.size..]);
            out.push((k, format!("swap locals {a} {b}"), m));
        }
        for (what, r) in replacements {
            let mut m = code[..x.offset].to_vec();
            m.extend(r);
            m.extend(&code[x.offset + x.size..]);
            out.push((k, what, m));
        }
    }
    out
}

#[test]
fn every_premised_mutant_the_validator_accepts_behaves_like_the_original() {
    let Some(node) = node() else {
        eprintln!("SKIP: node not found; no premised mutant was executed");
        return;
    };
    let module = trust_ir::parser::parse_module(CORPUS).expect("parses");
    CAPTURED.with(|c| *c.borrow_mut() = Some(Vec::new()));
    let compiled = crate::wasm::compile_module_with_evidence_policy_license_options(
        &module,
        &crate::wasm::WasmModulePolicy::closed(),
        &crate::license_test_support::permit_unlicensed(),
        crate::wasm::WasmOptOptions {
            level: OptLevel::O2,
            mid_end: false,
        },
    );
    let captured = CAPTURED.with(|c| c.borrow_mut().take()).expect("captured");
    let (_, evidence) = compiled.expect("compiles");
    assert!(
        evidence.local_emission.tv_premised_folds > 0,
        "{:?}",
        evidence.local_emission
    );
    let mut base = captured
        .into_iter()
        .rev()
        .find(|m| !m.clone().take_local_opt().is_empty())
        .expect("a module with queued bodies");
    let pending = base.take_local_opt();
    let types = ModuleTypes(&base);
    let (mut post_tried, mut post_accepted, mut pre_tried, mut pre_accepted) = (0, 0, 0, 0);
    let (mut premised_functions, mut wrapped_traps) = (0, 0);
    for p in &pending {
        let export = p.name.as_str();
        let mut summary = WasmLocalOptSummary::default();
        let cleaned = clean_control(&base, p, &mut summary);
        let pre = cleaned.as_ref().map_or(&p.pre, |c| &c.body);
        let premises = cleaned.as_ref().map_or(&p.premises, |c| &c.premises);
        assert_eq!(premises.len(), p.premises.len(), "{export}: premise lost");
        let nowrap: Vec<u32> = premises.iter().map(|q| q.result()).collect();
        let cand = optimize_with(
            &p.params,
            pre,
            &p.exclusive,
            p.frame_base,
            &nowrap,
            &types,
            Variant::FULL,
        )
        .unwrap_or_else(|d| panic!("{export}: no candidate: {}", d.as_str()));
        let report = validate_candidate(&base, &p.params, pre, &cand, &p.name, premises)
            .unwrap_or_else(|f| panic!("{export}: candidate refused: {f}"));
        let pre_bytes = module_with(&base, p.func, pre);
        let post_bytes = module_with(&base, p.func, &cand.body);
        let want = run(&node, &post_bytes, export, &INSIDE);
        assert_eq!(
            run(&node, &pre_bytes, export, &INSIDE),
            want,
            "{export}: the candidate differs from its pre body on defined GEPs"
        );
        let high = [(HIGH, 5)];
        let pre_high = run(&node, &pre_bytes, export, &high);
        let post_high = run(&node, &post_bytes, export, &high);
        // The rows each mutant is run on: the wrapping pointer too, except
        // where a premised fold traps on it (outside the conditional
        // relation). Only a premise may make the two differ, and only so.
        premised_functions += usize::from(report.premised_folds > 0);
        let rows: Vec<(i64, i64)> = if pre_high == post_high {
            INSIDE.iter().copied().chain(high).collect()
        } else {
            assert!(
                report.premised_folds > 0,
                "{export}: wrapped additions differ"
            );
            assert!(pre_high[0].is_some(), "{export}: {pre_high:?}");
            assert_eq!(post_high, vec![None], "{export}: a premised fold traps");
            wrapped_traps += 1;
            INSIDE.to_vec()
        };
        let want = run(&node, &post_bytes, export, &rows);
        eprintln!(
            "{export}: {} premises, {} premised folds, {} code bytes -> {}",
            premises.len(),
            report.premised_folds,
            pre.code.len(),
            cand.body.code.len()
        );
        for (k, what, code) in mutants(&p.params, &cand.body.declared, &cand.body.code) {
            post_tried += 1;
            let mutant = Candidate {
                body: Body {
                    code,
                    ..cand.body.clone()
                },
                image: cand.image.clone(),
                facts: cand.facts.clone(),
                copies_deleted: 0,
                rematerialized: 0,
                rewrite: RewriteStats::default(),
                dead_writes: 0,
            };
            if validate_candidate(&base, &p.params, pre, &mutant, &p.name, premises).is_err() {
                continue;
            }
            post_accepted += 1;
            let got = run(
                &node,
                &module_with(&base, p.func, &mutant.body),
                export,
                &rows,
            );
            assert_eq!(
                got, want,
                "{export}: accepted post mutant at {k} ({what}) changed the results"
            );
        }
        for (k, what, code) in mutants(&p.params, &pre.declared, &pre.code) {
            pre_tried += 1;
            let mutated = Body {
                code,
                ..pre.clone()
            };
            let Ok(r) = validate_candidate(&base, &p.params, &mutated, &cand, &p.name, premises)
            else {
                continue;
            };
            pre_accepted += 1;
            assert_eq!(
                r.premised_folds, 0,
                "{export}: a premise licensed a fold on a mutated pre body ({what} at {k})"
            );
            let got = run(&node, &module_with(&base, p.func, &mutated), export, &rows);
            assert_eq!(
                got, want,
                "{export}: an accepted pair with pre mutant at {k} ({what}) differs"
            );
        }
    }
    eprintln!(
        "premised mutants: {premised_functions} functions with premised folds \
         ({wrapped_traps} trapping on the wrapping pointer); post \
         {post_tried} tried, {post_accepted} accepted and executed; pre {pre_tried} tried, \
         {pre_accepted} accepted and executed"
    );
    assert!(premised_functions >= 2, "too few functions used a premise");
    assert!(
        wrapped_traps >= 1,
        "no premised fold met a wrapping pointer"
    );
    assert!(post_tried > 100 && pre_tried > 100, "too few mutants");
    assert!(post_accepted < post_tried, "every post mutant was accepted");
}
