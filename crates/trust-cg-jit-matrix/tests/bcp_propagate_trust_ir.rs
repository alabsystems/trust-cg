// trust-cg-jit-matrix/tests/bcp_propagate_trust_ir.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// First-pass BCP propagate kernel authored in trust_ir text format,
// loaded through the trust_ir text loader, JIT-compiled via the host
// JIT pipeline, and exercised on a tiny SAT formula whose expected
// outcome is computed by `BcpState::propagate()` (the Rust reference
// in `bcp_baseline.rs`).
//
// Scope: this kernel is a *scan-based* BCP step, not watched-literal
// BCP. It iterates clauses, looks for unit clauses (one unassigned
// literal, all others false) and propagates them, repeating until
// fixpoint or conflict. It detects conflicts (all-false clause) and
// returns a packed status word `(propagations << 32) | result`
// matching the existing native `bcp_kernel.rs` ABI. Watched-literal
// BCP is reserved for a future pass; see the report for the reason.
//
// ABI:
//   unsafe extern "C" fn(ctx: *mut KernelCtx, input: *const u32, len: usize) -> u64
//
// The trust_ir module signature is `(ptr, ptr, i64) -> i64`. The
// `input` / `len` args are accepted but currently ignored (the trail
// is seeded directly through the arena pointer for this first pass).
//
// Arena layout (pointed to by `KernelCtx.arena_ptr`):
//   +  0: u64 num_vars
//   +  8: u64 num_clauses
//   + 16: u64 clauses_lits_ptr   -> [i32; total_lits]
//   + 24: u64 clause_offsets_ptr -> [u32; num_clauses + 1]
//   + 32: u64 values_ptr         -> [i8;  num_vars + 1]   // 0 unassigned, 1 true, -1 false
//   + 40: u64 trail_ptr          -> [i32; trail_capacity]
//   + 48: u64 trail_len_ptr      -> u64                   // in/out
//
// The fixture is checked in at `crates/trust-cg-jit-matrix/fixtures/
// bcp_propagate.trust_ir`. To regenerate it from the builder code in
// this file, set `TRUST_CG_REGEN_FIXTURE=1` when running the test.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::collections::HashMap;
use std::path::PathBuf;

use trust_cg_codegen::pipeline::{FormatMode, encode_trust_ir_text, load_module_as};
use trust_cg_codegen::{Compiler, CompilerConfig};

use trust_cg_jit_matrix::bcp_baseline::BcpState;
use trust_cg_jit_matrix::bcp_module_builder::{ENTRY_NAME, build_bcp_propagate_module};

/// `KernelCtx` mirror used by the test harness. Layout must match
/// `trust_cg_jit_matrix::solver_kernel_abi::KernelCtx` exactly so the
/// JIT'd code can read `arena_ptr` from offset 0 and write the
/// implied-literals / conflicting-clause side channels at their
/// documented offsets.
#[repr(C)]
struct KernelCtxRaw {
    arena_ptr: *mut u8,
    arena_len: usize,
    formula_constants_ptr: *const u32,
    formula_constants_len: usize,
    user_data: *mut u8,
    status: u64,
    implied_literals_out: *mut i32,
    implied_literals_cap: usize,
    implied_literals_len: usize,
    conflicting_clause_index: i32,
    _reserved_pad: u32,
    implied_reasons_out: *mut i32,
    implied_reasons_cap: usize,
    clause_id_translation: *const i32,
    initial_values: *const i8,
    initial_values_len: usize,
}

/// Heap-pinned BCP arena.
struct Arena {
    header: Vec<u64>,
    clauses_lits: Vec<i32>,
    clause_offsets: Vec<u32>,
    values: Vec<i8>,
    trail: Vec<i32>,
    trail_len: Box<u64>,
}

impl Arena {
    fn build(num_vars: usize, clauses: &[Vec<i32>], trail_capacity: usize) -> Self {
        let mut clauses_lits: Vec<i32> = Vec::new();
        let mut clause_offsets: Vec<u32> = Vec::with_capacity(clauses.len() + 1);
        clause_offsets.push(0);
        for c in clauses {
            for &lit in c {
                clauses_lits.push(lit);
            }
            clause_offsets.push(clauses_lits.len() as u32);
        }
        let values = vec![0i8; num_vars + 1];
        let trail = vec![0i32; trail_capacity];
        let trail_len = Box::new(0u64);

        let mut arena = Arena {
            header: vec![0u64; 7],
            clauses_lits,
            clause_offsets,
            values,
            trail,
            trail_len,
        };
        arena.header[0] = num_vars as u64;
        arena.header[1] = clauses.len() as u64;
        arena.header[2] = arena.clauses_lits.as_ptr() as u64;
        arena.header[3] = arena.clause_offsets.as_ptr() as u64;
        arena.header[4] = arena.values.as_mut_ptr() as u64;
        arena.header[5] = arena.trail.as_mut_ptr() as u64;
        arena.header[6] = (&mut *arena.trail_len) as *mut u64 as u64;
        arena
    }

    fn header_ptr(&mut self) -> *mut u8 {
        self.header.as_mut_ptr() as *mut u8
    }

    fn trail_len(&self) -> u64 {
        *self.trail_len
    }

    fn values_at(&self, var: usize) -> i8 {
        self.values[var]
    }
}

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("bcp_propagate.trust_ir")
}

fn ensure_fixture() -> trust_ir::Module {
    let module = build_bcp_propagate_module();
    let text = encode_trust_ir_text(&module);

    let path = fixture_path();
    let regen = std::env::var("TRUST_CG_REGEN_FIXTURE").ok().as_deref() == Some("1");
    let on_disk = std::fs::read_to_string(&path).ok();

    let should_write = regen || on_disk.as_deref() != Some(text.as_str());
    if should_write {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("create fixtures dir");
        }
        std::fs::write(&path, &text).expect("write fixture text");
    }

    load_module_as(&path, FormatMode::Text)
        .unwrap_or_else(|e| panic!("text fixture failed to parse: {e}"))
}

fn pack_status(result: u32, counter: u32) -> u64 {
    (result as u64) | ((counter as u64) << 32)
}

fn run_jit_propagate(num_vars: usize, clauses: &[Vec<i32>]) -> (u64, Vec<(usize, i8)>) {
    let module = ensure_fixture();

    let config = CompilerConfig::for_host_jit();
    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &extern_symbols)
        .unwrap_or_else(|err| panic!("JIT compilation failed: {err}"));

    let func = unsafe {
        result
            .buffer
            .get_fn_bound::<unsafe extern "C" fn(*mut KernelCtxRaw, *const u32, usize) -> u64>(
                ENTRY_NAME,
            )
    }
    .unwrap_or_else(|| panic!("JIT buffer does not export `{ENTRY_NAME}`"));

    let trail_capacity = (num_vars + 1).max(8);
    let mut arena = Arena::build(num_vars, clauses, trail_capacity);
    let arena_header_ptr = arena.header_ptr();

    let mut ctx = KernelCtxRaw {
        arena_ptr: arena_header_ptr,
        arena_len: arena.header.len() * 8,
        formula_constants_ptr: core::ptr::null(),
        formula_constants_len: 0,
        user_data: core::ptr::null_mut(),
        status: 0,
        implied_literals_out: core::ptr::NonNull::<i32>::dangling().as_ptr(),
        implied_literals_cap: 0,
        implied_literals_len: 0,
        conflicting_clause_index: -1,
        _reserved_pad: 0,
        implied_reasons_out: core::ptr::null_mut(),
        implied_reasons_cap: 0,
        clause_id_translation: core::ptr::null(),
        initial_values: core::ptr::null(),
        initial_values_len: 0,
    };

    let packed = unsafe { (*func.as_ref())(&mut ctx, core::ptr::null(), 0) };

    let mut values_out: Vec<(usize, i8)> = Vec::new();
    for v in 1..=num_vars {
        values_out.push((v, arena.values_at(v)));
    }
    let _trail_len = arena.trail_len();
    (packed, values_out)
}

fn reference_propagate(num_vars: usize, clauses: &[Vec<i32>]) -> (u32, Vec<(usize, i8)>) {
    let mut state = BcpState::new(num_vars, clauses.to_vec());
    let result = state.propagate();
    let mut values_out: Vec<(usize, i8)> = Vec::new();
    for v in 1..=num_vars {
        let val = match state.value_of_lit(v as i32) {
            trust_cg_jit_matrix::bcp_baseline::Value::Unassigned => 0,
            trust_cg_jit_matrix::bcp_baseline::Value::True => 1,
            trust_cg_jit_matrix::bcp_baseline::Value::False => -1,
        };
        values_out.push((v, val));
    }
    let code = if result.is_some() { 1 } else { 0 };
    (code, values_out)
}

#[test]
fn fixture_round_trips_through_text_loader() {
    let _ = ensure_fixture();
}

#[test]
fn unit_clause_propagates_one_literal() {
    let num_vars = 3;
    let clauses = vec![vec![3]];
    let (packed, jit_values) = run_jit_propagate(num_vars, &clauses);
    let (ref_code, ref_values) = reference_propagate(num_vars, &clauses);

    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(
        status, ref_code,
        "result code mismatch (packed=0x{packed:x})"
    );
    assert_eq!(jit_values, ref_values, "value table mismatch");
}

#[test]
fn three_variable_unsat_reaches_conflict() {
    let num_vars = 3;
    let clauses = vec![vec![1, 2, 3], vec![-1], vec![-2], vec![-3]];
    let (packed, _jit_values) = run_jit_propagate(num_vars, &clauses);
    let (ref_code, _ref_values) = reference_propagate(num_vars, &clauses);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(
        status, ref_code,
        "result code mismatch (packed=0x{packed:x})"
    );
    assert_eq!(status, 1, "expected conflict result code");
}

#[test]
fn chain_propagation_assigns_all_implied() {
    let num_vars = 4;
    let clauses = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
    let (packed, jit_values) = run_jit_propagate(num_vars, &clauses);
    let (ref_code, ref_values) = reference_propagate(num_vars, &clauses);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(
        status, ref_code,
        "result code mismatch (packed=0x{packed:x})"
    );
    assert_eq!(status, 0, "expected OK result code");
    assert_eq!(jit_values, ref_values, "value table mismatch");
    let propagations = (packed >> 32) as u32;
    assert!(
        propagations >= 4,
        "expected >=4 propagations, got {propagations}"
    );
}

/// Drive the scan-kernel JIT with a caller-supplied implied-literals
/// buffer installed in `ctx` and return the packed return word
/// together with `(implied_literals_len, conflicting_clause_index)`.
fn run_jit_with_implied_buffer(
    num_vars: usize,
    clauses: &[Vec<i32>],
    buf: &mut [i32],
) -> (u64, usize, i32) {
    let module = ensure_fixture();
    let config = CompilerConfig::for_host_jit();
    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &extern_symbols)
        .unwrap_or_else(|err| panic!("JIT compilation failed: {err}"));

    let func = unsafe {
        result
            .buffer
            .get_fn_bound::<unsafe extern "C" fn(*mut KernelCtxRaw, *const u32, usize) -> u64>(
                ENTRY_NAME,
            )
    }
    .unwrap_or_else(|| panic!("JIT buffer does not export `{ENTRY_NAME}`"));

    let trail_capacity = (num_vars + 1).max(8);
    let mut arena = Arena::build(num_vars, clauses, trail_capacity);
    let arena_header_ptr = arena.header_ptr();

    let buf_ptr = if buf.is_empty() {
        core::ptr::NonNull::<i32>::dangling().as_ptr()
    } else {
        buf.as_mut_ptr()
    };
    let mut ctx = KernelCtxRaw {
        arena_ptr: arena_header_ptr,
        arena_len: arena.header.len() * 8,
        formula_constants_ptr: core::ptr::null(),
        formula_constants_len: 0,
        user_data: core::ptr::null_mut(),
        status: 0,
        implied_literals_out: buf_ptr,
        implied_literals_cap: buf.len(),
        implied_literals_len: 0,
        conflicting_clause_index: -1,
        _reserved_pad: 0,
        implied_reasons_out: core::ptr::null_mut(),
        implied_reasons_cap: 0,
        clause_id_translation: core::ptr::null(),
        initial_values: core::ptr::null(),
        initial_values_len: 0,
    };
    let packed = unsafe { (*func.as_ref())(&mut ctx, core::ptr::null(), 0) };
    (
        packed,
        ctx.implied_literals_len,
        ctx.conflicting_clause_index,
    )
}

#[test]
fn scan_returns_conflicting_clause_on_conflict() {
    // (x1 v x2 v x3) is clause 0 and becomes false once the unit
    // clauses propagate -x1, -x2, -x3.
    let num_vars = 3;
    let clauses = vec![vec![1, 2, 3], vec![-1], vec![-2], vec![-3]];
    let mut buf = vec![0i32; 16];
    let (packed, _len, conflict_ci) = run_jit_with_implied_buffer(num_vars, &clauses, &mut buf);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, 1, "expected conflict (packed=0x{packed:x})");
    assert_eq!(
        conflict_ci, 0,
        "expected clause 0 to be reported as the conflict (packed=0x{packed:x})"
    );
}

#[test]
fn scan_emits_implied_literals_in_propagation_order() {
    // Unit clause 1, then chained binary implications 2 <- 1, 3 <- 2,
    // 4 <- 3. The scan kernel propagates them in clause-scan order.
    let num_vars = 4;
    let clauses = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
    let mut buf = vec![0i32; 16];
    let (packed, len, _ci) = run_jit_with_implied_buffer(num_vars, &clauses, &mut buf);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, 0, "expected OK result (packed=0x{packed:x})");
    assert_eq!(len, 4, "expected 4 implied literals, got {len}");
    assert_eq!(
        &buf[..4],
        &[1i32, 2, 3, 4],
        "implied-literals stream out of order"
    );
}

#[test]
fn scan_implied_literals_overflow_signals() {
    // Same chain as above; capacity of 2 < 4 propagations -> sticky
    // overflow (`implied_literals_len == usize::MAX`).
    let num_vars = 4;
    let clauses = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
    let mut tiny = vec![0i32; 2];
    let (packed, len, _ci) = run_jit_with_implied_buffer(num_vars, &clauses, &mut tiny);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, 0, "expected OK result (packed=0x{packed:x})");
    assert_eq!(
        len,
        usize::MAX,
        "expected overflow sentinel, got {len} (packed=0x{packed:x})"
    );
}

/// Pack helper for ABI parity with native bcp_kernel.rs.
#[test]
fn pack_status_helper_round_trips() {
    let s = pack_status(1, 5);
    assert_eq!(s & 0xFFFF_FFFF, 1);
    assert_eq!(s >> 32, 5);
}

/// Sibling of `run_jit_with_implied_buffer` that also installs a
/// reasons buffer and optional translation table. Returns
/// `(packed, implied_literals_len, implied_reasons_present)`.
fn run_jit_with_reasons_buffer(
    num_vars: usize,
    clauses: &[Vec<i32>],
    lits_buf: &mut [i32],
    reasons_buf: &mut [i32],
    translation: Option<&[i32]>,
) -> (u64, usize, bool) {
    let module = ensure_fixture();
    let config = CompilerConfig::for_host_jit();
    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &extern_symbols)
        .unwrap_or_else(|err| panic!("JIT compilation failed: {err}"));

    let func = unsafe {
        result
            .buffer
            .get_fn_bound::<unsafe extern "C" fn(*mut KernelCtxRaw, *const u32, usize) -> u64>(
                ENTRY_NAME,
            )
    }
    .unwrap_or_else(|| panic!("JIT buffer does not export `{ENTRY_NAME}`"));

    let trail_capacity = (num_vars + 1).max(8);
    let mut arena = Arena::build(num_vars, clauses, trail_capacity);
    let arena_header_ptr = arena.header_ptr();

    let lits_ptr = if lits_buf.is_empty() {
        core::ptr::NonNull::<i32>::dangling().as_ptr()
    } else {
        lits_buf.as_mut_ptr()
    };
    let (reasons_ptr, reasons_cap) = if reasons_buf.is_empty() {
        (core::ptr::null_mut::<i32>(), 0usize)
    } else {
        (reasons_buf.as_mut_ptr(), reasons_buf.len())
    };
    let xlate_ptr = match translation {
        Some(t) if !t.is_empty() => t.as_ptr(),
        _ => core::ptr::null(),
    };

    let mut ctx = KernelCtxRaw {
        arena_ptr: arena_header_ptr,
        arena_len: arena.header.len() * 8,
        formula_constants_ptr: core::ptr::null(),
        formula_constants_len: 0,
        user_data: core::ptr::null_mut(),
        status: 0,
        implied_literals_out: lits_ptr,
        implied_literals_cap: lits_buf.len(),
        implied_literals_len: 0,
        conflicting_clause_index: -1,
        _reserved_pad: 0,
        implied_reasons_out: reasons_ptr,
        implied_reasons_cap: reasons_cap,
        clause_id_translation: xlate_ptr,
        initial_values: core::ptr::null(),
        initial_values_len: 0,
    };
    let packed = unsafe { (*func.as_ref())(&mut ctx, core::ptr::null(), 0) };
    let reasons_present = !ctx.implied_reasons_out.is_null()
        && ctx.implied_literals_len != 0
        && ctx.implied_reasons_cap != 0;
    (packed, ctx.implied_literals_len, reasons_present)
}

#[test]
fn scan_emits_reasons_in_passthrough_mode() {
    // Unit clause `1` (idx 0), chain via clauses 1, 2, 3.
    let num_vars = 4;
    let clauses = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
    let mut lits = vec![0i32; 16];
    let mut reasons = vec![-9i32; 16];
    let (packed, len, present) =
        run_jit_with_reasons_buffer(num_vars, &clauses, &mut lits, &mut reasons, None);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, 0, "expected OK");
    assert_eq!(len, 4);
    assert!(present);
    assert_eq!(&lits[..4], &[1, 2, 3, 4]);
    assert_eq!(&reasons[..4], &[0, 1, 2, 3]);
}

#[test]
fn scan_emits_reasons_via_translation_table() {
    let num_vars = 4;
    let clauses = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
    let translation: Vec<i32> = vec![1000, 1001, 1002, 1003];
    let mut lits = vec![0i32; 16];
    let mut reasons = vec![-9i32; 16];
    let (packed, len, present) = run_jit_with_reasons_buffer(
        num_vars,
        &clauses,
        &mut lits,
        &mut reasons,
        Some(&translation),
    );
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, 0);
    assert_eq!(len, 4);
    assert!(present);
    assert_eq!(&lits[..4], &[1, 2, 3, 4]);
    assert_eq!(&reasons[..4], &[1000, 1001, 1002, 1003]);
}

#[test]
fn scan_handles_no_reason_buffer() {
    // No reasons buffer installed -> literals still emitted, no
    // reason writes, status reports reasons absent.
    let num_vars = 4;
    let clauses = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3, 4]];
    let mut lits = vec![0i32; 16];
    let empty_reasons: Vec<i32> = Vec::new();
    let (packed, len, present) = run_jit_with_reasons_buffer(
        num_vars,
        &clauses,
        &mut lits,
        &mut empty_reasons.clone(),
        None,
    );
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, 0);
    assert_eq!(len, 4);
    assert!(!present);
    assert_eq!(&lits[..4], &[1, 2, 3, 4]);
}
