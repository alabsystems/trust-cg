// trust-cg-jit-matrix/tests/bcp_propagate_with_decisions_trust_ir.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sibling kernel exercising the JIT'd BCP entry that consumes its
// `input: &[u32]` slice. Each `u32` is decoded as `(var << 1) | polarity`
// matching `BCP_INPUT_FORMAT_VERSION`. Input literals are written to the
// arena's value array and pushed to the trail in order, with NO
// propagation between assignments. After the input phase, scan-based
// propagation runs once. Decode errors short-circuit and skip the
// propagation phase entirely.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::collections::HashMap;
use std::path::PathBuf;

use trust_cg_codegen::pipeline::{FormatMode, encode_trust_ir_text, load_module_as};
use trust_cg_codegen::{Compiler, CompilerConfig};

use trust_cg_jit_matrix::bcp_baseline::BcpState;
use trust_cg_jit_matrix::bcp_module_builder::{
    BCP_RESULT_CONFLICT, BCP_RESULT_DECODE_ERROR, BCP_RESULT_OK, ENTRY_NAME_WITH_DECISIONS,
    build_bcp_propagate_with_decisions_module,
};

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

    fn values_at(&self, var: usize) -> i8 {
        self.values[var]
    }
}

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("bcp_propagate_with_decisions.trust_ir")
}

fn ensure_fixture() -> trust_ir::Module {
    let module = build_bcp_propagate_with_decisions_module();
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

fn encode(var: u32, negated: bool) -> u32 {
    (var << 1) | if negated { 1 } else { 0 }
}

fn run_jit(num_vars: usize, clauses: &[Vec<i32>], input: &[u32]) -> (u32, u32, Vec<(usize, i8)>) {
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
                ENTRY_NAME_WITH_DECISIONS,
            )
    }
    .unwrap_or_else(|| panic!("JIT buffer does not export `{ENTRY_NAME_WITH_DECISIONS}`"));

    let trail_capacity = (num_vars + 1 + input.len()).max(8);
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

    let input_ptr = if input.is_empty() {
        core::ptr::null()
    } else {
        input.as_ptr()
    };
    let packed = unsafe { (*func.as_ref())(&mut ctx, input_ptr, input.len()) };

    let mut values_out: Vec<(usize, i8)> = Vec::new();
    for v in 1..=num_vars {
        values_out.push((v, arena.values_at(v)));
    }
    let status = (packed & 0xFFFF_FFFF) as u32;
    let counter = (packed >> 32) as u32;
    (status, counter, values_out)
}

fn decode_literal(encoded: u32, num_vars: u32) -> Option<i32> {
    let var = encoded >> 1;
    if var == 0 || var > num_vars {
        return None;
    }
    if var > i32::MAX as u32 {
        return None;
    }
    let polarity = encoded & 1;
    let signed = var as i32;
    Some(if polarity == 0 { signed } else { -signed })
}

fn reference_run(num_vars: usize, clauses: &[Vec<i32>], input: &[u32]) -> u32 {
    let mut state = BcpState::new(num_vars, clauses.to_vec());

    if state.propagate().is_some() {
        return BCP_RESULT_CONFLICT;
    }

    for &enc in input {
        let lit = match decode_literal(enc, num_vars as u32) {
            Some(l) => l,
            None => return BCP_RESULT_DECODE_ERROR,
        };
        state.assign(lit);
        if state.propagate().is_some() {
            return BCP_RESULT_CONFLICT;
        }
    }

    BCP_RESULT_OK
}

#[test]
fn fixture_round_trips_through_text_loader() {
    let _ = ensure_fixture();
}

#[test]
fn decision_literal_propagates_through_jit() {
    let num_vars = 2;
    let clauses = vec![vec![1i32, 2i32]];
    let input = vec![encode(1, false)];
    let (status, _props, _values) = run_jit(num_vars, &clauses, &input);
    let ref_status = reference_run(num_vars, &clauses, &input);
    assert_eq!(status, BCP_RESULT_OK);
    assert_eq!(status, ref_status);
}

#[test]
fn conflicting_decision_yields_conflict() {
    let num_vars = 3;
    let clauses = vec![vec![1i32, 2i32], vec![-1i32, 3i32], vec![-1i32, -3i32]];
    let input = vec![encode(1, false)];
    let (status, _props, _values) = run_jit(num_vars, &clauses, &input);
    let ref_status = reference_run(num_vars, &clauses, &input);
    assert_eq!(status, BCP_RESULT_CONFLICT);
    assert_eq!(status, ref_status);
}

#[test]
fn decode_error_on_zero_lit() {
    let num_vars = 3;
    let clauses: Vec<Vec<i32>> = vec![vec![1i32, 2i32]];
    let input = vec![0u32];
    let (status, props, _values) = run_jit(num_vars, &clauses, &input);
    assert_eq!(status, BCP_RESULT_DECODE_ERROR);
    assert_eq!(props, 0);
}

#[test]
fn decode_error_on_out_of_range_var() {
    let num_vars = 3;
    let clauses: Vec<Vec<i32>> = vec![vec![1i32, 2i32]];
    let oob_var = (num_vars as u32) + 1;
    let input = vec![oob_var << 1];
    let (status, props, _values) = run_jit(num_vars, &clauses, &input);
    assert_eq!(status, BCP_RESULT_DECODE_ERROR);
    assert_eq!(props, 0);
}

/// Drive the with-decisions JIT kernel with a caller-supplied
/// implied-literals output buffer installed in `ctx`; return the
/// packed return word plus the side-channel
/// `(implied_literals_len, conflicting_clause_index)`.
fn run_jit_with_implied_buffer(
    num_vars: usize,
    clauses: &[Vec<i32>],
    input: &[u32],
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
                ENTRY_NAME_WITH_DECISIONS,
            )
    }
    .unwrap_or_else(|| panic!("JIT buffer does not export `{ENTRY_NAME_WITH_DECISIONS}`"));

    let trail_capacity = (num_vars + 1 + input.len()).max(8);
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
    let input_ptr = if input.is_empty() {
        core::ptr::null()
    } else {
        input.as_ptr()
    };
    let packed = unsafe { (*func.as_ref())(&mut ctx, input_ptr, input.len()) };
    (
        packed,
        ctx.implied_literals_len,
        ctx.conflicting_clause_index,
    )
}

#[test]
fn scan_decisions_returns_conflicting_clause_on_conflict() {
    // Decision +1 makes clause 1 (-1 v 3) propagate +3; clause 2
    // (-1 v -3) then becomes all-false -> conflict on clause 2.
    let num_vars = 3;
    let clauses = vec![vec![1i32, 2i32], vec![-1i32, 3i32], vec![-1i32, -3i32]];
    let input = vec![encode(1, false)];
    let mut buf = vec![0i32; 16];
    let (packed, _len, conflict_ci) =
        run_jit_with_implied_buffer(num_vars, &clauses, &input, &mut buf);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, BCP_RESULT_CONFLICT);
    assert_eq!(conflict_ci, 2, "expected clause 2 (-1 v -3) to conflict");
}

#[test]
fn scan_decisions_emits_implied_literals_in_propagation_order() {
    // Decide +1; binary chain 2 <- 1, 3 <- 2 fires. Decoded decisions
    // are NOT counted (per the kernel-side contract); only the two
    // propagated implications should be reported.
    let num_vars = 3;
    let clauses = vec![vec![-1i32, 2i32], vec![-2i32, 3i32]];
    let input = vec![encode(1, false)];
    let mut buf = vec![0i32; 16];
    let (packed, len, _ci) = run_jit_with_implied_buffer(num_vars, &clauses, &input, &mut buf);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, BCP_RESULT_OK);
    assert_eq!(len, 2, "expected 2 implied literals, got {len}");
    assert_eq!(&buf[..2], &[2i32, 3]);
}

#[test]
fn scan_decisions_implied_literals_overflow_signals() {
    // Force the same 2-literal chain through a 1-slot buffer; the
    // first store fits, the second overflows -> sentinel.
    let num_vars = 3;
    let clauses = vec![vec![-1i32, 2i32], vec![-2i32, 3i32]];
    let input = vec![encode(1, false)];
    let mut tiny = vec![0i32; 1];
    let (_packed, len, _ci) = run_jit_with_implied_buffer(num_vars, &clauses, &input, &mut tiny);
    assert_eq!(
        len,
        usize::MAX,
        "expected overflow sentinel for too-small buffer"
    );
}

#[test]
fn multi_decision_propagation_chain() {
    let num_vars = 3;
    let clauses = vec![vec![-1i32, 2i32], vec![-2i32, 3i32]];
    let input = vec![encode(1, false)];
    let (status, _props, values) = run_jit(num_vars, &clauses, &input);
    let ref_status = reference_run(num_vars, &clauses, &input);
    assert_eq!(status, BCP_RESULT_OK);
    assert_eq!(status, ref_status);
    assert_eq!(values, vec![(1usize, 1i8), (2, 1), (3, 1)]);
}

/// Sibling of `run_jit_with_implied_buffer` that also installs a
/// reasons buffer and optional clause-id translation table.
/// Returns `(packed, implied_literals_len, reasons_present)`.
fn run_jit_with_reasons_buffer(
    num_vars: usize,
    clauses: &[Vec<i32>],
    input: &[u32],
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
                ENTRY_NAME_WITH_DECISIONS,
            )
    }
    .unwrap_or_else(|| panic!("JIT buffer does not export `{ENTRY_NAME_WITH_DECISIONS}`"));

    let trail_capacity = (num_vars + 1 + input.len()).max(8);
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
    let input_ptr = if input.is_empty() {
        core::ptr::null()
    } else {
        input.as_ptr()
    };
    let packed = unsafe { (*func.as_ref())(&mut ctx, input_ptr, input.len()) };
    let reasons_present = !ctx.implied_reasons_out.is_null()
        && ctx.implied_literals_len != 0
        && ctx.implied_reasons_cap != 0;
    (packed, ctx.implied_literals_len, reasons_present)
}

#[test]
fn scan_decisions_emits_reasons_in_passthrough_mode() {
    // Decide +1; clauses 0 (`-1 v 2`) and 1 (`-2 v 3`) fire BCP.
    let num_vars = 3;
    let clauses = vec![vec![-1i32, 2i32], vec![-2i32, 3i32]];
    let input = vec![encode(1, false)];
    let mut lits = vec![0i32; 8];
    let mut reasons = vec![-9i32; 8];
    let (packed, len, present) =
        run_jit_with_reasons_buffer(num_vars, &clauses, &input, &mut lits, &mut reasons, None);
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, BCP_RESULT_OK);
    assert_eq!(len, 2);
    assert!(present);
    assert_eq!(&lits[..2], &[2i32, 3]);
    assert_eq!(&reasons[..2], &[0i32, 1]);
}

#[test]
fn scan_decisions_emits_reasons_via_translation_table() {
    let num_vars = 3;
    let clauses = vec![vec![-1i32, 2i32], vec![-2i32, 3i32]];
    let input = vec![encode(1, false)];
    let translation: Vec<i32> = vec![777, 888];
    let mut lits = vec![0i32; 8];
    let mut reasons = vec![-9i32; 8];
    let (packed, len, present) = run_jit_with_reasons_buffer(
        num_vars,
        &clauses,
        &input,
        &mut lits,
        &mut reasons,
        Some(&translation),
    );
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, BCP_RESULT_OK);
    assert_eq!(len, 2);
    assert!(present);
    assert_eq!(&lits[..2], &[2i32, 3]);
    assert_eq!(&reasons[..2], &[777, 888]);
}

#[test]
fn scan_decisions_handles_no_reason_buffer() {
    let num_vars = 3;
    let clauses = vec![vec![-1i32, 2i32], vec![-2i32, 3i32]];
    let input = vec![encode(1, false)];
    let mut lits = vec![0i32; 8];
    let mut empty_reasons: Vec<i32> = Vec::new();
    let (packed, len, present) = run_jit_with_reasons_buffer(
        num_vars,
        &clauses,
        &input,
        &mut lits,
        &mut empty_reasons,
        None,
    );
    let status = (packed & 0xFFFF_FFFF) as u32;
    assert_eq!(status, BCP_RESULT_OK);
    assert_eq!(len, 2);
    assert!(!present);
    assert_eq!(&lits[..2], &[2i32, 3]);
}
