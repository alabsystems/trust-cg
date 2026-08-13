// E2E: AArch64 macOS exception-handling CATCH path, end to end.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the backend EH milestone: a function compiled by trust-cg that
// `Invoke`s a C++ callee which THROWS, catches the exception at a landing pad
// (`catch(...)`), reports a sentinel, and EXITS cleanly. It exercises the full
// host unwinding path: our `__compact_unwind` (FRAME mode + has-LSDA), our
// `__gcc_except_tab` LSDA (call-site table + action table + NULL catch-all type
// slot), the personality routine `___gxx_personality_v0`, and the landing-pad
// control transfer.
//
// SAFETY: the produced binary is ALWAYS run under a hard `timeout` so a broken
// catch (which would loop / abort / hang in the unwinder) becomes a fast,
// diagnosable failure instead of a hang.
//
// Hand-authored at the MachIR (`trust_cg_ir::MachFunction`) level because
// trust-ir (the frontend IR) does not model exceptions; `Invoke`/`LandingPad`/
// `Resume` live at the trust-cg machine/LIR layer. We build the post-regalloc
// MachIR directly (mirroring `pipeline::build_add_test_function`), populate the
// EH metadata from the *real* post-frame-lowering byte offsets, and emit via
// the standard single-function Mach-O path (which emits the LSDA + compact
// unwind).

use std::fs;
use std::process::Command;
use std::time::Duration;

use trust_cg_codegen::frame;
use trust_cg_codegen::pipeline::{
    self, OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups_and_blocks,
};
use trust_cg_ir::function::{
    EhCallSiteEntry, LandingPadEntry, MachFunction as IrMachFunction, Signature as IrSignature,
    Type,
};
use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};
use trust_cg_ir::operand::MachOperand as IrOperand;
use trust_cg_ir::regs::X0;
use trust_cg_ir::types::BlockId;

fn host_is_aarch64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// Build the `tc_try` MachIR function:
///
/// ```text
/// extern "C" int tc_try() {
///   try   { cxx_throw(); return 0; }   // bb0 (entry) — the invoke + normal path
///   catch (...) { return 42; }          // bb1 (landing pad)
/// }
/// ```
///
/// bb0:  BL cxx_throw            ; may throw -> unwinder may divert to bb1
///       MOVI X0, #0             ; normal path: return 0
///       RET
/// bb1:  BL ___cxa_begin_catch   ; X0 already = exception pointer (set by unwinder)
///       BL ___cxa_end_catch
///       MOVI X0, #42            ; caught: return the sentinel 42
///       RET
///
/// All registers are already physical (post-regalloc shape). The only pass we
/// still rely on is frame lowering, which prepends the standard FP/LR prologue
/// and appends the epilogue — exactly the FRAME-mode frame the host unwinder
/// needs to step `tc_try`.
fn build_tc_try() -> IrMachFunction {
    let sig = IrSignature::new(vec![], vec![Type::I32]);
    let mut func = IrMachFunction::new("tc_try".to_string(), sig);
    let entry = func.entry; // bb0
    let lpad = func.create_block(); // bb1

    // --- bb0: invoke cxx_throw, then the normal (no-exception) path ---
    let bl_throw = func.push_inst(IrMachInst::new(
        IrOpcode::Bl,
        vec![IrOperand::Symbol("cxx_throw".to_string())],
    ));
    func.append_inst(entry, bl_throw);

    let mov0 = func.push_inst(IrMachInst::new(
        IrOpcode::MovI,
        vec![IrOperand::PReg(X0), IrOperand::Imm(0)],
    ));
    func.append_inst(entry, mov0);

    let ret0 = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
    func.append_inst(entry, ret0);

    // --- bb1: the landing pad (catch(...)) ---
    // The unwinder transfers control here with X0 = exception object pointer.
    // `__cxa_begin_catch(X0)` claims the exception (decrements the handler
    // count); `__cxa_end_catch()` finalizes it. We then return the sentinel.
    let bl_begin = func.push_inst(IrMachInst::new(
        IrOpcode::Bl,
        vec![IrOperand::Symbol("__cxa_begin_catch".to_string())],
    ));
    func.append_inst(lpad, bl_begin);

    let bl_end = func.push_inst(IrMachInst::new(
        IrOpcode::Bl,
        vec![IrOperand::Symbol("__cxa_end_catch".to_string())],
    ));
    func.append_inst(lpad, bl_end);

    let mov42 = func.push_inst(IrMachInst::new(
        IrOpcode::MovI,
        vec![IrOperand::PReg(X0), IrOperand::Imm(42)],
    ));
    func.append_inst(lpad, mov42);

    let ret42 = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
    func.append_inst(lpad, ret42);

    func
}

/// Attach the `tc_try` exception table together with its non-local CFG edge.
///
/// The unwind transfer is not represented by an encoded branch instruction:
/// `EhCallSiteEntry::landing_pad_block` is its semantic source of truth.  The
/// MachIR successor/predecessor metadata must nevertheless carry the same edge
/// for liveness, block layout, and exact CFG validation.
fn attach_tc_try_eh_metadata(
    func: &mut IrMachFunction,
    landing_pad_offset: u32,
    call_start_offset: u32,
    call_length: u32,
) {
    let call_block = BlockId(0);
    let landing_pad_block = BlockId(1);

    func.eh_metadata.personality = Some("__gxx_personality_v0".to_string());
    func.eh_metadata.add_landing_pad(LandingPadEntry {
        block: landing_pad_block,
        offset: landing_pad_offset,
        catch_type_indices: vec![0], // 0 == catch-all (catch(...))
        is_cleanup: false,
    });
    func.eh_metadata.add_call_site(EhCallSiteEntry {
        call_block,
        start_offset: call_start_offset,
        length: call_length,
        landing_pad_block: Some(landing_pad_block),
    });
    func.add_edge(call_block, landing_pad_block);
}

/// Replicate `Pipeline::run_frame_lowering` on `func` (in place) and return the
/// resulting block offsets and the byte offset of the `cxx_throw` BL.
///
/// This mirrors the private `run_frame_lowering` exactly (same public frame
/// helpers in the same order), so the offsets it produces are identical to the
/// ones the real emit path computes when it lowers the same function. We use it
/// on a throwaway clone purely to learn the offsets needed for the LSDA.
fn frame_lower_and_measure(
    mut func: IrMachFunction,
) -> (std::collections::HashMap<BlockId, u32>, u32) {
    frame::ensure_stack_protector_slot(&mut func);
    let outgoing = frame::compute_max_outgoing_arg_size(&func);
    let layout = if frame::function_has_runtime_stack_slots(&func) {
        frame::compute_frame_layout_dynamic(&func, outgoing, true)
    } else {
        frame::compute_frame_layout(&func, outgoing, true)
    };
    frame::eliminate_frame_indices(&mut func, &layout);
    frame::insert_prologue_epilogue(&mut func, &layout).expect("prologue/epilogue");
    pipeline::resolve_branches(&mut func).expect("valid EH function must resolve branches");

    let (_code, fixups, block_offsets) =
        encode_function_with_fixups_and_blocks(&func).expect("encode probe");

    // The cxx_throw BL is the call site that may throw. Its fixup offset is the
    // byte position of that BL within the function.
    use trust_cg_codegen::macho::fixup::FixupTarget;
    let throw_off = fixups
        .iter()
        .find(|f| matches!(&f.target, FixupTarget::NamedSymbol(n) if n == "cxx_throw"))
        .map(|f| f.offset)
        .expect("cxx_throw BL must produce a Branch26 fixup");

    (block_offsets, throw_off)
}

#[test]
fn e2e_aarch64_eh_catch_all_link_and_run() {
    if !host_is_aarch64_macos() {
        eprintln!("SKIP: backend EH catch e2e requires an aarch64-apple-darwin host");
        return;
    }

    // 1) Build the function and measure real post-frame-lowering offsets.
    let func = build_tc_try();
    let (block_offsets, throw_off) = frame_lower_and_measure(func.clone());

    let lpad_off = *block_offsets
        .get(&BlockId(1))
        .expect("landing-pad block offset");

    // 2) Attach EH metadata referencing the measured offsets.
    //
    // The call-site region covers exactly the throwing BL (4 bytes on AArch64).
    // The Itanium personality matches a faulting PC against [start, start+len)
    // and, on a hit with a landing pad + catch action, transfers to the pad.
    let mut func = func;
    attach_tc_try_eh_metadata(&mut func, lpad_off, throw_off, 4);

    // 3) Emit the Mach-O .o through the standard single-function path (LSDA +
    //    compact unwind included). `encode_and_emit` frame-lowers the function
    //    again deterministically, so the offsets we attached stay valid.
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        ..Default::default()
    });
    let obj = pipeline
        .encode_and_emit(&mut func)
        .expect("encode_and_emit tc_try with EH metadata");

    assert_eq!(
        u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]),
        0xFEED_FACF,
        "valid Mach-O"
    );
    assert!(
        obj.windows(b"__gcc_except_tab".len())
            .any(|w| w == b"__gcc_except_tab"),
        "object must carry the LSDA section"
    );

    // 4) Write the .o, a C++ driver that throws, link with cc, run under a
    //    HARD timeout, and assert the catch was observed.
    let dir = std::env::temp_dir().join("trust_cg_eh_catch_e2e");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    let obj_path = dir.join("tc_try.o");
    fs::write(&obj_path, &obj).expect("write .o");

    let driver_path = dir.join("driver.cpp");
    fs::write(
        &driver_path,
        r#"
#include <cstdio>
extern "C" int tc_try();
extern "C" void cxx_throw() { throw 7; }
int main() {
    int r = tc_try();
    printf("tc_try returned %d\n", r);
    return r == 42 ? 0 : 1;
}
"#,
    )
    .expect("write driver");

    let bin_path = dir.join("eh_catch_bin");
    // Link with the C++ driver via `c++` so libc++/libc++abi (the personality
    // routine `___gxx_personality_v0`, `__cxa_*`, and `typeinfo for int`) are
    // pulled in. `cc` would leave those undefined.
    let link = Command::new("c++")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("c++ available");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    // Run under a hard timeout so a broken/hung unwinder fails fast.
    let (exit_code, stdout, stderr, timed_out) =
        run_with_timeout(&bin_path, Duration::from_secs(10));

    assert!(
        !timed_out,
        "tc_try HUNG (timed out) — the catch path did not return. \
         A hang here means the unwinder never resolved the landing pad. \
         stdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected a clean catch (exit 0, sentinel 42). \
         exit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("tc_try returned 42"),
        "expected the catch sentinel in stdout. stdout: {stdout}\nstderr: {stderr}"
    );

    eprintln!("EH catch e2e PASSED: {}", stdout.trim());
    let _ = fs::remove_dir_all(&dir);
}

/// ELF twin of the Mach-O catch e2e OBJECT stage: emit `tc_try` for
/// `aarch64-unknown-linux-gnu` through the standard single-function path and
/// assert the `.eh_frame`/`.gcc_except_table`/personality structure. The
/// LINK+RUN half needs a Linux aarch64 host (glibc + libstdc++ personality);
/// set `TCG_ELF_EH_DUMP=<dir>` to write `tc_try_elf.o` + `driver.cpp` for an
/// external runner (e.g. a Linux container):
///
/// ```text
/// g++ driver.cpp tc_try_elf.o -o eh_bin && ./eh_bin   # expect "tc_try returned 42"
/// ```
#[test]
fn e2e_aarch64_elf_eh_catch_object_emit() {
    // 1) Same function + measured offsets as the Mach-O e2e.
    let func = build_tc_try();
    let (block_offsets, throw_off) = frame_lower_and_measure(func.clone());
    let lpad_off = *block_offsets
        .get(&BlockId(1))
        .expect("landing-pad block offset");
    let mut func = func;
    attach_tc_try_eh_metadata(&mut func, lpad_off, throw_off, 4);

    // 2) Emit through the standard single-function path, ELF target.
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        target_triple: "aarch64-unknown-linux-gnu".to_string(),
        ..Default::default()
    });
    let obj = pipeline
        .encode_and_emit(&mut func)
        .expect("encode_and_emit tc_try for the ELF target");

    let contains = |needle: &[u8]| obj.windows(needle.len()).any(|w| w == needle);
    assert_eq!(&obj[..4], b"\x7fELF", "valid ELF");
    assert!(contains(b".eh_frame"), "object must carry .eh_frame");
    assert!(
        contains(b".gcc_except_table"),
        "object must carry the LSDA section"
    );
    assert!(
        contains(b"__gxx_personality_v0"),
        "object must reference the C++ personality (ELF spelling)"
    );

    // 3) Optional dump for the Linux link+run stage.
    if let Ok(dir) = std::env::var("TCG_ELF_EH_DUMP") {
        let dir = std::path::PathBuf::from(dir);
        fs::create_dir_all(&dir).expect("create dump dir");
        fs::write(dir.join("tc_try_elf.o"), &obj).expect("write ELF .o");
        fs::write(
            dir.join("driver.cpp"),
            r#"
#include <cstdio>
extern "C" int tc_try();
extern "C" void cxx_throw() { throw 7; }
int main() {
    int r = tc_try();
    printf("tc_try returned %d\n", r);
    return r == 42 ? 0 : 1;
}
"#,
        )
        .expect("write driver");
        eprintln!("ELF EH catch object dumped to {}", dir.display());
    }
}

// ---------------------------------------------------------------------------
// Whole-module unwind tables (EH A64 Lane 5 — the x86 FUZZ-7 [TCG-EH-WALK]
// analogue): a multi-function module in which one function carries EH
// structure must give EVERY function an unwind entry, and the uncovered
// shapes must FAIL CLOSED (never a silent table drop).
// ---------------------------------------------------------------------------

/// Build a plain `int forty() { return 40; }` MachIR function — the no-pad
/// walk-through frame of the multi-function EH module tests.
fn build_forty() -> IrMachFunction {
    let sig = IrSignature::new(vec![], vec![Type::I32]);
    let mut func = IrMachFunction::new("forty".to_string(), sig);
    let entry = func.entry;
    let mov = func.push_inst(IrMachInst::new(
        IrOpcode::MovI,
        vec![IrOperand::PReg(X0), IrOperand::Imm(40)],
    ));
    func.append_inst(entry, mov);
    let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
    func.append_inst(entry, ret);
    func
}

/// `tc_try` with EH metadata attached in the UNRESOLVED (pre-layout) form the
/// real ISel produces: byte offsets left 0, blocks named — the module encode
/// path resolves them post-layout (`resolve_eh_offsets`).
fn build_tc_try_with_unresolved_eh() -> IrMachFunction {
    let mut func = build_tc_try();
    // Zero offsets are the unresolved form; the module encoder fills them from
    // final instruction and block layout before emitting the LSDA.
    attach_tc_try_eh_metadata(&mut func, 0, 0, 0);
    func
}

#[test]
fn tc_try_unwind_edge_has_exact_reciprocal_cfg_metadata() {
    let func = build_tc_try_with_unresolved_eh();

    assert_eq!(func.block(BlockId(0)).succs, vec![BlockId(1)]);
    assert_eq!(func.block(BlockId(1)).preds, vec![BlockId(0)]);
}

/// Replicate `Pipeline::run_frame_lowering` in place (same public frame
/// helpers in the same order) and return the layout, leaving `func` in the
/// post-frame-lowering, branch-resolved state `compile_module` expects.
fn frame_lower_in_place(func: &mut IrMachFunction) -> frame::FrameLayout {
    frame::ensure_stack_protector_slot(func);
    let outgoing = frame::compute_max_outgoing_arg_size(func);
    let layout = if frame::function_has_runtime_stack_slots(func) {
        frame::compute_frame_layout_dynamic(func, outgoing, true)
    } else {
        frame::compute_frame_layout(func, outgoing, true)
    };
    frame::eliminate_frame_indices(func, &layout);
    frame::insert_prologue_epilogue(func, &layout).expect("prologue/epilogue");
    pipeline::resolve_branches(func).expect("valid EH function must resolve branches");
    layout
}

/// The generic module emitter emits WHOLE-MODULE unwind tables for an
/// EH-carrying multi-function aarch64 Mach-O module: one 32-byte
/// `__LD,__compact_unwind` entry per function (EH fn + plain walk-through
/// frame) and the EH function's LSDA.
#[test]
fn eh_module_emits_compact_unwind_entry_for_every_function() {
    let mut eh_func = build_tc_try_with_unresolved_eh();
    let eh_layout = frame_lower_in_place(&mut eh_func);
    let mut plain_func = build_forty();
    let plain_layout = frame_lower_in_place(&mut plain_func);

    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        ..Default::default()
    });
    let obj = pipeline
        .compile_module_with_globals_and_layouts(
            &[eh_func, plain_func],
            &[],
            &[Some(eh_layout), Some(plain_layout)],
        )
        .expect("multi-function EH module must compile with whole-module unwind tables");

    assert_eq!(
        u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]),
        0xFEED_FACF,
        "valid Mach-O"
    );
    assert!(
        obj.windows(16).any(|w| w == b"__compact_unwind".as_slice()),
        "module must carry __LD,__compact_unwind"
    );
    assert!(
        obj.windows(16).any(|w| w == b"__gcc_except_tab".as_slice()),
        "module must carry the EH function's LSDA"
    );
    // Exactly one 32-byte entry per function: locate the section_64 header
    // (sectname at +0, size u64 at +40) and check its size.
    let pos = obj
        .windows(16)
        .position(|w| w == b"__compact_unwind".as_slice())
        .unwrap();
    let size = u64::from_le_bytes(obj[pos + 40..pos + 48].try_into().unwrap());
    assert_eq!(
        size, 64,
        "expected 2 compact unwind entries (32 bytes each)"
    );
}

/// Missing frame layouts (the legacy `compile_module` call shape) FAIL CLOSED
/// for an EH-carrying module: without a layout a function would get NO unwind
/// entry — an unwalkable frame — so the emitter must reject, not drop.
#[test]
fn eh_module_without_frame_layouts_fails_closed() {
    let mut eh_func = build_tc_try_with_unresolved_eh();
    let _ = frame_lower_in_place(&mut eh_func);
    let mut plain_func = build_forty();
    let _ = frame_lower_in_place(&mut plain_func);

    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        ..Default::default()
    });
    let err = pipeline
        .compile_module(&[eh_func, plain_func])
        .expect_err("EH module without frame layouts must FAIL CLOSED");
    let msg = format!("{err}");
    assert!(
        msg.contains("no frame layout") && msg.contains("unwind"),
        "diagnostic must name the missing layout + unwind consequence, got: {msg}"
    );
}

/// An EH-carrying module headed for ELF emits whole-module `.eh_frame` unwind
/// tables (an FDE per function, LSDAs in `.gcc_except_table`), mirroring the
/// Mach-O whole-module unwind policy.
#[test]
fn eh_module_elf_target_emits_eh_frame() {
    let mut eh_func = build_tc_try_with_unresolved_eh();
    let eh_layout = frame_lower_in_place(&mut eh_func);
    let mut plain_func = build_forty();
    let plain_layout = frame_lower_in_place(&mut plain_func);

    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        target_triple: "aarch64-unknown-linux-gnu".to_string(),
        ..Default::default()
    });
    let obj = pipeline
        .compile_module_with_globals_and_layouts(
            &[eh_func, plain_func],
            &[],
            &[Some(eh_layout), Some(plain_layout)],
        )
        .expect("EH module on an ELF target must emit whole-module unwind tables");
    let contains = |needle: &[u8]| obj.windows(needle.len()).any(|w| w == needle);
    assert_eq!(&obj[..4], b"\x7fELF");
    assert!(contains(b".eh_frame"), "missing .eh_frame section");
    assert!(
        contains(b".gcc_except_table"),
        "missing .gcc_except_table (real + filler LSDAs)"
    );
    assert!(
        contains(b"__gxx_personality_v0"),
        "missing ELF personality symbol (fixture uses the C++ personality)"
    );
}

/// Run `bin` with a hard wall-clock timeout. Returns
/// `(exit_code, stdout, stderr, timed_out)`. On timeout the child is killed.
fn run_with_timeout(
    bin: &std::path::Path,
    timeout: Duration,
) -> (Option<i32>, String, String, bool) {
    use std::io::Read;

    let mut child = Command::new(bin)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn EH binary");

    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let mut out = String::new();
                let mut err = String::new();
                if let Some(mut s) = child.stdout.take() {
                    let _ = s.read_to_string(&mut out);
                }
                if let Some(mut s) = child.stderr.take() {
                    let _ = s.read_to_string(&mut err);
                }
                return (status.code(), out, err, false);
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return (None, String::new(), String::new(), true);
                }
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(e) => panic!("waiting on EH binary failed: {e}"),
        }
    }
}
