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
// Execution uses a polling deadline and nonblocking termination requests.
// Kernel-blocked children can survive a timeout; host cleanup is not guaranteed.
//
// Hand-authored at the MachIR (`trust_cg_ir::MachFunction`) level to isolate
// backend EH emission. The separate trust-ir fixtures exercise its
// `Invoke`/`LandingPad`/`Resume` lowering. We build post-regalloc MachIR directly,
// populate the
// EH metadata from the *real* post-frame-lowering byte offsets, and emit via
// the standard single-function Mach-O path (which emits the LSDA + compact
// unwind).

mod common;

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

#[path = "common/native_host.rs"]
mod native_host;

/// AArch64 Linux GNU (ELF: `.eh_frame` + `.gcc_except_table`, libstdc++) or
/// macOS (Mach-O: compact unwind + `__gcc_except_tab`, libc++abi) can link
/// and run the EH object with the host `c++`.
fn host_can_link_and_run_aarch64_eh() -> bool {
    native_host::NATIVE
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

    // The AArch64 authority gate requires a `Ret` to carry EXACTLY the ABI
    // return-register implicit-use alias set that production ISel attaches via
    // `AppleAArch64ABI::required_return_pregs(&sig_returns)`. This signature
    // returns [I32], which classifies to `Reg(X0)`, so the required set is
    // exactly {X0}. A bare `Ret` is malformed IR, not a shorthand.
    let ret0 = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]).with_implicit_uses(&[X0]));
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

    let ret42 = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]).with_implicit_uses(&[X0]));
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
    frame::ensure_stack_protector_slot(&mut func).unwrap();
    let outgoing = frame::compute_max_outgoing_arg_size(&func);
    let layout = if frame::function_has_runtime_stack_slots(&func) {
        frame::compute_frame_layout_dynamic(&func, outgoing, true)
    } else {
        frame::compute_frame_layout(&func, outgoing, true)
    };
    frame::eliminate_frame_indices(&mut func, &layout).unwrap();
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
    if !host_can_link_and_run_aarch64_eh() {
        eprintln!("SKIP: backend EH catch e2e requires an AArch64 Linux GNU or macOS host");
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

    // 3) Emit the host's .o through the standard single-function path (LSDA
    //    plus compact unwind on Mach-O, `.eh_frame` on ELF). `encode_and_emit`
    //    frame-lowers the function again deterministically, so the offsets we
    //    attached stay valid.
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        ..PipelineConfig::for_target(native_host::TRIPLE)
    });
    let obj = pipeline
        .encode_and_emit(&mut func)
        .expect("encode_and_emit tc_try with EH metadata");

    native_host::assert_native_object(&obj);
    let lsda: &[u8] = if native_host::DARWIN {
        b"__gcc_except_tab"
    } else {
        b".gcc_except_table"
    };
    assert!(
        obj.windows(lsda.len()).any(|w| w == lsda),
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

    // Bound process polling without blocking on termination/reaping afterward.
    let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
        &bin_path,
        common::rosetta::exec_timeout(Duration::from_secs(10)),
    );

    assert!(
        !timed_out,
        "tc_try exceeded its polling deadline. This does not isolate an \
         unwinder defect from a loader, translation, or host failure. \
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
/// LINK+RUN half is `e2e_aarch64_eh_catch_all_link_and_run` on an AArch64
/// Linux GNU host (glibc + libstdc++ personality); set `TCG_ELF_EH_DUMP=<dir>`
/// to also write `tc_try_elf.o` + `driver.cpp` for an external runner:
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
    // Returns [I32] -> ABI return-register alias set is exactly {X0}.
    let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]).with_implicit_uses(&[X0]));
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
    frame::ensure_stack_protector_slot(func).unwrap();
    let outgoing = frame::compute_max_outgoing_arg_size(func);
    let layout = if frame::function_has_runtime_stack_slots(func) {
        frame::compute_frame_layout_dynamic(func, outgoing, true)
    } else {
        frame::compute_frame_layout(func, outgoing, true)
    };
    frame::eliminate_frame_indices(func, &layout).unwrap();
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
        ..PipelineConfig::for_target("aarch64-apple-darwin")
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
        ..PipelineConfig::for_target("aarch64-apple-darwin")
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

#[cfg(unix)]
#[path = "common/direct_timeout_contract.rs"]
mod direct_timeout_contract;

#[cfg(unix)]
#[test]
fn eh_supervisor_preserves_direct_status_and_timeout_observations() {
    direct_timeout_contract::check(run_with_timeout);
}

/// Preserve direct-child exit codes with the shared polling/termination boundary.
/// A timeout requests termination; it does not guarantee child/host cleanup.
fn run_with_timeout(
    bin: &std::path::Path,
    timeout: Duration,
) -> (Option<i32>, String, String, bool) {
    let result = common::rosetta::command_output_with_timeout(&mut Command::new(bin), timeout)
        .expect("run supervised EH binary");
    (
        if result.timed_out {
            None
        } else {
            result.output.status.code()
        },
        String::from_utf8_lossy(&result.output.stdout).into_owned(),
        String::from_utf8_lossy(&result.output.stderr).into_owned(),
        result.timed_out,
    )
}

/// Write `tc_try`'s ELF object (`tc_try.o`, its CIE `zPLR`) and a C++
/// `driver.o` that calls it and throws through it into `dir`, and return
/// the `cc` drivers to link them with: GNU ld's `cc`, and shims that link
/// through LLD and gold when they are installed (`SKIP:` otherwise, unless
/// `TCG_REQUIRE_LLD` or `TCG_REQUIRE_GOLD` is set).
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn eh_window_inputs(dir: &std::path::Path) -> Vec<(&'static str, String)> {
    use std::path::{Path, PathBuf};

    let func = build_tc_try();
    let (block_offsets, throw_off) = frame_lower_and_measure(func.clone());
    let lpad_off = *block_offsets
        .get(&BlockId(1))
        .expect("landing-pad block offset");
    let mut func = func;
    attach_tc_try_eh_metadata(&mut func, lpad_off, throw_off, 4);
    let obj = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        target_triple: "aarch64-unknown-linux-gnu".to_string(),
        ..Default::default()
    })
    .encode_and_emit(&mut func)
    .expect("encode_and_emit tc_try for the ELF target");

    fs::write(dir.join("tc_try.o"), &obj).unwrap();
    fs::write(
        dir.join("driver.cpp"),
        "#include <cstdio>\nextern \"C\" int tc_try();\nextern \"C\" void cxx_throw() { throw 7; \
         }\nint main() {\n    int r = tc_try();\n    printf(\"tc_try returned %d\\n\", r);\n    \
         return r == 42 ? 0 : 1;\n}\n",
    )
    .unwrap();
    let compiled = Command::new("c++")
        .current_dir(dir)
        .args(["-c", "-O1", "-o", "driver.o", "driver.cpp"])
        .output()
        .expect("c++ available");
    assert!(compiled.status.success(), "{compiled:?}");

    // `cc` shims that link through LLD and gold, written from a child shell
    // (no writable descriptor to the script stays in this process).
    let shim = |name: &str, flags: String| -> String {
        let path = dir.join(name);
        let status = Command::new("/bin/sh")
            .arg("-c")
            .arg("printf '%s\\n' \"$2\" > \"$1\" && chmod 755 \"$1\"")
            .arg("sh")
            .arg(&path)
            .arg(format!("#!/bin/sh\nexec cc {flags} \"$@\""))
            .status()
            .unwrap();
        assert!(status.success());
        path.display().to_string()
    };
    let on_path = |tool: &str| -> Option<PathBuf> {
        std::env::var_os("PATH")
            .and_then(|paths| std::env::split_paths(&paths).find(|dir| dir.join(tool).is_file()))
    };
    let mut linkers = vec![("gnu", "cc".to_string())];
    match std::env::var_os("TCG_LLD_DIR")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
        .filter(|dir| dir.join("ld.lld").is_file())
        .or_else(|| on_path("ld.lld"))
    {
        Some(lld) => linkers.push((
            "lld",
            shim("lld-cc.sh", format!("-fuse-ld=lld -B'{}/'", lld.display())),
        )),
        None => {
            assert!(std::env::var_os("TCG_REQUIRE_LLD").is_none(), "no ld.lld");
            eprintln!(
                "SKIP: no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH); the LLD legs did not run"
            );
        }
    }
    match on_path("ld.gold")
        .or_else(|| Some(PathBuf::from("/usr/bin")).filter(|dir| dir.join("ld.gold").is_file()))
    {
        Some(_) => linkers.push(("gold", shim("gold-cc.sh", "-fuse-ld=gold".to_string()))),
        None => {
            assert!(std::env::var_os("TCG_REQUIRE_GOLD").is_none(), "no ld.gold");
            eprintln!("SKIP: no ld.gold (PATH, /usr/bin); the gold legs did not run");
        }
    }

    linkers
}

/// The linked-image `.eh_frame` check on trust-cg's own `zPLR` output
/// (L02-P10): `tc_try`'s CIE reaches `DW.ref.__gxx_personality_v0` through a
/// `DW_EH_PE_indirect|pcrel|sdata4` personality pointer and its FDE reaches
/// its `.gcc_except_table` LSDA through a `DW_EH_PE_pcrel|sdata4` pointer,
/// both `R_AARCH64_PREL32`. With `.gcc_except_table` (and the data after it)
/// placed at `0xd0000000` and `.eh_frame` at `0x10000000`, GNU ld 2.42
/// refuses both relocations itself, while LLD 22.1.6 and gold 2.42 write
/// them in `[2^31, 2^32)` and their own programs die with SIGSEGV when the
/// exception is thrown. `run_link` refuses the LLD and gold images with one
/// `[TCG-LINK-EH-FRAME-WINDOW]` line for the two pointers, removes them and
/// leaves no output; the default placement links through every linker and
/// the catch returns 42. Without LLD or gold their legs print `SKIP:`.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[test]
fn eh_frame_personality_and_lsda_pointers_out_of_window_are_refused_by_run_link() {
    use std::os::unix::process::ExitStatusExt;
    use std::path::Path;
    use trust_cg_codegen::link_driver::{LinkDiagnosticKind, LinkError, LinkRequest, run_link};
    use trust_cg_codegen::target::TargetSpec;

    let directory = tempfile::tempdir().unwrap();
    let dir = directory.path();
    let linkers = eh_window_inputs(dir);

    let far: Vec<String> = [
        "--section-start=.eh_frame=0x10000000",
        "--section-start=.eh_frame_hdr=0x0fff0000",
        "--section-start=.text=0x10010000",
        "--section-start=.gcc_except_table=0xd0000000",
    ]
    .map(str::to_string)
    .to_vec();
    let request = |output: &str, placed: bool| {
        let mut request = LinkRequest::executable(
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
            vec![dir.join("tc_try.o"), dir.join("driver.o")],
            dir.join(output),
        );
        request.libs = vec!["stdc++".to_string()];
        if placed {
            request.linker_arg_groups = vec![far.clone()];
        }
        request
    };
    // The far programs are expected to fault. On a host whose core_pattern
    // pipes to a crash handler (Ubuntu's apport), the faulting child is held
    // until the handler has read its core, which under load can take longer
    // than a few seconds; the bound is for a hang, not for that.
    let run = |program: &Path| {
        common::rosetta::command_output_with_timeout(
            &mut Command::new(program),
            Duration::from_secs(120),
        )
        .expect("run the EH program")
        .output
    };
    for (name, driver) in &linkers {
        let output = format!("far_{name}");
        match run_link(&request(&output, true), driver) {
            Err(LinkError::Failed(failure)) if *name == "gnu" => {
                let named: Vec<_> = failure
                    .diagnostics
                    .iter()
                    .map(|d| (d.kind, d.subject.as_deref(), d.relocation.as_deref()))
                    .collect();
                assert_eq!(
                    named,
                    [
                        (
                            LinkDiagnosticKind::RelocationOutOfRange,
                            Some("DW.ref.__gxx_personality_v0"),
                            Some("R_AARCH64_PREL32")
                        ),
                        (
                            LinkDiagnosticKind::RelocationOutOfRange,
                            Some(".gcc_except_table"),
                            Some("R_AARCH64_PREL32")
                        )
                    ],
                    "{}",
                    failure.stderr
                );
            }
            Err(LinkError::OutputRefused {
                removed,
                diagnostics,
                ..
            }) if *name != "gnu" => {
                assert!(removed);
                assert_eq!(diagnostics.len(), 1, "{name}: {diagnostics:#?}");
                assert_eq!(
                    diagnostics[0].kind,
                    LinkDiagnosticKind::RelocationOutOfRange
                );
                assert_eq!(
                    diagnostics[0].relocation.as_deref(),
                    Some("R_AARCH64_PREL32")
                );
                assert!(
                    diagnostics[0].line.starts_with(&format!(
                        "[TCG-LINK-EH-FRAME-WINDOW] the linked output for {} is refused: 2 \
                         personality or LSDA pointers in its .eh_frame resolve outside allocated \
                         memory; the first, the personality pointer of the CIE at ",
                        dir.join(&output).display()
                    )),
                    "{name}: {}",
                    diagnostics[0].line
                );
            }
            other => panic!("{name}: unexpected far link result {other:?}"),
        }
        assert!(!dir.join(&output).exists(), "{name}");
        // The linker outside the driver installs it, and the throw faults.
        if *name != "gnu" {
            let args = [
                "-o".to_string(),
                format!("raw_{name}"),
                "tc_try.o".into(),
                "driver.o".into(),
                "-lstdc++".into(),
                "-Wl,-z,noexecstack".into(),
                format!("-Wl,{}", far.join(",")),
            ];
            let linked = Command::new(driver)
                .current_dir(dir)
                .args(&args)
                .output()
                .unwrap();
            assert!(linked.status.success(), "{name}: {linked:?}");
            let status = run(&dir.join(format!("raw_{name}"))).status;
            assert_eq!(status.signal(), Some(11), "{name}: {status:?}");
        }
        // The default placement links and the catch returns 42.
        let near = format!("near_{name}");
        run_link(&request(&near, false), driver).unwrap_or_else(|error| panic!("{name}: {error}"));
        let ran = run(&dir.join(&near));
        assert_eq!(ran.status.code(), Some(0), "{name}: {ran:?}");
        assert_eq!(String::from_utf8_lossy(&ran.stdout), "tc_try returned 42\n");
    }
}

/// The lowest `p_vaddr` of the `PT_LOAD` segments of the ELF64 image at
/// `path`.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn lowest_load_address(path: &std::path::Path) -> u64 {
    let image = fs::read(path).unwrap();
    let u64_at = |at: usize| u64::from_le_bytes(image[at..at + 8].try_into().unwrap());
    let u16_at = |at: usize| u16::from_le_bytes(image[at..at + 2].try_into().unwrap());
    let (phoff, size, count) = (u64_at(0x20) as usize, u16_at(0x36), u16_at(0x38));
    (0..usize::from(count))
        .map(|index| phoff + index * usize::from(size))
        .filter(|at| image[*at..*at + 4] == 1u32.to_le_bytes())
        .map(|at| u64_at(at + 16))
        .min()
        .expect("a PT_LOAD segment")
}

/// The L02-P10 closure audit at `43de0bebe`: the image check refused an
/// LSDA pointer only when it resolved outside allocated memory, but a
/// `PREL32` value in `[2^31, 2^32)` that LLD 22.1.6 writes truncated can
/// land in other allocated memory. With `tc_try`'s `.gcc_except_table`
/// moved alone (an `INSERT AFTER .bss` script) to 2^32 + 0x100 above the
/// image's first load segment, LLD installs a program whose LSDA pointer
/// gives an address in that segment, and the program dies when `cxx_throw`
/// throws (SIGSEGV in this position-independent executable; the audit's
/// `-no-pie` one aborted with "terminate called after throwing an instance
/// of 'int'"). `run_link` refuses the LLD image with one
/// `[TCG-LINK-EH-FRAME-UNPROVEN]` line (`unclassified`) naming the LSDA
/// pointer and its other address, removes it and leaves no output; GNU ld
/// 2.42 refuses the link itself, classified. The default placement links
/// and the catch returns 42. gold 2.42 reads no `INSERT` and moves the
/// sections after one given by `--section-start` with it, so it has no leg
/// here; `link_options`' `an_eh_frame_pointer_whose_bits_also_give_other_code_*`
/// covers gold. Without LLD its leg prints `SKIP:`.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[test]
fn an_lsda_pointer_whose_bits_also_give_allocated_memory_is_refused_by_run_link() {
    use std::os::unix::process::ExitStatusExt;
    use std::path::Path;
    use trust_cg_codegen::link_driver::{LinkDiagnosticKind, LinkError, LinkRequest, run_link};
    use trust_cg_codegen::target::TargetSpec;

    let directory = tempfile::tempdir().unwrap();
    let dir = directory.path();
    let linkers: Vec<(&str, String)> = eh_window_inputs(dir)
        .into_iter()
        .filter(|(name, _)| *name != "gold")
        .collect();
    let request = |output: &str, script: Option<&str>| {
        let mut request = LinkRequest::executable(
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
            vec![dir.join("tc_try.o"), dir.join("driver.o")],
            dir.join(output),
        );
        request.libs = vec!["stdc++".to_string()];
        if let Some(script) = script {
            request.linker_arg_groups = vec![vec!["-T".to_string(), script.to_string()]];
        }
        request
    };
    // The far programs are expected to fault. On a host whose core_pattern
    // pipes to a crash handler (Ubuntu's apport), the faulting child is held
    // until the handler has read its core, which under load can take longer
    // than a few seconds; the bound is for a hang, not for that.
    let run = |program: &Path| {
        common::rosetta::command_output_with_timeout(
            &mut Command::new(program),
            Duration::from_secs(120),
        )
        .expect("run the EH program")
        .output
    };
    for (name, driver) in &linkers {
        // The default placement links and the catch returns 42.
        let near = format!("near_{name}");
        run_link(&request(&near, None), driver).unwrap_or_else(|error| panic!("{name}: {error}"));
        let ran = run(&dir.join(&near));
        assert_eq!(ran.status.code(), Some(0), "{name}: {ran:?}");
        assert_eq!(String::from_utf8_lossy(&ran.stdout), "tc_try returned 42\n");
        // `.gcc_except_table` alone, 2^32 above the first load segment.
        let base = lowest_load_address(&dir.join(&near));
        let (lsda, alias) = ((1u64 << 32) + base + 0x100, base + 0x100);
        let script = format!("lsda_{name}.ld");
        fs::write(
            dir.join(&script),
            format!(
                "SECTIONS {{ .gcc_except_table {lsda:#x} : {{ *(.gcc_except_table \
                 .gcc_except_table.*) }} }} INSERT AFTER .bss;\n"
            ),
        )
        .unwrap();
        let script = dir.join(&script).display().to_string();
        let output = format!("far_{name}");
        match run_link(&request(&output, Some(&script)), driver) {
            Err(LinkError::Failed(failure)) if *name == "gnu" => {
                let named: Vec<_> = failure
                    .diagnostics
                    .iter()
                    .map(|d| (d.kind, d.subject.as_deref(), d.relocation.as_deref()))
                    .collect();
                assert_eq!(
                    named,
                    [(
                        LinkDiagnosticKind::RelocationOutOfRange,
                        Some(".gcc_except_table"),
                        Some("R_AARCH64_PREL32")
                    )],
                    "{}",
                    failure.stderr
                );
            }
            Err(LinkError::OutputRefused {
                removed,
                diagnostics,
                ..
            }) if *name == "lld" => {
                assert!(removed);
                assert_eq!(diagnostics.len(), 1, "{name}: {diagnostics:#?}");
                assert_eq!(diagnostics[0].kind, LinkDiagnosticKind::Unclassified);
                assert_eq!(
                    diagnostics[0].relocation.as_deref(),
                    Some("R_AARCH64_PREL32")
                );
                let line = &diagnostics[0].line;
                assert!(
                    line.starts_with(&format!(
                        "[TCG-LINK-EH-FRAME-UNPROVEN] the linked output for {} is refused \
                         because the check cannot show that 1 of its .eh_frame pointers name the \
                         address their linker was given: the first, the LSDA pointer of the FDE \
                         at ",
                        dir.join(&output).display()
                    )) && line.contains(&format!(
                        "and so gives {alias:#x}, but a linker writes the same bits truncated \
                         for {lsda:#x}, and both are in allocated memory"
                    )),
                    "{name}: {line}"
                );
            }
            other => panic!("{name}: unexpected far link result {other:?}"),
        }
        assert!(!dir.join(&output).exists(), "{name}");
        // LLD outside the driver installs it, and the throw aborts.
        if *name == "lld" {
            let raw = format!("raw_{name}");
            let linked = Command::new(driver)
                .current_dir(dir)
                .args([
                    "-o",
                    raw.as_str(),
                    "tc_try.o",
                    "driver.o",
                    "-lstdc++",
                    "-Wl,-z,noexecstack",
                    &format!("-Wl,-T,{script}"),
                ])
                .output()
                .unwrap();
            assert!(linked.status.success(), "{name}: {linked:?}");
            // The unwinder reads the first load segment as `tc_try`'s LSDA:
            // it faults, or finds no handler and aborts.
            let ran = run(&dir.join(&raw));
            assert!(
                matches!(ran.status.signal(), Some(6 | 11)) && ran.stdout.is_empty(),
                "{name}: {ran:?}"
            );
        }
    }
}
