// E2E (x86_64-apple-darwin): the x86-64 macOS exception-handling CATCH path,
// end to end, RUN NATIVELY. [EH Lane 3]
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the x86 backend EH runtime milestone: a function compiled by trust-cg
// that CALLs a C++ callee which THROWS, catches the exception at a landing pad
// (`catch(...)`), reports a sentinel, and EXITS cleanly. It exercises the full
// host unwinding path that EH x86 Lane 2 emits:
//
//   * the zPLR `__eh_frame` CIE (personality `___gxx_personality_v0`, GOT-indirect
//     `0x9b` encoding) + FDE-with-LSDA,
//   * the `__gcc_except_tab` LSDA (call-site table + catch-all action),
//   * the `X86_64_RELOC_GOT` personality relocation (whose field-END pcrel bias
//     the FDE addend must account for — the EH Lane 3 addend concern), and
//   * the landing-pad control transfer.
//
// If the personality relocation resolved to garbage, libunwind would call a bad
// personality and `std::terminate()` (abort) instead of catching. A clean
// `exit(0)` / "returned 42" therefore PROVES the personality reloc + LSDA are
// wired correctly at runtime, not just structurally.
//
// x86_64 is the HOST here, so the binary runs directly (mirrors the AArch64
// `e2e_aarch64_eh_catch` catch milestone, which runs on an aarch64 host).
//
// SAFETY: the produced binary is ALWAYS run under a hard timeout so a broken
// catch (which would loop / abort / hang in the unwinder) becomes a fast,
// diagnosable failure instead of a hang.
//
// Built at the x86 ISel (`X86ISelFunction`) level because trust-ir (the frontend
// IR) does not model exceptions and the Rust frontend cannot yet compile a
// cleanup-bearing frame on x86 (its only droppable types — Box/Vec/String —
// require alloc internals the x86 backend fails closed on). This test drives the
// SAME emit path (`X86Pipeline::compile_module`, which emits the LSDA + zPLR FDE
// + personality) the bridge would, so it validates the Lane 2 emission at
// runtime independently of that frontend gap.

use std::fs;
use std::process::Command;
use std::time::Duration;

use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs;
use trust_cg_lower::function::{EhCallSite, EhFunctionInfo, EhLandingPad, Signature};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};

fn host_is_x86_64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "x86_64"))
}

/// How to RUN the emitted x86_64-apple-darwin binary on this host, or `None`
/// if it cannot be run here (SKIP).
///
///  * x86_64 macOS host  -> native, no prefix.
///  * arm64 macOS host    -> Rosetta 2: `arch -x86_64 <bin>` transparently runs
///    an x86_64 Mach-O. Probe `arch -x86_64 true` once so a machine WITHOUT
///    Rosetta SKIPs cleanly instead of hard-failing.
///
/// This is what turns the x86 EH catch from a structural (host-gated, never-run)
/// fixture into an EXECUTED catch on an arm64 developer machine — the object is
/// always cross-emitted for x86_64 by `X86Pipeline`, only the run needed a host.
fn x86_64_run_prefix() -> Option<Vec<String>> {
    if host_is_x86_64_macos() {
        return Some(vec![]);
    }
    if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        let rosetta_ok = Command::new("arch")
            .args(["-x86_64", "true"])
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false);
        if rosetta_ok {
            return Some(vec!["arch".to_string(), "-x86_64".to_string()]);
        }
    }
    None
}

/// Build the `tc_try_x86` function:
///
/// ```text
/// extern "C" int tc_try_x86() {
///   try   { cxx_throw(); return 0; }   // bb0 (entry) — the call + normal path
///   catch (...) { return 42; }          // bb1 (landing pad)
/// }
/// ```
///
/// bb0:  CALL cxx_throw          ; may throw -> unwinder may divert to bb1
///       MOV RAX, 0              ; normal path: return 0
///       RET
/// bb1:  MOV RDI, RAX            ; exn pointer (RAX, Itanium eh regno 0) -> arg0
///       CALL __cxa_begin_catch
///       CALL __cxa_end_catch
///       MOV RAX, 42            ; caught: return the sentinel 42
///       RET
fn build_tc_try_x86() -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let mut func = X86ISelFunction::new("tc_try_x86".to_string(), sig);
    let entry = Block(0);
    let pad = Block(1);
    func.ensure_block(entry);
    func.ensure_block(pad);
    func.blocks.get_mut(&entry).unwrap().successors = vec![pad];

    // --- bb0: the throwing call + normal (no-exception) path ---
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("cxx_throw".to_string())],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::Imm(0),
            ],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));

    // --- bb1: the catch-all landing pad ---
    // The unwinder installs the exception object in RAX (Itanium eh data regno 0)
    // before transferring here; move it to RDI (arg0) for __cxa_begin_catch.
    func.push_inst(
        pad,
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RDI),
                X86ISelOperand::PReg(x86_64_regs::RAX),
            ],
        ),
    );
    func.push_inst(
        pad,
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("__cxa_begin_catch".to_string())],
        ),
    );
    func.push_inst(
        pad,
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("__cxa_end_catch".to_string())],
        ),
    );
    func.push_inst(
        pad,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::Imm(42),
            ],
        ),
    );
    func.push_inst(pad, X86ISelInst::new(X86Opcode::Ret, vec![]));

    // --- EH metadata: catch-all landing pad + call-site over the throwing block ---
    func.eh_info = EhFunctionInfo {
        personality: Some("__gxx_personality_v0".to_string()),
        landing_pads: vec![EhLandingPad {
            block: pad,
            catch_type_indices: vec![0], // 0 == catch-all (catch(...))
            is_cleanup: false,
        }],
        call_sites: vec![EhCallSite {
            call_block: entry,
            landing_pad_block: pad,
        }],
    };
    func
}

#[test]
fn e2e_x86_64_eh_catch_all_link_and_run() {
    let Some(run_prefix) = x86_64_run_prefix() else {
        eprintln!(
            "SKIP: x86 backend EH catch e2e needs an x86_64-apple-darwin host \
             or an arm64 macOS host with Rosetta 2"
        );
        return;
    };
    if Command::new("c++").arg("--version").output().is_err() {
        eprintln!("SKIP: c++ (clang) not available");
        return;
    }

    // 1) Build the function and emit the Mach-O .o through the standard module
    //    path (LSDA + zPLR FDE + personality). compile_module SUCCEEDING is
    //    itself the ENC-EHDC decode-check round-trip proof.
    let func = build_tc_try_x86();
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        emit_frame: true,
        output_format: X86OutputFormat::MachO,
        ..X86PipelineConfig::default()
    });
    let obj = pipeline
        .compile_module(&[func])
        .expect("compile_module tc_try_x86 with EH metadata");

    assert_eq!(
        u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]),
        0xFEED_FACF,
        "valid 64-bit Mach-O"
    );
    assert!(
        obj.windows(b"__gcc_except_tab".len())
            .any(|w| w == b"__gcc_except_tab"),
        "object must carry the LSDA section"
    );
    assert!(
        obj.windows(b"__eh_frame".len()).any(|w| w == b"__eh_frame"),
        "object must carry the __eh_frame section"
    );

    // 2) Write the .o, a C++ driver that throws, link with c++, run under a HARD
    //    timeout, and assert the catch was observed (sentinel 42, clean exit).
    let dir = std::env::temp_dir().join("trust_cg_x86_eh_catch_e2e");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    let obj_path = dir.join("tc_try_x86.o");
    fs::write(&obj_path, &obj).expect("write .o");

    let driver_path = dir.join("driver.cpp");
    fs::write(
        &driver_path,
        r#"
#include <cstdio>
extern "C" int tc_try_x86();
extern "C" void cxx_throw() { throw 7; }
int main() {
    int r = tc_try_x86();
    printf("tc_try_x86 returned %d\n", r);
    return r == 42 ? 0 : 1;
}
"#,
    )
    .expect("write driver");

    let bin_path = dir.join("eh_catch_bin");
    // Link with `c++` so libc++/libc++abi (___gxx_personality_v0, __cxa_*,
    // typeinfo) are pulled in. `cc` would leave those undefined. `-arch x86_64`
    // forces the x86_64 slice even when the host toolchain defaults to arm64
    // (harmless on a native x86_64 host); the emitted `.o` is x86_64 regardless.
    let link = Command::new("c++")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
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

    let (exit_code, stdout, stderr, timed_out) =
        run_with_timeout(&bin_path, &run_prefix, Duration::from_secs(10));

    assert!(
        !timed_out,
        "tc_try_x86 HUNG (timed out) — the catch path did not return. A hang \
         means the unwinder never resolved the landing pad.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected a clean catch (exit 0, sentinel 42). A non-zero/abort here means \
         the personality reloc or LSDA is wrong (libunwind called a bad personality \
         or found no handler).\nexit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("tc_try_x86 returned 42"),
        "expected the catch sentinel in stdout.\nstdout: {stdout}\nstderr: {stderr}"
    );

    eprintln!("x86 EH catch e2e PASSED: {}", stdout.trim());
    let _ = fs::remove_dir_all(&dir);
}

/// Run `bin` (optionally under `prefix`, e.g. `["arch", "-x86_64"]` for Rosetta)
/// with a hard wall-clock timeout. Returns `(exit_code, stdout, stderr,
/// timed_out)`. On timeout the child is killed.
fn run_with_timeout(
    bin: &std::path::Path,
    prefix: &[String],
    timeout: Duration,
) -> (Option<i32>, String, String, bool) {
    use std::io::Read;

    let mut command = if let Some((launcher, rest)) = prefix.split_first() {
        let mut c = Command::new(launcher);
        c.args(rest);
        c.arg(bin);
        c
    } else {
        Command::new(bin)
    };
    let mut child = command
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
                std::thread::sleep(Duration::from_millis(25));
            }
            Err(_) => return (None, String::new(), String::new(), false),
        }
    }
}
