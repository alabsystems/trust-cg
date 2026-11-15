// E2E (x86-64): the x86-64 exception-handling CATCH path, end to end, on both
// wired containers — ELF on x86-64 Linux GNU and Mach-O on x86-64 macOS (or
// through Rosetta on Apple Silicon).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the x86 backend EH runtime milestone: a function compiled by trust-cg
// that CALLs a C++ callee which THROWS, catches the exception at a landing pad
// (`catch(...)`), reports a sentinel, and EXITS cleanly. It exercises the full
// host unwinding path the x86 EH lane emits, in whichever container the host
// links:
//
//   Mach-O: the zPLR `__eh_frame` CIE (personality `___gxx_personality_v0`,
//   GOT-indirect `0x9b` encoding) + FDE-with-LSDA, the `__gcc_except_tab` LSDA,
//   and the `X86_64_RELOC_GOT` personality relocation whose field-END pcrel bias
//   the FDE addend must account for.
//
//   ELF: the zPLR `.eh_frame` CIE (personality `__gxx_personality_v0` reached
//   INDIRECTLY through the weak hidden `DW.ref.__gxx_personality_v0` slot, the
//   same `0x9b` encoding), an FDE-with-LSDA for every function, the
//   `.gcc_except_table` LSDA, and the ascending `R_X86_64_PC32` records that
//   resolve the pc-begin, LSDA and personality fields against local section
//   anchors.
//
// If the personality indirection resolved to garbage, libunwind/libgcc would
// call a bad personality and `std::terminate()` (abort) instead of catching; if
// `.rela.eh_frame` were not sorted by ascending offset, GNU ld would emit no
// `.eh_frame_hdr` and the unwinder would find no FDEs at all. A clean `exit(0)`
// / "returned 42" exercises the personality indirection and the LSDA at runtime
// for this fixture. It is not a proof of all unwind paths.
//
// HOST GATING IS COMPILE-TIME (`common/x86_64_native_host.rs`): the native row
// exists only on a host that links and runs x86-64 objects, so no runtime SKIP
// can be counted as a pass by a floor runner. The host-neutral rows below
// cross-emit BOTH containers on every host and check their unwind sections.
//
// The ELF rows carry four CONTROLS, so a run that exits 0 for some other reason
// cannot read as unwind evidence:
//
//   * GNU `readelf` reads the CIE, the FDE, the ascending `R_X86_64_PC32`
//     records and the slot's binding back out of the object — the reader whose
//     `.eh_frame` expectations GNU ld enforces at link time;
//   * dropping the covering LSDA call-site row's landing pad loses the catch;
//   * turning the CIE personality encoding from indirect (`0x9b`) to DIRECT
//     (`0x1b`) loses it too;
//   * two independent objects, each with its own COMDAT slot, both catch in one
//     link, and the object links as a SHARED object while the same object with
//     its personality record retargeted at `__gxx_personality_v0` directly is
//     refused by GNU ld — which is why the indirection exists.
//
// Built at the x86 ISel (`X86ISelFunction`) level to isolate backend EH metadata
// and object emission. `e2e_x86_64_eh_invoke_trust_ir_run` separately exercises
// the adapter through TrustIR Invoke/LandingPad; TrustIR does model exceptions.

#[cfg(any(
    all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "x86_64", target_os = "macos"),
))]
use std::{fs, process::Command, time::Duration};

mod common;
#[cfg(any(
    all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "x86_64", target_os = "macos"),
))]
use common::rosetta::run_executable_with_timeout;
use common::x86_64_native_host as host;

use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs;
use trust_cg_lower::function::{EhCallSite, EhFunctionInfo, EhLandingPad, Signature};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};

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
/// `name` is explicit so the cross-object control can put a SECOND EH function,
/// under a second name, in a SECOND object of the same link.
fn build_tc_try_x86(name: &str) -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let mut func = X86ISelFunction::new(name.to_string(), sig);
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

/// Compile `tc_try_x86` through the standard module path for `format`,
/// including its LSDA, zPLR FDE, personality and decode-check round trip.
fn compile_tc_try(format: X86OutputFormat) -> Vec<u8> {
    compile_tc_try_named(format, "tc_try_x86")
}

/// [`compile_tc_try`] for an explicitly named function.
fn compile_tc_try_named(format: X86OutputFormat, name: &str) -> Vec<u8> {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        emit_frame: true,
        output_format: format,
        ..X86PipelineConfig::default()
    });
    pipeline
        .compile_module(&[build_tc_try_x86(name)])
        .unwrap_or_else(|error| panic!("compile_module {name} for {format:?}: {error}"))
}

/// Host-neutral: BOTH wired containers carry the unwind bundle, each in its own
/// spelling, with the personality named the way its linker expects — Mach-O's
/// `_`-prefixed `___gxx_personality_v0` (the C name already starts with `__`)
/// and ELF's BARE `__gxx_personality_v0`, reached through the `DW.ref` slot the
/// zPLR CIE's indirect encoding names.
#[test]
fn eh_catch_x86_cross_emits_the_unwind_bundle_for_both_containers() {
    let macho = compile_tc_try(X86OutputFormat::MachO);
    host::assert_macho_x86_64_object(&macho);
    assert!(
        host::object_contains(&macho, b"__gcc_except_tab"),
        "the Mach-O object must carry the LSDA section"
    );
    assert!(
        host::object_contains(&macho, b"__eh_frame"),
        "the Mach-O object must carry the __eh_frame section"
    );
    assert!(
        host::object_contains(&macho, b"\x00___gxx_personality_v0\x00"),
        "Mach-O prefixes the personality symbol with `_`"
    );

    let elf = compile_tc_try(X86OutputFormat::Elf);
    host::assert_elf_x86_64_object(&elf);
    assert!(
        host::object_contains(&elf, b".gcc_except_table"),
        "the ELF object must carry the LSDA section"
    );
    assert!(
        host::object_contains(&elf, b".eh_frame"),
        "the ELF object must carry the .eh_frame section"
    );
    assert!(
        host::object_contains(&elf, b"\x00__gxx_personality_v0\x00"),
        "ELF names the personality BARE, with no container prefix"
    );
    assert!(
        host::object_contains(&elf, b"DW.ref.__gxx_personality_v0"),
        "the zPLR CIE's `DW_EH_PE_indirect` personality field names a DW.ref slot"
    );
}

// ---------------------------------------------------------------------------
// Independent GNU readback of the ELF unwind surface.
//
// The unit rows read the object back with trust-cg's own reparse reader; this
// one hands the same bytes to GNU `readelf`, the reader whose `.eh_frame`
// expectations GNU ld enforces at link time. `readelf` is a REQUIREMENT on a
// Linux GNU host, as in the AArch64 Linux EH controls — not a probe.
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
fn readelf(object: &std::path::Path, args: &[&str]) -> String {
    let output = Command::new(host::READELF)
        .args(args)
        .arg(object)
        .output()
        .unwrap_or_else(|error| panic!("{} is required on {}: {error}", host::READELF, host::HOST));
    assert!(
        output.status.success(),
        "readelf {args:?} failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
#[test]
fn eh_catch_x86_elf_unwind_surface_reads_back_through_gnu_readelf() {
    let dir = tempfile::Builder::new()
        .prefix("trust_cg_x86_eh_readelf_")
        .tempdir()
        .expect("create owned test dir");
    let obj_path = dir.path().join("tc_try_x86.o");
    fs::write(&obj_path, compile_tc_try(X86OutputFormat::Elf)).expect("write .o");

    // The CIE the GNU reader sees: zPLR, x86-64 factors, and the three encodings
    // the augmentation data carries in order — personality 0x9b
    // (indirect|pcrel|sdata4), LSDA 0x1b and FDE pointer 0x1b (pcrel|sdata4).
    let frames = readelf(&obj_path, &["--debug-dump=frames"]);
    for expected in [
        "Augmentation:          \"zPLR\"",
        "Code alignment factor: 1",
        "Data alignment factor: -8",
        "Return address column: 16",
        "DW_CFA_def_cfa: r7 (rsp) ofs 8",
        "DW_CFA_offset: r16 (rip) at cfa-8",
    ] {
        assert!(
            frames.contains(expected),
            "readelf did not report {expected:?}:\n{frames}"
        );
    }
    let cie_augmentation = frames
        .lines()
        .find_map(|line| line.trim().strip_prefix("Augmentation data:"))
        .map(|rest| rest.trim().to_owned())
        .expect("the CIE carries augmentation data");
    assert!(
        cie_augmentation.starts_with("9b "),
        "the personality encoding must be DW_EH_PE_indirect|pcrel|sdata4: \
         {cie_augmentation}"
    );
    assert!(
        cie_augmentation.ends_with(" 1b 1b"),
        "the LSDA and FDE pointer encodings must both be DW_EH_PE_pcrel|sdata4: \
         {cie_augmentation}"
    );
    // One FDE, whose pc range GNU resolved from the pc-begin relocation, and
    // whose own augmentation data is the LSDA pointer.
    let fdes: Vec<&str> = frames
        .lines()
        .filter(|line| line.contains(" FDE cie="))
        .collect();
    assert_eq!(fdes.len(), 1, "one FDE per function:\n{frames}");
    assert!(
        fdes[0].contains("pc=0000000000000000.."),
        "the FDE covers the function from .text offset 0: {}",
        fdes[0]
    );
    assert_eq!(
        frames.matches("Augmentation data:").count(),
        2,
        "the CIE's personality field and the FDE's LSDA field:\n{frames}"
    );

    // `.rela.eh_frame`: every record R_X86_64_PC32, in ASCENDING offset order.
    // GNU ld walks the section with one monotonically advancing relocation
    // cursor; out of order it reports "error in <obj>(.eh_frame); no
    // .eh_frame_hdr table will be created" and the unwinder then finds no FDEs
    // at run time.
    let relocs = readelf(&obj_path, &["-r"]);
    let eh_frame_rows: Vec<&str> = relocs
        .split("Relocation section '.rela.eh_frame'")
        .nth(1)
        .expect(".rela.eh_frame must exist")
        .lines()
        .skip(2)
        .take_while(|line| !line.trim().is_empty())
        .collect();
    assert_eq!(eh_frame_rows.len(), 3, "personality + pc-begin + LSDA");
    let mut previous: Option<u64> = None;
    for row in &eh_frame_rows {
        assert!(
            row.contains("R_X86_64_PC32"),
            "every .eh_frame relocation is PC32: {row}"
        );
        let offset =
            u64::from_str_radix(row.split_whitespace().next().unwrap(), 16).expect("hex r_offset");
        if let Some(previous) = previous {
            assert!(previous < offset, "ascending r_offset:\n{eh_frame_rows:?}");
        }
        previous = Some(offset);
    }
    assert!(
        eh_frame_rows[0].contains("DW.ref"),
        "the first (lowest-offset) record is the CIE personality field, naming \
         the DW.ref slot: {}",
        eh_frame_rows[0]
    );
    assert!(
        eh_frame_rows[1].contains(".text"),
        "the FDE pc-begin names the local .text anchor: {}",
        eh_frame_rows[1]
    );

    // The slot's own cell holds the personality's absolute address.
    assert!(
        relocs.contains("Relocation section '.rela.data.DW.ref.__gxx_personality_v0'"),
        "the DW.ref slot carries its own relocation section:\n{relocs}"
    );
    let slot_row = relocs
        .split("Relocation section '.rela.data.DW.ref.__gxx_personality_v0'")
        .nth(1)
        .unwrap()
        .lines()
        .nth(2)
        .unwrap();
    assert!(
        slot_row.contains("R_X86_64_64") && slot_row.contains("__gxx_personality_v0"),
        "the slot holds an absolute pointer to the personality: {slot_row}"
    );

    // The slot symbol GNU reads back: weak, hidden, 8-byte object, and its
    // section is a COMDAT group member so every object's copy coalesces.
    let symbols = readelf(&obj_path, &["-s"]);
    let slot = symbols
        .lines()
        .find(|line| line.contains("DW.ref.__gxx_per"))
        .expect("the DW.ref slot symbol");
    for expected in ["OBJECT", "WEAK", "HIDDEN"] {
        assert!(slot.contains(expected), "{expected} expected in: {slot}");
    }
    let sections = readelf(&obj_path, &["-S"]);
    assert!(
        sections.contains("GROUP"),
        "an external personality's slot lives in a GRP_COMDAT group:\n{sections}"
    );
    assert!(
        sections.contains(".gcc_except_table"),
        "the LSDA section:\n{sections}"
    );

    eprintln!(
        "x86-64 ELF EH surface read back by GNU readelf on {}",
        host::HOST
    );
}

// ---------------------------------------------------------------------------
// Native row: link with the host `c++` and observe the catch.
//
// COMPILE-TIME gated (see `common/x86_64_native_host.rs`). On a native host the
// `c++` driver is a REQUIREMENT: a missing one fails this row rather than
// printing a SKIP a floor runner would read as a pass.
// ---------------------------------------------------------------------------

#[cfg(any(
    all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "x86_64", target_os = "macos"),
))]
struct Run {
    exit_code: Option<i32>,
    stdout: String,
    stderr: String,
    timed_out: bool,
}

/// Write `object`, link it with the host `c++` against a throwing C++ driver,
/// and run the result under a hard timeout.
#[cfg(any(
    all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "x86_64", target_os = "macos"),
))]
fn link_and_run(label: &str, object: &[u8]) -> Run {
    let dir = tempfile::Builder::new()
        .prefix(&format!("trust_cg_x86_eh_catch_{label}_"))
        .tempdir()
        .expect("create owned test dir");
    let obj_path = dir.path().join("tc_try_x86.o");
    fs::write(&obj_path, object).expect("write .o");

    let driver_path = dir.path().join("driver.cpp");
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

    let bin_path = dir.path().join("eh_catch_bin");
    // Link with the host C++ driver so the C++ runtime (the personality,
    // `__cxa_*`, typeinfo) is pulled in: libstdc++/libgcc_s on GNU/Linux,
    // libc++/libc++abi on macOS. `cc` would leave those undefined.
    let link = Command::new(host::CXX_COMPILER)
        .args(host::cxx_link_args())
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .unwrap_or_else(|error| {
            panic!(
                "{} is required on {}, not optional: {error}",
                host::CXX_COMPILER,
                host::HOST
            )
        });
    assert!(
        link.status.success(),
        "link failed on {} for {label}:\n{}",
        host::HOST,
        String::from_utf8_lossy(&link.stderr)
    );

    // The supervising shell stays independently killable; waiting synchronously
    // on a stuck (possibly translated) child defeated the old helper's deadline
    // even after it sent SIGKILL.
    let run = run_executable_with_timeout(
        &bin_path,
        common::rosetta::exec_timeout(Duration::from_secs(10)),
    )
    .expect("supervise EH executable");
    Run {
        exit_code: run.output.status.code(),
        stdout: String::from_utf8_lossy(&run.output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&run.output.stderr).into_owned(),
        timed_out: run.timed_out,
    }
}

#[cfg(any(
    all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "x86_64", target_os = "macos"),
))]
#[test]
fn e2e_x86_64_eh_catch_all_link_and_run() {
    let format = if host::LINUX_GNU {
        X86OutputFormat::Elf
    } else {
        X86OutputFormat::MachO
    };
    let obj = compile_tc_try(format);
    host::assert_native_object(&obj);
    let (lsda_section, cfi_section) = host::eh_section_names();
    assert!(
        host::object_contains(&obj, lsda_section),
        "the {} object must carry the LSDA section",
        host::HOST
    );
    assert!(
        host::object_contains(&obj, cfi_section),
        "the {} object must carry the DWARF CFI section",
        host::HOST
    );

    let run = link_and_run("pristine", &obj);
    assert!(
        !run.timed_out,
        "tc_try_x86 timed out without a catch result; this does not distinguish \
         an unwind defect from loader/host failure.\nstdout: {}\nstderr: {}",
        run.stdout, run.stderr
    );
    assert_eq!(
        run.exit_code,
        Some(0),
        "expected a clean catch (exit 0, sentinel 42); inspect the loader and \
         unwind diagnostics.\nexit={:?}\nstdout: {}\nstderr: {}",
        run.exit_code,
        run.stdout,
        run.stderr
    );
    assert!(
        run.stdout.contains("tc_try_x86 returned 42"),
        "expected the catch sentinel in stdout.\nstdout: {}\nstderr: {}",
        run.stdout,
        run.stderr
    );

    eprintln!(
        "x86 EH catch e2e PASSED on {}: {}",
        host::HOST,
        run.stdout.trim()
    );
}

// ---------------------------------------------------------------------------
// Mutation controls (ELF): the catch above must come FROM the emitted tables,
// not past them.
//
// Each mutant changes ONE field of the emitted object, relinks, and must lose
// the catch. Without these, a fixture that happened to exit 0 for any other
// reason would read as unwind evidence.
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
fn elf_section_bytes(object: &[u8], name: &str) -> std::ops::Range<usize> {
    let u16_at = |at: usize| u16::from_le_bytes(object[at..at + 2].try_into().unwrap());
    let u32_at = |at: usize| u32::from_le_bytes(object[at..at + 4].try_into().unwrap());
    let u64_at = |at: usize| {
        usize::try_from(u64::from_le_bytes(object[at..at + 8].try_into().unwrap())).unwrap()
    };
    let shoff = u64_at(40);
    let shentsize = usize::from(u16_at(58));
    let shnum = usize::from(u16_at(60));
    let shstr = shoff + usize::from(u16_at(62)) * shentsize;
    let names = u64_at(shstr + 24);
    for index in 0..shnum {
        let shdr = shoff + index * shentsize;
        let start = names + u32_at(shdr) as usize;
        let end = start + object[start..].iter().position(|b| *b == 0).unwrap();
        if &object[start..end] == name.as_bytes() {
            let offset = u64_at(shdr + 24);
            return offset..offset + u64_at(shdr + 32);
        }
    }
    panic!("section {name} not found");
}

/// Decode one ULEB128 at `at`, returning `(value, byte length)`.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
fn uleb(bytes: &[u8], at: usize) -> (u64, usize) {
    let mut value = 0u64;
    let mut shift = 0u32;
    let mut len = 0usize;
    loop {
        let byte = bytes[at + len];
        value |= u64::from(byte & 0x7f) << shift;
        len += 1;
        if byte & 0x80 == 0 {
            return (value, len);
        }
        shift += 7;
    }
}

/// Mutant A: retarget the covering call-site row's landing pad to 0 (no
/// handler) inside `.gcc_except_table`. The personality then reads "keep
/// unwinding" for the throwing call and the exception must leave `tc_try_x86`
/// uncaught.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
fn drop_the_landing_pad(object: &mut [u8]) {
    let table = elf_section_bytes(object, ".gcc_except_table");
    let base = table.start;
    assert_eq!(object[base], 0xff, "LPStart is DW_EH_PE_omit");
    let mut at = base + 2; // past LPStart + TType encodings
    at += uleb(object, at).1; // TType base offset
    assert_eq!(object[at], 0x01, "the call-site table is ULEB128-encoded");
    at += 1;
    let (cs_len, len) = uleb(object, at);
    at += len;
    let cs_end = at + usize::try_from(cs_len).unwrap();
    while at < cs_end {
        at += uleb(object, at).1; // start
        at += uleb(object, at).1; // length
        let (landing_pad, lp_len) = uleb(object, at);
        let (_, action_len) = uleb(object, at + lp_len);
        if landing_pad != 0 {
            assert_eq!(lp_len, 1, "this fixture's landing-pad offset is one byte");
            assert_eq!(action_len, 1, "this fixture's action index is one byte");
            object[at] = 0; // no landing pad
            object[at + 1] = 0; // no action
            return;
        }
        at += lp_len + action_len;
    }
    panic!("the emitted LSDA has no call-site row with a landing pad");
}

/// Mutant B: turn the CIE's personality encoding from
/// `DW_EH_PE_indirect|pcrel|sdata4` (0x9b) into the DIRECT
/// `DW_EH_PE_pcrel|sdata4` (0x1b), leaving the relocation alone. The unwinder
/// then takes the SLOT's address for the personality routine and calls into
/// data — exactly the failure the Darwin lane documents, and the reason the
/// indirection exists.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
fn make_the_personality_direct(object: &mut [u8]) {
    let eh_frame = elf_section_bytes(object, ".eh_frame");
    // CIE: length(4) id(4) version(1) "zPLR\0"(5) code_align(1) data_align(1)
    // RA(1) aug-data-length(uleb) then the augmentation data, whose first byte
    // is the personality encoding.
    let mut at = eh_frame.start + 4 + 4;
    assert_eq!(object[at], 1, "eh_frame CIE version");
    at += 1;
    assert_eq!(&object[at..at + 5], b"zPLR\0", "zPLR augmentation");
    at += 5;
    at += uleb(object, at).1; // code alignment factor
    at += 1; // data alignment factor (SLEB128, -8: one byte)
    at += uleb(object, at).1; // return address register
    at += uleb(object, at).1; // augmentation data length
    assert_eq!(
        object[at], 0x9b,
        "the personality encoding is DW_EH_PE_indirect|pcrel|sdata4"
    );
    object[at] = 0x1b;
}

#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
#[test]
fn eh_catch_x86_elf_mutants_lose_the_catch() {
    let pristine = compile_tc_try(X86OutputFormat::Elf);

    let mut without_pad = pristine.clone();
    drop_the_landing_pad(&mut without_pad);
    assert_ne!(
        without_pad, pristine,
        "the landing-pad mutant must change the object"
    );
    let run = link_and_run("no_landing_pad", &without_pad);
    assert!(!run.timed_out, "the mutant must not hang");
    assert_ne!(
        run.exit_code,
        Some(0),
        "an LSDA call-site row with no landing pad must lose the catch, but the \
         run still succeeded.\nstdout: {}\nstderr: {}",
        run.stdout,
        run.stderr
    );
    assert!(
        !run.stdout.contains("returned 42"),
        "the mutant must not reach the catch sentinel.\nstdout: {}",
        run.stdout
    );

    let mut direct_personality = pristine.clone();
    make_the_personality_direct(&mut direct_personality);
    assert_ne!(
        direct_personality, pristine,
        "the personality-encoding mutant must change the object"
    );
    let run = link_and_run("direct_personality", &direct_personality);
    assert!(!run.timed_out, "the mutant must not hang");
    assert_ne!(
        run.exit_code,
        Some(0),
        "a DIRECT personality encoding makes the unwinder call the DW.ref slot \
         itself, so the run must not succeed.\nstdout: {}\nstderr: {}",
        run.stdout,
        run.stderr
    );
    assert!(
        !run.stdout.contains("returned 42"),
        "the mutant must not reach the catch sentinel.\nstdout: {}",
        run.stdout
    );

    eprintln!("x86-64 ELF EH mutation controls held on {}", host::HOST);
}

// ---------------------------------------------------------------------------
// Cross-object and shared-object controls (ELF).
//
// The `DW.ref.<personality>` indirection exists for two reasons that a
// single-object executable link cannot show. These rows show both.
// ---------------------------------------------------------------------------

/// The `.symtab` index of `name`, read by this file's own ELF walker.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
fn elf_symbol_index(object: &[u8], name: &str) -> u32 {
    let symtab = elf_section_bytes(object, ".symtab");
    let strtab = elf_section_bytes(object, ".strtab");
    let entry = 24usize;
    for index in 0..(symtab.len() / entry) {
        let at = symtab.start + index * entry;
        let st_name = u32::from_le_bytes(object[at..at + 4].try_into().unwrap()) as usize;
        let start = strtab.start + st_name;
        let end = start + object[start..].iter().position(|b| *b == 0).unwrap();
        if &object[start..end] == name.as_bytes() {
            return u32::try_from(index).unwrap();
        }
    }
    panic!("symbol {name} not found");
}

/// Link `objects` (plus the throwing C++ driver `driver`) into an executable and
/// run it. `extra` holds any additional `c++` arguments.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
fn link_objects(label: &str, objects: &[(&str, &[u8])], driver: &str, extra: &[&str]) -> Run {
    let dir = tempfile::Builder::new()
        .prefix(&format!("trust_cg_x86_eh_multi_{label}_"))
        .tempdir()
        .expect("create owned test dir");
    let mut args: Vec<String> = host::cxx_link_args()
        .iter()
        .map(|a| a.to_string())
        .collect();
    args.extend(extra.iter().map(|a| a.to_string()));
    let driver_path = dir.path().join("driver.cpp");
    fs::write(&driver_path, driver).expect("write driver");
    args.push(driver_path.to_str().unwrap().to_owned());
    for (name, bytes) in objects {
        let path = dir.path().join(name);
        fs::write(&path, bytes).expect("write .o");
        args.push(path.to_str().unwrap().to_owned());
    }
    let bin_path = dir.path().join("eh_multi_bin");
    args.push("-o".to_owned());
    args.push(bin_path.to_str().unwrap().to_owned());

    let link = Command::new(host::CXX_COMPILER)
        .args(&args)
        .output()
        .unwrap_or_else(|error| panic!("{} is required: {error}", host::CXX_COMPILER));
    assert!(
        link.status.success(),
        "link failed for {label}:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    // GNU ld builds `.eh_frame_hdr` / `PT_GNU_EH_FRAME` only when it could parse
    // every input `.eh_frame`; without that segment the run-time unwinder finds
    // no FDEs at all, so its presence in the LINKED image is the link-level
    // check that our `.rela.eh_frame` ordering was accepted.
    let segments = readelf(&bin_path, &["-lW"]);
    assert!(
        segments.contains("GNU_EH_FRAME"),
        "the linked image must carry PT_GNU_EH_FRAME:\n{segments}"
    );

    let run = run_executable_with_timeout(
        &bin_path,
        common::rosetta::exec_timeout(Duration::from_secs(10)),
    )
    .expect("supervise EH executable");
    Run {
        exit_code: run.output.status.code(),
        stdout: String::from_utf8_lossy(&run.output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&run.output.stderr).into_owned(),
        timed_out: run.timed_out,
    }
}

/// TWO objects, each an independent module with its own EH function and its own
/// `DW.ref.__gxx_personality_v0` slot — the real bridge shape, which emits one
/// object per mono item. The slots are weak hidden members of a `GRP_COMDAT`
/// group signed by the slot symbol, so the link keeps one cell instead of
/// colliding, and BOTH frames must still catch.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
#[test]
fn eh_catch_x86_elf_two_objects_each_with_a_personality_slot_both_catch() {
    let first = compile_tc_try_named(X86OutputFormat::Elf, "tc_try_x86");
    let second = compile_tc_try_named(X86OutputFormat::Elf, "tc_try_x86_b");
    for object in [first.as_slice(), second.as_slice()] {
        assert!(host::object_contains(
            object,
            b"DW.ref.__gxx_personality_v0"
        ));
    }
    let run = link_objects(
        "two_objects",
        &[("a.o", first.as_slice()), ("b.o", second.as_slice())],
        r#"
#include <cstdio>
extern "C" int tc_try_x86();
extern "C" int tc_try_x86_b();
extern "C" void cxx_throw() { throw 7; }
int main() {
    int a = tc_try_x86();
    int b = tc_try_x86_b();
    printf("a=%d b=%d\n", a, b);
    return (a == 42 && b == 42) ? 0 : 1;
}
"#,
        &[],
    );
    assert!(!run.timed_out, "the two-object link must not hang");
    assert_eq!(
        run.exit_code,
        Some(0),
        "both objects' frames must catch.\nstdout: {}\nstderr: {}",
        run.stdout,
        run.stderr
    );
    assert!(run.stdout.contains("a=42 b=42"), "stdout: {}", run.stdout);
    eprintln!(
        "x86-64 ELF EH cross-object link PASSED: {}",
        run.stdout.trim()
    );
}

/// The reason the indirection exists, shown both ways.
///
/// A SHARED object must link: every `.eh_frame` pointer is either a local
/// section anchor or the hidden `DW.ref` slot, all link-time constants. Rewrite
/// the CIE personality record to name `__gxx_personality_v0` DIRECTLY — the
/// spelling a "direct is simpler" reading would produce — and GNU ld must refuse
/// it, because an `R_X86_64_PC32` against a preemptible symbol has no
/// representation in a shared object.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
#[test]
fn eh_catch_x86_elf_shared_link_needs_the_personality_indirection() {
    let pristine = compile_tc_try(X86OutputFormat::Elf);

    let shared_link = |label: &str, object: &[u8]| -> std::process::Output {
        let dir = tempfile::Builder::new()
            .prefix(&format!("trust_cg_x86_eh_shared_{label}_"))
            .tempdir()
            .expect("create owned test dir");
        let obj_path = dir.path().join("tc_try_x86.o");
        fs::write(&obj_path, object).expect("write .o");
        let so_path = dir.path().join("libtc_try.so");
        Command::new(host::CXX_COMPILER)
            .args(["-shared", "-o"])
            .arg(&so_path)
            .arg(&obj_path)
            .output()
            .unwrap_or_else(|error| panic!("{} is required: {error}", host::CXX_COMPILER))
    };

    let ok = shared_link("pristine", &pristine);
    assert!(
        ok.status.success(),
        "the emitted object must link into a SHARED object; the personality \
         indirection is what makes its .eh_frame reference a link-time \
         constant:\n{}",
        String::from_utf8_lossy(&ok.stderr)
    );

    // Point the CIE personality record at the personality symbol itself.
    // `.rela.eh_frame`'s records are emitted in ascending r_offset order and the
    // CIE personality field has the lowest offset, so it is record 0.
    let mut direct = pristine.clone();
    let personality = elf_symbol_index(&direct, "__gxx_personality_v0");
    let rela = elf_section_bytes(&direct, ".rela.eh_frame");
    let r_info = rela.start + 8;
    let reloc_type = u32::from_le_bytes(direct[r_info..r_info + 4].try_into().unwrap());
    assert_eq!(reloc_type, 2, "R_X86_64_PC32");
    direct[r_info + 4..r_info + 8].copy_from_slice(&personality.to_le_bytes());

    let refused = shared_link("direct", &direct);
    assert!(
        !refused.status.success(),
        "a DIRECT R_X86_64_PC32 to the preemptible personality must be refused \
         when making a shared object; it linked instead"
    );
    let diagnostic = String::from_utf8_lossy(&refused.stderr);
    assert!(
        diagnostic.contains("__gxx_personality_v0"),
        "the refusal must name the personality: {diagnostic}"
    );

    eprintln!(
        "x86-64 ELF EH shared-object control held on {}: direct personality refused",
        host::HOST
    );
}
