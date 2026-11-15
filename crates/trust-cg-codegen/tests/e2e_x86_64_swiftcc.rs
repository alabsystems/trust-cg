// trust-cg-codegen/tests/e2e_x86_64_swiftcc.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// x86-64 swiftcc RETURN PLACEMENT — the (E4) lane of e2e_x86_64_calling_conv
// ===========================================================================
//
// This is the swiftcc SOURCE-side measurement that licenses the x86-64 Swift
// return budget (`PerClass { int: 2, fp: 2 }`, asserted at the end of the
// test). It lives in its own target because it needs a C driver that honours
// `__attribute__((swiftcall))`, which only clang provides: GCC ignores the
// attribute (with a warning), so on a GCC-only host the "swiftcall" readings
// would silently be C readings and the divergence rows would refute nothing.
//
// On such a host the test probes the driver and prints a SKIP naming XD-03.
// Ruling XD-03 (docs/decision-record.md, 2026-10-02) makes swiftcc a required
// Linux x86-64 convention, so scripts/check_linux_x86_64.py lists this target
// in TARGETS and counts that SKIP as a failure: the row is red until a driver
// that honours the attribute is provisioned for this test. The (E3) admission
// controls and the C-convention oracles stay in e2e_x86_64_calling_conv and
// run on every floor host.
//
// PROVISIONING THE DRIVER (`TRUST_CG_SWIFTCALL_CC`, OD-SWIFTCC-DRIVER-20261020).
// STOCK EXCEPTION, this target only: `__attribute__((swiftcall))` is a clang
// capability Trust's compiler does not supply and GCC refuses — measured on
// `x86_64-unknown-linux-gnu`, GCC 0: "error: `swiftcall` attribute directive
// ignored [-Werror=attributes]". Name a C driver in
// `TRUST_CG_SWIFTCALL_CC` and this target uses it INSTEAD of `cc`, for both
// its swiftcall and its plain-C readings, so the two sides of every
// divergence row come from one compiler. Unset or empty keeps `cc`.
//
// The NAME IS NOT THE AUTHORITY: `cc_honours_swiftcall` still compiles a
// one-function probe under `-Werror` with whatever driver is selected, and a
// driver that does not honour the attribute still SKIPs. So naming the wrong
// driver cannot turn a C reading into a swiftcall reading; it can only make
// the lane runnable where a capable driver exists. Nothing here is a Trust
// toolchain substitution: the trust-cg object under test is still produced by
// this backend, and the driver only supplies the C oracle side.

mod common;

use std::fs;
use std::path::Path;
use std::process::Command;
use std::sync::Mutex;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout,
};
use common::x86_64_corpus::x86_64_oracle_enabled;

/// One global lock: the lane links and runs a native binary.
static SERIAL: Mutex<()> = Mutex::new(());

/// The assembler-level spelling of a C symbol on this host: Mach-O prefixes
/// every C symbol with `_`; ELF carries the bare name.
fn host_sym(name: &str) -> String {
    let prefix = if cfg!(target_os = "macos") { "_" } else { "" };
    format!("{prefix}{name}")
}

/// The C drivers this target will try, in order: `TRUST_CG_SWIFTCALL_CC`
/// when it names one, then the host `cc`, then the clang spellings. See the
/// PROVISIONING note at the top of the file. A name only nominates a
/// CANDIDATE; [`cc_honours_swiftcall`] decides which one is used, and if none
/// is honoured the lane SKIPs exactly as before.
fn swiftcall_cc_candidates() -> Vec<String> {
    let mut candidates = Vec::new();
    if let Ok(driver) = std::env::var("TRUST_CG_SWIFTCALL_CC")
        && !driver.trim().is_empty()
    {
        candidates.push(driver.trim().to_owned());
    }
    // `cc` first among the discovered names: a host whose `cc` IS a capable
    // clang must not be second-guessed, and on a GCC host it costs one probe.
    for name in [
        "cc", "clang", "clang-21", "clang-20", "clang-19", "clang-18",
    ] {
        if !candidates.iter().any(|c| c == name) {
            candidates.push(name.to_owned());
        }
    }
    candidates
}

/// The driver selected for this process, set once by
/// [`select_swiftcall_cc`] before any compile and read by [`cc_x86_64`].
/// `cc` until then, which is what every other target uses.
static SELECTED_CC: Mutex<Option<String>> = Mutex::new(None);

/// The driver [`cc_x86_64`] runs.
fn swiftcall_cc() -> String {
    SELECTED_CC
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .clone()
        .unwrap_or_else(|| "cc".to_owned())
}

/// Probe each candidate in order and keep the first that honours
/// `__attribute__((swiftcall))`. Returns the selected driver, or `None` when
/// no candidate does — the SKIP case, which names everything it tried.
fn select_swiftcall_cc(dir: &Path) -> Option<String> {
    for candidate in swiftcall_cc_candidates() {
        *SELECTED_CC.lock().unwrap_or_else(|p| p.into_inner()) = Some(candidate.clone());
        if cc_honours_swiftcall(dir) {
            return Some(candidate);
        }
    }
    *SELECTED_CC.lock().unwrap_or_else(|p| p.into_inner()) = None;
    None
}

fn cc_x86_64(args: &[&str]) -> (bool, String) {
    let mut cmd = Command::new(swiftcall_cc());
    // Apple's driver flag only; GNU/Linux `cc` rejects `-arch`.
    if cfg!(target_os = "macos") {
        cmd.arg("-arch").arg("x86_64");
    }
    for a in args {
        cmd.arg(a);
    }
    let out = command_output_with_timeout(&mut cmd, codegen_link_timeout()).expect("cc must spawn");
    let stderr = String::from_utf8_lossy(&out.output.stderr).to_string();
    (!out.timed_out && out.output.status.success(), stderr)
}

/// A scratch directory owned by the returned guard, removed when it drops
/// (after the test, passed, failed or skipped).
fn scratch_dir(tag: &str) -> tempfile::TempDir {
    tempfile::Builder::new()
        .prefix(&format!("trust_cg_x86_swiftcc_{tag}_"))
        .tempdir()
        .expect("create scratch dir")
}

/// Whether the host `cc` implements `__attribute__((swiftcall))`, measured by
/// compiling a one-function probe under `-Werror`: GCC reports the attribute
/// as ignored (`-Wattributes`), which `-Werror` turns into a failed compile;
/// clang accepts it silently.
fn cc_honours_swiftcall(dir: &Path) -> bool {
    let probe = dir.join("swiftcall_probe.c");
    fs::write(
        &probe,
        "__attribute__((swiftcall)) int probe(void) { return 1; }\n\
         int main(void) { return probe() - 1; }\n",
    )
    .expect("write swiftcall probe");
    let bin = dir.join("swiftcall_probe");
    let (ok, stderr) = cc_x86_64(&[
        "-Werror",
        "-o",
        bin.to_str().unwrap(),
        probe.to_str().unwrap(),
    ]);
    if !ok {
        eprintln!(
            "[E4] `{} -Werror` rejected the swiftcall probe:\n{stderr}",
            swiftcall_cc()
        );
    }
    ok
}

fn build_and_run(
    dir: &Path,
    sources: &[(&str, String)],
    objects: &[(&str, &[u8])],
) -> (i32, String) {
    let mut args: Vec<String> = vec![
        "-O2".into(),
        "-o".into(),
        dir.join("bin").to_string_lossy().into_owned(),
    ];
    for (name, text) in sources {
        let path = dir.join(name);
        fs::write(&path, text).expect("write source");
        args.push(path.to_string_lossy().into_owned());
    }
    for (name, bytes) in objects {
        let path = dir.join(name);
        fs::write(&path, bytes).expect("write object");
        args.push(path.to_string_lossy().into_owned());
    }
    let refs: Vec<&str> = args.iter().map(String::as_str).collect();
    let (ok, stderr) = cc_x86_64(&refs);
    assert!(ok, "link failed; files={dir:?}\n{stderr}");
    let run = run_executable_with_timeout(&dir.join("bin"), codegen_run_timeout())
        .expect("run swiftcc oracle");
    assert!(!run.timed_out, "swiftcc oracle timed out; files={dir:?}");
    let stdout = String::from_utf8_lossy(&run.output.stdout).to_string();
    (run.output.status.code().unwrap_or(-1), stdout)
}

fn format_g17(v: f64) -> String {
    // A `%.17g` of an exactly-representable integral double prints the integer
    // with no exponent as long as its magnitude is below 1e17, which every
    // value in this file is.
    if v == v.trunc() && v.abs() < 1e17 {
        format!("{}", v as i64)
    } else {
        format!("{v:.17e}")
    }
}

// ===========================================================================
// (E4) The swiftcc SOURCE side — MEASURED on this host, not asserted
// ===========================================================================
//
// The x86-64 Swift return budget `PerClass { int: 2, fp: 2 }` rests on ONE
// premise: that System V's C return file (RAX,RDX / XMM0,XMM1) is a SAME-INDEX
// PREFIX of `swiftcc`'s (RAX,RDX,RCX,R8 / XMM0-XMM3). Half of that premise —
// the C half — is trust-cg's own `X86_RET_GPRS` / `X86_RET_XMMS`, which the
// tripwire below pins. The OTHER half, the `swiftcc` half, was prose: this tree
// never emits `swiftcc`, so nothing in it could be compared against.
//
// This section measures it. Each callee is HAND-WRITTEN ASSEMBLY that deposits
// known values in NAMED registers and returns — it takes no arguments and
// computes nothing, so the only thing a reading of it can measure is WHICH
// REGISTER a convention takes each returned component from. The host toolchain
// provides the readings: clang declares the same symbol with
// `__attribute__((swiftcall))` and with the plain C convention, and the values
// either arrive or they do not.
//
// The two sides are structurally distinct, which is what makes this not a
// self-comparison:
//   * the ASSEMBLY says "value V is in register R" and is executed;
//   * the PREDICTION says "convention X reads component k from file[k]" and is
//     computed in Rust from the declared register files below;
//   * neither is trust-cg, and neither is the other.
// A callee whose deposits line up with the file must be read back exactly
// (AGREES); a callee that deposits one component one register off must NOT be
// (REFUTES), and its prediction is asserted to differ from the correct values,
// so a no-op cannot pose as a control.

/// The x86-64 `swiftcc` RETURN register file, per class, as this lane states it
/// on the SOURCE side. Writing it down is not evidence — the readings below
/// are. It is here so the prediction is computed from a stated rule rather than
/// from a hand-listed expected value per row.
const SWIFTCC_RET_GPRS: [&str; 4] = ["%rax", "%rdx", "%rcx", "%r8"];
const SWIFTCC_RET_XMMS: [&str; 4] = ["%xmm0", "%xmm1", "%xmm2", "%xmm3"];

/// The register file trust-cg's OWN x86-64 multi-scalar return placement
/// allocates from — `classify_x86_scalar_return_locations` over
/// `X86_RET_GPRS` / `X86_RET_XMMS`, on two INDEPENDENT class counters. The
/// System V C ABI coincides with it for the shapes C can express (see
/// `SYSV_C_REGISTER_RETURN_EIGHTBYTES`), which is why a `ReadConv::C` reading
/// can measure it at all.
const SYSV_C_RET_GPRS: [&str; 2] = ["%rax", "%rdx"];
const SYSV_C_RET_XMMS: [&str; 2] = ["%xmm0", "%xmm1"];

/// System V AMD64 returns an aggregate in registers only while it is at most
/// TWO EIGHTBYTES **in total**, across both classes; anything larger goes
/// through a hidden sret pointer. This is NOT "2 integer and 2 FP": a
/// `{i64,i64,double,double}` return is 32 bytes and is MEMORY class, which the
/// (E4) readings below measure directly.
///
/// The committed derivation of the x86-64 Swift budget said "SysV C returns in
/// RAX,RDX plus XMM0,XMM1", which is true only within this limit. The
/// agreement that actually licenses the budget is between trust-cg's own
/// multi-scalar return placement and `swiftcc`'s — both of which DO run two
/// independent class counters to depth 2 and 4 respectively. Building this
/// oracle is what surfaced the difference.
const SYSV_C_REGISTER_RETURN_EIGHTBYTES: usize = 2;

/// The value a CORRECT callee deposits for return component `k` of its class.
/// Distinct, so any permutation of the file shows up in the reading.
const SC_INT: [i64; 4] = [1_000_003, 2_000_003, 3_000_003, 4_000_003];
const SC_FP: [f64; 4] = [100.0, 200.0, 300.0, 400.0];

/// Deposited where a correct reading WOULD look but a control's value is not.
/// Without it a control's prediction would depend on whatever the caller left
/// in that register, and an unfalsifiable prediction is not a control.
const SC_SENTINEL_INT: i64 = -7_777_777;
const SC_SENTINEL_FP: f64 = -8888.0;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ReadConv {
    /// Read back through `__attribute__((swiftcall))`.
    Swiftcall,
    /// Read back through the platform C convention (System V AMD64 here).
    C,
}

impl ReadConv {
    fn files(self) -> (&'static [&'static str], &'static [&'static str]) {
        match self {
            ReadConv::Swiftcall => (&SWIFTCC_RET_GPRS, &SWIFTCC_RET_XMMS),
            ReadConv::C => (&SYSV_C_RET_GPRS, &SYSV_C_RET_XMMS),
        }
    }
    fn tag(self) -> &'static str {
        match self {
            ReadConv::Swiftcall => "swiftcall",
            ReadConv::C => "c",
        }
    }
}

/// One hand-written assembly callee: `(name, GPR deposits, XMM deposits)`.
struct ScCallee {
    name: &'static str,
    gprs: &'static [(&'static str, i64)],
    xmms: &'static [(&'static str, f64)],
}

const SC_CALLEES: &[ScCallee] = &[
    // --- agreement rows: deposits line up with BOTH files at index 0 and 1 ---
    ScCallee {
        name: "sc_two_int",
        gprs: &[("%rax", SC_INT[0]), ("%rdx", SC_INT[1])],
        xmms: &[],
    },
    ScCallee {
        name: "sc_two_fp",
        gprs: &[],
        xmms: &[("%xmm0", SC_FP[0]), ("%xmm1", SC_FP[1])],
    },
    // The exact upper corner of the x86-64 Swift return budget: 2 integer + 2
    // FP components, which is what `e3_swift_full_sysv_return_file_is_admitted`
    // ADMITS and lowers as C.
    ScCallee {
        name: "sc_mix_2i2f",
        gprs: &[("%rax", SC_INT[0]), ("%rdx", SC_INT[1])],
        xmms: &[("%xmm0", SC_FP[0]), ("%xmm1", SC_FP[1])],
    },
    // --- the swiftcc file EXTENDS past C's, which is why the budget is 2 ---
    ScCallee {
        name: "sc_three_int",
        gprs: &[
            ("%rax", SC_INT[0]),
            ("%rdx", SC_INT[1]),
            ("%rcx", SC_INT[2]),
        ],
        xmms: &[],
    },
    ScCallee {
        name: "sc_four_int",
        gprs: &[
            ("%rax", SC_INT[0]),
            ("%rdx", SC_INT[1]),
            ("%rcx", SC_INT[2]),
            ("%r8", SC_INT[3]),
        ],
        xmms: &[],
    },
    ScCallee {
        name: "sc_four_fp",
        gprs: &[],
        xmms: &[
            ("%xmm0", SC_FP[0]),
            ("%xmm1", SC_FP[1]),
            ("%xmm2", SC_FP[2]),
            ("%xmm3", SC_FP[3]),
        ],
    },
    // --- controls: one component deposited ONE REGISTER OFF ---
    // Component 1 put in RCX (swiftcc's THIRD integer return register) instead
    // of RDX. Both conventions must read the sentinel and refute.
    ScCallee {
        name: "sc_two_int_ctl",
        gprs: &[
            ("%rax", SC_INT[0]),
            ("%rdx", SC_SENTINEL_INT),
            ("%rcx", SC_INT[1]),
        ],
        xmms: &[],
    },
    // FP component 1 put in XMM2 instead of XMM1.
    ScCallee {
        name: "sc_two_fp_ctl",
        gprs: &[],
        xmms: &[
            ("%xmm0", SC_FP[0]),
            ("%xmm1", SC_SENTINEL_FP),
            ("%xmm2", SC_FP[1]),
        ],
    },
    // THE INDEPENDENT-COUNTERS control. If swiftcc walked ONE shared counter
    // over the return file, the two FP components of a (i64,i64,f64,f64) return
    // would land after the two integers rather than at XMM0,XMM1. This callee
    // deposits them that way; the reading must refute it.
    ScCallee {
        name: "sc_mix_shared_counter_ctl",
        gprs: &[("%rax", SC_INT[0]), ("%rdx", SC_INT[1])],
        xmms: &[
            ("%xmm0", SC_SENTINEL_FP),
            ("%xmm1", SC_SENTINEL_FP),
            ("%xmm2", SC_FP[0]),
            ("%xmm3", SC_FP[1]),
        ],
    },
];

/// `(callee, convention, integer components, FP components, must AGREE)`.
///
/// A reading whose shape reaches past the convention's file is not expressible
/// here — `sc_prediction` panics on it — and that panic is itself the statement
/// that the C file has no third entry.
const SC_READINGS: &[(&str, ReadConv, usize, usize, bool)] = &[
    // The AGREEMENT, measured on the SAME machine code through BOTH
    // conventions. This pair is the whole licence for lowering an admitted
    // Swift return as C.
    ("sc_two_int", ReadConv::Swiftcall, 2, 0, true),
    ("sc_two_int", ReadConv::C, 2, 0, true),
    ("sc_two_fp", ReadConv::Swiftcall, 0, 2, true),
    ("sc_two_fp", ReadConv::C, 0, 2, true),
    // The upper corner of the budget. Read through `swiftcall` ONLY: this
    // shape is 32 bytes, which System V's C ABI returns through sret, so there
    // is no C REGISTER reading of it to compare against. `sc_c_sret_mix` below
    // measures that fact instead.
    ("sc_mix_2i2f", ReadConv::Swiftcall, 2, 2, true),
    // swiftcc's files are WIDER than C's: components 2 and 3 exist there.
    ("sc_three_int", ReadConv::Swiftcall, 3, 0, true),
    ("sc_four_int", ReadConv::Swiftcall, 4, 0, true),
    ("sc_four_fp", ReadConv::Swiftcall, 0, 4, true),
    // The controls. Each must be read WRONG, under every convention that can
    // express its shape.
    ("sc_two_int_ctl", ReadConv::Swiftcall, 2, 0, false),
    ("sc_two_int_ctl", ReadConv::C, 2, 0, false),
    ("sc_two_fp_ctl", ReadConv::Swiftcall, 0, 2, false),
    ("sc_two_fp_ctl", ReadConv::C, 0, 2, false),
    (
        "sc_mix_shared_counter_ctl",
        ReadConv::Swiftcall,
        2,
        2,
        false,
    ),
];

fn sc_callee(name: &str) -> &'static ScCallee {
    SC_CALLEES
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("(E4) reading names undefined callee `{name}`"))
}

/// What convention `conv` reads out of `callee`, computed from the DECLARED
/// register files. Panics if the reading touches a register the callee deposits
/// nothing in — an unmodelled reading is not a control, it is noise.
fn sc_prediction(
    callee: &ScCallee,
    conv: ReadConv,
    n_int: usize,
    n_fp: usize,
) -> (Vec<i64>, Vec<f64>) {
    let (gfile, xfile) = conv.files();
    assert!(
        conv != ReadConv::C || n_int + n_fp <= SYSV_C_REGISTER_RETURN_EIGHTBYTES,
        "(E4) System V's C register return file holds at most {SYSV_C_REGISTER_RETURN_EIGHTBYTES} \
         eightbytes in TOTAL, so a {n_int}-integer/{n_fp}-FP aggregate is MEMORY class and comes \
         back through a hidden sret pointer. That shape is witnessed by `sc_c_sret_mix`, not by a \
         register reading"
    );
    let ints = (0..n_int)
        .map(|k| {
            let reg = gfile.get(k).unwrap_or_else(|| {
                panic!(
                    "(E4) a {}-component integer return is past {}'s return file, which has {} \
                     entries — that shape is the DIVERGENCE, not a reading",
                    n_int,
                    conv.tag(),
                    gfile.len()
                )
            });
            callee
                .gprs
                .iter()
                .find(|(r, _)| r == reg)
                .unwrap_or_else(|| {
                    panic!(
                        "(E4) callee `{}` deposits nothing in {reg}, so reading component {k} \
                         through {} is unmodelled",
                        callee.name,
                        conv.tag()
                    )
                })
                .1
        })
        .collect();
    let fps = (0..n_fp)
        .map(|k| {
            let reg = xfile.get(k).unwrap_or_else(|| {
                panic!(
                    "(E4) a {}-component FP return is past {}'s FP return file",
                    n_fp,
                    conv.tag()
                )
            });
            callee
                .xmms
                .iter()
                .find(|(r, _)| r == reg)
                .unwrap_or_else(|| {
                    panic!(
                        "(E4) callee `{}` deposits nothing in {reg}, so reading component {k} \
                         through {} is unmodelled",
                        callee.name,
                        conv.tag()
                    )
                })
                .1
        })
        .collect();
    (ints, fps)
}

/// The C-sret witness's three values, shared by the assembly and the Rust side.
const SC_SRET_VALUES: [i64; 3] = [SC_INT[0], SC_INT[1], SC_INT[2]];

fn swiftcc_asm() -> String {
    let mut out = String::from("    .text\n");
    for callee in SC_CALLEES {
        out.push_str(&format!("\n    .globl {0}\n{0}:\n", host_sym(callee.name)));
        for (reg, value) in callee.gprs {
            out.push_str(&format!("    movq    ${value}, {reg}\n"));
        }
        for (reg, value) in callee.xmms {
            // %r11 is volatile under System V and is none of swiftcc's reserved
            // registers (self R13 / error R12 / async R14), so using it as a
            // staging register cannot itself perturb a reading.
            out.push_str(&format!(
                "    movabsq $0x{:016x}, %r11\n    movq    %r11, {reg}\n",
                value.to_bits()
            ));
        }
        out.push_str("    ret\n");
    }
    // The other half of the divergence, and the only row that is NOT a register
    // deposit: a CORRECT System V sret callee. It takes the hidden destination
    // pointer in RDI, writes the three components THROUGH it, and returns that
    // pointer in RAX. If C returned a three-integer aggregate in registers this
    // callee would set none of them and the reading would be garbage; the
    // reading succeeding is the measurement that C uses MEMORY here, i.e. that
    // C has no third integer return register for the Swift budget to borrow.
    out.push_str(&format!(
        "\n    .globl {0}\n{0}:\n",
        host_sym("sc_c_sret_three")
    ));
    out.push_str("    movq    %rdi, %rax\n");
    for (index, value) in SC_SRET_VALUES.iter().enumerate() {
        out.push_str(&format!("    movq    ${value}, {}(%rdi)\n", index * 8));
    }
    out.push_str("    ret\n");
    // The SAME witness for the 2-integer/2-FP shape — the exact upper corner of
    // the x86-64 Swift return budget. `swiftcc` returns it in RAX,RDX,XMM0,XMM1
    // (reading `sc_mix_2i2f`), but it is 32 bytes, so System V's C ABI returns
    // it through sret. The budget is therefore NOT licensed by C's register
    // file for this shape; it is licensed by trust-cg's own multi-scalar return
    // placement agreeing with swiftcc's, which is what `e4_...` asserts.
    out.push_str(&format!(
        "\n    .globl {0}\n{0}:\n",
        host_sym("sc_c_sret_mix")
    ));
    out.push_str("    movq    %rdi, %rax\n");
    out.push_str(&format!("    movq    ${}, 0(%rdi)\n", SC_INT[0]));
    out.push_str(&format!("    movq    ${}, 8(%rdi)\n", SC_INT[1]));
    out.push_str(&format!(
        "    movabsq $0x{:016x}, %r11\n    movq    %r11, 16(%rdi)\n",
        SC_FP[0].to_bits()
    ));
    out.push_str(&format!(
        "    movabsq $0x{:016x}, %r11\n    movq    %r11, 24(%rdi)\n",
        SC_FP[1].to_bits()
    ));
    out.push_str("    ret\n");
    out
}

/// The struct type name for an `(n_int, n_fp)` return shape.
fn sc_struct(n_int: usize, n_fp: usize) -> String {
    format!("ScS{n_int}_{n_fp}")
}

fn swiftcc_driver_c() -> String {
    let mut types = String::new();
    let mut seen: Vec<(usize, usize)> = Vec::new();
    for (_, _, n_int, n_fp, _) in SC_READINGS {
        if !seen.contains(&(*n_int, *n_fp)) {
            seen.push((*n_int, *n_fp));
        }
    }
    if !seen.contains(&(3, 0)) {
        seen.push((3, 0)); // the sret witness's shape
    }
    for (n_int, n_fp) in &seen {
        let mut fields = String::new();
        for k in 0..*n_int {
            fields.push_str(&format!("int64_t i{k}; "));
        }
        for k in 0..*n_fp {
            fields.push_str(&format!("double f{k}; "));
        }
        types.push_str(&format!(
            "typedef struct {{ {fields}}} {};\n",
            sc_struct(*n_int, *n_fp)
        ));
    }

    let mut decls = String::new();
    let mut calls = String::new();
    for (index, (name, conv, n_int, n_fp, _)) in SC_READINGS.iter().enumerate() {
        let sym = format!("sc_read{index}");
        let attr = match conv {
            ReadConv::Swiftcall => "__attribute__((swiftcall)) ",
            ReadConv::C => "",
        };
        decls.push_str(&format!(
            "{attr}{} {sym}(void) __asm__(\"{}\");\n",
            sc_struct(*n_int, *n_fp),
            host_sym(name)
        ));
        let mut fmt = String::new();
        let mut args = String::new();
        for k in 0..*n_int {
            fmt.push_str(" %lld");
            args.push_str(&format!(", (long long)v.i{k}"));
        }
        for k in 0..*n_fp {
            fmt.push_str(" %.17g");
            args.push_str(&format!(", v.f{k}"));
        }
        calls.push_str(&format!(
            "  {{ {} v = {sym}(); printf(\"reading {index} {name} via {}:{fmt}\\n\"{args}); ran++; }}\n",
            sc_struct(*n_int, *n_fp),
            conv.tag()
        ));
    }
    // The sret witness, read through the PLAIN C convention only.
    decls.push_str(&format!("{} sc_c_sret_three(void);\n", sc_struct(3, 0)));
    calls.push_str(&format!(
        "  {{ {} v = sc_c_sret_three(); printf(\"sret witness: %lld %lld %lld\\n\", \
         (long long)v.i0, (long long)v.i1, (long long)v.i2); ran++; }}\n",
        sc_struct(3, 0)
    ));
    decls.push_str(&format!("{} sc_c_sret_mix(void);\n", sc_struct(2, 2)));
    calls.push_str(&format!(
        "  {{ {} v = sc_c_sret_mix(); printf(\"sret mix witness: %lld %lld %.17g %.17g\\n\", \
         (long long)v.i0, (long long)v.i1, v.f0, v.f1); ran++; }}\n",
        sc_struct(2, 2)
    ));

    format!(
        r#"
#include <stdio.h>
#include <stdint.h>

{types}
{decls}

int main(void) {{
    int ran = 0;
{calls}
    printf("SWIFTCC_READINGS_RUN=%d\n", ran);
    return 0;
}}
"#
    )
}

/// The exact line the C driver prints for reading `index`, built from the Rust
/// prediction. The C side prints what the HARDWARE produced; this is what the
/// declared register files say it must be.
fn sc_expected_line(index: usize) -> String {
    let (name, conv, n_int, n_fp, _) = SC_READINGS[index];
    let (ints, fps) = sc_prediction(sc_callee(name), conv, n_int, n_fp);
    let mut line = format!("reading {index} {name} via {}:", conv.tag());
    for v in &ints {
        line.push_str(&format!(" {v}"));
    }
    for v in &fps {
        line.push_str(&format!(" {}", format_g17(*v)));
    }
    line
}

#[test]
fn e4_swiftcc_return_placement_is_measured_not_asserted() {
    if !x86_64_oracle_enabled("x86_64_swiftcc_return_placement") {
        eprintln!(
            "SKIP: (E4) NOT RUN — the x86-64 execution oracle is unavailable on this host, so the \
             swiftcc SOURCE side of the x86-64 Swift return budget was NOT measured and the \
             budget rests on prose again. The (E3) admission controls in \
             e2e_x86_64_calling_conv still ran."
        );
        return;
    }
    let _guard = SERIAL.lock().unwrap_or_else(|p| p.into_inner());

    let scratch = scratch_dir("swiftcc");
    let dir = scratch.path();
    let Some(driver) = select_swiftcall_cc(dir) else {
        eprintln!(
            "SKIP: (E4) NOT RUN — no C driver on this host honours \
             `__attribute__((swiftcall))` (GCC ignores it; clang is required), so the swiftcc \
             SOURCE side of the x86-64 Swift return budget was NOT measured here. Tried, in \
             order: {}. Ruling XD-03 makes this a required Linux x86-64 row \
             (docs/decision-record.md), so the floor counts this SKIP as a failure; the (E3) \
             admission controls in e2e_x86_64_calling_conv still ran. PROVISION one: name a \
             clang in TRUST_CG_SWIFTCALL_CC (OD-SWIFTCC-DRIVER-20261020) — this target then \
             uses it for both its swiftcall and its plain-C readings, and the probe still \
             decides whether it is honoured.",
            swiftcall_cc_candidates().join(", ")
        );
        return;
    };
    // Which driver produced the C oracle side is part of the reading: a row
    // read by a different compiler than the prose assumes is a different
    // measurement.
    eprintln!("[E4] swiftcall C driver: {driver}");
    let (code, stdout) = build_and_run(
        dir,
        &[
            ("swiftcc.s", swiftcc_asm()),
            ("swiftcc_driver.c", swiftcc_driver_c()),
        ],
        &[],
    );
    eprintln!("[E4 swiftcc readings]\n{stdout}");
    assert_eq!(
        code, 0,
        "the (E4) driver itself failed; files={dir:?}\n{stdout}"
    );

    let mut checked = 0usize;
    for (index, (name, conv, n_int, n_fp, agrees)) in SC_READINGS.iter().enumerate() {
        let expected = sc_expected_line(index);
        assert!(
            stdout.contains(&expected),
            "(E4) reading {index} (`{name}` via {}) did not print its INDEPENDENTLY PREDICTED \
             values.\n  predicted: {expected}\nEither {} does not take its return components from \
             the file this lane declares, or the assembly does not deposit what it says it \
             does — both must fail here:\n{stdout}",
            conv.tag(),
            conv.tag()
        );
        let (ints, fps) = sc_prediction(sc_callee(name), *conv, *n_int, *n_fp);
        let correct_ints = &SC_INT[..*n_int];
        let correct_fps = &SC_FP[..*n_fp];
        if *agrees {
            assert_eq!(
                (ints.as_slice(), fps.as_slice()),
                (correct_ints, correct_fps),
                "(E4) reading {index} (`{name}` via {}) is declared an AGREEMENT but its \
                 prediction is not the correct component values — the anchor is broken",
                conv.tag()
            );
        } else {
            assert_ne!(
                (ints.as_slice(), fps.as_slice()),
                (correct_ints, correct_fps),
                "(E4) reading {index} (`{name}` via {}) is declared a CONTROL but predicts the \
                 correct values, so it refutes nothing: a no-op dressed as a control",
                conv.tag()
            );
        }
        checked += 1;
    }
    assert_eq!(checked, SC_READINGS.len());
    assert!(
        stdout.contains(&format!("SWIFTCC_READINGS_RUN={}", SC_READINGS.len() + 2)),
        "(E4) the driver did not report all {} readings plus the TWO sret witnesses as RUN; a \
         reading that never executed cannot be counted:\n{stdout}",
        SC_READINGS.len()
    );

    // The sret half of the divergence.
    assert!(
        stdout.contains(&format!(
            "sret witness: {} {} {}",
            SC_SRET_VALUES[0], SC_SRET_VALUES[1], SC_SRET_VALUES[2]
        )),
        "(E4) the System V C convention did not return a three-integer aggregate through the \
         hidden sret pointer. If it had returned it in registers, this callee — which sets only \
         RAX to the incoming pointer — would have produced garbage. This is the measurement that \
         C has no third integer return register:\n{stdout}"
    );

    assert!(
        stdout.contains(&format!(
            "sret mix witness: {} {} {} {}",
            SC_INT[0],
            SC_INT[1],
            format_g17(SC_FP[0]),
            format_g17(SC_FP[1])
        )),
        "(E4) System V's C ABI did not return the 2-integer/2-FP aggregate through sret. This is \
         the reading that CORRECTS the committed derivation: `swiftcc` returns that shape in \
         RAX,RDX,XMM0,XMM1 (reading `sc_mix_2i2f`), but C returns 32 bytes through MEMORY, so \
         the budget's upper corner is licensed by trust-cg's own multi-scalar return placement \
         matching swiftcc's, NOT by C's register file:\n{stdout}"
    );

    // ---------------------------------------------------------------------
    // THE LICENCE, now measured on BOTH sides rather than stated on one.
    //
    //   * `sc_two_int` and `sc_two_fp`: the SAME machine code read through
    //     `swiftcall` and through C returns the same values, so the two
    //     conventions take components 0 and 1 of each class from the same
    //     registers — RAX,RDX and XMM0,XMM1;
    //   * `sc_mix_2i2f`: `swiftcc` runs the two class counters INDEPENDENTLY
    //     (RAX,RDX + XMM0,XMM1), exactly as trust-cg's return classifier does,
    //     and `sc_mix_shared_counter_ctl` refutes the one-counter reading;
    //   * `sc_three_int`, `sc_four_int`, `sc_four_fp`: `swiftcc`'s files extend
    //     to RCX, R8, XMM2, XMM3 — trust-cg's stop at 2, and the two sret
    //     witnesses show C does not reach there either;
    //   * every control is read WRONG.
    //
    // The agreement therefore holds exactly while each class stays within 2,
    // which is `PerClass { int: 2, fp: 2 }`. The constant the adapter consults
    // is compared against that MEASUREMENT here, not against a second copy of
    // itself.
    // ---------------------------------------------------------------------
    assert_eq!(
        trust_cg_lower::swift_return_budget_for_arch(trust_cg_lower::GuardCarrierArch::X86_64),
        trust_cg_lower::SwiftReturnBudget::PerClass { int: 2, fp: 2 },
        "the x86-64 Swift return budget no longer matches the swiftcc/C agreement measured \
         above: the two conventions were just observed to agree on 2 integer and 2 FP return \
         components on this host and to diverge past that"
    );
}
