// trust-cg-codegen/tests/macho_code_signature_native.rs - Apple Silicon code-signing controls
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Native code-signing controls for Mach-O images on Apple Silicon.
//!
//! The standalone linker ad-hoc signs every executable and dylib and checks
//! the result with the independent verifier `macho::codesign`. Here Apple's
//! `codesign --verify --strict` and the kernel judge the same bytes: signed
//! standalone images verify and run (or load through `dlopen`), while a changed
//! code byte, a broken SuperBlob and an ld64 image linked without its signature
//! are refused by the verifier and by `codesign`, and the kernel kills the
//! process with SIGKILL. The verifier is held to Apple's own signers as well:
//! ld64 signatures and `codesign -s - --options runtime --entitlements`
//! signatures (internal requirements, XML and DER entitlements, the empty CMS
//! wrapper and 16 KiB code pages) verify, and an entitlements byte changed
//! after signing is refused by both the verifier and `codesign`. The verifier
//! is stricter than `codesign --verify` where the kernel is: 8 KiB and
//! whole-image code pages, and a 32-bit `codeLimit` that disagrees with
//! `codeLimit64`, are killed at exec and refused by the verifier.
//!
//! This is execution and tool-agreement evidence on this host (macOS 26.6,
//! Apple M4 Max). The kernel's signing policy remains trusted base; nothing
//! here models or proves it.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/rosetta.rs"]
mod process;

use std::ffi::{CStr, CString};
use std::fs;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use trust_cg_codegen::macho::codesign::{
    CS_ADHOC, CS_EXECSEG_MAIN_BINARY, CS_LINKER_SIGNED, CS_RUNTIME, CSSLOT_DER_ENTITLEMENTS,
    CSSLOT_ENTITLEMENTS, CSSLOT_REQUIREMENTS, CodeSignatureError, verify_ad_hoc_signature,
};
use trust_cg_codegen::macho::linker::{
    DylibConfig, MachOParser, link, link_dylib, link_with_dylibs,
};
use trust_cg_codegen::macho::writer::MachOWriter;

/// Resolved on PATH, as the Darwin floor records its identity.
const CODESIGN: &str = "codesign";
const SIGKILL: i32 = 9;
/// `mov x0, #42`, the exit status of the standalone program.
const MOV_X0_42: u32 = 0xD280_0540;
/// `mov x0, #43`.
const MOV_X0_43: u32 = 0xD280_0560;
const ALLOW_JIT_PLIST: &str = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \
\"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n\
<plist version=\"1.0\"><dict><key>com.apple.security.cs.allow-jit</key><true/></dict></plist>\n";

fn text_object(symbol: &str, words: &[u32]) -> Vec<u8> {
    let code: Vec<u8> = words.iter().flat_map(|word| word.to_le_bytes()).collect();
    let mut writer = MachOWriter::new();
    writer.add_text_section(&code);
    writer.add_symbol(symbol, 1, 0, true).unwrap();
    writer.write().unwrap()
}

/// `_main`: `mov x16, #1; mov x0, #42; svc #0x80` (Darwin exit(42)).
fn exit42_object() -> Vec<u8> {
    text_object("_main", &[0xD280_0030, MOV_X0_42, 0xD400_1001])
}

fn standalone_executable() -> Vec<u8> {
    link(&[MachOParser::parse(&exit42_object()).unwrap()]).unwrap()
}

fn write_executable(directory: &Path, name: &str, bytes: &[u8]) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = directory.join(name);
    fs::write(&path, bytes).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    path
}

fn run_tool(program: &str, args: &[&str], path: &Path) -> Output {
    let mut command = Command::new(program);
    command.args(args).arg(path);
    let result =
        process::command_output_with_timeout(&mut command, process::codegen_link_timeout())
            .unwrap_or_else(|error| panic!("{program} could not start: {error}"));
    assert!(!result.timed_out, "{program} {args:?} timed out");
    result.output
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// `codesign --verify --strict`; returns whether it accepted and its stderr.
fn codesign_verify(path: &Path) -> (bool, String) {
    let output = run_tool(CODESIGN, &["--verify", "--strict", "--verbose=2"], path);
    (output.status.success(), stderr(&output))
}

/// `codesign --display --verbose=4` (it reports on stderr).
fn codesign_display(path: &Path) -> String {
    let output = run_tool(CODESIGN, &["--display", "--verbose=4"], path);
    assert!(output.status.success(), "{}", stderr(&output));
    stderr(&output)
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Exited(i32),
    Signaled(i32),
}

fn run(path: &Path) -> Outcome {
    let mut command = Command::new(path);
    let result = process::command_output_with_timeout(&mut command, process::codegen_run_timeout())
        .unwrap_or_else(|error| panic!("{} could not start: {error}", path.display()));
    assert!(!result.timed_out, "{} timed out", path.display());
    let status = result.output.status;
    match (status.code(), status.signal()) {
        (Some(code), _) => Outcome::Exited(code),
        (None, Some(signal)) => Outcome::Signaled(signal),
        _ => panic!("{} ended without a status: {status:?}", path.display()),
    }
}

fn replace_word(bytes: &mut [u8], from: u32, to: u32) {
    let at = bytes
        .windows(4)
        .position(|window| window == from.to_le_bytes())
        .expect("instruction word present");
    bytes[at..at + 4].copy_from_slice(&to.to_le_bytes());
}

fn compile_c(directory: &Path, name: &str, source: &str, args: &[&str]) -> PathBuf {
    let source_path = directory.join(format!("{name}.c"));
    fs::write(&source_path, source).unwrap();
    let output_path = directory.join(name);
    let mut command = Command::new("cc");
    command
        .args(["-O1", "-o"])
        .arg(&output_path)
        .args(args)
        .arg(&source_path);
    let result =
        process::command_output_with_timeout(&mut command, process::codegen_link_timeout())
            .expect("cc starts");
    assert!(!result.timed_out, "cc timed out");
    assert!(
        result.output.status.success(),
        "cc {args:?}: {}",
        stderr(&result.output)
    );
    output_path
}

mod dl {
    use std::ffi::{c_char, c_int, c_void};
    pub const RTLD_NOW: c_int = 2;
    unsafe extern "C" {
        pub fn dlopen(path: *const c_char, mode: c_int) -> *mut c_void;
        pub fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
        pub fn dlerror() -> *const c_char;
    }
}

#[test]
fn standalone_executables_verify_with_codesign_and_run() {
    let directory = tempfile::tempdir().unwrap();
    let with_libsystem = link_with_dylibs(
        &[MachOParser::parse(&exit42_object()).unwrap()],
        &DylibConfig::with_libsystem(),
    )
    .unwrap();
    for (name, bytes) in [
        ("plain", standalone_executable()),
        ("libsystem", with_libsystem),
    ] {
        let signature = verify_ad_hoc_signature(&bytes).unwrap();
        assert_eq!(
            signature.code_directory.flags,
            CS_ADHOC | CS_LINKER_SIGNED,
            "{name}"
        );
        let path = write_executable(directory.path(), name, &bytes);
        let (accepted, detail) = codesign_verify(&path);
        assert!(accepted, "codesign refused standalone {name}: {detail}");
        let display = codesign_display(&path);
        for expected in [
            "Identifier=trust-cg",
            "flags=0x20002(adhoc,linker-signed)",
            "Hash type=sha256",
            "Page size=4096",
            "Executable Segment flags=0x1",
        ] {
            assert!(display.contains(expected), "{name}: {expected}\n{display}");
        }
        assert_eq!(run(&path), Outcome::Exited(42), "{name}");
    }
}

#[test]
fn standalone_dylib_verifies_with_codesign_and_loads() {
    let directory = tempfile::tempdir().unwrap();
    let object = text_object("_tcg_answer", &[0x5280_0540, 0xD65F_03C0]);
    let bytes = link_dylib(
        &[MachOParser::parse(&object).unwrap()],
        &DylibConfig::new(),
        "@rpath/libtcg_signed_answer.dylib",
    )
    .unwrap();
    let signature = verify_ad_hoc_signature(&bytes).unwrap();
    assert_eq!(
        signature.code_directory.exec_segment.unwrap().flags & CS_EXECSEG_MAIN_BINARY,
        0
    );
    let path = write_executable(directory.path(), "libtcg_signed_answer.dylib", &bytes);
    let (accepted, detail) = codesign_verify(&path);
    assert!(accepted, "codesign refused the standalone dylib: {detail}");
    let display = codesign_display(&path);
    assert!(
        display.contains("flags=0x20002(adhoc,linker-signed)"),
        "{display}"
    );
    assert!(
        display.contains("Executable Segment flags=0x0"),
        "{display}"
    );

    let c_path = CString::new(path.to_str().unwrap()).unwrap();
    // SAFETY: dlopen/dlsym receive NUL-terminated strings; the dylib stays
    // loaded for the process lifetime and `_tcg_answer` is `mov w0, #42; ret`,
    // an `extern "C" fn() -> i32`.
    let answer = unsafe {
        let handle = dl::dlopen(c_path.as_ptr(), dl::RTLD_NOW);
        assert!(
            !handle.is_null(),
            "dlopen refused the standalone dylib: {:?}",
            CStr::from_ptr(dl::dlerror())
        );
        let symbol = dl::dlsym(handle, c"tcg_answer".as_ptr());
        assert!(!symbol.is_null(), "tcg_answer is exported");
        let function: extern "C" fn() -> i32 = std::mem::transmute(symbol);
        function()
    };
    assert_eq!(answer, 42);
}

#[test]
fn changed_code_byte_is_refused_by_the_verifier_codesign_and_the_kernel() {
    let directory = tempfile::tempdir().unwrap();
    let mut bytes = standalone_executable();
    replace_word(&mut bytes, MOV_X0_42, MOV_X0_43);
    assert!(matches!(
        verify_ad_hoc_signature(&bytes),
        Err(CodeSignatureError::CodePageHashMismatch { slot: 0, .. })
    ));
    let path = write_executable(directory.path(), "tampered", &bytes);
    let (accepted, detail) = codesign_verify(&path);
    assert!(!accepted, "codesign accepted a changed code page");
    assert!(detail.contains("invalid signature"), "{detail}");
    // The kernel checks the page hash when the page is mapped in, before the
    // changed instruction can run: the process never exits 43.
    assert_eq!(run(&path), Outcome::Signaled(SIGKILL));
}

#[test]
fn broken_superblob_is_refused_by_the_verifier_codesign_and_the_kernel() {
    let directory = tempfile::tempdir().unwrap();
    let mut bytes = standalone_executable();
    let start = verify_ad_hoc_signature(&bytes).unwrap().signature_offset as usize;
    bytes[start] ^= 0xFF;
    assert!(matches!(
        verify_ad_hoc_signature(&bytes),
        Err(CodeSignatureError::MalformedSuperBlob { .. })
    ));
    let path = write_executable(directory.path(), "broken", &bytes);
    let (accepted, detail) = codesign_verify(&path);
    assert!(!accepted, "codesign accepted a broken SuperBlob: {detail}");
    assert_eq!(run(&path), Outcome::Signaled(SIGKILL));
}

#[test]
fn ld64_signatures_verify_independently_and_unsigned_output_is_killed() {
    let directory = tempfile::tempdir().unwrap();
    let program = "int main(void) { return 3; }\n";
    let library = "int tcg_scale(int x) { return x * 7 + 1; }\n";
    let executable = compile_c(directory.path(), "ld64prog", program, &[]);
    let dylib = compile_c(directory.path(), "libld64.dylib", library, &["-dynamiclib"]);
    for (path, main_binary) in [(&executable, true), (&dylib, false)] {
        let name = path.file_name().unwrap().to_str().unwrap();
        let signature = verify_ad_hoc_signature(&fs::read(path).unwrap())
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        let code_directory = &signature.code_directory;
        assert_eq!(code_directory.flags, CS_ADHOC | CS_LINKER_SIGNED, "{name}");
        assert_eq!(code_directory.identifier, name);
        assert_eq!(
            code_directory.exec_segment.unwrap().flags & CS_EXECSEG_MAIN_BINARY != 0,
            main_binary,
            "{name}"
        );
        let (accepted, detail) = codesign_verify(path);
        assert!(accepted, "{name}: {detail}");
    }
    assert_eq!(run(&executable), Outcome::Exited(3));

    // The same program linked without ld64's signature: unsigned by the
    // verifier and codesign, and killed by the kernel at exec.
    let unsigned = compile_c(
        directory.path(),
        "ld64unsigned",
        program,
        &["-Wl,-no_adhoc_codesign"],
    );
    assert_eq!(
        verify_ad_hoc_signature(&fs::read(&unsigned).unwrap()),
        Err(CodeSignatureError::Unsigned)
    );
    let (accepted, detail) = codesign_verify(&unsigned);
    assert!(!accepted);
    assert!(detail.contains("not signed at all"), "{detail}");
    assert_eq!(run(&unsigned), Outcome::Signaled(SIGKILL));
}

#[test]
fn codesign_hardened_runtime_entitlement_signatures_verify_independently() {
    let directory = tempfile::tempdir().unwrap();
    let entitlements = directory.path().join("allow-jit.plist");
    fs::write(&entitlements, ALLOW_JIT_PLIST).unwrap();
    let path = write_executable(directory.path(), "entitled", &standalone_executable());
    let output = run_tool(
        CODESIGN,
        &[
            "--force",
            "--sign",
            "-",
            "--options",
            "runtime",
            "--entitlements",
            entitlements.to_str().unwrap(),
        ],
        &path,
    );
    assert!(output.status.success(), "{}", stderr(&output));

    let bytes = fs::read(&path).unwrap();
    let signature = verify_ad_hoc_signature(&bytes).unwrap();
    let code_directory = &signature.code_directory;
    assert_eq!(code_directory.flags, CS_ADHOC | CS_RUNTIME);
    assert!(code_directory.has_hardened_runtime());
    assert!(!code_directory.is_linker_signed());
    assert_eq!(code_directory.page_size, 16384);
    assert!(code_directory.runtime_version.is_some());
    assert_eq!(
        code_directory.exec_segment.unwrap().flags & CS_EXECSEG_MAIN_BINARY,
        CS_EXECSEG_MAIN_BINARY
    );
    for slot in [
        CSSLOT_REQUIREMENTS,
        CSSLOT_ENTITLEMENTS,
        CSSLOT_DER_ENTITLEMENTS,
    ] {
        assert!(
            signature.bound_special_slots.contains(&slot),
            "{:?}",
            signature.bound_special_slots
        );
    }
    let xml = signature.entitlements_xml.as_deref().unwrap();
    assert!(
        xml.contains("<key>com.apple.security.cs.allow-jit</key>"),
        "{xml}"
    );
    assert!(signature.has_der_entitlements);
    assert!(signature.has_empty_cms_wrapper);
    let (accepted, detail) = codesign_verify(&path);
    assert!(accepted, "{detail}");
    // The hardened runtime does not change what this program does.
    assert_eq!(run(&path), Outcome::Exited(42));

    // One entitlements byte changed after signing breaks special slot 5 for
    // both the verifier and codesign.
    let mut edited = bytes.clone();
    let key = edited
        .windows(b"allow-jit".len())
        .position(|window| window == b"allow-jit")
        .expect("XML entitlements are embedded");
    edited[key] = b'A';
    assert_eq!(
        verify_ad_hoc_signature(&edited),
        Err(CodeSignatureError::SpecialSlotHashMismatch {
            slot: 0,
            special_slot: CSSLOT_ENTITLEMENTS
        })
    );
    let edited_path = write_executable(directory.path(), "entitled-edited", &edited);
    let (accepted, detail) = codesign_verify(&edited_path);
    assert!(!accepted, "codesign accepted edited entitlements: {detail}");
}

/// Signatures whose every hash matches but which the arm64 kernel kills at
/// exec: `codesign --pagesize 8192` and `--pagesize 0` (one page for the whole
/// image), and a CodeDirectory whose 32-bit `codeLimit` is zero while
/// `codeLimit64` names the signature offset. `codesign --verify --strict`
/// accepted all three on macOS 26.6; the verifier refuses each by name, so the
/// post-link check cannot pass an image the kernel will not run.
#[test]
fn kernel_killed_page_sizes_and_code_limits_are_refused_by_the_verifier() {
    let directory = tempfile::tempdir().unwrap();
    for (page_size, shift) in [("8192", 13u8), ("0", 0)] {
        let path = write_executable(
            directory.path(),
            &format!("pages-{page_size}"),
            &standalone_executable(),
        );
        let output = run_tool(
            CODESIGN,
            &["--force", "--sign", "-", "--pagesize", page_size],
            &path,
        );
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(
            verify_ad_hoc_signature(&fs::read(&path).unwrap()),
            Err(CodeSignatureError::UnsupportedPageSize { slot: 0, shift }),
            "--pagesize {page_size}"
        );
        assert_eq!(
            run(&path),
            Outcome::Signaled(SIGKILL),
            "--pagesize {page_size}"
        );
    }

    // The CodeDirectory is not itself hashed by an ad-hoc signature, so its
    // limit fields can be rewritten with every page hash still matching.
    let mut bytes = standalone_executable();
    let signature_offset = verify_ad_hoc_signature(&bytes).unwrap().signature_offset;
    let start = signature_offset as usize;
    let be32 = |bytes: &[u8], at: usize| u32::from_be_bytes(bytes[at..at + 4].try_into().unwrap());
    assert_eq!(be32(&bytes, start + 12), 0, "slot 0 is indexed first");
    let cd = start + be32(&bytes, start + 16) as usize;
    let code_limit = be32(&bytes, cd + 32);
    assert_eq!(u64::from(code_limit), signature_offset);
    bytes[cd + 56..cd + 64].copy_from_slice(&signature_offset.to_be_bytes());
    // Agreeing 32- and 64-bit limits verify and run.
    verify_ad_hoc_signature(&bytes).unwrap();
    let agreeing = write_executable(directory.path(), "limit64-agreeing", &bytes);
    assert_eq!(run(&agreeing), Outcome::Exited(42));
    bytes[cd + 32..cd + 36].copy_from_slice(&0u32.to_be_bytes());
    assert_eq!(
        verify_ad_hoc_signature(&bytes),
        Err(CodeSignatureError::CodeLimitMismatch {
            slot: 0,
            code_limit: 0,
            signature_offset
        })
    );
    let disagreeing = write_executable(directory.path(), "limit64-only", &bytes);
    assert_eq!(run(&disagreeing), Outcome::Signaled(SIGKILL));
}
