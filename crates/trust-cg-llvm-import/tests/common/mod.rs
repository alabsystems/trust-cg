// trust-cg-llvm-import / tests / common / mod.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Host facts and object readers shared by the importer's native tests.
//!
//! Two hosts link and run imported programs: AArch64 Linux GNU (ELF objects
//! for `aarch64-unknown-linux-gnu`) and AArch64 macOS (Mach-O objects for
//! `aarch64-apple-darwin`). Every compile names its triple explicitly, so the
//! object container, calling convention and ISA contract never come from the
//! host through `Compiler::new`. A leg that needs a native host prints
//! `SKIP <test>: <reason>` on any other host and returns; that line is what the
//! floor runners refuse, so a skipped leg can never count as a pass.
//!
//! External readers are chosen per container and come with the host's C
//! toolchain: Mach-O objects are read by Apple's `otool -tv` and `nm -u`, and
//! ELF objects by the binutils `objdump -d --no-show-raw-insn` and `nm -u` that
//! the Linux `cc` itself runs on. Their syntax differs only in how NEON
//! arrangements are spelled, which [`has_vector_insn`] accepts in both forms.
//! The in-tree Mach-O and ELF readers ([`undefined_symbols`]) read either
//! container on every host.

#![allow(dead_code)]

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::elf::reparse::{ElfObjectRecords, read_object_records};
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_llvm_import::import_text_for_target;

#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;

/// Apple arm64: Mach-O objects, DarwinPCS, C symbols with a `_` prefix.
pub const APPLE: &str = "aarch64-apple-darwin";
/// Generic Linux AArch64: ELF objects, AAPCS64, unprefixed C symbols.
pub const LINUX: &str = "aarch64-unknown-linux-gnu";
/// Both explicit targets, for object-level checks that need no host tool.
pub const TARGETS: [&str; 2] = [APPLE, LINUX];

/// AArch64 Linux GNU: ELF objects linked by the host `cc`.
pub const LINUX_GNU: bool = cfg!(all(
    target_arch = "aarch64",
    target_os = "linux",
    target_env = "gnu"
));
/// AArch64 macOS: Mach-O objects linked by the host `cc`/ld64.
pub const DARWIN: bool = cfg!(all(target_arch = "aarch64", target_os = "macos"));
/// Whether objects for [`HOST_TRIPLE`] can be linked, run and read here.
pub const NATIVE: bool = LINUX_GNU || DARWIN;
/// The triple whose objects this host links, runs and reads with its own
/// tools. A non-native host keeps the Apple spelling but never links it.
pub const HOST_TRIPLE: &str = if LINUX_GNU { LINUX } else { APPLE };

/// `true` on a native host. Elsewhere prints the explicit skip line naming
/// the missing authority and returns `false` so the caller can `return`.
pub fn native_host_or_skip(test: &str) -> bool {
    if NATIVE {
        return true;
    }
    eprintln!(
        "SKIP {test}: needs a native AArch64 Linux GNU or macOS host to link, run and read \
         {HOST_TRIPLE} objects (host is {} / {})",
        std::env::consts::OS,
        std::env::consts::ARCH
    );
    false
}

/// Object container of an explicit triple.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Container {
    MachO,
    Elf,
}

/// The container `triple` selects. Only the two native triples are modeled.
pub fn container(triple: &str) -> Container {
    match triple {
        APPLE => Container::MachO,
        LINUX => Container::Elf,
        other => panic!("no modeled object container for {other:?}"),
    }
}

/// The object-file spelling of C symbol `name` for `triple`.
pub fn object_symbol(triple: &str, name: &str) -> String {
    match container(triple) {
        Container::MachO => format!("_{name}"),
        Container::Elf => name.to_owned(),
    }
}

/// The importer's standard test configuration at `opt_level`.
pub fn config(opt_level: OptLevel, spec: &TargetSpec) -> CompilerConfig {
    CompilerConfig {
        opt_level,
        target: spec.architecture,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        jit_external_symbol_resolution: Default::default(),
        panic_unwind: false,
        ..CompilerConfig::default()
    }
}

/// A compiler for the explicit `triple` at `opt_level`.
pub fn compiler_for(triple: &str, opt_level: OptLevel) -> Compiler {
    let spec = TargetSpec::parse(triple).expect("target spec");
    Compiler::new_for_target_spec(config(opt_level, &spec), spec)
        .with_codegen_license(permit_unlicensed())
}

/// Import `src` for the explicit `triple` and compile it for that triple; the
/// object must be in that triple's container.
///
/// The import names the triple ([`import_text_for_target`], llc's
/// `-mtriple`): the module then states the target it is compiled for, which
/// trust-ir requires of a module with an FFI boundary (`TargetInfoRequired`,
/// refused at every ingestion entry since WS7.3), and the importer's
/// target-dependent readings are the compiled target's.
pub fn compile_for(src: &str, module_name: &str, triple: &str, opt_level: OptLevel) -> Vec<u8> {
    let module = import_text_for_target(src, module_name, triple).expect("import");
    let object = compiler_for(triple, opt_level)
        .compile(&module)
        .unwrap_or_else(|e| panic!("compile `{module_name}` for `{triple}` failed: {e}"))
        .object_code;
    assert_container(&object, triple, module_name);
    object
}

/// [`compile_for`] for this host's [`HOST_TRIPLE`].
pub fn compile_for_host(src: &str, module_name: &str, opt_level: OptLevel) -> Vec<u8> {
    compile_for(src, module_name, HOST_TRIPLE, opt_level)
}

/// `object` is a relocatable AArch64 object in `triple`'s container:
/// Mach-O 64 arm64 MH_OBJECT, or ELF64 little-endian ET_REL EM_AARCH64.
pub fn assert_container(object: &[u8], triple: &str, what: &str) {
    let u16_at = |at: usize| u16::from_le_bytes([object[at], object[at + 1]]);
    let u32_at = |at: usize| u32::from_le_bytes(object[at..at + 4].try_into().unwrap());
    assert!(object.len() >= 64, "`{what}` for `{triple}` is too short");
    match container(triple) {
        // MH_MAGIC_64, CPU_TYPE_ARM64, MH_OBJECT.
        Container::MachO => assert_eq!(
            (u32_at(0), u32_at(4), u32_at(12)),
            (0xfeed_facf, 0x0100_000c, 1),
            "`{what}` for `{triple}` is not a Mach-O arm64 relocatable object"
        ),
        // ELF magic, ELFCLASS64, ELFDATA2LSB, ET_REL, EM_AARCH64.
        Container::Elf => assert!(
            object.starts_with(b"\x7fELF")
                && object[4] == 2
                && object[5] == 1
                && u16_at(16) == 1
                && u16_at(18) == 183,
            "`{what}` for `{triple}` is not an ELF64 AArch64 relocatable object"
        ),
    }
}

/// The named undefined symbols of `object`, read by the in-tree Mach-O or ELF
/// reader for its container.
pub fn undefined_symbols(object: &[u8]) -> BTreeSet<String> {
    if object.starts_with(b"\x7fELF") {
        read_object_records(object)
            .expect("read ELF object records")
            .symbols
            .into_iter()
            .filter(|symbol| symbol.is_undefined_reference())
            .map(|symbol| symbol.name)
            .collect()
    } else {
        MachOParser::parse(object)
            .expect("parse Mach-O object")
            .symbols
            .into_iter()
            .filter(|symbol| symbol.is_undefined())
            .map(|symbol| symbol.name.as_str().to_owned())
            .collect()
    }
}

/// The bytes of ELF section `index`: its file extent from the section header
/// table (`e_shoff`; `sh_offset`, `sh_size`).
pub fn elf_section_bytes(object: &[u8], index: usize) -> &[u8] {
    let u64_at = |at: usize| {
        usize::try_from(u64::from_le_bytes(object[at..at + 8].try_into().unwrap())).unwrap()
    };
    let header = u64_at(0x28) + index * 64;
    &object[u64_at(header + 0x18)..][..u64_at(header + 0x20)]
}

pub fn elf_section_index(records: &ElfObjectRecords, name: &str) -> usize {
    records
        .sections
        .iter()
        .position(|section| section.name == name)
        .unwrap_or_else(|| panic!("ELF section `{name}` in {:?}", records.sections))
}

pub fn elf_symbol_index(records: &ElfObjectRecords, name: &str) -> usize {
    records
        .symbols
        .iter()
        .position(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("ELF symbol `{name}` in {:?}", records.symbols))
}

/// Relocation types in `.text` against symbol index `symbol`, in record order.
pub fn elf_text_relocation_kinds(records: &ElfObjectRecords, symbol: usize) -> Vec<u32> {
    let text = elf_section_index(records, ".text");
    records
        .relocations
        .iter()
        .filter(|relocation| {
            relocation.target_section == text && relocation.record.symbol_index as usize == symbol
        })
        .map(|relocation| relocation.record.reloc_type)
        .collect()
}

/// The environment variable that keeps a failing test's scratch directory.
pub const KEEP_ON_FAILURE: &str = "TRUST_CG_KEEP_TEST_OBJECTS";

/// A scratch directory this test owns (RAII). It dereferences to its path,
/// and dropping it removes the directory and everything in it, whether the
/// test passed or failed; a failing test's directory is kept (and named)
/// only when [`KEEP_ON_FAILURE`] is set.
pub struct ScratchDir(PathBuf);

impl ScratchDir {
    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl std::ops::Deref for ScratchDir {
    type Target = PathBuf;

    fn deref(&self) -> &PathBuf {
        &self.0
    }
}

impl AsRef<Path> for ScratchDir {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

impl AsRef<std::ffi::OsStr> for ScratchDir {
    fn as_ref(&self) -> &std::ffi::OsStr {
        self.0.as_os_str()
    }
}

impl std::fmt::Debug for ScratchDir {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, formatter)
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        if std::thread::panicking() && std::env::var_os(KEEP_ON_FAILURE).is_some() {
            eprintln!(
                "{KEEP_ON_FAILURE} is set: keeping the failing test's scratch directory {}",
                self.0.display()
            );
        } else {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
}

/// A fresh directory under the system temporary directory, owned by the
/// returned [`ScratchDir`]. The name carries the process id, the clock and a
/// per-process sequence number, and the directory is made with an exclusive
/// `mkdir`, so two tests of one process can never be handed the same one.
pub fn unique_temp_dir(name: &str) -> ScratchDir {
    use std::sync::atomic::{AtomicU64, Ordering};
    static SEQUENCE: AtomicU64 = AtomicU64::new(0);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust-cg-import-{name}-{}-{nanos}-{}",
        std::process::id(),
        SEQUENCE.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&dir).unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
    ScratchDir(dir)
}

/// Use one developer-selected compiler and SDK for Darwin's C/LLVM oracle
/// and linker. Lean ships a `clang` without Apple's default SDK discovery;
/// searching PATH independently for `clang` and `cc` can split that oracle.
/// `xcrun --sdk macosx` names the selected developer toolchain explicitly.
pub fn native_c_command() -> Command {
    #[cfg(target_os = "macos")]
    {
        use std::sync::OnceLock;
        static TOOLCHAIN: OnceLock<(PathBuf, PathBuf)> = OnceLock::new();
        let (compiler, sdk) = TOOLCHAIN.get_or_init(|| {
            let discover = |argument: &str, name: Option<&str>| {
                let mut command = Command::new("/usr/bin/xcrun");
                command.args(["--sdk", "macosx", argument]);
                if let Some(name) = name {
                    command.arg(name);
                }
                let output = command.output().expect("run Apple's xcrun");
                assert!(
                    output.status.success(),
                    "xcrun {argument}: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let text = String::from_utf8(output.stdout).expect("xcrun path is UTF-8");
                let path = PathBuf::from(text.trim());
                assert!(
                    path.is_absolute(),
                    "xcrun returned a relative path: {text:?}"
                );
                path.canonicalize().expect("xcrun path exists")
            };
            let compiler = discover("--find", Some("clang"));
            let sdk = discover("--show-sdk-path", None);
            assert!(compiler.is_file(), "xcrun clang is not a file");
            assert!(sdk.is_dir(), "xcrun macosx SDK is not a directory");
            (compiler, sdk)
        });
        let mut command = Command::new(compiler);
        command.arg("-isysroot").arg(sdk);
        command
    }
    #[cfg(not(target_os = "macos"))]
    Command::new("cc")
}

/// Link `obj_path` into `bin_path` with this host's C oracle.
pub fn link_with_cc(obj_path: &Path, bin_path: &Path) {
    let output = native_c_command()
        .arg(obj_path)
        .arg("-o")
        .arg(bin_path)
        .output()
        .expect("run cc");
    assert!(
        output.status.success(),
        "cc failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// `exit N` or `signal N`.
pub fn describe_status(status: ExitStatus) -> String {
    if let Some(code) = status.code() {
        return format!("exit {code}");
    }
    #[cfg(unix)]
    if let Some(signal) = status.signal() {
        return format!("signal {signal}");
    }
    "unknown status".to_string()
}

/// Run `program args... path`, require success, and return stdout.
fn run_reader(program: &str, args: &[&str], path: &Path) -> String {
    let output = Command::new(program)
        .args(args)
        .arg(path)
        .output()
        .unwrap_or_else(|e| panic!("run {program}: {e}"));
    assert!(
        output.status.success(),
        "{program} {} {} failed with {}\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        path.display(),
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// `nm -u` of the object at `obj_path`: Apple `nm` for Mach-O on macOS,
/// binutils `nm` for ELF on Linux.
pub fn nm_undefined(obj_path: &Path) -> String {
    run_reader("nm", &["-u"], obj_path)
}

/// The instructions of a disassembled object, grouped by function symbol.
/// Each instruction is one lower-cased `mnemonic\toperands` line with its
/// address removed.
#[derive(Debug)]
pub struct Disassembly {
    raw: String,
    functions: Vec<(String, Vec<String>)>,
}

impl Disassembly {
    /// Every instruction of the object.
    pub fn text(&self) -> String {
        self.functions
            .iter()
            .flat_map(|(_, body)| body.iter().map(String::as_str))
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// The instructions of the function whose C name is `symbol`.
    pub fn function(&self, symbol: &str) -> String {
        let wanted = symbol.to_lowercase();
        let (_, body) = self
            .functions
            .iter()
            .find(|(name, _)| *name == wanted)
            .unwrap_or_else(|| panic!("missing disassembly for symbol `{symbol}`:\n{}", self.raw));
        body.join("\n")
    }
}

/// Disassemble the text of the `triple` object at `obj_path` with the reader
/// for its container: `otool -tv` (Apple syntax, `_`-prefixed labels) for
/// Mach-O, `objdump -d --no-show-raw-insn` (generic syntax, `<name>:`
/// labels) for ELF.
pub fn disassemble(obj_path: &Path, triple: &str) -> Disassembly {
    let raw = match container(triple) {
        Container::MachO => run_reader("otool", &["-tv"], obj_path),
        Container::Elf => run_reader("objdump", &["-d", "--no-show-raw-insn"], obj_path),
    }
    .to_lowercase();
    let mut functions: Vec<(String, Vec<String>)> = Vec::new();
    for line in raw.lines() {
        let label = match container(triple) {
            // `_main:`; `ltmp0:` section labels and the `path:` header line
            // do not start a function.
            Container::MachO => line
                .strip_suffix(':')
                .filter(|label| !label.contains('\t'))
                .and_then(|label| label.strip_prefix('_')),
            // `0000000000000000 <main>:`
            Container::Elf => line
                .strip_suffix(">:")
                .and_then(|head| head.split_once(" <"))
                .filter(|(address, _)| address.bytes().all(|b| b.is_ascii_hexdigit()))
                .map(|(_, name)| name),
        };
        if let Some(name) = label {
            functions.push((name.to_owned(), Vec::new()));
            continue;
        }
        let instruction = match container(triple) {
            // `0000000000000000\trbit\tw0, w0`
            Container::MachO => line
                .split_once('\t')
                .filter(|(address, _)| {
                    !address.is_empty() && address.bytes().all(|b| b.is_ascii_hexdigit())
                })
                .map(|(_, rest)| rest),
            // `   0:\trbit\tw0, w0`
            Container::Elf => line
                .split_once(":\t")
                .filter(|(address, _)| {
                    let address = address.trim_start();
                    !address.is_empty() && address.bytes().all(|b| b.is_ascii_hexdigit())
                })
                .map(|(_, rest)| rest),
        };
        if let Some(instruction) = instruction {
            let instruction = instruction.trim_end().to_owned();
            match functions.last_mut() {
                Some((_, body)) => body.push(instruction),
                None => functions.push((String::new(), vec![instruction])),
            }
        }
    }
    assert!(
        functions.iter().any(|(_, body)| !body.is_empty()),
        "no instructions read from the disassembly:\n{raw}"
    );
    Disassembly { raw, functions }
}

/// Whether `body` holds `mnemonic` on `arrangement` vectors, in Apple syntax
/// (`rbit.8b\tv0, v1`) or generic syntax (`rbit\tv0.8b, v1.8b`, every vector
/// operand carrying the arrangement).
pub fn has_vector_insn(body: &str, mnemonic: &str, arrangement: &str) -> bool {
    let apple = format!("{mnemonic}.{arrangement}");
    let suffix = format!(".{arrangement}");
    body.lines().any(|line| {
        let (name, operands) = line.split_once('\t').unwrap_or((line, ""));
        if name == apple {
            return true;
        }
        if name != mnemonic {
            return false;
        }
        let vectors: Vec<&str> = operands
            .split(',')
            .map(str::trim)
            .filter(|operand| {
                operand.starts_with('v')
                    && operand[1..].split_once('.').is_some_and(|(n, _)| {
                        !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit())
                    })
            })
            .collect();
        !vectors.is_empty() && vectors.iter().all(|operand| operand.ends_with(&suffix))
    })
}

/// Imported modules carry no codegen license (`body_gate: None`: the LLVM
/// importer stamps none), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). The compiles of this directory's tests state
/// `Permit` explicitly through this helper, so none of them passes (or fails
/// by name) because it was silently refused.
pub fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
