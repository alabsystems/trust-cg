//! Native Linux ELF twin of `tls_thread_local_aarch64.rs`: a real
//! `#[thread_local]` static, read and written through the rustc bridge for
//! `aarch64-unknown-linux-gnu`, links with GNU `cc -pthread` and runs a C driver
//! that observes per-thread isolation, with an LLVM twin of every lane.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0
//!
//! This target is mandatory on its named host, not a portable skip. The
//! separate bridge runner binds a freshly built backend by path and SHA-256
//! (`TCG_TEST_BACKEND_PATH`/`TCG_TEST_BACKEND_SHA256`); a standalone invocation
//! instead loads, and hashes, the library Cargo built for this test build. It
//! never builds into the shared target directory or selects a cached library.
//!
//! WHAT IS CHECKED, AT O0-O3. The bridge lowers one module per `MonoItem`, so
//! the static and its accessors start in separate objects; since the
//! multi-object publication (`ld -r`, 2026-10-23) the requested `--emit=obj`
//! output is those objects partial-linked into one. Objects are selected by
//! defined symbol (`readelf -sW`), never by file name or count; an object
//! that defines none of `X`/`read_x`/`bump_x` is not linked. `X` must be an
//! `STT_TLS` definition in exactly one object, inside an `SHF_TLS` section
//! (`.tdata` or `.tbss`); an accessor in that object must not also import it,
//! and an accessor in any other object must import it as an undefined
//! `STT_TLS` symbol. Every accessor object reads the thread pointer
//! (`tpidr_el0`), names `X` in no relocation outside a TLS sequence, and
//! carries only complete AArch64 ELF TLS relocation sequences of exactly one
//! access model against `X` (at least one sequence): the general-dynamic TLS descriptor
//! (`R_AARCH64_TLSDESC_{ADR_PAGE21,LD64_LO12,ADD_LO12,CALL}`), initial-exec
//! (`R_AARCH64_TLSIE_*_GOTTPREL_*`) or local-exec (`R_AARCH64_TLSLE_ADD_TPREL_*`).
//! The bridge takes the access model from the session's relocation model, and
//! a `staticlib` on this target gets the target-default PIC model, so the
//! accessors use the TLS descriptor, as LLVM's do for the same session: at each
//! level the CG objects' set of TLS relocation kinds must equal the LLVM
//! twin's. The observed model is recorded, not assumed. The linked executable
//! must carry a `PT_TLS` segment and run to exit 0 with the exact isolated
//! output.
//!
//! CONTROLS. The same crate without `#[thread_local]` (a plain `static mut`),
//! built by both compilers and run by the identical driver, must exit 3 with
//! the shared-storage output: the driver detects a non-thread-local `X`. A
//! `#[link_section = ".custom"]` thread-local must be refused by the bridge
//! with its exact named diagnostic and leave no object defining `X`, `read_x`
//! or `bump_x` (the allocator shim object may remain); LLVM compiles the same
//! valid Rust.
//!
//! EVIDENCE BOUNDARY. The frontend runs with `-Ztrust-verify=off` and the
//! backend with the `no-proof-certs` knob. The TLS relocation sequences and
//! the `.tdata` symbol rows are unproven object-side rows. Execution and
//! object inspection here are native testing evidence for the bridge's ELF TLS
//! lane only; GNU cc/ld and the glibc TLS runtime are trusted. The executable
//! link may relax a TLS descriptor access to an executable-image model, so
//! these runs do not execute the descriptor resolver: no certificate, proof,
//! `dlopen` or shared-object TLS behaviour is claimed.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TARGET: &str = "aarch64-unknown-linux-gnu";
const OPT_LEVELS: [u32; 4] = [0, 1, 2, 3];
/// Native executions of each linked CG/LLVM executable.
const RUNS_PER_LANE: usize = 5;
const ISOLATED_STDOUT: &str = "43981 43982 44181 43982\n";
const SHARED_STORAGE_STDOUT: &str = "43981 43982 44182 44182\n";
/// The driver's "worker's write not observed in its own copy" exit code.
const SHARED_STORAGE_EXIT: i32 = 3;
const ITEMS: [&str; 3] = ["X", "read_x", "bump_x"];
const LINK_SECTION_REFUSAL: &str = "thread-local static with explicit \
    #[link_section = \".custom\"] is not supported (default TLV-section emission only)";
/// (model, relocations) of each complete AArch64 ELF TLS access sequence:
/// one of every listed relocation per access.
const ACCESS_MODELS: [(&str, &[&str]); 3] = [
    (
        "general-dynamic-tlsdesc",
        &[
            "R_AARCH64_TLSDESC_ADR_PAGE21",
            "R_AARCH64_TLSDESC_LD64_LO12",
            "R_AARCH64_TLSDESC_ADD_LO12",
            "R_AARCH64_TLSDESC_CALL",
        ],
    ),
    (
        "initial-exec",
        &[
            "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21",
            "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC",
        ],
    ),
    (
        "local-exec",
        &[
            "R_AARCH64_TLSLE_ADD_TPREL_HI12",
            "R_AARCH64_TLSLE_ADD_TPREL_LO12_NC",
        ],
    ),
];

/// Single-crate form of Darwin's `TLS_DESCRIPTOR_CRATE` and `TLS_ACCESSOR_CRATE`
/// in `tls_thread_local_aarch64.rs`. The script test
/// `test_tls_target_keeps_the_darwin_crate_and_driver` pins their definitions
/// and function bodies against this complete guest.
const TLS_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
#![feature(thread_local)]\n\
\n\
#[no_mangle]\n\
#[thread_local]\n\
pub static mut X: i32 = 0xABCD;\n\
\n\
#[no_mangle]\n\
pub extern \"C\" fn read_x() -> i32 {\n\
    unsafe { X }\n\
}\n\
\n\
#[no_mangle]\n\
pub extern \"C\" fn bump_x(delta: i32) -> i32 {\n\
    unsafe { X += delta; X }\n\
}\n";

/// Byte-identical to `DRIVER` in `tls_thread_local_aarch64.rs`. Exit 0 iff the
/// initial read is 0xABCD, each thread's write is observed in its own copy and
/// `main`'s copy is unperturbed by the worker.
const DRIVER: &str = r#"
#include <stdio.h>
#include <pthread.h>

extern int read_x(void);
extern int bump_x(int);

static int worker_result;
static void *worker(void *arg) {
    (void)arg;
    bump_x(100);
    worker_result = bump_x(100); /* worker's OWN copy: 0xABCD + 200 = 44181 */
    return NULL;
}

int main(void) {
    int v0 = read_x();   /* init 0xABCD = 43981 */
    int vm = bump_x(1);  /* main's copy -> 43982 */
    pthread_t t;
    pthread_create(&t, NULL, worker, NULL);
    pthread_join(t, NULL);
    int vm2 = read_x();  /* main's copy must be unperturbed by the worker */
    printf("%d %d %d %d\n", v0, vm, worker_result, vm2);
    int ok = (v0 == 43981) && (vm == 43982) && (worker_result == 44181) && (vm2 == 43982);
    if (v0 != 43981) return 1;          /* wrong initial TLS read */
    if (vm != 43982) return 2;          /* main's TLS write not observed */
    if (worker_result != 44181) return 3; /* worker's TLS write not observed */
    if (vm2 != 43982) return 4;         /* main's copy perturbed == NOT isolated */
    return ok ? 0 : 5;
}
"#;

/// Replace the one `#[thread_local]` attribute line of [`TLS_CRATE`].
fn crate_variant(replacement: &str) -> String {
    const ATTRIBUTE: &str = "#[thread_local]\n";
    assert_eq!(TLS_CRATE.matches(ATTRIBUTE).count(), 1);
    TLS_CRATE.replace(ATTRIBUTE, replacement)
}

// Every compile of this target, CG and LLVM alike, starts from the shared
// build-compiler constructor (edition 2021, `-Ztrust-verify=off` on Trust).
// Test-only backend selection never enters a compiler environment.
fn rustc_command() -> Command {
    let mut command = toolchain_support::rustc_command();
    command
        .env_remove("TCG_TEST_BACKEND_PATH")
        .env_remove("TCG_TEST_BACKEND_SHA256");
    command
}

fn run_bounded(command: &mut Command, seconds: u32, log: &Path) -> (Output, String) {
    // GNU timeout bounds the complete child process group. output() drains both
    // pipes concurrently, including a verbose failed compiler diagnostic.
    let mut bounded = Command::new("timeout");
    bounded.args(["--kill-after=5", &seconds.to_string()]);
    bounded.arg(command.get_program()).args(command.get_args());
    if let Some(dir) = command.get_current_dir() {
        bounded.current_dir(dir);
    }
    for (key, value) in command.get_envs() {
        if let Some(value) = value {
            bounded.env(key, value);
        } else {
            bounded.env_remove(key);
        }
    }
    let output = bounded.output().expect("execute bounded native TLS step");
    let transcript = format!(
        "command: {command:?}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::write(log, &transcript).expect("retain complete step log");
    (output, transcript)
}

fn checked(command: &mut Command, seconds: u32, log: &Path) -> Output {
    let (output, transcript) = run_bounded(command, seconds, log);
    assert!(
        output.status.success(),
        "{transcript}\nartifacts: {}",
        log.display()
    );
    output
}

fn sha256(path: &Path) -> String {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .expect("sha256sum");
    assert!(output.status.success(), "hash {}", path.display());
    let text = String::from_utf8(output.stdout).expect("SHA256 output");
    let hash = text.split_whitespace().next().expect("SHA256 digest");
    assert!(hash.len() == 64 && hash.bytes().all(|b| b.is_ascii_hexdigit()));
    hash.to_owned()
}

fn backend() -> (PathBuf, String) {
    let path = std::env::var_os("TCG_TEST_BACKEND_PATH");
    let hash = std::env::var("TCG_TEST_BACKEND_SHA256").ok();
    match (path, hash) {
        (Some(path), Some(expected)) => {
            let path = PathBuf::from(path);
            assert!(
                path.is_absolute() && path.is_file(),
                "exact backend path required"
            );
            let actual = sha256(&path);
            assert_eq!(actual, expected, "runner's fresh backend identity changed");
            (path, actual)
        }
        (None, None) => {
            // No runner binding: the library Cargo built for this test build,
            // never a nested build into the shared target directory.
            let path = backend_artifact_support::current_test_backend();
            let hash = sha256(&path);
            (path, hash)
        }
        _ => panic!("backend path and SHA256 must be supplied together"),
    }
}

/// One `readelf -sW` row. The name is the last field and the section index the
/// one before it, so an `st_other` annotation such as `[VARIANT_PCS]` after the
/// visibility cannot shift them.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ElfSymbol {
    name: String,
    kind: String,
    bind: String,
    section: String,
}

fn parse_symbols(text: &str) -> Vec<ElfSymbol> {
    text.lines()
        .filter_map(|line| {
            let fields: Vec<&str> = line.split_whitespace().collect();
            let index = fields.first()?.strip_suffix(':')?;
            if fields.len() < 8 || index.parse::<u64>().is_err() {
                return None;
            }
            Some(ElfSymbol {
                name: fields[fields.len() - 1].to_owned(),
                kind: fields[3].to_owned(),
                bind: fields[4].to_owned(),
                section: fields[fields.len() - 2].to_owned(),
            })
        })
        .collect()
}

/// `readelf -SW` rows as section index -> (name, flags). Rows without flags
/// have one field fewer; the unnamed null section is skipped.
fn parse_sections(text: &str) -> BTreeMap<String, (String, String)> {
    let mut sections = BTreeMap::new();
    for line in text.lines() {
        let Some(rest) = line.trim_start().strip_prefix('[') else {
            continue;
        };
        let Some((index, fields)) = rest.split_once(']') else {
            continue;
        };
        let index = index.trim();
        if index.parse::<u64>().is_err() {
            continue;
        }
        let fields: Vec<&str> = fields.split_whitespace().collect();
        let row = match fields.len() {
            10 => (fields[0].to_owned(), fields[6].to_owned()),
            9 => (fields[0].to_owned(), String::new()),
            _ => continue,
        };
        sections.insert(index.to_owned(), row);
    }
    sections
}

/// `readelf -rW` rows as (relocation type, symbol name).
fn parse_relocations(text: &str) -> Vec<(String, String)> {
    text.lines()
        .filter_map(|line| {
            let fields: Vec<&str> = line.split_whitespace().collect();
            (fields.len() >= 5 && fields[2].starts_with("R_AARCH64_"))
                .then(|| (fields[2].to_owned(), fields[4].to_owned()))
        })
        .collect()
}

struct ObjectFacts {
    path: PathBuf,
    symbols: Vec<ElfSymbol>,
    sections: BTreeMap<String, (String, String)>,
    relocations: Vec<(String, String)>,
}

impl ObjectFacts {
    fn defined(&self, name: &str) -> Option<&ElfSymbol> {
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name && symbol.section != "UND")
    }

    fn imported(&self, name: &str) -> Option<&ElfSymbol> {
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name && symbol.section == "UND")
    }

    fn defines_any_item(&self) -> bool {
        ITEMS.iter().any(|item| self.defined(item).is_some())
    }

    fn file_name(&self) -> String {
        self.path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .into_owned()
    }
}

fn readelf(flag: &str, object: &Path, log: &Path) -> String {
    let output = checked(Command::new("readelf").arg(flag).arg(object), 30, log);
    String::from_utf8(output.stdout).expect("readelf output")
}

/// Inspect every freshly emitted object in `object_dir`, retaining the symbol,
/// section and relocation dumps beside it.
fn inspect_objects(object_dir: &Path) -> Vec<ObjectFacts> {
    let mut objects = std::fs::read_dir(object_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect::<Vec<_>>();
    objects.sort();
    objects
        .into_iter()
        .map(|path| {
            let dump = |kind: &str| object_dir.join(format!("{}.{kind}.txt", path.display()));
            let symbols = parse_symbols(&readelf("-sW", &path, &dump("symbols")));
            let sections = parse_sections(&readelf("-SW", &path, &dump("sections")));
            let relocations = parse_relocations(&readelf("-rW", &path, &dump("relocations")));
            ObjectFacts {
                path,
                symbols,
                sections,
                relocations,
            }
        })
        .collect()
}

fn compile(
    source: &Path,
    object_dir: &Path,
    opt: u32,
    backend: Option<&Path>,
    log: &Path,
) -> (Output, String) {
    std::fs::create_dir(object_dir).unwrap();
    let mut command = rustc_command();
    command.args(["--crate-type", "staticlib"]);
    if let Some(backend) = backend {
        command.arg(format!("-Zcodegen-backend={}", backend.display()));
        command.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    // One CGU keeps the per-MonoItem objects predictable, as in the Darwin twin.
    command
        .args(["-Ccodegen-units=1", "-Cpanic=abort", "--target", TARGET])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(object_dir)
        .arg(source);
    run_bounded(&mut command, 180, log)
}

/// Link the selected objects with the driver (`cc -pthread`). Undefined core
/// diverging helpers (the unoptimized overflow/alignment checks) get aborting
/// stubs, as the other bridge differentials do: a reached stub aborts the run
/// and fails the lane. Returns the number of stubs.
fn link(lane: &Path, driver: &Path, objects: &[&ObjectFacts], executable: &Path) -> usize {
    let defined: BTreeSet<&str> = objects
        .iter()
        .flat_map(|facts| facts.symbols.iter())
        .filter(|symbol| symbol.section != "UND")
        .map(|symbol| symbol.name.as_str())
        .collect();
    let stubs: BTreeSet<&str> = objects
        .iter()
        .flat_map(|facts| facts.symbols.iter())
        .filter(|symbol| symbol.section == "UND" && !defined.contains(symbol.name.as_str()))
        .map(|symbol| symbol.name.as_str())
        .filter(|name| toolchain_support::is_abort_stub_symbol(name))
        .collect();
    let mut command = Command::new("cc");
    command
        .arg("-pthread")
        .arg("-o")
        .arg(executable)
        .arg(driver);
    if !stubs.is_empty() {
        let mut source = String::from("#include <stdlib.h>\n");
        for (index, symbol) in stubs.iter().enumerate() {
            source.push_str(&format!(
                "void tcg_abort_stub_{index}(void) __asm__(\"{symbol}\");\n\
                 void tcg_abort_stub_{index}(void) {{ abort(); }}\n"
            ));
        }
        let path = lane.join("abort_stubs.c");
        std::fs::write(&path, source).unwrap();
        command.arg(path);
    }
    for facts in objects {
        command.arg(&facts.path);
    }
    checked(&mut command, 60, &lane.join("link.log"));
    stubs.len()
}

/// The linked executable must carry a `PT_TLS` program header.
fn assert_tls_segment(lane: &Path, executable: &Path) {
    let headers = checked(
        Command::new("readelf").arg("-lW").arg(executable),
        30,
        &lane.join("program-headers.txt"),
    );
    let headers = String::from_utf8_lossy(&headers.stdout);
    assert!(
        headers
            .lines()
            .any(|line| line.trim_start().starts_with("TLS ")),
        "linked executable {} has no PT_TLS segment",
        executable.display()
    );
}

/// Select the objects that define an item; everything else (the allocator
/// shim) is excluded from the link. Returns (linked, excluded count).
fn select(objects: &[ObjectFacts]) -> (Vec<&ObjectFacts>, usize) {
    let linked: Vec<&ObjectFacts> = objects.iter().filter(|o| o.defines_any_item()).collect();
    for item in ITEMS {
        let definers = linked.iter().filter(|o| o.defined(item).is_some()).count();
        assert_eq!(definers, 1, "`{item}` must be defined exactly once");
    }
    let excluded = objects.len() - linked.len();
    (linked, excluded)
}

/// Object-level facts of one CG TLS lane; see the module doc.
struct CgTlsFacts {
    definition_section: String,
    accessor_objects: usize,
    access_model: &'static str,
    access_sequences: usize,
}

fn cg_tls_facts(lane: &Path, linked: &[&ObjectFacts]) -> CgTlsFacts {
    let definers: Vec<&&ObjectFacts> = linked.iter().filter(|o| o.defined("X").is_some()).collect();
    assert_eq!(definers.len(), 1, "exactly one object defines `X`");
    let definer = definers[0];
    let x = definer.defined("X").unwrap();
    assert_eq!(
        (x.kind.as_str(), x.bind.as_str()),
        ("TLS", "GLOBAL"),
        "`X` must be a global STT_TLS definition in {}",
        definer.file_name()
    );
    let (section, flags) = definer.sections.get(&x.section).unwrap_or_else(|| {
        panic!(
            "`X` section {} missing in {}",
            x.section,
            definer.file_name()
        )
    });
    assert!(
        flags.contains('T') && (section == ".tdata" || section == ".tbss"),
        "`X` must live in an SHF_TLS .tdata/.tbss section, found {section} [{flags}]"
    );

    let accessors: Vec<&&ObjectFacts> = linked
        .iter()
        .filter(|o| o.defined("read_x").is_some() || o.defined("bump_x").is_some())
        .collect();
    assert!(!accessors.is_empty(), "no read_x/bump_x accessor object");
    let mut model = None;
    let mut sequences = 0;
    for accessor in &accessors {
        let name = accessor.file_name();
        for function in ["read_x", "bump_x"] {
            if let Some(symbol) = accessor.defined(function) {
                assert_eq!(symbol.kind, "FUNC", "{function} in {name}");
            }
        }
        // The accessor reaches `X` either in its own object, which is then
        // the one object defining it (the bridge's published `--emit=obj`
        // object: its per-item objects partial-linked by `ld -r`, so the
        // accessors' references bind to the `.tdata` definition checked
        // above), or as an undefined `STT_TLS` import of the definition in
        // another object. Never both, and never as anything but TLS.
        if accessor.path == definer.path {
            assert!(
                accessor.imported("X").is_none(),
                "accessor {name} defines `X` and must not also import it"
            );
        } else {
            assert!(
                accessor.defined("X").is_none(),
                "accessor {name} must not define a second `X`"
            );
            let import = accessor
                .imported("X")
                .unwrap_or_else(|| panic!("accessor {name} must import `X`"));
            assert_eq!(
                import.kind, "TLS",
                "accessor {name} must import `X` as STT_TLS"
            );
        }
        // Every relocation naming `X` is a TLS access-sequence relocation:
        // no plain address of the thread-local's template.
        assert!(
            accessor
                .relocations
                .iter()
                .filter(|(_, symbol)| symbol == "X")
                .all(|(kind, _)| kind.starts_with("R_AARCH64_TLS")),
            "accessor {name} addresses `X` outside a TLS sequence: {:?}",
            accessor.relocations
        );
        let tls: Vec<&(String, String)> = accessor
            .relocations
            .iter()
            .filter(|(kind, _)| kind.contains("_TLS"))
            .collect();
        assert!(
            tls.iter().all(|(_, symbol)| symbol == "X"),
            "accessor {name} has a TLS relocation against another symbol: {tls:?}"
        );
        let count = |kind: &str| tls.iter().filter(|(k, _)| k == kind).count();
        let observed = ACCESS_MODELS
            .iter()
            .find(|(_, kinds)| {
                let accesses = count(kinds[0]);
                accesses > 0
                    && kinds.iter().all(|kind| count(kind) == accesses)
                    && accesses * kinds.len() == tls.len()
            })
            .unwrap_or_else(|| {
                panic!("accessor {name} has no single complete TLS access sequence: {tls:?}")
            });
        assert!(
            model.is_none_or(|model| model == observed.0),
            "accessors disagree on the TLS access model"
        );
        model = Some(observed.0);
        sequences += count(observed.1[0]);
        let disassembly = checked(
            Command::new("objdump").arg("-d").arg(&accessor.path),
            30,
            &lane.join(format!("{name}.disassembly.txt")),
        );
        assert!(
            String::from_utf8_lossy(&disassembly.stdout).contains("tpidr_el0"),
            "accessor {name} never reads the thread pointer"
        );
    }
    CgTlsFacts {
        definition_section: section.clone(),
        accessor_objects: accessors.len(),
        access_model: model.unwrap(),
        access_sequences: sequences,
    }
}

fn run_executable(lane: &Path, executable: &Path, run: usize) -> Output {
    let (output, transcript) = run_bounded(
        &mut Command::new(executable),
        20,
        &lane.join(format!("run{run}.log")),
    );
    assert!(
        output.status.code().is_some(),
        "killed by a signal: {transcript}"
    );
    output
}

/// Compile, inspect, link and run `source` with one compiler at one level.
/// Returns the lane's marker row and the set of TLS relocation kinds its
/// linked objects carry.
fn tls_lane(
    artifacts: &Path,
    source: &Path,
    driver: &Path,
    opt: u32,
    backend: Option<(&Path, &str)>,
) -> (String, BTreeSet<String>) {
    let compiler = if backend.is_some() { "cg" } else { "llvm" };
    let lane = artifacts.join(format!("tls_{compiler}_O{opt}"));
    let object_dir = lane.join("objects");
    std::fs::create_dir(&lane).unwrap();
    let (output, transcript) = compile(
        source,
        &object_dir,
        opt,
        backend.map(|(path, _)| path),
        &lane.join("compile.log"),
    );
    assert!(
        output.status.success(),
        "{compiler} TLS compile failed: {transcript}"
    );
    let objects = inspect_objects(&object_dir);
    let (linked, excluded) = select(&objects);
    let x = linked.iter().find_map(|o| o.defined("X")).unwrap();
    assert_eq!(x.kind, "TLS", "{compiler} must define `X` as STT_TLS");
    let cg = backend.is_some().then(|| cg_tls_facts(&lane, &linked));
    let executable = lane.join("tls.elf");
    let abort_stubs = link(&lane, driver, &linked, &executable);
    assert_tls_segment(&lane, &executable);
    for run in 0..RUNS_PER_LANE {
        let output = run_executable(&lane, &executable, run);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{compiler} O{opt} TLS driver failed (1=wrong initial read, 2=main write lost, \
             3=worker write lost, 4=main copy PERTURBED == not per-thread isolated): {}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert_eq!(String::from_utf8_lossy(&output.stdout), ISOLATED_STDOUT);
        assert!(output.stderr.is_empty());
    }
    if let Some((path, digest)) = backend {
        assert_eq!(sha256(path), digest, "backend changed during TLS lane");
    }
    let tls_relocations: BTreeSet<String> = linked
        .iter()
        .flat_map(|o| o.relocations.iter())
        .filter(|(kind, _)| kind.contains("_TLS"))
        .map(|(kind, _)| kind.clone())
        .collect();
    let relocations = tls_relocations
        .iter()
        .map(|kind| format!("\"{kind}\""))
        .collect::<Vec<_>>()
        .join(",");
    let common = format!(
        "\"compiler\":\"{compiler}\",\"opt_level\":{opt},\"runs\":{RUNS_PER_LANE},\
         \"passes\":{RUNS_PER_LANE},\"tls_definers\":1,\"linked_objects\":{},\
         \"excluded_objects\":{excluded},\"abort_stubs\":{abort_stubs},\
         \"tls_relocations\":[{relocations}]",
        linked.len()
    );
    let row = match cg {
        Some(facts) => format!(
            "{{{common},\"definition_section\":\"{}\",\"accessor_objects\":{},\
             \"access_model\":\"{}\",\"access_sequences\":{}}}",
            facts.definition_section,
            facts.accessor_objects,
            facts.access_model,
            facts.access_sequences
        ),
        None => format!("{{{common}}}"),
    };
    (row, tls_relocations)
}

/// The plain-`static mut` control: the identical driver must detect shared
/// storage (exit 3) with either compiler.
fn shared_storage_control(
    artifacts: &Path,
    source: &Path,
    driver: &Path,
    opt: u32,
    backend: Option<&Path>,
) -> String {
    let compiler = if backend.is_some() { "cg" } else { "llvm" };
    let lane = artifacts.join(format!("shared_{compiler}_O{opt}"));
    let object_dir = lane.join("objects");
    std::fs::create_dir(&lane).unwrap();
    let (output, transcript) =
        compile(source, &object_dir, opt, backend, &lane.join("compile.log"));
    assert!(
        output.status.success(),
        "{compiler} shared-storage control compile failed: {transcript}"
    );
    let objects = inspect_objects(&object_dir);
    let (linked, _) = select(&objects);
    let x = linked.iter().find_map(|o| o.defined("X")).unwrap();
    assert_eq!(
        x.kind, "OBJECT",
        "the control's `X` must be ordinary data, not TLS"
    );
    let executable = lane.join("shared.elf");
    link(&lane, driver, &linked, &executable);
    let output = run_executable(&lane, &executable, 0);
    assert_eq!(
        output.status.code(),
        Some(SHARED_STORAGE_EXIT),
        "{compiler} O{opt}: the driver must detect shared (non-thread-local) storage"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        SHARED_STORAGE_STDOUT
    );
    format!(
        "{{\"compiler\":\"{compiler}\",\"opt_level\":{opt},\"exit_code\":{SHARED_STORAGE_EXIT}}}"
    )
}

/// The `#[link_section]` refusal control: exact named CG refusal with no item
/// object left behind, and the LLVM twin of the same valid Rust.
fn link_section_refusal(artifacts: &Path, source: &Path, opt: u32, backend: &Path) -> String {
    let lane = artifacts.join(format!("link_section_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let (output, transcript) = compile(
        source,
        &lane.join("cg-objects"),
        opt,
        Some(backend),
        &lane.join("cg-compile.log"),
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected compiler refusal, not timeout/crash: {transcript}"
    );
    assert!(
        stderr.contains("[TCG-MIR-UNSUPPORTED]") && stderr.contains(LINK_SECTION_REFUSAL),
        "wrong refusal boundary: {transcript}"
    );
    // One refusal row per item: the static itself and each accessor that
    // reaches it through `Rvalue::ThreadLocalRef`.
    let rows: Vec<&str> = stderr.lines().map(str::trim).collect();
    for item in ITEMS {
        let prefix = if item == "X" {
            "- static `X` (symbol `X`,".to_owned()
        } else {
            format!("- {item}:")
        };
        let suffix = format!(": {LINK_SECTION_REFUSAL}");
        assert_eq!(
            rows.iter()
                .filter(|row| row.starts_with(&prefix) && row.ends_with(&suffix))
                .count(),
            1,
            "refusal must name `{item}` exactly once: {transcript}"
        );
    }
    let leftover = inspect_objects(&lane.join("cg-objects"));
    let item_definitions = leftover.iter().filter(|o| o.defines_any_item()).count();
    assert_eq!(
        item_definitions, 0,
        "a refused compile left an object defining X/read_x/bump_x"
    );
    let (output, transcript) = compile(
        source,
        &lane.join("llvm-objects"),
        opt,
        None,
        &lane.join("llvm-compile.log"),
    );
    assert!(
        output.status.success(),
        "valid-Rust control failed: {transcript}"
    );
    let objects = inspect_objects(&lane.join("llvm-objects"));
    let definers: Vec<&ObjectFacts> = objects
        .iter()
        .filter(|o| o.defined("X").is_some())
        .collect();
    assert_eq!(
        definers.len(),
        1,
        "LLVM control must emit one object defining `X`"
    );
    let x = definers[0].defined("X").unwrap();
    let (section, flags) = definers[0]
        .sections
        .get(&x.section)
        .expect("LLVM `X` section");
    assert!(
        x.kind == "TLS" && section == ".custom" && flags.contains('T'),
        "LLVM control must place TLS `X` in the requested section: {x:?} {section} [{flags}]"
    );
    format!(
        "{{\"name\":\"link_section\",\"opt_level\":{opt},\"cg_refusals\":1,\
         \"cg_item_definitions\":{item_definitions},\"cg_leftover_objects\":{},\"llvm_objects\":1}}",
        leftover.len()
    )
}

#[test]
fn readelf_rows_parse_names_sections_and_relocation_pairs() {
    let symbols = parse_symbols(
        "Symbol table '.symtab' contains 3 entries:\n   Num:    Value          Size Type    Bind   Vis      Ndx Name\n     \
         0: 0000000000000000     0 NOTYPE  LOCAL  DEFAULT  UND \n     \
         4: 0000000000000000     4 TLS     GLOBAL DEFAULT    3 X\n     \
         5: 0000000000000000     0 TLS     GLOBAL DEFAULT  UND X\n     \
         6: 0000000000000000    24 FUNC    GLOBAL DEFAULT [VARIANT_PCS]     1 read_x\n",
    );
    assert_eq!(symbols.len(), 3, "{symbols:?}");
    assert_eq!(
        symbols[0],
        ElfSymbol {
            name: "X".into(),
            kind: "TLS".into(),
            bind: "GLOBAL".into(),
            section: "3".into()
        }
    );
    assert_eq!(symbols[1].section, "UND");
    assert_eq!(
        (symbols[2].name.as_str(), symbols[2].section.as_str()),
        ("read_x", "1")
    );
    let sections = parse_sections(
        "  [Nr] Name              Type            Address          Off    Size   ES Flg Lk Inf Al\n  \
         [ 0]                   NULL            0000000000000000 000000 000000 00      0   0  0\n  \
         [ 1] .text             PROGBITS        0000000000000000 000040 000018 00  AX  0   0  4\n  \
         [ 3] .tdata            PROGBITS        0000000000000000 000058 000004 00 WAT  0   0  4\n  \
         [ 4] .comment          PROGBITS        0000000000000000 00005c 000010 01  MS  0   0  1\n  \
         [ 5] .note.GNU-stack   PROGBITS        0000000000000000 00006c 000000 00      0   0  1\n",
    );
    assert_eq!(
        sections.get("3"),
        Some(&(".tdata".to_owned(), "WAT".to_owned()))
    );
    assert_eq!(
        sections.get("5"),
        Some(&(".note.GNU-stack".to_owned(), String::new()))
    );
    assert!(!sections.contains_key("0") && !sections.contains_key("Nr"));
    let relocations = parse_relocations(
        "Relocation section '.rela.text' at offset 0x100 contains 2 entries:\n    \
         Offset             Info             Type               Symbol's Value  Symbol's Name + Addend\n\
         0000000000000000  000000050000021d R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21 0000000000000000 X + 0\n\
         0000000000000004  000000050000021e R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC 0000000000000000 X + 0\n",
    );
    assert_eq!(
        relocations,
        vec![
            (
                "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21".to_owned(),
                "X".to_owned()
            ),
            (
                "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC".to_owned(),
                "X".to_owned()
            ),
        ]
    );
}

#[test]
fn thread_local_static_is_elf_tls_and_per_thread_isolated_linux() {
    // The bridge compiles pass a backend knob on `-Ztrust-ir-cg-args`; its
    // former `TCG_*` environment spelling is refused outright, so a compiler
    // without that option cannot express this test at all.
    if toolchain_support::skip_without_backend_knobs("tls_thread_local_linux") {
        return;
    }
    for name in [
        "TCG_NO_PROOF_CERTS",
        "TCG_JIT_UNCHECKED",
        "TCG_OPT_LEVEL",
        "TRUST_CG_DISABLE_PASSES",
        "TRUST_CG_DISABLE_CFGSIMPLIFY_SUBPASSES",
        "TCG_DATAFLOW_INTEGRITY",
    ] {
        assert!(
            std::env::var_os(name).is_none(),
            "qualification rejects {name}"
        );
    }
    let temp = Command::new("mktemp")
        .args(["-d", "/tmp/trust-cg-tls-linux.XXXXXX"])
        .output()
        .expect("mktemp artifacts");
    assert!(temp.status.success());
    let artifacts = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("native bridge TLS artifacts: {}", artifacts.display());
    let host = checked(
        toolchain_support::rustc_driver_command().arg("-vV"),
        30,
        &artifacts.join("rustc.log"),
    );
    assert!(
        String::from_utf8_lossy(&host.stdout)
            .lines()
            .any(|line| line == format!("host: {TARGET}"))
    );
    let (backend, digest) = backend();

    let tls_source = artifacts.join("tls.rs");
    let shared_source = artifacts.join("shared.rs");
    let refusal_source = artifacts.join("tlsneg.rs");
    let driver = artifacts.join("driver.c");
    std::fs::write(&tls_source, TLS_CRATE).unwrap();
    std::fs::write(&shared_source, crate_variant("")).unwrap();
    std::fs::write(
        &refusal_source,
        crate_variant("#[thread_local]\n#[link_section = \".custom\"]\n"),
    )
    .unwrap();
    std::fs::write(&driver, DRIVER).unwrap();

    let mut lanes = Vec::new();
    let mut shared = Vec::new();
    let mut unsupported = Vec::new();
    for opt in OPT_LEVELS {
        let (cg_row, cg_relocations) = tls_lane(
            &artifacts,
            &tls_source,
            &driver,
            opt,
            Some((&backend, &digest)),
        );
        let (llvm_row, llvm_relocations) = tls_lane(&artifacts, &tls_source, &driver, opt, None);
        // The access model is a link contract of the session's relocation
        // model; the bridge must not pick a different one than LLVM.
        assert_eq!(
            cg_relocations, llvm_relocations,
            "O{opt}: the CG and LLVM objects use different TLS access models"
        );
        lanes.push(cg_row);
        lanes.push(llvm_row);
        shared.push(shared_storage_control(
            &artifacts,
            &shared_source,
            &driver,
            opt,
            Some(&backend),
        ));
        shared.push(shared_storage_control(
            &artifacts,
            &shared_source,
            &driver,
            opt,
            None,
        ));
        unsupported.push(link_section_refusal(
            &artifacts,
            &refusal_source,
            opt,
            &backend,
        ));
    }
    assert_eq!(
        sha256(&backend),
        digest,
        "backend changed during TLS qualification"
    );
    println!(
        "\nTCG_BRIDGE_TLS_EXECUTION {{\"schema\":1,\"target\":\"{TARGET}\",\"opt_levels\":[0,1,2,3],\
         \"runs_per_lane\":{RUNS_PER_LANE},\"lanes\":[{}],\"shared_storage_controls\":[{}],\
         \"unsupported\":[{}],\"backend_sha256\":\"{digest}\"}}",
        lanes.join(","),
        shared.join(","),
        unsupported.join(",")
    );
}
