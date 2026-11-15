"""Regression lint: bridge tests load the backend of their own Cargo build.

Source lint for closure row L06-P13. A bridge test that looks for
`target/{release,debug}/librustc_codegen_trust_cg.*` accepts whatever library a
previous build left there (once 517 commits stale). A nested backend build into
the shared target directory replaces the library that every later test target
of the same `targo test` run loads, possibly with other features. A hard-coded
`.dylib` name panics on Linux. The sanctioned selector is
`tests/support/backend_artifact.rs::current_test_backend()`, which returns the
library Cargo built beside the running test executable. The three runner-bound
Linux lane targets, and the harness of the three Linux runtime twins
(`support/linux_runtime_twin.rs`), also accept the exact path and SHA-256 that
`scripts/check_linux_aarch64_bridge.py` supplies, and otherwise use the same
selector. The Darwin runner binds its snapshot by running a copy of each test
executable beside it, so its fixtures need no second route.

Every `.rs` file under the bridge's `tests/` directory is scanned, recursively:
Cargo also builds `tests/<dir>/main.rs` as a test target, and support modules
and included files are shared code. Three checks run on each file.

1. Line rules, on every line including comments, refuse: the backend's file
   name (the crate name followed by an extension, a format placeholder or a
   quote; a sentence ending in the crate name is not a file name) or a
   shared-library extension literal; the host `DLL_*` constants; a
   Cargo profile or `deps` directory (`.join`/`.push` of `release`, `debug` or
   `deps`, or a literal path through them); `CARGO_TARGET_DIR`,
   `CARGO_BUILD_TARGET_DIR` or `cargo_target_dir(`; `current_exe(` outside the
   selector; a `cargo`/`targo`/`--unverified` literal, `Command::new` of
   cargo/targo or `backend_build_command(`; and `RUSTFLAGS`.
2. On the file with comments removed and whitespace, line breaks included,
   ignored inside the call: an environment read (`var`, `var_os`, `env!`,
   `option_env!`) whose name contains `BACKEND` or `DYLIB`.
3. A file that mentions `codegen-backend` or `codegen_backend` anywhere
   (joined, split across arguments, or in `RUSTFLAGS`) must call
   `backend_artifact_support::current_test_backend()` in code; a mention in a
   comment does not count. The selector module itself is exempt from this
   check only. A support module may instead take its backend from the test
   files that include it through `#[path = "support/<file>"]`: through
   `use super::{.., backend, ..}` or `super::backend(`, when every including
   file defines `fn backend(` and calls the selector in code; or as an
   argument its callers pass, when it is included at least once and every
   including file calls the selector in code.

The only exceptions are the exact lines in `ALLOWED_LINES`, including the
relocation corpus library, a cdylib a test builds and inspects, native drivers
that directly execute themselves, and the announced `SIGFAM_DYLIB` diagnostic,
which the Darwin bridge gate refuses.
The four runner-bound files must also name both `TCG_TEST_BACKEND_*` variables.

This is a regression lint for known spellings, not a proof. Source written to
evade it passes, for example: a name or path assembled with `concat!`, from
pieces or at run time; a stale path passed through a variable in a file that
also calls the selector; an allowlisted line under `if false` with a different
fallthrough; an environment variable whose name contains neither `BACKEND` nor
`DYLIB`; a parent-directory walk from the test executable, `/proc/self/exe` or
`CARGO_TARGET_TMPDIR`; a profile name held in a variable; a backend name built
from `CARGO_PKG_NAME`; and a backend injected through `RUSTC` or
`RUSTC_WRAPPER`. It does not show that any test passes or that a selected
library is correct.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
BRIDGE_TESTS = ROOT / "crates/rustc-codegen-trust-cg/tests"
SELECTOR_MODULE = "support/backend_artifact.rs"
SELECTOR_CALL = "backend_artifact_support::current_test_backend"

# Each rule flags one known way a test could pick a backend other than its own build.
RULES = (
    ("backend-file-name",
     re.compile(r"librustc_codegen_trust_cg|rustc_codegen_trust_cg(?:\{\}|\.(?=\S)|\")"
                r"|\bDLL_(?:PREFIX|SUFFIX|EXTENSION)\b|\bbackend_file_name\b|\bdylib_name\b"),
     "names or constructs the backend library file name"),
    ("library-extension",
     re.compile(r"\"[^\"\n]*\.(?:so|dylib|dll)\"|\"(?:so|dylib|dll)\""),
     "names a shared-library file or extension"),
    ("profile-directory",
     re.compile(r"""\.(?:join|push)\(\s*"(?:release|debug|deps)(?:/[^"]*)?"\s*\)"""
                r"""|"(?:[^"\n]*/)?(?:release|debug|deps)/|"target/|/deps\""""),
     "looks inside a Cargo profile or deps directory"),
    ("target-directory",
     re.compile(r"\bCARGO_(?:BUILD_)?TARGET_DIR\b|\bcargo_target_dir\s*\("),
     "resolves Cargo's target directory"),
    ("executable-directory",
     re.compile(r"\bcurrent_exe\s*\("),
     "derives a path from the test executable outside the selector"),
    ("nested-build",
     re.compile(r"\bbackend_build_command\s*\(|\"(?:cargo|targo|CARGO|--unverified)\""
                r"|Command::new\([^)\n]*\b(?:cargo|targo)\b"),
     "runs or locates a separate cargo/targo build"),
    ("compiler-flags-environment",
     re.compile(r"\b(?:CARGO_ENCODED_)?RUSTFLAGS\b"),
     "passes compiler flags through the environment"),
)
# Whole-file rules, run on the comment-stripped text so that a call trustfmt
# splits across lines is still one match: (rule, pattern, meaning).
CODE_RULES = (
    ("backend-environment",
     re.compile(r"(?:\bvar_os|\bvar|\benv!|\boption_env!)\s*\(\s*\"[^\"]*(?:BACKEND|DYLIB)"),
     "reads a backend path from the environment"),
)
# Mentions of the codegen-backend option: joined (`-Zcodegen-backend=`), split
# (`"-Z", "codegen-backend=…"`), with a space, or in RUSTFLAGS.
LOADS_BACKEND = re.compile(r"codegen[-_]backend")
# An actual call of the selector, in code with comments removed.
SELECTOR_USE = re.compile(r"\bbackend_artifact_support::current_test_backend\s*\(\s*\)")
# A support module that delegates backend selection to its including test file.
DELEGATES_BACKEND = re.compile(r"\buse\s+super::\{[^}]*\bbackend\b[^}]*\}|\bsuper::backend\s*\(")
DEFINES_BACKEND = re.compile(r"\bfn\s+backend\s*\(")
INCLUDED_MODULE = re.compile(r'#\[path\s*=\s*"(support/[^"]+\.rs)"\]')

RUNNER_BOUND_FILES = (
    "aarch64_c_fnabi_aggregate_linux.rs",
    "tls_thread_local_linux.rs",
    "unwind_cleanup_linux.rs",
    "support/linux_runtime_twin.rs",
)
RUNNER_BOUND_CONTRACT = ("TCG_TEST_BACKEND_PATH", "TCG_TEST_BACKEND_SHA256")
_RUNNER_BOUND_LINES = (
    'let path = std::env::var_os("TCG_TEST_BACKEND_PATH");',
    'let hash = std::env::var("TCG_TEST_BACKEND_SHA256").ok();',
)
_RUNNER_BOUND_REASON = (
    "runner-bound Linux lane target: the exact path and SHA-256 that "
    "check_linux_aarch64_bridge.py supplies; without them the file uses the selector"
)
_SELECTOR_REASON = "the selector itself: the exact current test's library dependency"
_RELOCATION_FIXTURE_REASON = (
    "freshly linked relocation corpus library, inspected by readelf and passed to the C driver; "
    "the module delegates backend selection to its including test"
)
_SELF_EXECUTION_REASON = (
    "native abort-control driver launches itself directly; no backend path is derived"
)
_CDYLIB_FIXTURE_REASON = (
    "the cdylib this test compiles from DYLIB_CRATE (into a scratch directory named dylib) and "
    "inspects with nm; the backend that compiles it comes from the selector"
)
_SIGFAM_DIAGNOSTIC_REASON = (
    "explicit, announced diagnostic override that measures another build against the same rows "
    "(the LIMITATIONS.md and CHANGELOG.md measurements against 65e816a73); the Darwin bridge gate "
    "refuses SIGFAM_DYLIB as an ambient override (scripts/check_darwin_aarch64_bridge.py, pinned by "
    "test_signature_family_filters_and_backend_overrides_are_always_refused), so no gate run "
    "credits another build, and without it the file uses the selector"
)
# (path relative to the bridge tests directory, exact stripped line) -> reason.
ALLOWED_LINES = {
    **{(name, line): _RUNNER_BOUND_REASON for name in RUNNER_BOUND_FILES for line in _RUNNER_BOUND_LINES},
    (SELECTOR_MODULE, 'let executable = std::env::current_exe().expect("running integration-test path");'):
        _SELECTOR_REASON,
    (SELECTOR_MODULE, '"{}rustc_codegen_trust_cg{}",'): _SELECTOR_REASON,
    (SELECTOR_MODULE, "std::env::consts::DLL_PREFIX,"): _SELECTOR_REASON,
    (SELECTOR_MODULE, "std::env::consts::DLL_SUFFIX"): _SELECTOR_REASON,
    (SELECTOR_MODULE, 'edge.get(1).and_then(serde_json::Value::as_str) == Some("rustc_codegen_trust_cg")'):
        _SELECTOR_REASON,
    (SELECTOR_MODULE, 'let fingerprint = entry.path().join("fingerprint/lib-rustc_codegen_trust_cg");'):
        _SELECTOR_REASON,
    ("support/linux_relocations.rs", '.arg(dir.join("libfixture.so")),'):
        _RELOCATION_FIXTURE_REASON,
    ("support/residual_conversion/intrinsic_validity_driver.rs",
     "let result = std::process::Command::new(std::env::current_exe().unwrap())"):
        _SELF_EXECUTION_REASON,
    ("support/residual_conversion/virtual_unwind_driver.rs",
     "let output = std::process::Command::new(std::env::current_exe().unwrap())"):
        _SELF_EXECUTION_REASON,
    ("support/intercept_panic/driver.rs",
     "let output = std::process::Command::new(std::env::current_exe().unwrap())"):
        _SELF_EXECUTION_REASON,
    ("support/intrinsic_validity_darwin/generic_driver.rs",
     "let result = std::process::Command::new(std::env::current_exe().unwrap())"):
        _SELF_EXECUTION_REASON,
    ("linkage_macho_aarch64.rs", 'let dir = scratch.sub("dylib");'): _CDYLIB_FIXTURE_REASON,
    ("linkage_macho_aarch64.rs", 'let dylib = dir.join("libdy.dylib");'): _CDYLIB_FIXTURE_REASON,
    ("signature_placement_families_xback.rs", 'match std::env::var_os("SIGFAM_DYLIB") {'):
        _SIGFAM_DIAGNOSTIC_REASON,
}


def bridge_sources(tests_dir: Path = BRIDGE_TESTS) -> dict[str, str]:
    """Every Rust source under the bridge tests directory, keyed by relative path."""
    return {path.relative_to(tests_dir).as_posix(): path.read_text(encoding="utf-8", errors="replace")
            for path in sorted(tests_dir.rglob("*.rs")) if path.is_file()}


def strip_comments(text: str) -> str:
    """Replace Rust comments (`//`, doc comments, nested `/* */`) with spaces.

    String, byte-string, raw-string and character literals are kept, so a
    comment marker inside a literal is not a comment. Line breaks are kept, so
    offsets map to the same line numbers. Lifetimes are not character literals.
    """
    out = []
    i, n = 0, len(text)

    def blank(chunk: str) -> str:
        return "".join("\n" if char == "\n" else " " for char in chunk)

    while i < n:
        char = text[i]
        if text.startswith("//", i):
            end = text.find("\n", i)
            end = n if end == -1 else end
            out.append(blank(text[i:end]))
            i = end
        elif text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(blank(text[i:j]))
            i = j
        elif char == "r" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")
                              or text[i - 1] in "bc" and (i < 2 or not (text[i - 2].isalnum() or text[i - 2] == "_"))):
            match = re.match(r'r(#*)"', text[i:])
            if match is None:
                out.append(char)
                i += 1
                continue
            closing = '"' + match.group(1)
            end = text.find(closing, i + len(match.group(0)))
            end = n if end == -1 else end + len(closing)
            out.append(text[i:end])
            i = end
        elif char == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif char == "'":
            if text.startswith("\\", i + 1):
                end = text.find("'", i + 3)
                end = n if end == -1 else end + 1
            elif i + 2 < n and text[i + 2] == "'":
                end = i + 3
            else:
                end = i + 1
            out.append(text[i:end])
            i = end
        else:
            out.append(char)
            i += 1
    return "".join(out)


def violations(name: str, text: str) -> list[str]:
    """Every backend-selection violation in one bridge source file."""
    found = []
    lines = text.splitlines()
    for number, line in enumerate(lines, 1):
        stripped = line.strip()
        if (name, stripped) in ALLOWED_LINES:
            continue
        for rule, pattern, meaning in RULES:
            if pattern.search(line):
                found.append(f"{name}:{number}: [{rule}] {meaning}: {stripped}")
    code = strip_comments(text)
    for rule, pattern, meaning in CODE_RULES:
        for match in pattern.finditer(code):
            number = code.count("\n", 0, match.start()) + 1
            stripped = lines[number - 1].strip() if number <= len(lines) else ""
            if (name, stripped) not in ALLOWED_LINES:
                found.append(f"{name}:{number}: [{rule}] {meaning}: {stripped}")
    if name in RUNNER_BOUND_FILES:
        missing = [key for key in RUNNER_BOUND_CONTRACT if key not in text]
        if missing:
            found.append(f"{name}: [runner-contract] runner-bound target lacks {missing}")
    delegates = name.startswith("support/") and DELEGATES_BACKEND.search(code)
    if (name != SELECTOR_MODULE and not delegates and LOADS_BACKEND.search(text)
            and not SELECTOR_USE.search(code)):
        found.append(f"{name}: [no-current-build-selector] mentions codegen-backend "
                     f"without calling {SELECTOR_CALL}() in code")
    return found


def includers_of(name: str, codes: dict[str, str]) -> list[str]:
    """The files that include support module NAME through `#[path = "support/<file>"]`."""
    return [other for other, other_code in codes.items() if name in INCLUDED_MODULE.findall(other_code)]


def caller_selected_modules(sources: dict[str, str]) -> set[str]:
    """Support modules that load the backend their callers pass in.

    Such a module mentions codegen-backend, calls no selector and does not
    delegate through `super::`; it passes only when it is included at least
    once and every file that includes it calls the selector in code.
    """
    codes = {name: strip_comments(text) for name, text in sources.items()}
    selected = set()
    for name, code in codes.items():
        if (not name.startswith("support/") or name == SELECTOR_MODULE or SELECTOR_USE.search(code)
                or DELEGATES_BACKEND.search(code) or not LOADS_BACKEND.search(sources[name])):
            continue
        includers = includers_of(name, codes)
        if includers and all(SELECTOR_USE.search(codes[includer]) for includer in includers):
            selected.add(name)
    return selected


def delegation_problems(sources: dict[str, str]) -> list[str]:
    """A delegating support module is only as current as every file that includes it."""
    found = []
    codes = {name: strip_comments(text) for name, text in sources.items()}
    for name, code in codes.items():
        if not (name.startswith("support/") and DELEGATES_BACKEND.search(code)):
            continue
        includers = includers_of(name, codes)
        if not includers:
            found.append(f"{name}: [delegated-backend] takes its backend from super:: "
                         f"but no test file includes it")
        for includer in includers:
            if not (DEFINES_BACKEND.search(codes[includer]) and SELECTOR_USE.search(codes[includer])):
                found.append(f"{name}: [delegated-backend] takes its backend from {includer}, "
                             f"which does not define fn backend( calling {SELECTOR_CALL}()")
    return found


def scan(sources: dict[str, str]) -> list[str]:
    caller_selected = caller_selected_modules(sources)
    found = [problem for name, text in sources.items() for problem in violations(name, text)
             if not (name in caller_selected and problem.startswith(f"{name}: [no-current-build-selector]"))]
    found += delegation_problems(sources)
    for (name, line), _reason in sorted(ALLOWED_LINES.items()):
        if name not in sources:
            found.append(f"{name}: [stale-allowlist] allowlisted file is gone")
        elif not any(candidate.strip() == line for candidate in sources[name].splitlines()):
            found.append(f"{name}: [stale-allowlist] allowlisted line is gone: {line}")
    return found


def rules_of(problems: list[str]) -> set[str]:
    return {problem.split("[", 1)[1].split("]", 1)[0] for problem in problems}


LEGACY_DARWIN_HELPER = '''
fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir.join("debug").join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = toolchain_support::backend_build_command(crate_dir, false).status().unwrap();
    assert!(status.success());
    target_dir.join("debug").join("librustc_codegen_trust_cg.dylib")
}
fn compile(dylib: &Path) { let _ = format!("-Zcodegen-backend={}", dylib.display()); }
'''
LEGACY_HOST_NAME_HELPER = '''
fn dylib_name() -> String {
    format!("{}rustc_codegen_trust_cg{}", std::env::consts::DLL_PREFIX, std::env::consts::DLL_SUFFIX)
}
fn ensure_dylib_built() -> PathBuf {
    let dir = target_dir_support::cargo_target_dir(Path::new(env!("CARGO_MANIFEST_DIR")));
    for c in [dir.join("release").join(dylib_name()), dir.join("debug").join(dylib_name())] {
        if c.exists() { return c; }
    }
    unreachable!()
}
fn compile(dylib: &Path) { let _ = format!("-Zcodegen-backend={}", dylib.display()); }
'''
# The standalone branch the lane targets had before this lint: a nested
# default-features build into the shared target directory.
LEGACY_LANE_FALLBACK = '''
fn backend() -> (PathBuf, String) {
    match (std::env::var_os("TCG_TEST_BACKEND_PATH"), std::env::var("TCG_TEST_BACKEND_SHA256").ok()) {
        (None, None) => {
            let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
            let target = target_dir_support::cargo_target_dir(manifest_dir);
            toolchain_support::backend_build_command(manifest_dir, true).status().unwrap();
            let path = target.join("release/librustc_codegen_trust_cg.so");
            (path, sha256(&path))
        }
        _ => unreachable!(),
    }
}
fn compile(dylib: &Path) { let _ = format!("-Zcodegen-backend={}", dylib.display()); }
'''
AMBIENT_OVERRIDE = '''
fn ensure_dylib_built() -> PathBuf {
    PathBuf::from(std::env::var_os("TRUST_CG_BACKEND").expect("backend path"))
}
fn compile(dylib: &Path) { let _ = format!("-Zcodegen-backend={}", dylib.display()); }
'''
CURRENT_BUILD = '''
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}
fn compile(dylib: &Path) { let _ = format!("-Zcodegen-backend={}", dylib.display()); }
'''
# The independent verifier's bypasses of the first version of this lint
# (2026-09-24): (label, file name, source, rules that must now fire).
VERIFIER_BYPASSES = (
    ("split -Z argument", "split_arg.rs",
     'fn c(p: &Path) { cmd.arg("-Z").arg(format!("codegen-backend={}", p.display())); }\n',
     {"no-current-build-selector"}),
    ("RUSTFLAGS", "rustflags.rs",
     'fn c() { cmd.env("RUSTFLAGS", "-Zcodegen-backend=/cache/stale"); }\n',
     {"compiler-flags-environment", "no-current-build-selector"}),
    ("DLL_EXTENSION", "extension.rs",
     'fn n() -> String { format!("librustc_{}.{}", "codegen_trust_cg", std::env::consts::DLL_EXTENSION) }\n',
     {"backend-file-name"}),
    ("target-dir environment", "target_env.rs",
     'fn t() -> PathBuf { PathBuf::from(std::env::var("CARGO_TARGET_DIR").unwrap()) }\n',
     {"target-directory"}),
    ("nested cargo build", "nested_cargo.rs",
     'fn b() { Command::new("cargo").args(["build", "--release"]).status().unwrap(); }\n',
     {"nested-build"}),
    ("nested targo build from the environment", "nested_targo.rs",
     'fn b() { Command::new(std::env::var("TOY_CARGO").unwrap())'
     '.args(["--unverified", "build", "--release"]).status().unwrap(); }\n',
     {"nested-build"}),
    ("read_dir scan for a library", "read_dir.rs",
     'fn f(d: &Path) -> Option<PathBuf> { std::fs::read_dir(d).ok()?.flatten().map(|e| e.path())'
     '.find(|p| p.extension().is_some_and(|x| x == "so")) }\n',
     {"library-extension"}),
    ("support module loading a backend", "support/extra.rs",
     'pub fn arg(p: &Path) -> String { format!("-Zcodegen-backend={}", p.display()) }\n',
     {"no-current-build-selector"}),
    ("allowlisted line under if false", "tls_thread_local_linux.rs",
     'fn backend() -> PathBuf {\n    if false {\n        let path = std::env::var_os("TCG_TEST_BACKEND_PATH");\n'
     '        let hash = std::env::var("TCG_TEST_BACKEND_SHA256").ok();\n    }\n'
     '    PathBuf::from("/cache/target/release/librustc_codegen_trust_cg.so")\n}\n',
     {"backend-file-name", "library-extension", "profile-directory"}),
)
# The round-2 verifier's plausible bypasses (2026-09-24).
VERIFIER_BYPASSES_ROUND2 = (
    ("selector named only in a comment", "probe.rs",
     "// Callers pass backend_artifact_support::current_test_backend() here.\n"
     "/// Or /* backend_artifact_support::current_test_backend() */ in a doc comment.\n"
     'fn compile(backend: &Path) { cmd.arg(format!("-Zcodegen-backend={}", backend.display())); }\n'
     'fn main_test() { compile(&PathBuf::from(std::env::var_os("TRUST_CG_LIB").unwrap())); }\n',
     {"no-current-build-selector"}),
    ("trustfmt-split backend environment read", "probe.rs",
     '#[path = "support/backend_artifact.rs"]\nmod backend_artifact_support;\n'
     "fn backend() -> PathBuf {\n"
     "    if let Some(path) = std::env::var_os(\n"
     '        "TRUST_CG_BRIDGE_TEST_BACKEND_OVERRIDE_FOR_LOCAL_DEBUGGING_ONLY",\n'
     "    ) {\n"
     "        return PathBuf::from(path);\n"
     "    }\n"
     "    backend_artifact_support::current_test_backend()\n"
     "}\n"
     'fn c(p: &Path) { let _ = format!("-Zcodegen-backend={}", p.display()); }\n',
     {"backend-environment"}),
)


class BridgeBackendSelectionTests(unittest.TestCase):
    def test_every_bridge_source_loads_its_own_cargo_backend(self):
        sources = bridge_sources()
        self.assertGreater(len(sources), 300, "bridge test inventory unexpectedly small")
        self.assertTrue(any("/" in name and not name.startswith("support/") for name in sources),
                        "the scan must include files below tests/ subdirectories")
        problems = scan(sources)
        self.assertEqual(problems, [], "\n".join(problems))
        users = sorted(name for name, text in sources.items()
                       if SELECTOR_USE.search(strip_comments(text)))
        delegating = sorted(name for name, text in sources.items() if name.startswith("support/")
                            and DELEGATES_BACKEND.search(strip_comments(text)))
        caller_selected = sorted(caller_selected_modules(sources))
        loaders = sorted(name for name, text in sources.items() if LOADS_BACKEND.search(text))
        self.assertEqual(sorted(set(loaders) - set(users) - set(delegating) - set(caller_selected)), [])
        self.assertTrue(set(RUNNER_BOUND_FILES) <= set(users))
        print(f"BRIDGE_BACKEND_SELECTION files={len(sources)} selector_users={len(users)} "
              f"delegating_modules={len(delegating)} caller_selected_modules={len(caller_selected)} "
              f"allowlisted_lines={len(ALLOWED_LINES)}")

    def test_legacy_selectors_are_refused(self):
        for label, text, rules in (
            ("darwin-literal", LEGACY_DARWIN_HELPER,
             {"backend-file-name", "library-extension", "profile-directory", "target-directory",
              "nested-build", "no-current-build-selector"}),
            ("host-name", LEGACY_HOST_NAME_HELPER,
             {"backend-file-name", "profile-directory", "target-directory", "no-current-build-selector"}),
            ("lane-nested-build", LEGACY_LANE_FALLBACK,
             {"backend-file-name", "library-extension", "profile-directory", "target-directory",
              "nested-build", "backend-environment", "no-current-build-selector"}),
            ("ambient-override", AMBIENT_OVERRIDE, {"backend-environment", "no-current-build-selector"}),
        ):
            with self.subTest(label=label):
                self.assertEqual(rules_of(violations("legacy_probe.rs", text)), rules)

    def test_verifier_bypasses_are_refused(self):
        for label, name, text, rules in VERIFIER_BYPASSES + VERIFIER_BYPASSES_ROUND2:
            with self.subTest(label=label):
                self.assertTrue(rules <= rules_of(violations(name, text)), violations(name, text))

    def test_a_subdirectory_test_target_is_scanned(self):
        # Cargo builds tests/<dir>/main.rs as its own test target.
        with tempfile.TemporaryDirectory() as temp:
            tests = Path(temp)
            (tests / "newdir").mkdir()
            (tests / "newdir" / "main.rs").write_text(LEGACY_DARWIN_HELPER)
            self.assertIn("newdir/main.rs", bridge_sources(tests))
            self.assertTrue(any(problem.startswith("newdir/main.rs:") for problem in scan(bridge_sources(tests))))

    def test_current_build_selector_is_accepted(self):
        self.assertEqual(violations("current_build.rs", CURRENT_BUILD), [])
        # Comment markers inside literals are not comments; the call still counts.
        literal = CURRENT_BUILD.replace("fn compile", 'const URL: &str = "http://x/*"; fn compile')
        self.assertEqual(violations("current_build.rs", literal), [])

    def test_comments_are_stripped_but_literals_and_lines_are_kept(self):
        for source, expected in (
            ('let a = "http://x"; // c', 'let a = "http://x";     '),
            ("fn f<'a>(x: &'a str) {} // c", "fn f<'a>(x: &'a str) {}     "),
            ('let r = r#"a // b "c" "#; /* x /* y */ z */ q', 'let r = r#"a // b "c" "#;                   q'),
            ("let e = '\\''; let q = '\"'; // c", "let e = '\\''; let q = '\"';     "),
            ("/// doc\n//! inner\nfn f() {}", "       \n         \nfn f() {}"),
        ):
            with self.subTest(source=source):
                self.assertEqual(strip_comments(source), expected)

    def test_a_delegating_support_module_follows_its_includer(self):
        module = ('use super::{backend, rustc_command};\n'
                  'fn run(root: &Path) {\n    let (backend, _) = backend(root);\n'
                  '    rustc_command().arg(format!("-Zcodegen-backend={}", backend.display()));\n}\n')
        current = ('#[path = "support/backend_artifact.rs"]\nmod backend_artifact_support;\n'
                   '#[path = "support/delegating.rs"]\nmod delegating;\n'
                   'fn backend(_root: &Path) -> (PathBuf, String) {\n'
                   '    let path = backend_artifact_support::current_test_backend();\n    (path, String::new())\n}\n')
        stale = ('#[path = "support/delegating.rs"]\nmod delegating;\n'
                 'fn backend(root: &Path) -> (PathBuf, String) {\n'
                 '    (root.join("librustc_codegen_trust_cg.so"), String::new())\n}\n')
        def check(sources):
            return ([problem for name, text in sources.items() for problem in violations(name, text)]
                    + delegation_problems(sources))

        self.assertEqual(check({"support/delegating.rs": module, "a.rs": current}), [])
        problems = check({"support/delegating.rs": module, "a.rs": current, "b.rs": stale})
        self.assertIn("delegated-backend", rules_of(problems))
        self.assertTrue(any("b.rs" in problem and "delegated-backend" in problem for problem in problems))
        self.assertIn("delegated-backend", rules_of(check({"support/delegating.rs": module})))

    def test_a_support_module_given_its_backend_follows_every_includer(self):
        # The module loads the library its caller passes; only an inclusion by
        # files that all call the selector covers it.
        module = ('pub fn compile(dylib: &Path) {\n'
                  '    let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");\n'
                  '    arg.push(dylib);\n}\n')
        current = ('#[path = "support/backend_artifact.rs"]\nmod backend_artifact_support;\n'
                   '#[path = "support/passed.rs"]\nmod passed;\n'
                   'fn t() { passed::compile(&backend_artifact_support::current_test_backend()); }\n')
        stale = ('#[path = "support/passed.rs"]\nmod passed;\n'
                 'fn t(root: &Path) { passed::compile(&root.join("old")); }\n')
        self.assertEqual(caller_selected_modules({"support/passed.rs": module, "a.rs": current}),
                         {"support/passed.rs"})
        for sources in ({"support/passed.rs": module},
                        {"support/passed.rs": module, "a.rs": current, "b.rs": stale}):
            with self.subTest(files=sorted(sources)):
                self.assertEqual(caller_selected_modules(sources), set())
                self.assertIn("no-current-build-selector", rules_of(violations("support/passed.rs", module)))
        # Outside support/ a file that loads a backend must call the selector itself.
        self.assertEqual(caller_selected_modules({"passed.rs": module, "a.rs": current}), set())

    def test_a_sentence_ending_in_the_crate_name_is_not_a_file_name(self):
        self.assertEqual(violations("corpus.rs", "// wasm32 execution corpus for rustc_codegen_trust_cg.\n"), [])
        for line in ('let p = dir.join("rustc_codegen_trust_cg.so");',
                     'let p = format!("rustc_codegen_trust_cg.{}", ext);',
                     "// rustc_codegen_trust_cg.dylib from the last build"):
            with self.subTest(line=line):
                self.assertIn("backend-file-name", rules_of(violations("probe.rs", line + "\n")))

    def test_allowlist_is_exact_to_its_files(self):
        # Allowlisted lines are violations anywhere else, a runner-bound file
        # without its path/SHA contract is refused, and the selector module is
        # scanned like any other file apart from its own exact lines.
        for (name, line), _reason in ALLOWED_LINES.items():
            with self.subTest(line=line):
                self.assertNotEqual(violations("other.rs", f"fn f() {{\n    {line}\n}}\n"), [])
        self.assertEqual(violations("unwind_cleanup_linux.rs", CURRENT_BUILD),
                         ["unwind_cleanup_linux.rs: [runner-contract] runner-bound target lacks "
                          "['TCG_TEST_BACKEND_PATH', 'TCG_TEST_BACKEND_SHA256']"])
        self.assertEqual(rules_of(violations(SELECTOR_MODULE, 'fn f() { p.join("release"); }\n')),
                         {"profile-directory"})
        self.assertEqual(rules_of(scan({"hello.rs": CURRENT_BUILD})), {"stale-allowlist"})

    def test_non_backend_fixture_exceptions_keep_selection_controls(self):
        # These exact operations are fixture use, not backend discovery. A
        # different library use or deriving a path from the executable is refused.
        for name, source, rule in (
            ("support/linux_relocations.rs", '.arg(dir.join("libother.so")),',
             "library-extension"),
            ("support/linux_relocations.rs", 'let backend = dir.join("libfixture.so");',
             "library-extension"),
            ("support/residual_conversion/intrinsic_validity_driver.rs",
             'let result = std::process::Command::new(std::env::current_exe().unwrap().parent().unwrap())',
             "executable-directory"),
            ("support/residual_conversion/virtual_unwind_driver.rs",
             'let output = std::process::Command::new(std::env::current_exe().unwrap().parent().unwrap())',
             "executable-directory"),
        ):
            with self.subTest(name=name, source=source):
                self.assertIn(rule, rules_of(violations(name, source)))
        for (name, line), reason in ALLOWED_LINES.items():
            if reason not in (_RELOCATION_FIXTURE_REASON, _SELF_EXECUTION_REASON):
                continue
            with self.subTest(name=name):
                self.assertEqual(violations(name, line), [])
                injected = line + '\nlet backend = std::env::var("TRUST_CG_BACKEND").unwrap();\n'
                self.assertIn("backend-environment", rules_of(violations(name, injected)))


def main(argv: list[str]) -> int:
    """`--scan DIR` reports violations for another checkout's bridge tests."""
    if len(argv) == 3 and argv[1] == "--scan":
        problems = [problem for name, text in bridge_sources(Path(argv[2])).items()
                    for problem in violations(name, text)]
        print("\n".join(problems))
        print(f"BRIDGE_BACKEND_SELECTION violations={len(problems)}")
        return 1 if problems else 0
    unittest.main(argv=argv, verbosity=2)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
