#!/usr/bin/env python3
"""Run every Darwin AArch64 rustc-bridge test target against one fresh backend.

This is the Darwin twin of scripts/check_linux_aarch64_bridge.py. It refuses
every host but aarch64-apple-darwin and resolves trustc/targo from ONE installed
Trust package through scripts/trust_toolchain.py: a branded trustc with a 40-hex
commit identity, never the retired nightly-2026-04-20 pin, a split PATH pair, or
a rustup `trust` link naming a different sysroot (gate_env.sh's divergence
rule). Before any build it refuses, with a named diagnostic, a package that
cannot build or exercise the bridge: missing rustc-dev private crates, missing
Darwin rust-std, or no -Ztrust-ir-cg-args backend-knob option. The report
records the package's trustc/targo identities and SHA-256 hashes and its
sysroot.

Every bridge test target that names the Darwin AArch64 triple or gates on
aarch64 macOS is required (TARGETS): the native fixtures, the host-target
oracles, the fixed-cost bound and the compile-verdict corpus. Positive
execution is accounted per test. libtest reports `ok` for an early return as
readily as for a checked claim, so each required test prints one
`TCG_DARWIN_BRIDGE_POSITIVE kind=<evidence> certs=<on|off|none> test=<name>`
marker (tests/support/positive_evidence.rs) once its claim is asserted, and a
passed test is credited only when its own captured output carries a marker
naming it. A passed test without one, a skip, an early return and a refusal
treated as success are failures, never passes. Each target also has an exact
evidence profile (how many of its tests run natively, only compile, or pin an
expected refusal) and an exact count of proofs-off tests. The marker's certs=
is not taken on the test's word: tests/support/toolchain.rs backend_knobs_arg
prints a `TCG_BRIDGE_BACKEND_KNOBS knobs=<list>` trace into the calling test's
captured output, a credited certs=on or certs=none test must have traced no
`no-proof-certs` argument, and a certs=off test must have traced one. The
inventory check refuses a required fixture that spells the knob option itself
(bypassing the trace), one whose row has no proofs-off test but whose code
names `"no-proof-certs"`, and one whose row has proofs-off tests but whose code
never names it. It also follows every module a required fixture compiles in
(`#[path]` and bare `mod` declarations and literal `include!`s, transitively),
and refuses a `no-proof-certs` or a spelling of the knob option in any of them
outside the few owner items in KNOB_OPTION_OWNERS: a raw option in a shared
compile constructor such as toolchain_support::rustc_command would print no
trace and reach every compile of every fixture that includes it. So a direct
edit that weakens a test from native execution to a compile, or from
certificates on to the `no-proof-certs` knob, fails the target until this table
is edited. The scan reads source text, so a knob string assembled from pieces
at run time is outside it; the one generated include it admits
(GENERATED_INCLUDES) holds only the build compiler's path.

The backend is release-built with `targo --unverified` into a dedicated target
directory. The runner refuses a backend older than any local source Cargo lists
in its dep-info, then snapshots the exact dylib, read-only, into `release/deps`
of a runtime target directory under --out, beside a read-only copy of each
required test executable. A fixture loads the library beside its own executable
(tests/support/backend_artifact.rs), so every required test executable is run,
from that copy, in its own bounded process with --show-output against exactly
the snapshot bytes. The Cargo cache dylib, which the test build may rebuild,
is never beside a running fixture, and a fixture's fallback build or cache
write into the runtime target directory is detected.

Transcripts are classified through scripts/matrix_results.py, plus a
bridge-specific refusal rule: any line with a skip word or TCG-PROOF-465. A
SKIP, ignored or filtered test, a guard return or an accepted TCG-PROOF-465
early return therefore fails its target. Two exceptions are exact: a backend
diagnostic in DIAGNOSTIC_EXEMPTIONS (a provisioning report that contains a
skip word but skips no test) is counted and reported, not treated as a
refusal; and a TCG-PROOF-465 line without a skip word is data in a test whose
credited evidence is itself a refusal (expected-refusal) or a refusal census
(compile-verdict). A target allowlisted in NAMED_REFUSALS with its exact
refusal lines is recorded as an open named refusal, never as a pass. Every
target must also report its minimum executed passes and required execution
markers.

real_program_corpus_a64 is compile-verdict-only (--emit=obj for
aarch64-apple-darwin, no link or execution) and is reported as such, never as
native execution. fixed_cost_budget_aarch64 is a fixed-cost bound: it compiles
a one-function library cold and warm and bounds the checker-probe requests,
solver-command requests and executable digests counted by the backend (`time`
knob); request counts are not confirmed process starts. It links and
runs nothing, so it is reported as a bound, never as native execution.

This is the explicit UNVERIFIED Trust lane: `targo --unverified` builds and the
fixtures' -Ztrust-verify=off compiles. Tests whose marker says `certs=off`
passed the backend's `no-proof-certs` knob and are proofs-off diagnostics; the
report lists them. Passing is testing evidence for the named tests only. It is
not Darwin FnAbi completion (no Darwin C FnAbi aggregate regression exists
yet), frontend qualification, proof authority, Trust-verified compilation or
self-hosting.

Exit status: 0 every required target executed and passed; 1 failure or refusal;
3 no failure, but at least one allowlisted named refusal (an open row, not a
pass); 2 usage error.
"""

from __future__ import annotations

import argparse
import collections
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
BRIDGE_DIR = ROOT / "crates" / "rustc-codegen-trust-cg"
MANIFEST = BRIDGE_DIR / "Cargo.toml"
PIN = BRIDGE_DIR / "rust-toolchain.toml"
TESTS_DIR = BRIDGE_DIR / "tests"
CORPUS_FLOOR = TESTS_DIR / "real_program_corpus" / "A64_COMPILE_FLOOR.txt"
HOST = "aarch64-apple-darwin"
MACHINE = "arm64"
BACKEND_NAME = "librustc_codegen_trust_cg.dylib"
DEP_INFO_NAME = "librustc_codegen_trust_cg.d"
PACKAGE_TARGET = "rustc_codegen_trust_cg"
DEFAULT_TARGET_DIR = BRIDGE_DIR / "target" / "darwin-aarch64-bridge-gate"
KNOB_OPTION = "trust-ir-cg-args"
SCHEMA = "trust-cg-darwin-aarch64-bridge-v1"
EXIT_NAMED_REFUSAL = 3

# Named diagnostics. Each preflight refusal is reported with its code so a log
# names the missing prerequisite instead of a doomed build's compiler errors.
HOST_REFUSED = "DARWIN_BRIDGE_HOST_REFUSED"
AMBIENT_OVERRIDE = "DARWIN_BRIDGE_AMBIENT_OVERRIDE"
PIN_NOT_TRUST = "DARWIN_BRIDGE_PIN_NOT_TRUST"
TOOLCHAIN_UNRESOLVED = "DARWIN_BRIDGE_TOOLCHAIN_UNRESOLVED"
RUSTC_DEV_ABSENT = "DARWIN_BRIDGE_RUSTC_DEV_ABSENT"
RUST_STD_ABSENT = "DARWIN_BRIDGE_RUST_STD_ABSENT"
KNOBS_ABSENT = "DARWIN_BRIDGE_BACKEND_KNOBS_ABSENT"
DIVERGENT = "DARWIN_BRIDGE_TRUST_TOOLCHAINS_DIVERGENT"
IDENTITY_UNKNOWN = "DARWIN_BRIDGE_TRUST_IDENTITY_UNKNOWN"
HOST_TOOL_MISSING = "DARWIN_BRIDGE_HOST_TOOL_MISSING"
CARGO_CONFIG_REROUTE = "DARWIN_BRIDGE_CARGO_CONFIG_REROUTE"
INVENTORY_INCONSISTENT = "DARWIN_BRIDGE_INVENTORY_INCONSISTENT"
TARGET_DIR_REFUSED = "DARWIN_BRIDGE_TARGET_DIR_REFUSED"
DIRTY_TREE = "DARWIN_BRIDGE_DIRTY_TREE"
BUILD_FAILED = "DARWIN_BRIDGE_BUILD_FAILED"
STALE_BACKEND = "DARWIN_BRIDGE_STALE_BACKEND"
STALENESS_UNDECIDABLE = "DARWIN_BRIDGE_STALENESS_UNDECIDABLE"
TEST_BUILD_FAILED = "DARWIN_BRIDGE_TEST_BUILD_FAILED"
BACKEND_CHANGED = "DARWIN_BRIDGE_BACKEND_CHANGED"
FALLBACK_BUILD = "DARWIN_BRIDGE_FIXTURE_FALLBACK_BUILD"
SOURCE_CHANGED = "DARWIN_BRIDGE_SOURCE_CHANGED"

# These reroute the compiler or build, run test binaries through another
# program, or select another target. They are refused, never recorded.
REFUSED_ENVIRONMENT = (
    "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTFLAGS", "CARGO_BUILD_TARGET",
    "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER", "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS",
    "CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER",
)
# Trust compilers refuse every TRUST_CG_*/TCG_* variable as an untracked
# codegen control. SIGFAM_* selects a replacement backend or narrows a required
# signature-family matrix; no such diagnostic override may earn gate credit.
REFUSED_PREFIXES = ("TCG_", "TRUST_CG_", "SIGFAM_")
RECORDED_CONFIGURATION = (
    "CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR", "CARGO_HOME", "RUSTUP_HOME",
    "RUSTUP_TOOLCHAIN", "AY_SOLVER_PATH", "RUST_MIN_STACK", "RUST_TEST_THREADS",
    "DEVELOPER_DIR", "SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "XDG_CACHE_HOME",
)
# Host tools the required fixtures invoke. A missing one turns a fixture into
# a guard return ("skipping: cc not available") or a spawn panic. No GNU
# `timeout`: macOS ships none, and the fixtures bound their native runs in
# process (tests/support/darwin_native_prerequisites.rs run_with_deadline).
HOST_TOOLS = ("git", "cc", "nm", "ar", "otool", "objdump", "dwarfdump", "dsymutil", "lldb", "shasum")
HOST_TOOL_PROBES = {
    "git": ("--version",), "cc": ("--version",), "nm": ("--version",),
    "otool": ("--version",), "objdump": ("--version",),
    "dwarfdump": ("--version",), "dsymutil": ("--version",), "lldb": ("--version",),
    "shasum": ("--version",),
}
EXTERN_CRATE = re.compile(r"^\s*extern\s+crate\s+(rustc_[A-Za-z0-9_]+)\s*;", re.MULTILINE)
# The backend knob that turns off per-function proof certificates. A fixture
# that passes it produces testing evidence only, and the report says so.
NO_PROOF_CERTS_KNOB = '"no-proof-certs"'
NO_PROOF_CERTS_KEY = "no-proof-certs"
# The backend's Shape::Boolean spellings that keep a boolean knob OFF
# (src/knobs.rs); every other spelling of no-proof-certs, including a malformed
# one, is read as disabling certificates, so a mismatch fails closed.
BOOLEAN_OFF_VALUES = ("0", "false", "off", "no")
# tests/support/toolchain.rs backend_knobs_arg prints one trace line for every
# knob argument it builds, into the calling test's captured output. The
# required fixtures build knob arguments only through it (inventory_problems
# refuses a fixture that spells the option itself), so the trace, not the
# test's own marker, says whether a test compiled with certificates off.
KNOB_TRACE = "TCG_BRIDGE_BACKEND_KNOBS"
KNOB_TRACE_LINE = re.compile(re.escape(KNOB_TRACE) + r" knobs=(.*)")
# A required fixture that spells the knob option itself would bypass the trace.
RAW_KNOB_OPTION = re.compile(r"trust-ir-cg-args\s*=|trust_ir_cg_args|BACKEND_KNOBS_OPTION")
COMMENT_LINE = re.compile(r"^\s*//")
# Every module compiled into a required test executable is held to the knob
# rule, not only its root: a raw option in a shared constructor
# (toolchain_support::rustc_command) prints no trace and reaches every compile
# of every fixture that includes it. In a module, `no-proof-certs` is never
# spelled (a fixture passes it to backend_knobs_arg itself), and the knob
# option may be named only inside these items (tests/-relative path: the fn or
# const names that may), none of which builds a compile argument except the
# traced constructor.
KNOB_OPTION_OWNERS = {
    "support/toolchain.rs": {
        "BACKEND_KNOBS_OPTION": "the option's one definition",
        "backend_knobs_arg": "the traced constructor every knob argument comes from",
        "backend_knobs_supported": "asks `-Z help` whether the option exists; builds no compile argument",
        "skip_without_backend_knobs": "names the option in another host's skip message",
    },
    "support/darwin_native_prerequisites.rs": {
        "require": "names the option in its missing-prerequisite panic; builds no compile argument",
    },
}
NO_PROOF_CERTS_WORD = re.compile(r"no[-_]proof[-_]certs")
# Module declarations and includes, matched on the skeleton view (comments and
# literal contents blanked), so a guest program in a string is never read as a
# declaration; a literal's text is then read from the same offsets of the code.
PATH_MODULE = re.compile(
    r'#\[path\s*=\s*"([^"\n]*)"\]\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?mod\s+\w+\s*;')
PATH_ATTRIBUTE = re.compile(r"#\[path\b|#\[cfg_attr\([^\]]*\bpath\s*=")
BARE_MODULE = re.compile(r"\bmod\s+(\w+)\s*;")
LITERAL_INCLUDE = re.compile(r'\binclude!\s*\(\s*"([^"\n]*)"\s*\)')
INCLUDE_MACRO = re.compile(r"\binclude!\s*\(")
# build.rs writes this file as one `const BUILD_COMPILER: &str = "<path>";`.
GENERATED_INCLUDES = ('include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));',)
RAW_STRING_START = re.compile(r'b?r(#*)"')
CHAR_LITERAL = re.compile(r"'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f]{1,6}\}|.)|[^\\'\n])'")
# `fn name`, `const NAME` and `static [mut] NAME` items; not `'static`, and a
# `const fn` / `const unsafe fn` is matched as its fn.
ITEM_DEFINITION = re.compile(
    r"(?<![\w'])(?:(fn)|(const|static)(?:\s+mut)?(?!\s+(?:fn|unsafe|async|extern)\b))\s+(\w+)")

# Positive evidence (tests/support/positive_evidence.rs). A passed test is
# credited only when its own captured output carries exactly one kind of
# marker naming it.
POSITIVE_MARKER = "TCG_DARWIN_BRIDGE_POSITIVE"
POSITIVE_LINE = re.compile(re.escape(POSITIVE_MARKER) + r" kind=(\S+) certs=(\S+) test=(\S+)")
NATIVE_RUN = "native-run"
COMPILED = "compiled"
EXPECTED_REFUSAL = "expected-refusal"
VERDICT = "compile-verdict"
FIXED_COST_EVIDENCE = "fixed-cost"
UNIT_CHECK = "unit-check"
EVIDENCE_KINDS = (NATIVE_RUN, COMPILED, EXPECTED_REFUSAL, VERDICT, FIXED_COST_EVIDENCE, UNIT_CHECK)
CERTS = ("on", "off", "none")
# Evidence whose own claim is a refusal, or a census of refusals: a
# TCG-PROOF-465 line without a skip word in its echoed compiler output is data.
REFUSAL_BEARING_EVIDENCE = (EXPECTED_REFUSAL, VERDICT)

# Required targets: complete integration-test names, never substring filters.
# minimum is the number of #[test] functions the target defines (every one is
# compiled on aarch64-apple-darwin), so a test that vanishes or returns early
# cannot be replaced by the others. markers are lines the fixture prints only on
# its asserted success path. evidence is the exact (kind, count) profile of the
# credited tests of a complete pass, and certs_off the exact number of them that
# are proofs-off diagnostics (`no-proof-certs`). Lowering a minimum, dropping a
# marker, moving a count between evidence kinds, raising certs_off or removing a
# row is a denominator change that needs an explicit, reviewed edit here.
Target = collections.namedtuple("Target", "name minimum kind markers evidence certs_off")
NATIVE = "native-link-run"
HOST_ORACLE = "host-target-oracle"
COMPILE_VERDICT = "compile-verdict-only"
FIXED_COST = "fixed-cost-bound"
KINDS = (NATIVE, HOST_ORACLE, COMPILE_VERDICT, FIXED_COST)
# Which marker kinds each target kind may credit.
ALLOWED_EVIDENCE = {
    NATIVE: (NATIVE_RUN, COMPILED, EXPECTED_REFUSAL),
    HOST_ORACLE: (NATIVE_RUN, COMPILED, EXPECTED_REFUSAL),
    COMPILE_VERDICT: (VERDICT,),
    FIXED_COST: (FIXED_COST_EVIDENCE, UNIT_CHECK),
}
TARGETS = (
    Target("coroutine_generator_aarch64", 1, NATIVE, (), ((NATIVE_RUN, 1),), 1),
    Target("drop_heap_aarch64", 3, NATIVE, (), ((NATIVE_RUN, 3),), 3),
    Target("hello_loop", 1, NATIVE, ("rustc_codegen_trust_cg: #574 entry wrapper uses lang_start",),
           ((NATIVE_RUN, 1),), 0),
    Target("static_data_aarch64", 4, NATIVE, (
        "EXTERN_STATIC_LINK rows=2 matched=2 opts=0,2",
    ), ((NATIVE_RUN, 4),), 3),
    Target("tls_thread_local_aarch64", 1, NATIVE, (), ((NATIVE_RUN, 1),), 1),
    Target("unwind_cleanup_aarch64", 2, NATIVE, (
        "bridge unwind-cleanup EH lowering VERIFIED (object level)",
        "REAL Rust panic CAUGHT through the bridge: AY_CAUGHT=1 CLEANUP_RAN=1",
    ), ((NATIVE_RUN, 1), (COMPILED, 1)), 2),
    Target("m142_bridge_bookkeeping_aarch64", 7, NATIVE, (), ((NATIVE_RUN, 7),), 7),
    # The argument-placement family matrix across the backend boundary: the
    # aarch64 lane natively, the x86-64 lane under Rosetta (its core built from
    # the compiler's own library source), and the Rosetta route's self-test.
    Target("signature_placement_families_xback", 3, NATIVE, (), ((NATIVE_RUN, 3),), 2),
    # The `rust-call` / closure-body boundary checks the Linux AArch64 target
    # runs (shared support modules, the same fixtures and LLVM-computed values),
    # compiled for this host: every program must match LLVM in all four
    # pairings at O0-O3.
    Target("rust_call_boundary_aarch64", 2, NATIVE, (), ((NATIVE_RUN, 2),), 2),
    # The x86-64 rlib x bin cross-backend fixtures: host-target oracles (they
    # run natively on an x86-64 Linux or macOS host too) that run here under
    # Rosetta (support/x86_rosetta.rs) since round 10 instead of returning
    # early: scalar-pair returns and arguments, pairs at register exhaustion,
    # loaded bools. m145 runs the host's own aarch64 lane natively AND the
    # x86-64 lane. On this host every one of them compiles proofs-off
    # (`no-proof-certs`): certificates on, each trust-cg x86-64 object is
    # refused [TCG-PROOF-465] at proof promotion, unrelated to placement.
    Target("m140_x86_scalar_pair_return_xback", 1, HOST_ORACLE, (), ((NATIVE_RUN, 1),), 1),
    Target("m141_x86_scalar_pair_arg_xback", 1, HOST_ORACLE, (), ((NATIVE_RUN, 1),), 1),
    Target("m144_x86_pair_arg_exhaustion_xback", 1, HOST_ORACLE, (), ((NATIVE_RUN, 1),), 1),
    Target("m145_x86_indirect_arg_xback", 2, HOST_ORACLE, (), ((NATIVE_RUN, 2),), 2),
    Target("m146_x86_bool_load_xback", 1, HOST_ORACLE, (), ((NATIVE_RUN, 1),), 1),
    # trust-cg-opt's loop-state rows (aarch64 natively, x86-64 under Rosetta
    # against a `core` built from the compiler's own library source), its
    # iteration-coverage rows on both targets, its early-exit canary rows, the
    # programs its NEON passes must keep vectorized, and the real-program
    # corpus's run lane, bridge against LLVM, proofs off (the rows judge
    # codegen).
    Target("opt_loop_state_run", 9, NATIVE, (), ((NATIVE_RUN, 9),), 9),
    # The x86-64 register allocator's split copies through the replay into the
    # emitted stream (trust-cg-codegen `replay_x86_regalloc_stream_mutations`):
    # whole x86-64 programs under Rosetta, bridge against LLVM at O2 and O3,
    # proofs off (the rows judge codegen). The marker pins the row count.
    Target("x86_split_copy_replay_run", 1, NATIVE, ("X86_SPLIT_COPY_REPLAY rows=20 matched=20",),
           ((NATIVE_RUN, 1),), 1),
    # L06-P7. DWARF line tables through dsymutil, dwarfdump --verify and lldb
    # (packed and unpacked split debuginfo, proofs off); every unhonoured
    # codegen option refused by its [TCG-OPT-*] code with certificates on;
    # the honoured notes/warnings and the DWARF-version refusal, proofs off.
    Target("debuginfo_dwarf_aarch64", 4, NATIVE, (),
           ((NATIVE_RUN, 2), (COMPILED, 1), (EXPECTED_REFUSAL, 1)), 3),
    # L06-P7. rustc linkage on Mach-O through ld64: CGU-local copies hidden and
    # distinct (a symbol-binding differential against LLVM's objects), weak
    # definitions coalescing and yielding to a strong one, a cdylib's export
    # list (proofs off); common and weak thread-local definitions refused as
    # [TCG-LINKAGE] with certificates on.
    Target("linkage_macho_aarch64", 4, NATIVE, (), ((NATIVE_RUN, 3), (EXPECTED_REFUSAL, 1)), 3),
    # L06-P8. SetDiscriminant and Rvalue::Discriminant for every layout and
    # place class, explicit and fieldless repr discriminants included (custom
    # MIR, -O0..-O3); user Drop glue (enum cons lists and trees included) and
    # indirect calls (thread_local!, Box<dyn Fn>, Box<dyn Trait>) with cleanup
    # edges taken by real panics under an LLVM-built counting allocator and
    # catch_unwind (-O0..-O3); #[link_section]
    # statics in their Mach-O sections with a __mod_init_func constructor; the
    # bounded FP asm! grammar against the hardware-checked C driver (-O0..-O3;
    # proofs off); the unmodeled families (become, asm!, global_asm!, a
    # function's or thread-local's section, an unplaced Mach-O section,
    # wrap_binder!) refused by name with certificates on.
    Target("mir_families_aarch64", 6, NATIVE, (
        "SET_DISCRIMINANT_LAYOUTS slots=18 writes=19 opts=0,1,2,3 matched=4",
        "DISCRIMINANT_READS values=43 opts=0,1,2,3 matched=4",
        "USER_DROP_CLEANUP scenarios=16 opts=0,1,2,3 matched=4 caught_panics=28",
        "LINK_SECTION_STATICS sections=3 ctor=ran opts=0,2 matched=2",
        "BOUNDED_FP_ASM checks=2359296 opts=0,1,2,3 llvm=4 bridge=4",
        "UNMODELED_MIR_FAMILIES refused=7",
    ), ((NATIVE_RUN, 5), (EXPECTED_REFUSAL, 1)), 5),
    Target("panic_hook_differential", 2, HOST_ORACLE, (
        "panic-hook rows: 49/49 matched LLVM",
        "PRE_PANIC_EFFECTS matched=24 strategies=abort,unwind opts=0,2,3",
    ), ((NATIVE_RUN, 2),), 2),
    Target("assert_panic_differential_aarch64", 1, NATIVE, (
        "ASSERT_PANIC_KINDS entries=14 cells=16 cases=18 native_runs=304 controls=272 caught=120 aborts=168",
    ), ((NATIVE_RUN, 1),), 1),
    # Every failed MIR Assert kind (bounds incl. an intercepted Vec index,
    # overflow, division, the -Zub-checks pointer / enum kinds incl. a u128
    # payload, coroutine resume) against the host's LLVM binary at -O0..-O3 x
    # panic abort/unwind x overflow checks on/off, set_hook and default-hook
    # rows; no configuration may be refused.
    Target("panic_assert_kinds_differential", 1, HOST_ORACLE, (
        "ASSERT_PANIC_KIND_ROWS fixtures=4 configs=16 rows=1344 matched=1344 refused=0",
    ), ((NATIVE_RUN, 1),), 1),
    # Every std panic route the bridge raises itself — the failure edges of
    # intercepted std calls, panic calls in compiled bodies (formatted
    # messages, std's #[track_caller] helpers) and the -Cdebug-assertions
    # precondition checks — against the host's LLVM binary at -O0..-O3 x
    # panic abort/unwind: std's payload type and text, Location and
    # abort/unwind, under an LLVM-compiled observer hook, a bridge-compiled
    # hook and the default hook; no configuration may be refused.
    Target("std_panic_payload_differential", 1, HOST_ORACLE, (
        "STD_PANIC_PAYLOAD_ROWS fixtures=3 configs=8 rows=1680 matched=1680 refused=0",
    ), ((NATIVE_RUN, 1),), 1),
    # The second test pins the call-site regions of an abort-built frame's
    # table against LLVM's: covered where a region holds an indirect call, a
    # gap where it holds only direct nounwind calls (memcmp counts as
    # nounwind only above O0, as LLVM infers it); a call the backend creates
    # itself is a gap exactly where LLVM expands, folds or inlines the
    # operation, per level, and no tail branch skips the frame's table. The
    # third test pins unwind-built frames calling a Rust-defined extern "C"
    # callee whose panic reaches them: the callee's MIR cleanups, then its Abi
    # termination, matching LLVM wherever LLVM's search passes every frame up
    # to a handler and following MIR where LLVM's search fails in a gap
    # (OD-NOUNWIND-CALLEE-EDGE-20261011); controls whose panic is caught must
    # match exactly.
    Target("terminate_panic_differential_aarch64", 3, NATIVE, (
        "TERMINATE_PANIC_KINDS reasons=2 cells=16 cases=2 native_runs=48 controls=32 aborts=32 hooks=56 cleanup_drops=8",
        "TERMINATE_PANIC_ROUTES llvm_runs=24 cg_runs=24 opts=0,1,2,3 strategies=abort,unwind",
        "TERMINATE_FOREIGN_ABORT_KINDS cells=8 cases=3 native_runs=32 controls=16 aborts=24 hooks=48 throw_drops=24 throw_callbacks=40",
        "TERMINATE_FOREIGN_ABORT_OUTCOMES reached_abi=16 fatal_search=8 nested_reason_hooks=0",
        "TERMINATE_FOREIGN_ABORT_OBJECTS cells=8 complete_sets=8 stable=1 max_per_cell=16",
        "TERMINATE_FOREIGN_ABORT_ROUTES llvm_runs=16 cg_runs=16 opts=0,1,2,3 callee_strategy=abort driver_strategy=unwind",
        "TERMINATE_FOREIGN_ABORT_BOUNDARY_CONTROLS expected_refusals=12 compiled_nounwind_roots=8 llvm_source_roots=16 native_runs=0 opts=0,1,2,3",
        "TERMINATE_NOUNWIND_REGIONS rows=68 cells=8 native_runs=544 llvm_runs=272 cg_runs=272 opts=0,1,2,3 callee_strategy=abort driver_strategy=unwind",
        "TERMINATE_NOUNWIND_REGION_OUTCOMES returns=40 fatal_search=135 reached_abi=48 caught=49",
        "TERMINATE_UNWIND_CALLEE_REGIONS rows=38 cells=8 native_runs=304 llvm_runs=152 cg_runs=152 opts=0,1,2,3 callee_strategy=unwind driver_strategy=unwind",
        "TERMINATE_UNWIND_CALLEE_OUTCOMES returns=8 caught=56 reached_abi=63 mir_cleanup_where_llvm_fails_search=25",
    ), ((NATIVE_RUN, 3),), 3),
    # Unsized by-value slice/str parameters (`unsized_arguments`): the Linux
    # corpus unchanged, plus `[&str]` rows (alloc's by-value
    # `SpecExtendStr::spec_extend_into` shape, the data/length pair split
    # across x7 and the stack, and behind narrow scalars macOS packs on the
    # stack) at O0-O3 under both panic strategies, against LLVM. Elements with
    # drop glue must still be refused.
    Target("unsized_arguments_aarch64", 3, NATIVE, (
        "TCG_UNSIZED_ARGUMENT_DARWIN_CORPUS executions=8 checks=912384 opts=0,1,2,3 panic=abort",
        "TCG_UNSIZED_ARGUMENT_DARWIN_STR_SLICES executions=16 checks=359424 opts=0,1,2,3 panic=abort,unwind",
        "TCG_UNSIZED_ARGUMENT_DARWIN_ADMISSION fixtures=3 compilations=24 refusals=8 opts=0,1,2,3",
    ), ((NATIVE_RUN, 2), (EXPECTED_REFUSAL, 1)), 3),
    # The validity intrinsics (`assert_zero_valid`, `assert_inhabited`,
    # `assert_mem_uninitialized_valid`): rustc's validity query, a branch for a
    # valid instantiation and rustc's `panic_nounwind` message and abort for an
    # invalid one, against LLVM at O0-O3 under both panic strategies and both
    # strict-init policies: the Linux fixture unchanged, and generic wrappers that
    # keep every valid and invalid instantiation in the backend at every level.
    Target("atomic_load_store_aarch64", 3, NATIVE, (
        "TCG_ATOMIC_NONVOLATILE fixtures=20 cells=160 executions=320 opts=0,1,2,3 panic=abort,unwind",
        "TCG_ATOMIC_VOLATILE fixtures=2 cells=16 refused=16 llvm_runs=16 opts=0,1,2,3 panic=abort,unwind",
        "TCG_ATOMIC_POLICY order_fixtures=4 type_fixtures=5 cells=72 refused=72 llvm_type_refusals=40 opts=0,1,2,3 panic=abort,unwind layout_abi_fixtures=2 layout_abi_refusals=16 llvm_abi_runs=16",
    ), ((NATIVE_RUN, 1), (EXPECTED_REFUSAL, 2)), 3),
    Target("abort_immediate_aarch64", 1, NATIVE, (
        "TCG_ABORT_IMMEDIATE_DARWIN fixtures=3 executions=48 opts=0,1,2,3 panic=abort,unwind trap=5 libc_abort=6",
    ), ((NATIVE_RUN, 1),), 1),
    Target("intrinsic_validity_aarch64", 1, NATIVE, (
        "TCG_INTRINSIC_VALIDITY_DARWIN fixtures=linux,generic executions=64 opts=0,1,2,3 panic=abort,unwind strict=no,yes",
    ), ((NATIVE_RUN, 1),), 1),
    # A fat-pointer-leaf aggregate stored whole through a field projection
    # (alloc's `<CStr as ToOwned>::clone_into`) and the `Box<DST>` deref idiom
    # through a pointer (`drop_glue::<Box<[T]>>`), against LLVM at O0-O3 under
    # a size-checking allocator, including `Box<[T]>` drops whose element needs
    # drop (the slice glue's length decides the drop count). A packed container
    # must stay refused.
    Target("deref_field_wide_image_store_aarch64", 3, NATIVE, (
        "DEREF_FIELD_WIDE_IMAGE_STORES subjects=subject,strings,bombs opts=0,1,2,3 matched=12 refused=0",
        "DEREF_FIELD_WIDE_IMAGE_KINDS kinds=7 opts=0,1,2,3 matched=4 refused=0",
        "DEREF_FIELD_WIDE_IMAGE_REFUSALS subjects=packed opts=0,1,2,3 matched=0 refused=4",
    ), ((NATIVE_RUN, 2), (EXPECTED_REFUSAL, 1)), 3),
    # Real Rust-metadata Box<i64> formals and opaque LLVM retargeting, not
    # allocator/image authority. Credit requires every O0--O3 native ledger
    # plus the bounded emitted-MIR reader's positive and mutation controls.
    Target("box_pointer_entry_aarch64", 1, NATIVE, (
        "BOX_POINTER_ENTRY_DIFFERENTIAL cells=8 cases=2 native_runs=16 llvm_runs=8 cg_runs=8 mir_routes=16 box_drop_frees=24 reads=16 retargets=8 bad_layout=0 provider=LLVM oracle=LLVM certs=off",
        "BOX_POINTER_ENTRY_MIR_TRACE_CONTROLS cases=14 accepted=3 refused=11",
    ), ((NATIVE_RUN, 1),), 1),
    # The reversed-inclusive rows build and match since the bridge drives that
    # walk itself (refusals=0; the strict differential is the unregistered,
    # host-native rev_range_inclusive_fold_differential). The dead-iterator rows
    # are the gate's live witnesses: all four must still refuse, so a change
    # that lowers them (and leaves the gate unwitnessed) is a reviewed edit
    # here. The first such edit (2026-10-03): f09e5fa9c sent Repeat/Successors
    # take chains to core's real bodies, so the original rows build and match
    # LLVM; they moved to the generator-take guard (all four must run
    # natively), and RepeatN/Cycle rows that still reach the gate (SIGTRAP
    # with it removed) became the witnesses. The dyn-heap test records all
    # four guarded outcomes: its two -O0 rows must run natively since
    # heap_image_glue lowers the vtable's drop glue, and its -O2 rows may
    # refuse or match (guarded_trap_profile).
    Target("executable_trap_stub_routes_aarch64", 5, HOST_ORACLE, (
        "EXECUTABLE_TRAP_STUB_RANGE refusals=0 llvm_native=6 cg_native=6",
        "EXECUTABLE_TRAP_STUB_DEAD_ITER rows=4 llvm_native=4 cg_native=0 cg_refused=4",
        "EXECUTABLE_TRAP_STUB_GENERATOR_TAKE rows=4 llvm_native=4 cg_native=4 cg_refused=0",
        "LIBRARY_TRAP_STUB_REACHED refused=4 compiled=5",
    ), ((NATIVE_RUN, 3), (EXPECTED_REFUSAL, 2)), 5),
    # Box<dyn Trait> drop glue for intercepted heap values (heap_image_glue):
    # the LLVM differential under a net heap ledger (every must-match cell
    # built and matched, the refuse-or-match cells' split pinned, the
    # HashMap rows still refusing); the borrowed Vec/String vtables building
    # and matching (their rustc-layout glue frees only the data buffer, so any
    # origin is valid; 2 of the 4 refuse-or-match `dyn_raw_dyn_drop` cells
    # now build and match LLVM as well); the borrowed map vtables failing
    # closed (BTreeMap by [TCG-HEAP-IMAGE-VTABLE], HashMap on its unlowered
    # glue); and the staticlib pair (a six-box chain freed 7/7 through rustc's
    # box glue since L06-P8, a two-level chain freed 3/3).
    Target("dyn_heap_glue_differential_aarch64", 5, HOST_ORACLE, (
        "DYN_HEAP_GLUE cells=48 must_match=31 matched=36 refused=12",
        "DYN_HEAP_GLUE_BORROWED_VEC_STRING cells=20 must_match=16 matched=18 refused=2",
        "DYN_HEAP_GLUE_BORROWED_MAP refused=8 heap_image_vtable=4",
        "DYN_HEAP_GLUE_REAL_OWNED_MAP refused=4",
        "DYN_HEAP_GLUE_STATICLIB deep_chain: r=8 allocs=7 deallocs=7 live=0 box_chain: r=42 allocs=3 deallocs=3 live=0",
    ), ((NATIVE_RUN, 3), (EXPECTED_REFUSAL, 2)), 5),
    # Multi-CGU linking: rustc gives every CGU that uses an `#[inline]` item
    # its own `Internal` copy under one name, which the bridge emits as a
    # CGU-private, private-extern (N_PEXT) symbol. An executable, an rlib with
    # a downstream binary and a staticlib in a C driver, each at -O0..-O3 x
    # -Ccodegen-units 2/4/16, must link and match LLVM; the objects are read
    # back (no global defined twice, every private copy a private extern).
    Target("multi_cgu_link_aarch64", 4, HOST_ORACLE, (
        "MULTI_CGU_EXECUTABLES rows=24 matched=24",
        "MULTI_CGU_RLIB_PAIR rows=12 matched=12",
        "MULTI_CGU_STATICLIB rows=12 matched=12",
        "MULTI_CGU_PRIVATE_EXTERNS cgus>=2 duplicated=0 exported=0",
    ), ((NATIVE_RUN, 4),), 4),
    Target("cross_crate_copies_native_aarch64", 1, NATIVE, (
        "CROSS_CRATE_COPIES cells=6 llvm_runs=6 cg_runs=18 opts=0,1,2 cgus=1,16",
    ), ((NATIVE_RUN, 1),), 1),
    Target("statics_linkage_native_aarch64", 1, NATIVE, (
        "STATICS_LINKAGE cells=4 llvm_runs=4 cg_runs=4 combined_object_sets=2 opts=0,2 cgus=1,16",
    ), ((NATIVE_RUN, 1),), 1),
    # A MIR Assert whose condition is a known constant emits no panic path, as
    # rustc's codegen does: a `no_std` object with constant array indices links
    # against a C driver without `core`; a run-time index keeps its raise.
    Target("assert_constant_condition_aarch64", 1, NATIVE, (
        "ASSERT_CONSTANT_CONDITION const_index=folded dynamic_index=raises",
    ), ((NATIVE_RUN, 1),), 1),
    # `vec![value; n]` reports rustc's capacity, 0 included, through every
    # LLVM/bridge library-and-binary pairing at -O0 and -O3.
    Target("vec_from_elem_capacity_aarch64", 1, NATIVE, (
        "VEC_FROM_ELEM_CAPACITY cases=2 cells=16 opts=0,3",
    ), ((NATIVE_RUN, 1),), 1),
    # The loop rewrites of the Darwin runtime-parity work (xorshift-pair
    # fusion, scalar-unroll's lane-offset gather, the late Madd addend, SROA
    # and LICM through a constant-register field address) and its size
    # offsets (even-divisor pre-shift, W-form remainder tail, repeated
    # constant chains): 333 rows at -O2 and -O3 against LLVM, with witnesses
    # that the rewrites ran; proofs off.
    Target("runtime_parity_rewrites_aarch64", 1, NATIVE, (
        "RUNTIME_PARITY_REWRITES rows=666 matched=666 opts=2,3 "
        "fused_xorshift_instances=30 paired_gathers=1",
    ), ((NATIVE_RUN, 1),), 1),
    # Constant-index slice and array places (`(*s)[k of n]`, `(*s)[-k of n]`,
    # `a[from..to]`): std's slice algorithms, slice patterns and raw pointers
    # over four element types, stdout and exit against LLVM at -O0..-O3. Cells
    # another lowering family refuses are pinned by name in the fixture.
    Target("slice_constant_index_aarch64", 3, NATIVE, (
        "SLICE_CONSTANT_INDEX test=elements cells=64 matched=60 refused_by_name=4 opts=0,1,2,3",
        "SLICE_CONSTANT_INDEX test=from_end_kinds cells=12 matched=12 refused_by_name=0 "
        "opts=0,1,2,3",
        "SLICE_CONSTANT_INDEX test=stable_select cells=32 matched=4 refused_by_name=28 "
        "opts=0,1,2,3",
    ), ((NATIVE_RUN, 3),), 3),
    # The slice chunk/window iterator family (all nine chunk/window iterators,
    # as_chunks and chunk_by) against LLVM at -O0..-O3 x abort/unwind, stdout,
    # exit status and panic stderr. count() refuses by name at -O0/-O1; every
    # zero-size row prints std's own message, the windows(0) rows at -O2/-O3
    # included (std_panic_route raises the MIR-inlined expect_failed), so no
    # synthesized message is counted.
    Target("stride_iter_family_differential_aarch64", 1, NATIVE, (
        "STRIDE_ITER_FAMILY fixtures=4 cells=32 matched=28 refused=4 runs=92 rows=164072 "
        "synthesized_messages=0 opts=0,1,2,3 strategies=abort,unwind",
    ), ((NATIVE_RUN, 1),), 1),
    # The slice-sort interception orders u64/usize and unstable key sorts as std
    # does: every cell matches LLVM or is refused by name, never another order.
    Target("slice_sort_order_aarch64", 1, NATIVE, (
        "SLICE_SORT_ORDER cases=4 cells=16 matched=10 refused=6 opts=0,1,2,3",
    ), ((NATIVE_RUN, 1),), 1),
    # Every cached-key level must execute with exactly one callback per item.
    # The fixture's old all-refusal outcome remains data, never native credit.
    Target("slice_sort_cached_key_effects_aarch64", 1, NATIVE, (
        "CACHED_KEY_COUNTER cells=4 matched=4 refused=0 certs=off",
    ), ((NATIVE_RUN, 1),), 1),
    # Closure Pair entry/call transport must agree across LLVM/CG boundaries,
    # including register exhaustion, at all four optimization levels.
    Target("aarch64_closure_body_pair_xback", 1, NATIVE, (
        "CLOSURE_BODY_PAIR_XBACK rows=7 cells=16 opts=0,1,2,3 certs=off",
    ), ((NATIVE_RUN, 1),), 1),
    # A loop that reborrows a slice by a sub-slice of itself compiles within a
    # time bound and matches LLVM (the address-identity fixpoint is bounded).
    Target("subslice_loop_compile_bound_aarch64", 1, NATIVE, (
        "SUBSLICE_LOOP_COMPILE_BOUND cases=4 cells=16 matched=16 opts=0,1,2,3",
    ), ((NATIVE_RUN, 1),), 1),
    # A `.len()` printed through format!/println!/eprintln!/write! (no
    # [TCG-FMT-LEN] refusal) and std's black_box of a Vec by value, `&` and
    # `&mut` (not claimed by the Vec interceptor) match LLVM at -O0..-O3 under
    # panic abort and unwind. The Vec<Vec<_>> and BTreeMap black_box rows may
    # refuse only by their own named reasons; their counts are reported apart.
    Target("format_length_black_box_aarch64", 2, NATIVE, (
        "FORMAT_LENGTH programs=9 cells=72 matched=72 opts=0,1,2,3 strategies=abort,unwind",
        "STD_BLACK_BOX programs=6 cells=48 must_match=32 opts=0,1,2,3 strategies=abort,unwind",
    ), ((NATIVE_RUN, 2),), 2),
    # Values the bridge itself produces, against LLVM at -O0..-O3: a call or
    # intrinsic result stored into a field of a memory-backed local (tuple and
    # closure Clone shims, custom-MIR calls; abort and unwind), the
    # layout-derived None byte of Vec<f32/f64>::partial_cmp, and Vec == array or
    # slice operands (std's body, never the Vec == Vec intercept). The refused
    # cells are named refusals each row pins.
    Target("core_values_user_trait_differential_aarch64", 3, HOST_ORACLE, (
        "CORE_VALUES_FIELD_RESULTS cases=16 cells=96 matched=92 refused=4",
        "CORE_VALUES_PARTIAL_CMP cases=7 cells=28 matched=28 refused=0",
        "CORE_VALUES_VEC_EQ cases=9 cells=36 matched=34 refused=2",
    ), ((NATIVE_RUN, 3),), 3),
    # The integer-lane BTreeMap/HashMap model: a key whose Ord / PartialEq /
    # Hash, a value whose Default, a Drop key or value, a user hasher, or a
    # `&Q` lookup with Q != K must refuse by [TCG-MAP-MODEL-TRAIT] at -O0..-O3
    # (each compiled and diverged from LLVM before the admission checked
    # them), including an upstream hand-written impl under the ungated
    # #[automatically_derived] attribute and a derived Default with a default
    # field value, while primitive, char and builtin-derived (local, core or
    # upstream) controls still build and match LLVM.
    Target("map_model_user_trait_differential_aarch64", 2, NATIVE, (
        "MAP_MODEL_USER_TRAIT_REFUSALS guests=34 cells=136 refused=136 llvm_runs=136 opts=0,1,2,3",
        "MAP_MODEL_LANE_CONTROLS guests=16 cells=64 matched=64 opts=0,1,2,3",
    ), ((NATIVE_RUN, 1), (EXPECTED_REFUSAL, 1)), 2),
    # The in-place `Vec` models (retain/retain_mut, dedup/dedup_by/dedup_by_key,
    # resize_with, insert) for elements and keys whose `Drop` or `PartialEq` is
    # user code, against LLVM at -O0..-O3 under panic=abort and panic=unwind:
    # removed and truncated elements destroyed in std's order, std's repair of
    # the Vec when a closure or destructor unwinds, the key closure and key
    # `PartialEq` called as std calls them, primitive and derived-element
    # controls, and the named refusals of the drops the models do not run.
    # A by-value terminal over an owning `vec::IntoIter` frees its buffer (and
    # a collect's result) when its payload or `Sum`'s checked add unwinds, as
    # std's terminal does; `extend` reserves as std does, and a `Sum` /
    # `Product` overflow reports core's check. The -O2/-O3 cells of shapes
    # refused before the terminal is lowered are pinned by code and reason.
    Target("vec_compact_user_trait_differential_aarch64", 5, NATIVE, (
        "VEC_COMPACT_DESTRUCTION cases=18 cells=144 matched=144 refused=0 opts=0,1,2,3 "
        "strategies=abort,unwind",
        "VEC_COMPACT_UNWIND cases=15 cells=60 matched=60 opts=0,1,2,3 strategies=unwind",
        "VEC_COMPACT_CONTROLS cases=6 cells=48 matched=48 opts=0,1,2,3 strategies=abort,unwind",
        "VEC_COMPACT_REFUSALS cases=3 cells=24 refused=24 opts=0,1,2,3 strategies=abort,unwind",
        "VEC_INTO_ITER_UNWIND cases=35 cells=188 matched=120 refused=68 opts=0,1,2,3 "
        "strategies=abort,unwind",
    ), ((NATIVE_RUN, 4), (EXPECTED_REFUSAL, 1)), 5),
    # The `vec![x; n]`, `.cloned()` and slice-sort models against the user
    # code std runs in them (a hand-written `Clone`, a `Cell`'s clone, an
    # unsigned element order, a key closure with effects), bridge against LLVM
    # at -O0..-O3 under abort and unwind: every cell builds and matches LLVM or
    # refuses with the code its row names, and the primitive-element and
    # derived-clone controls keep building; a closure that writes a `Cell`
    # clone through `&` passes the written clone on; a `Cell` over a
    # hand-written `clone`, `RefCell`, `OnceCell` and a local type named `Cell`
    # keep refusing.
    Target("clone_sort_user_trait_differential_aarch64", 4, HOST_ORACLE, (
        "CLONE_SORT_FROM_ELEM rows=11 cells=56 matched=20 refused=36 opts=0,1,2,3 strategies=abort,unwind",
        "CLONE_SORT_CELL_CLONES rows=30 cells=240 matched=156 refused=84 opts=0,1,2,3 strategies=abort,unwind",
        "CLONE_SORT_SLICE_SORTS rows=34 cells=164 matched=96 refused=68 opts=0,1,2,3 strategies=abort,unwind",
        "CLONE_SORT_TUPLE_SCALARS rows=7 cells=56 matched=56 refused=0 opts=0,1,2,3 strategies=abort,unwind",
    ), ((NATIVE_RUN, 4),), 4),
    # A `match` on a signed integer with negative arms compiles and takes
    # LLVM's arm at every width (`switch_case_literal`); unsigned cases above
    # the sign bit keep their bits.
    Target("switch_case_signed_aarch64", 1, NATIVE, (
        "SWITCH_CASE_SIGNED cases=2 cells=8 matched=8 opts=0,1,2,3",
    ), ((NATIVE_RUN, 1),), 1),
    # format!, write! and integer to_string() Strings have std's capacity and
    # make std's allocator calls, and no write passes the bytes it reserved
    # (a canary allocator under exact-fit Strings), at -O0..-O3, abort and unwind.
    Target("format_capacity_aarch64", 1, NATIVE, (
        "FORMAT_CAPACITY programs=5 cells=40 matched=40 opts=0,1,2,3 strategies=abort,unwind",
    ), ((NATIVE_RUN, 1),), 1),
    # Vec::extend from an iterator chain leaves std's capacity (SpecExtend:
    # a TrustedLen chain reserves its count up front, any other exact chain at
    # the first full Vec), also from a `Chain` whose half core's own bodies
    # cleared, and a bare integer `Range` of each of the ten integer types
    # fills as LLVM's does, from runtime or constant endpoints: -O0/-O1 must
    # match LLVM; -O2/-O3 match or refuse std's extend bodies by name.
    Target("vec_extend_capacity_aarch64", 1, NATIVE, (
        "VEC_EXTEND_CAPACITY programs=6 cells=48 must_match=24 opts=0,1,2,3 strategies=abort,unwind",
    ), ((NATIVE_RUN, 1),), 1),
    # A switch case constant the cascade materializes is not reused on the
    # paths that skipped it (GVN/CSE across a mid-block exit): -O0..-O3,
    # abort and unwind, every cell matches LLVM.
    Target("switch_join_constant_aarch64", 1, NATIVE, (
        "SWITCH_JOIN_CONSTANT programs=5 cells=40 matched=40 opts=0,1,2,3 strategies=abort,unwind",
    ), ((NATIVE_RUN, 1),), 1),
    # Iterator drives over a `Range` or slice source whose `map` yields an item
    # with a user `Drop`, when a payload the drive calls unwinds, against LLVM
    # at -O0..-O3 under abort and unwind: the item a by-reference payload
    # (`find`, `filter`, `take_while`, `skip_while`, `inspect`) borrows is
    # dropped before the unwind leaves the drive (an abort when its destructor
    # panics there), as the payload left it when it is interior-mutable; an
    # interior-mutable item a payload writes is the one the drive keeps; drives
    # that hold nothing across the unwind still match; a `collect` frees the
    # `Vec` it builds (a counting allocator sees no buffer left live); and a
    # held item whose drop the drive does not lower, a droppable value a
    # terminal carries across adapter closures, a held item in a body without
    # EH lowering and a collect without EH lowering refuse by name.
    Target("iter_chain_unwind_item_differential_aarch64", 5, NATIVE, (
        "ITER_CHAIN_UNWIND_HELD cases=26 cells=208 matched=190 refused=18 opts=0,1,2,3 "
        "strategies=abort,unwind",
        "ITER_CHAIN_INTERIOR_MUT_ITEMS cases=9 cells=72 matched=52 refused=20 opts=0,1,2,3 "
        "strategies=abort,unwind",
        "ITER_CHAIN_UNWIND_CONTROLS cases=10 cells=80 matched=70 refused=10 opts=0,1,2,3 "
        "strategies=abort,unwind",
        "ITER_CHAIN_UNWIND_COLLECT cases=9 cells=72 matched=72 refused=0 no_eh_levels=4 "
        "opts=0,1,2,3 strategies=abort,unwind",
        "ITER_CHAIN_UNWIND_REFUSALS cases=8 cells=56 matched=30 refused=26 no_eh_sites=16 "
        "opts=0,1,2,3 strategies=abort,unwind",
    ), ((NATIVE_RUN, 4), (EXPECTED_REFUSAL, 1)), 5),
    Target("float_semantics", 4, HOST_ORACLE, (), ((NATIVE_RUN, 3), (EXPECTED_REFUSAL, 1)), 0),
    Target("overflow_asserts", 9, HOST_ORACLE, (), ((NATIVE_RUN, 9),), 0),
    # scalar_reference_return_non_escaping pins the named scalar-borrow refusal
    # (TCG-MIR-UNSUPPORTED) until borrow materialization lands, then runs.
    Target("reference_union_semantics", 35, HOST_ORACLE, (),
           ((NATIVE_RUN, 28), (COMPILED, 6), (EXPECTED_REFUSAL, 1)), 0),
    # no_mangle_roots_are_never_dropped_when_their_object_compile_fails (L14-P10)
    # credits a compile in a complete pass, where its `write_choice` compiles as
    # multi_variant_enum_reference_parameter_abi_fails_after_backend_load
    # requires; until then it passes as an expected refusal of both roots.
    # The incoming bridge fixes add five: three named refusals (the two
    # [TCG-ADDR-IDENTITY] pairs and the non-promoted ZST trait-object constants)
    # and two proofs-off compiles (interior-ZST whole stores and retained
    # pointer locals). The native pointer-loop control remains proofs off.
    Target("unsupported_program", 18, HOST_ORACLE, (),
           ((NATIVE_RUN, 1), (COMPILED, 9), (EXPECTED_REFUSAL, 8)), 4),
    # L06-P3: the bridge differential corpus (the x86 lane's corpus() table)
    # and the whole programs of the x86 feature suites' tables, run natively
    # on this host against LLVM, every cell checked against the committed
    # census in tests/a64_census/ (a divergence fails; a refusal, a
    # PANIC-MESSAGE text divergence and an LLVM-unbuildable program are
    # listed there by name). The proofs-off lanes are diagnostics; the
    # certificates-on corpus lane (-O2) is the refusal census of the proof
    # wall (L07-P2), credited as an expected refusal. The regressions pin the
    # miscompiles this lane found, fixed: a consumed closure whose skipped
    # drop glue does more than free Global memory (a user Drop, Rc/Arc counts,
    # or any glue under a #[global_allocator]) either run by the drive and
    # matching LLVM's destructor-counting exit or refused by name by every
    # interception, the in-place Vec models included (each verdict counted;
    # since L06-P8 the two -O3 cells whose drive runs a Box drop in the
    # closure's glue match through rustc's box glue, so none refuses at that
    # drop here), the Global-memory-only controls (Box-owning closures, also
    # consumed by the Vec models) matching LLVM as a leak (ruling OD-171), the
    # float partial_cmp None niche and the u128 saturating clamp matching LLVM;
    # (found in review) a `Chain` drive that reads each half's `Option` tag,
    # so a half core cleared is skipped; and the in-place Vec models running a
    # closure that captures a pair-returning closure (-O0..-O3, both
    # strategies), with the iterator drives' real-body routes, the std bodies
    # of Vec calls no model runs the closure of (pop_if, extract_if,
    # Option/Result::map_or[_else]) and own-output pair controls beside them.
    Target("bridge_differential_aarch64", 2, HOST_ORACLE, (
        "A64_CORPUS lane=proofs-off cases=154 cells=462 llvm_runs=462 cg_runs=432 matched=432 refused=30 refusals=TCG-MIR-UNSUPPORTED:13,TCG-MIR-UNSUPPORTED/TCG-IR-LOWER:3,TCG-MIR-UNSUPPORTED/TCG-RET-ABI:6,TCG-MIR-UNSUPPORTED/TCG-SCALAR-CELL-LAYOUT:8 panic_message=0 diverged=0",
        "A64_CORPUS lane=certs-on cases=154 cells=154 llvm_runs=154 cg_runs=0 matched=0 refused=154 refusals=TCG-MIR-UNSUPPORTED:4,TCG-MIR-UNSUPPORTED/TCG-PROOF-465:144,TCG-MIR-UNSUPPORTED/TCG-RET-ABI:2,TCG-MIR-UNSUPPORTED/TCG-SCALAR-CELL-LAYOUT:4 panic_message=0 diverged=0",
    ), ((NATIVE_RUN, 1), (EXPECTED_REFUSAL, 1)), 1),
    Target("bridge_feature_suites_aarch64", 8, HOST_ORACLE, (
        "A64_FEATURE_SUITES family=closures suites=4 programs=48 cells=96 llvm_runs=96 cg_runs=96 matched=96 refused=0 refusals=none panic_message=0 diverged=0 unbuildable=0 oracle_off_pin=0",
        "A64_FEATURE_SUITES family=iterators suites=6 programs=153 cells=306 llvm_runs=306 cg_runs=239 matched=239 refused=67 refusals=TCG-MIR-UNSUPPORTED:27,TCG-MIR-UNSUPPORTED/TCG-MAP-ENTRY-USE:1,TCG-MIR-UNSUPPORTED/TCG-RET-ABI:21,TCG-MIR-UNSUPPORTED/TCG-STEPBY-METHOD:2,TCG-MIR-UNSUPPORTED/TCG-STEPBY-OPT-LEVEL:16 panic_message=0 diverged=0 unbuildable=0 oracle_off_pin=0",
        "A64_FEATURE_SUITES family=dyn_enums_try suites=5 programs=63 cells=126 llvm_runs=126 cg_runs=126 matched=126 refused=0 refusals=none panic_message=0 diverged=0 unbuildable=0 oracle_off_pin=0",
        "A64_FEATURE_SUITES family=heap_collections suites=7 programs=77 cells=154 llvm_runs=154 cg_runs=140 matched=140 refused=14 refusals=TCG-MIR-UNSUPPORTED:12,TCG-MIR-UNSUPPORTED/TCG-IR-LOWER:2 panic_message=0 diverged=0 unbuildable=0 oracle_off_pin=0",
        "A64_FEATURE_SUITES family=strings_format suites=7 programs=165 cells=330 llvm_runs=330 cg_runs=285 matched=285 refused=45 refusals=TCG-MIR-UNSUPPORTED:13,TCG-MIR-UNSUPPORTED/TCG-COLLECTION-IMAGE:2,TCG-MIR-UNSUPPORTED/TCG-FMT-DECLINED:6,TCG-MIR-UNSUPPORTED/TCG-FMT-RTSTR:2,TCG-MIR-UNSUPPORTED/TCG-IR-LOWER:3,TCG-MIR-UNSUPPORTED/TCG-ITER-UNMODELED:6,TCG-MIR-UNSUPPORTED/TCG-PARSE-F64:6,TCG-MIR-UNSUPPORTED/TCG-RET-ABI:1,TCG-MIR-UNSUPPORTED/TCG-STR-CASE:6 panic_message=0 diverged=0 unbuildable=0 oracle_off_pin=0",
        "A64_FEATURE_SUITES family=std_main_statics_memory suites=8 programs=72 cells=144 llvm_runs=144 cg_runs=143 matched=143 refused=1 refusals=TCG-MIR-UNSUPPORTED:1 panic_message=0 diverged=0 unbuildable=0 oracle_off_pin=0",
        "A64_FEATURE_SUITES family=slices_aggregates_numerics suites=9 programs=157 cells=314 llvm_runs=314 cg_runs=314 matched=314 refused=0 refusals=none panic_message=0 diverged=0 unbuildable=0 oracle_off_pin=0",
        "A64_FEATURE_SUITES family=panics_unwind suites=2 programs=34 cells=68 llvm_runs=60 cg_runs=60 matched=60 refused=0 refusals=none panic_message=0 diverged=0 unbuildable=8 oracle_off_pin=0",
    ), ((NATIVE_RUN, 8),), 8),
    Target("bridge_regressions_aarch64", 7, HOST_ORACLE, (
        "CLOSURE_DROP_CONSUMED rows=20 cells=40 matched=18 refused_closure_drop=8 refused_owned_drop=14 refused_box_glue=0 opts=0,3",
        "CLOSURE_DROP_ALLOCATION rows=5 cells=10 matched=2 refused_closure_drop=6 refused_owned_drop=2 opts=0,3",
        "CLOSURE_DROP_CONTROLS rows=4 cells=8 matched=8 opts=0,3",
        "FLOAT_PARTIAL_CMP_NONE rows=4 cells=8 matched=8 opts=0,3",
        "U128_SATURATING rows=3 cells=6 matched=6 opts=0,3",
        "CHAIN_CLEARED_HALF rows=8 cells=16 matched=16 opts=0,3",
        "CAPTURED_PAIR_CALLBACKS rows=29 cells=232 matched=224 refused_by_name=8 opts=0,1,2,3 strategies=abort,unwind",
    ), ((NATIVE_RUN, 5), (EXPECTED_REFUSAL, 2)), 7),
    Target("fixed_cost_budget_aarch64", 2, FIXED_COST, ("fixed-cost budget held: cold",),
           ((FIXED_COST_EVIDENCE, 1), (UNIT_CHECK, 1)), 0),
    Target("real_program_corpus_a64", 1, COMPILE_VERDICT, (), ((VERDICT, 1),), 0),
    # The current private API must refuse Box validity casts and execute its
    # scalar/allocation comparisons. The latter remains a proofs-off diagnostic.
    Target("current_private_api", 2, NATIVE, (),
           ((EXPECTED_REFUSAL, 1), (NATIVE_RUN, 1)), 1),
)
COMPILE_VERDICT_LABEL = (
    "compile-verdict-only: --emit=obj for aarch64-apple-darwin at O0 and O3; "
    "no link or execution, so not native execution evidence"
)
# Bridge test files that name the Darwin AArch64 triple or carry an
# aarch64+macOS gate but are not required here. They are reported, never
# counted. Every such target is required since 2026-09-29 (L06-P10); a new
# entry needs a reason and is a denominator change.
NOT_COVERED: dict = {}
OUT_OF_SCOPE = {
    "m100_str_memcpy_x86": (
        "x86_64-apple-darwin execution fixture; names the AArch64 triple only in a runner-probe "
        "unit test"
    ),
    "target_dir_resolution": (
        "unit tests of Cargo target-directory resolution; the triple is data, not a compile target"
    ),
}
# Required targets whose refusal may be recorded as an OPEN named refusal
# instead of a failure: {target: {"gap": ledger id, "reason": text,
# "markers": [full-line regular expressions]}}. Every refusal line in the
# target's transcript must fullmatch one of the markers. A named refusal is
# never a pass, never counts executed passes, and makes the run exit 3. It is
# deliberately empty: which refusal, if any, may be recorded this way is an
# owner decision.
NAMED_REFUSALS: dict = {}

# These newly required single-test native rows need one exact summary in the
# same captured output as their native evidence, not a matching substring or
# a second contradictory ledger. Counts live only in TARGETS above.
STRICT_NATIVE_TESTS = {
    "slice_sort_cached_key_effects_aarch64":
        "cached_key_counter_calls_once_per_element_or_refuses_by_name",
    "aarch64_closure_body_pair_xback":
        "closure_body_pairs_match_llvm_across_native_backend_boundaries",
}
STRICT_NATIVE_PREFIXES = (
    "CACHED_KEY_COUNTER ", "CLOSURE_BODY_PAIR_XBACK ",
)

AARCH64_MACOS_GATE = re.compile(
    r'target_arch\s*=\s*"aarch64"\s*,\s*target_os\s*=\s*"macos"'
    r'|target_os\s*=\s*"macos"\s*,\s*target_arch\s*=\s*"aarch64"'
)
DARWIN_TRIPLE = '"aarch64-apple-darwin"'
TEST_ATTRIBUTE = re.compile(r"#\[test\]")
IGNORE_ATTRIBUTE = re.compile(r"#\[ignore\b")
POSITIVE_EVIDENCE_MODULE = '#[path = "support/positive_evidence.rs"]'
# Bridge fixtures spelled their guard returns many ways ("skipping: cc not
# available", "hello_loop: SKIPPED", "coverage floor SKIPPED:"), and a
# TCG-PROOF-465 promotion refusal was an accepted early return. Any such line
# is a refusal; this is deliberately broader than matrix_results' SKIP rule.
SKIP_WORD = re.compile(r"\bskip(?:s|ped|ping)?\b", re.IGNORECASE)
PROOF_REFUSAL = re.compile(r"TCG-PROOF-465")
REFUSAL_LINE = re.compile(SKIP_WORD.pattern + "|" + PROOF_REFUSAL.pattern, re.IGNORECASE)
# Backend diagnostics that contain a skip word but skip no test. Each must
# fullmatch the whole stripped line: the fixed text is the diagnostic's exact
# wording in trust-cg-verify, and only its paths and digests vary. Any other
# skip-word line still fails its target, and every exempted line is counted in
# the report. Ruling OD-06 (docs/decision-record.md) admits exactly these two:
# each reports a check that ran by another route (a passed-over checker
# candidate and the checker then used; certificates declined for a live
# discharge), never a skipped one. A new exemption needs its own ruling, and
# emptying the table restores option A.
# An absolute path to the named tool, built segment by segment: a segment holds
# no `/`, parenthesis, semicolon, comma or newline and never the sequence " -",
# so a message appended after a path ("... -- test SKIPPED, see /x/bin/clean")
# cannot be absorbed into it (a regex cannot prove a path is one; this keeps
# the classes of appended text a transcript actually shows out). Every checker
# candidate trust-cg-verify reports is a `bin/clean` (a sysroot's, an overlay's
# or the managed Clean package's), so the checker path must end there.
PATH_SEGMENT = r"(?:(?! -)[^/()\n;,])+"
CHECKER_PATH = r"(?:/" + PATH_SEGMENT + r")*/bin/clean"
DRAT_TRIM_PATH = r"(?:/" + PATH_SEGMENT + r")*/drat-trim"
EXEMPT_DIGEST = r"[0-9a-f]{64}"
DIAGNOSTIC_EXEMPTIONS = {
    # A default checker candidate is passed over, and the next is used (X-HOST-P8;
    # obligation_cert_store.rs note_checker_skipped, CarcaraFeatureMissing).
    # The reason is `CheckerDefect::reason()` alone: since 4ff6cd0fe the package
    # repair hint is no longer part of it, and test_darwin_aarch64_bridge_gate
    # rebuilds this line from the Rust source so the two cannot drift again.
    "checker-candidate-passed-over": re.compile(
        re.escape("[trust-cg] proof checker ") + CHECKER_PATH
        + re.escape(" skipped (it was built WITHOUT the `carcara-verify` cargo feature, so it rejects "
                    "every Alethe proof regardless of validity); using ")
        + CHECKER_PATH),
    # The certificate fast path is declined and every query is discharged live
    # (canary_cert.rs announce_checker_identity_drift_once).
    "portable-certificates-declined": re.compile(
        re.escape("trust-cg-verify::canary_cert: WARNING: portable certificate set is DISABLED; CERT-SKIP "
                  "declined for every query and live discharge retained: the vendored drat-trim checker ")
        + DRAT_TRIM_PATH + " hashes to " + EXEMPT_DIGEST + " but manifest.v1 authorizes " + EXEMPT_DIGEST
        + re.escape("; the checker's bytes follow the host C toolchain (compiler, SDK, and the deployment "
                    "target pinned in crates/trust-cg-drat-trim/build.rs). Options: restore the toolchain "
                    "the manifest was minted against, or review the toolchain change and re-authorize the "
                    "complete set with `scripts/trust_cargo.sh run --release -p trust-cg-verify --bin regen_canary_certs`")),
}
TCG_CODE = re.compile(r"\bTCG-[A-Z0-9]+(?:-[A-Z0-9]+)*")
CORPUS_SUMMARY = re.compile(
    r"\[a64 corpus row\] (\d+)/(\d+) rows COMPILED \((\d+\.\d)%\), (\d+) incomplete, (\d+) hard errors"
)
CORPUS_ROW = re.compile(r"\[a64\] (\S+@O\d): (COMPILED|INCOMPLETE|HARD ERROR)(?: .*)?")
CORPUS_FLOOR_LINE = re.compile(r"^a64_compile_floor_percent\s*=\s*(\d+(?:\.\d+)?)\s*$", re.MULTILINE)


def load_helper(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"required helper is missing: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# The Darwin floor supplies the bounded process-group runner, report writing,
# source-content fingerprint and matrix_results classification; trust_toolchain
# is the single package-resolution rule shared with the other bridge helpers.
DARWIN = load_helper("_darwin_aarch64_bridge_floor", ROOT / "scripts" / "check_darwin_aarch64.py")
TOOLCHAIN = load_helper("_darwin_aarch64_bridge_toolchain", ROOT / "scripts" / "trust_toolchain.py")
MATRIX = DARWIN.MATRIX
write_report = DARWIN.write_report
positive_seconds = DARWIN.positive_seconds
positive_jobs = DARWIN.positive_jobs


class GateError(RuntimeError):
    """One or more named findings that stop the run."""

    def __init__(self, findings: Sequence[tuple[str, str]]):
        self.findings = [(code, message) for code, message in findings]
        super().__init__("; ".join(f"{code}: {message}" for code, message in self.findings))


def refuse(code: str, message: str) -> GateError:
    return GateError([(code, message)])


def current_source(git: str) -> dict:
    return DARWIN.source_provenance(git)


def require_darwin_host() -> str:
    """Refuse every host but native aarch64-apple-darwin before probing tools."""
    machine = platform.machine()
    if sys.platform != "darwin" or machine != MACHINE:
        raise refuse(HOST_REFUSED, f"required host is {HOST}, observed {sys.platform}/{machine}")
    return machine


def ambient_findings(environment: dict) -> list[tuple[str, str]]:
    present = [name for name in REFUSED_ENVIRONMENT if name in environment]
    present += sorted(name for name in environment if name.startswith(REFUSED_PREFIXES))
    findings = []
    if present:
        findings.append((AMBIENT_OVERRIDE,
                         f"bridge qualification rejects ambient compiler/backend/codegen overrides: {present}"))
    toolchain = environment.get("RUSTUP_TOOLCHAIN")
    if toolchain is not None and toolchain != TOOLCHAIN.REQUIRED_CHANNEL:
        findings.append((AMBIENT_OVERRIDE, f"RUSTUP_TOOLCHAIN selects {toolchain!r}, not the bridge pin"))
    return findings


def probe_environment(environment: dict) -> dict:
    """Trust compilers refuse TRUST_CG_*/TCG_*; identity probes run without them."""
    return {name: value for name, value in environment.items() if not name.startswith(REFUSED_PREFIXES)}


def probe(command: Sequence[str], environment: dict | None = None, timeout: float = 60) -> str:
    try:
        result = subprocess.run(
            list(command), cwd=BRIDGE_DIR, capture_output=True, text=True, timeout=timeout,
            check=False, env=environment,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(f"probe {list(command)!r} failed: {error}") from error
    if result.returncode != 0:
        raise RuntimeError(f"probe {list(command)!r} exited {result.returncode}: {result.stderr.strip()}")
    return "\n".join(part.strip() for part in (result.stdout, result.stderr) if part.strip())


def required_private_crates(source_dir: Path = BRIDGE_DIR / "src") -> tuple[str, ...]:
    """The rustc_private crates the backend source names with `extern crate`."""
    names = set()
    for path in sorted(source_dir.rglob("*.rs")):
        names.update(EXTERN_CRATE.findall(path.read_text(encoding="utf-8", errors="replace")))
    return tuple(sorted(names))


def missing_private_crates(target_lib: Path, required: Sequence[str]) -> list[str]:
    missing = []
    for name in required:
        if not any(
            path.is_file() and path.suffix in (".rmeta", ".rlib", ".dylib")
            for path in target_lib.glob(f"lib{name}-*")
        ):
            missing.append(name)
    return missing


def rustup_trust_link(environment: dict) -> tuple[str, str] | None:
    """Locate rustup's `trust` toolchain rustc as gate_env.sh does, or None.

    A rustup that cannot answer does not hide the link: the RUSTUP_HOME
    toolchains/trust entry is checked as well.
    """
    home = Path(environment.get("HOME") or "/")
    candidates = [shutil.which("rustup", path=environment.get("PATH"))]
    candidates.append(str(Path(environment.get("CARGO_HOME") or home / ".cargo") / "bin" / "rustup"))
    for rustup in dict.fromkeys(candidates):
        if not rustup or not os.path.isfile(rustup) or not os.access(rustup, os.X_OK):
            continue
        query = {**probe_environment(environment), "RUSTUP_AUTO_INSTALL": "0"}
        try:
            result = subprocess.run(
                [rustup, "which", "--toolchain", "trust", "rustc"], capture_output=True,
                text=True, timeout=30, check=False, env=query, cwd=BRIDGE_DIR,
            )
        except (OSError, subprocess.TimeoutExpired):
            continue
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip().splitlines()[-1], f"{rustup} which --toolchain trust rustc"
    link = Path(environment.get("RUSTUP_HOME") or home / ".rustup") / "toolchains" / "trust" / "bin" / "rustc"
    if link.is_file() and os.access(link, os.X_OK):
        return str(link), "RUSTUP_HOME toolchains/trust"
    return None


def trust_link_findings(record: dict, environment: dict) -> tuple[dict | None, list[tuple[str, str]]]:
    """Refuse a rustup `trust` link that is not the resolved package."""
    located = rustup_trust_link(environment)
    if located is None:
        return None, []
    rustc, source = located
    try:
        reported = probe([rustc, "--print", "sysroot"], probe_environment(environment)).strip().splitlines()[-1]
        sysroot = str(Path(reported).resolve(strict=True))
    except (RuntimeError, OSError, IndexError) as error:
        return {"rustc": rustc, "source": source}, [(IDENTITY_UNKNOWN,
            f"rustup `trust` resolves to {rustc} but its sysroot cannot be measured, so "
            f"divergence cannot be decided: {error}")]
    identity = {"rustc": rustc, "source": source, "sysroot": sysroot}
    if sysroot != record["sysroot"]:
        # A copied tree carrying the same compiler (same 40-hex commit, same
        # TOOLCHAIN.compiler_digest bytes: bin/trustc, bin/rustc, bin/ay, lib/
        # and libexec/) is one compiler at two paths.
        try:
            verbose = probe([rustc, "-vV"], probe_environment(environment))
        except RuntimeError:
            verbose = ""
        commits = re.findall(r"^commit-hash: ([0-9a-f]{40})$", verbose, re.MULTILINE)
        if len(commits) == 1 and TOOLCHAIN.same_compiler(
                Path(sysroot), commits[0], Path(record["sysroot"]), record.get("commit") or ""):
            identity["same_compiler_as"] = record["sysroot"]
            return identity, []
        return identity, [(DIVERGENT,
            f"rustup `trust` -> {sysroot} but the resolved package is {record['sysroot']}; "
            "`channel = \"trust\"` builds would use a different compiler than this runner. "
            "Relink one to the other (`rustup toolchain link trust <sealed sysroot>` or "
            "`aterm pkg repair`)")]
    return identity, []


def host_tool_identities(environment: dict) -> tuple[dict, list[tuple[str, str]]]:
    identities, findings = {}, []
    for name in HOST_TOOLS:
        path = shutil.which(name, path=environment.get("PATH"))
        if path is None:
            findings.append((HOST_TOOL_MISSING, f"required host tool is missing: {name}"))
            continue
        record = {"path": path, "resolved": str(Path(path).resolve()), "sha256": DARWIN.file_sha256(Path(path).resolve())}
        arguments = HOST_TOOL_PROBES.get(name)
        if arguments is not None:
            try:
                record["identity"] = probe([path, *arguments], probe_environment(environment), timeout=30)
            except RuntimeError as error:
                findings.append((HOST_TOOL_MISSING, f"host tool {name} at {path} cannot be identified: {error}"))
        identities[name] = record
    return identities, findings


def cargo_config_files(environment: dict) -> list[Path]:
    """Config files Cargo loads for a command started in BRIDGE_DIR, nearest first."""
    home = Path(environment.get("CARGO_HOME") or Path(environment.get("HOME") or "/") / ".cargo")
    candidates = [
        directory / ".cargo" / name
        for directory in (BRIDGE_DIR, *BRIDGE_DIR.parents) for name in ("config.toml", "config")
    ]
    candidates += [home / name for name in ("config.toml", "config")]
    files, seen = [], set()
    for path in candidates:
        if path.is_file() and path.resolve() not in seen:
            seen.add(path.resolve())
            files.append(path)
    return files


def cargo_config_findings(environment: dict) -> tuple[dict, list[tuple[str, str]]]:
    identities, findings = {}, []
    for path in cargo_config_files(environment):
        data = path.read_bytes()
        match = DARWIN.CARGO_CONFIG_REROUTE.search(data.decode("utf-8", errors="replace"))
        if match is not None:
            findings.append((CARGO_CONFIG_REROUTE,
                             f"Cargo config {path} sets {match.group(1)}, which would bypass the resolved "
                             "compiler or run test binaries through another program"))
        identities[str(path)] = hashlib.sha256(data).hexdigest()
    return identities, findings


def evidence_profile_problems(target: Target) -> list[str]:
    """A target's evidence profile names allowed kinds once and sums to its minimum."""
    problems = []
    profile = target.evidence
    allowed = ALLOWED_EVIDENCE.get(target.kind, ())
    if (not isinstance(profile, tuple) or not profile
            or any(not isinstance(row, tuple) or len(row) != 2 for row in profile)):
        return ["evidence profile must be a nonempty tuple of (kind, count) pairs"]
    kinds = [kind for kind, _ in profile]
    if len(set(kinds)) != len(kinds):
        problems.append("evidence profile names a kind twice")
    for kind, count in profile:
        if kind not in allowed:
            problems.append(f"evidence kind {kind!r} is not credited for a {target.kind} target")
        if type(count) is not int or count < 1:
            problems.append(f"evidence count for {kind!r} must be a positive integer")
    if type(target.minimum) is int and sum(
            count for _, count in profile if type(count) is int) != target.minimum:
        problems.append(f"evidence profile does not sum to the minimum {target.minimum}")
    if type(target.certs_off) is not int or not 0 <= target.certs_off <= (
            target.minimum if type(target.minimum) is int else 0):
        problems.append("certs_off must be an integer between 0 and the minimum")
    return problems


def code_lines(text: str) -> list[str]:
    """The source lines that are not whole-line `//` comments."""
    return [line for line in text.splitlines() if not COMMENT_LINE.match(line)]


def certificate_knob_problems(target: Target, text: str) -> list[str]:
    """Tie a fixture's no-proof-certs use to its certs_off row.

    A target with no proofs-off test must not name the knob at all, and one with
    proofs-off tests must name it. Knob arguments must come from
    toolchain_support::backend_knobs_arg, whose trace the transcript check
    compares with each test's marker; a fixture that spells the option itself
    is refused.
    """
    problems = []
    code = code_lines(text)
    names_knob = any(NO_PROOF_CERTS_KNOB in line for line in code)
    if type(target.certs_off) is int and target.certs_off == 0 and names_knob:
        problems.append(f"passes {NO_PROOF_CERTS_KNOB} but its row has no proofs-off (certs_off) test")
    if type(target.certs_off) is int and target.certs_off > 0 and not names_knob:
        problems.append(f"its row counts {target.certs_off} proofs-off tests but it never passes "
                        f"{NO_PROOF_CERTS_KNOB}")
    raw = sorted({match[0] for line in code for match in [RAW_KNOB_OPTION.search(line)] if match})
    if raw:
        problems.append(f"spells the backend knob option itself ({raw}); build knob arguments with "
                        "toolchain_support::backend_knobs_arg, whose trace the runner checks")
    return problems


def rust_views(text: str) -> tuple[str, str]:
    """Two offset-preserving views of Rust source: (code, skeleton).

    code blanks every comment (line, and nested block); skeleton also blanks the
    contents of every string, raw string and char literal, so its braces and
    declarations are the program's own. Newlines are kept in both.
    """
    code, skeleton = list(text), list(text)

    def blank(view: list, start: int, end: int) -> None:
        for index in range(start, min(end, len(view))):
            if view[index] != "\n":
                view[index] = " "

    index, size = 0, len(text)
    while index < size:
        if text.startswith("//", index):
            end = text.find("\n", index)
            end = size if end < 0 else end
            blank(code, index, end)
            blank(skeleton, index, end)
            index = end
            continue
        if text.startswith("/*", index):
            depth, end = 1, index + 2
            while end < size and depth:
                if text.startswith("/*", end):
                    depth, end = depth + 1, end + 2
                elif text.startswith("*/", end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
            blank(code, index, end)
            blank(skeleton, index, end)
            index = end
            continue
        raw = RAW_STRING_START.match(text, index)
        if raw and (index == 0 or not (text[index - 1].isalnum() or text[index - 1] == "_")):
            close = text.find('"' + raw.group(1), raw.end())
            end = size if close < 0 else close
            blank(skeleton, raw.end(), end)
            index = size if close < 0 else close + 1 + len(raw.group(1))
            continue
        if text[index] == '"':
            end = index + 1
            while end < size and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            blank(skeleton, index + 1, end)
            index = end + 1
            continue
        if text[index] == "'":
            char = CHAR_LITERAL.match(text, index)
            if char:
                blank(skeleton, index + 1, char.end() - 1)
                index = char.end()
                continue
        index += 1
    return "".join(code), "".join(skeleton)


def item_spans(skeleton: str) -> list[tuple[str, int, int]]:
    """(name, start, end) of every fn, const and static item in a skeleton view.

    A fn's span runs to its body's matching brace (a bodiless fn to its `;`);
    a const or static runs to its `;` at brace depth zero, and no span runs past
    the block that encloses it.
    """
    spans = []
    for match in ITEM_DEFINITION.finditer(skeleton):
        kind, name = match.group(1) or match.group(2), match.group(3)
        position, depth = match.end(), 0
        while position < len(skeleton):
            char = skeleton[position]
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0 and kind == "fn":
                    position += 1
                    break
                if depth < 0:
                    # The enclosing block closed first (a generic `const N`).
                    break
            elif char == ";" and depth == 0:
                position += 1
                break
            position += 1
        spans.append((name, match.start(), position))
    return spans


def module_children(path: Path, text: str) -> tuple[list[Path], list[str]]:
    """The source files one Rust file compiles in, and the declarations it cannot resolve.

    A `#[path]` or literal `include!` path is relative to the file's directory.
    A bare `mod name;` may resolve beside the file or under a directory named
    after it, so every existing candidate is scanned; none existing is a problem.
    """
    code, skeleton = rust_views(text)
    children, problems = [], []
    directory = path.parent
    remaining = list(skeleton)
    for match in PATH_MODULE.finditer(skeleton):
        children.append(directory / code[match.start(1):match.end(1)])
        remaining[match.start():match.end()] = " " * (match.end() - match.start())
    for match in LITERAL_INCLUDE.finditer(skeleton):
        children.append(directory / code[match.start(1):match.end(1)])
        remaining[match.start():match.end()] = " " * (match.end() - match.start())
    remaining = "".join(remaining)
    lines = code.splitlines()
    for match in PATH_ATTRIBUTE.finditer(remaining):
        line = remaining.count("\n", 0, match.start())
        problems.append(f"line {line + 1}: a #[path] attribute that is not on a `mod name;` declaration "
                        "(or sits in a cfg_attr) cannot be followed")
    for match in BARE_MODULE.finditer(remaining):
        name = match.group(1)
        candidates = [base / relative for base in (directory, directory / path.stem)
                      for relative in (Path(f"{name}.rs"), Path(name) / "mod.rs")]
        found = [candidate for candidate in candidates if candidate.is_file()]
        if not found:
            problems.append(f"`mod {name};` resolves to no file ({[str(c) for c in candidates]})")
        children.extend(found)
    for match in INCLUDE_MACRO.finditer(remaining):
        line = lines[remaining.count("\n", 0, match.start())].strip()
        if line not in GENERATED_INCLUDES:
            problems.append(f"`{line}` includes a source whose path is not a literal, so it cannot be scanned")
    return children, problems


def module_knob_problems(relative: str, text: str) -> list[str]:
    """Knob spellings in one module a required fixture compiles in (see KNOB_OPTION_OWNERS)."""
    code, skeleton = rust_views(text)
    owners = KNOB_OPTION_OWNERS.get(relative, {})
    spans = item_spans(skeleton)
    problems = []
    for name in sorted(owners):
        count = sum(1 for item, _, _ in spans if item == name)
        if count > 1:
            problems.append(f"owner item {name} is defined {count} times; the exemption names one item")

    def enclosing(offset: int) -> str | None:
        inside = [(end - start, item) for item, start, end in spans if start <= offset < end]
        return min(inside)[1] if inside else None

    def line_of(offset: int) -> int:
        return code.count("\n", 0, offset) + 1

    for match in NO_PROOF_CERTS_WORD.finditer(code):
        problems.append(f"line {line_of(match.start())}: spells {match.group(0)!r}; a module never turns proof "
                        "certificates off (a fixture passes the knob to backend_knobs_arg itself)")
    for match in RAW_KNOB_OPTION.finditer(code):
        item = enclosing(match.start())
        if item not in owners:
            where = f"fn/item {item}" if item else "no owner item"
            problems.append(f"line {line_of(match.start())}: spells the backend knob option ({match.group(0)!r}) "
                            f"in {where}; only {sorted(owners) or 'no item of this module'} may, and a knob "
                            "argument must come from toolchain_support::backend_knobs_arg, whose trace the "
                            "runner checks")
    return problems


def fixture_module_problems(tests_dir: Path, targets: Sequence[Target]) -> list[str]:
    """Follow every module each required fixture compiles in and check its knob use."""
    problems, users, seen = [], {}, {}
    root = tests_dir.resolve()
    for target in targets:
        fixture = tests_dir / f"{target.name}.rs"
        if not fixture.is_file():
            continue
        queue, visited = [fixture], {fixture.resolve()}
        while queue:
            path = queue.pop(0)
            try:
                text = path.read_text(encoding="utf-8", errors="replace")
            except OSError as error:
                problems.append(f"{target.name}: cannot read {path}: {error}")
                continue
            children, unresolved = module_children(path, text)
            label = path.name if path == fixture else path
            problems.extend(f"{target.name}: {label}: {problem}" for problem in unresolved)
            for child in children:
                if not child.is_file():
                    problems.append(f"{target.name}: {label} compiles in {child}, which is not a file")
                    continue
                resolved = child.resolve()
                if resolved in visited:
                    continue
                visited.add(resolved)
                queue.append(child)
                seen[resolved] = child
                users.setdefault(resolved, []).append(target.name)
    for resolved in sorted(users):
        try:
            relative = resolved.relative_to(root).as_posix()
        except ValueError:
            relative = str(resolved)
        text = seen[resolved].read_text(encoding="utf-8", errors="replace")
        for problem in module_knob_problems(relative, text):
            problems.append(f"{relative} (compiled into {', '.join(users[resolved])}): {problem}")
    return problems


def inventory_problems(tests_dir: Path = TESTS_DIR, named_refusals: dict | None = None) -> list[str]:
    """Check the required inventory against the fixture sources."""
    named_refusals = NAMED_REFUSALS if named_refusals is None else named_refusals
    problems = []
    names = [target.name for target in TARGETS]
    if len(set(names)) != len(names):
        problems.append("duplicate required target")
    for target in TARGETS:
        path = tests_dir / f"{target.name}.rs"
        if target.kind not in KINDS:
            problems.append(f"{target.name}: unknown kind {target.kind!r}")
        if type(target.minimum) is not int or target.minimum < 1:
            problems.append(f"{target.name}: minimum must be a positive integer")
        if not all(isinstance(marker, str) and marker for marker in target.markers):
            problems.append(f"{target.name}: execution markers must be nonempty strings")
        problems.extend(f"{target.name}: {problem}" for problem in evidence_profile_problems(target))
        if not path.is_file():
            problems.append(f"{target.name}: missing test file {path}")
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        defined = len(TEST_ATTRIBUTE.findall(text))
        if type(target.minimum) is int and defined != target.minimum:
            problems.append(f"{target.name}: minimum {target.minimum} differs from its {defined} #[test] functions")
        if IGNORE_ATTRIBUTE.search(text):
            problems.append(f"{target.name}: an #[ignore] test can never execute in this runner")
        if POSITIVE_EVIDENCE_MODULE not in text:
            problems.append(f"{target.name}: required fixture does not include {POSITIVE_EVIDENCE_MODULE}, "
                            "so no test of it can be credited")
        # A host-target oracle compiles for whatever host runs it; every other
        # required fixture is Darwin AArch64 specific.
        if target.kind != HOST_ORACLE and HOST not in text:
            problems.append(f"{target.name}: required fixture no longer names {HOST}")
        problems.extend(f"{target.name}: {problem}" for problem in certificate_knob_problems(target, text))
    problems.extend(fixture_module_problems(tests_dir, TARGETS))
    classified = set(names)
    for table, label in ((NOT_COVERED, "not-covered"), (OUT_OF_SCOPE, "out-of-scope")):
        for name, reason in table.items():
            if not reason or not (tests_dir / f"{name}.rs").is_file():
                problems.append(f"{name}: {label} entry needs a reason and an existing test file")
            if name in classified:
                problems.append(f"{name}: classified more than once")
            classified.add(name)
    for path in sorted(tests_dir.glob("*.rs")):
        text = path.read_text(encoding="utf-8", errors="replace")
        if (DARWIN_TRIPLE in text or AARCH64_MACOS_GATE.search(text)) and path.stem not in classified:
            problems.append(f"{path.stem}: names {HOST} or gates on aarch64 macOS but is unclassified")
    for name, entry in named_refusals.items():
        if name not in names:
            problems.append(f"{name}: named refusal is not a required target")
            continue
        markers = entry.get("markers") if isinstance(entry, dict) else None
        if (not isinstance(entry, dict) or not entry.get("gap") or not entry.get("reason")
                or not isinstance(markers, (list, tuple)) or not markers):
            problems.append(f"{name}: named refusal needs a ledger gap, a reason and exact markers")
            continue
        for marker in markers:
            try:
                re.compile(marker)
            except (re.error, TypeError):
                problems.append(f"{name}: named-refusal marker {marker!r} is not a regular expression")
    return problems


def preflight(target_dir: Path, driver: str | None = None, environment: dict | None = None) -> dict:
    """Refuse, with named findings, every environment that cannot qualify the bridge."""
    environment = dict(os.environ if environment is None else environment)
    require_darwin_host()
    findings = ambient_findings(environment)
    record = None
    try:
        TOOLCHAIN.require_trust_pin(PIN)
    except TOOLCHAIN.ToolchainError as error:
        findings.append((PIN_NOT_TRUST, str(error)))
    else:
        try:
            record = TOOLCHAIN.resolve(driver, pin=PIN, path=environment.get("PATH"))
        except TOOLCHAIN.ToolchainError as error:
            code = RUSTC_DEV_ABSENT if "private crate missing" in str(error) else TOOLCHAIN_UNRESOLVED
            findings.append((code, str(error)))
    rustup_trust = None
    required = required_private_crates()
    if record is not None:
        if record["host"] != HOST:
            findings.append((HOST_REFUSED, f"resolved Trust compiler host is {record['host']}, not {HOST}"))
        target_lib = Path(record["sysroot"]) / "lib" / "rustlib" / HOST / "lib"
        missing = missing_private_crates(target_lib, required)
        if missing:
            findings.append((RUSTC_DEV_ABSENT,
                             f"the Trust package ships no rustc-dev metadata for {missing} in {target_lib}; "
                             "the backend cannot be built against it (X-HOST-P12)"))
        if not any(path.is_file() for path in target_lib.glob("libstd-*.rlib")):
            findings.append((RUST_STD_ABSENT, f"the Trust package has no {HOST} rust-std in {target_lib}"))
        try:
            listing = probe([record["compiler"], "-Zhelp"], probe_environment(environment))
        except RuntimeError as error:
            findings.append((KNOBS_ABSENT, f"cannot list the compiler's -Z options: {error}"))
        else:
            if f"{KNOB_OPTION}=" not in listing:
                findings.append((KNOBS_ABSENT,
                                 f"{record['compiler']} does not list -Z{KNOB_OPTION}; the fixtures' "
                                 "backend knobs cannot be expressed and they would skip"))
        rustup_trust, divergence = trust_link_findings(record, environment)
        findings.extend(divergence)
    tools, tool_findings = host_tool_identities(environment)
    findings.extend(tool_findings)
    cargo_configs, config_findings = cargo_config_findings(environment)
    findings.extend(config_findings)
    problems = inventory_problems()
    if problems:
        findings.append((INVENTORY_INCONSISTENT, "; ".join(problems)))
    if target_dir == ROOT or target_dir in ROOT.parents:
        findings.append((TARGET_DIR_REFUSED, "backend target directory must not be the source root or its ancestor"))
    if findings:
        raise GateError(findings)
    return {
        **current_source(tools["git"]["path"]), "host": HOST, "machine": platform.machine(),
        "toolchain": record, "requested_driver": driver, "rustup_trust": rustup_trust,
        "toolchain_sha256": {
            name: DARWIN.file_sha256(Path(record[key]))
            for name, key in (("trustc", "compiler"), ("targo", "targo"))
        },
        "backend_knobs_option": f"-Z{KNOB_OPTION}", "private_crates": list(required),
        "lane": "unverified: targo --unverified builds, -Ztrust-verify=off fixture compiles",
        "tools": tools, "cargo_configs": cargo_configs,
        "target_dir": str(target_dir), "manifest": str(MANIFEST),
        "configuration": {name: environment[name] for name in RECORDED_CONFIGURATION if name in environment},
    }


def backend_stat(info: os.stat_result) -> dict:
    return {
        "device": info.st_dev, "inode": info.st_ino, "mode": info.st_mode,
        "links": info.st_nlink, "size": info.st_size,
        "modified_ns": info.st_mtime_ns, "changed_ns": info.st_ctime_ns,
    }


def backend_identity(path: Path) -> dict:
    """Hash a regular file without following a replacement symlink or FIFO."""
    before = path.lstat()
    if not stat.S_ISREG(before.st_mode):
        raise RuntimeError(f"artifact must be a regular file, not a symlink: {path}")
    digest = hashlib.sha256()
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK), "rb") as source:
        if backend_stat(before) != backend_stat(os.fstat(source.fileno())):
            raise RuntimeError(f"artifact changed while opening: {path}")
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
        if backend_stat(before) != backend_stat(os.fstat(source.fileno())):
            raise RuntimeError(f"artifact changed while hashing: {path}")
    after = path.lstat()
    if backend_stat(before) != backend_stat(after) or before.st_size == 0:
        raise RuntimeError(f"artifact is empty or changed while hashing: {path}")
    return {"path": str(path), "sha256": digest.hexdigest(), "size": before.st_size, "stat": backend_stat(before)}


def snapshot_backend(source: Path, destination: Path, expected: dict, mode: int = 0o444,
                     what: str = "built backend") -> dict:
    """Copy the identified build artifact into a new, read-only, independent file.

    `mode` is the copy's permission bits: 0o444 for the backend, 0o555 for a
    test executable, which must stay runnable. `what` names the artifact in
    refusals.
    """
    before = source.lstat()
    if expected["path"] != str(source) or backend_stat(before) != expected["stat"]:
        raise refuse(BACKEND_CHANGED, f"{what} changed before snapshot creation")
    digest = hashlib.sha256()
    size = 0
    with os.fdopen(os.open(source, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK), "rb") as reader:
        if backend_stat(os.fstat(reader.fileno())) != expected["stat"]:
            raise refuse(BACKEND_CHANGED, f"{what} changed while opening the snapshot source")
        with destination.open("xb") as writer:
            copied = os.fstat(writer.fileno())
            if (not stat.S_ISREG(copied.st_mode) or copied.st_nlink != 1
                    or (copied.st_dev, copied.st_ino) == (before.st_dev, before.st_ino)):
                raise RuntimeError(f"{what} snapshot must be a new independent regular file")
            for chunk in iter(lambda: reader.read(1024 * 1024), b""):
                writer.write(chunk)
                digest.update(chunk)
                size += len(chunk)
            writer.flush()
            os.fchmod(writer.fileno(), mode)
            os.fsync(writer.fileno())
        if backend_stat(os.fstat(reader.fileno())) != expected["stat"]:
            raise refuse(BACKEND_CHANGED, f"{what} changed during snapshot copy")
    if digest.hexdigest() != expected["sha256"] or size != expected["size"]:
        raise refuse(BACKEND_CHANGED, f"{what} snapshot bytes do not match the identified build")
    if backend_identity(source) != expected:
        raise refuse(BACKEND_CHANGED, f"{what} changed during snapshot creation")
    observed = backend_identity(destination)
    if (observed["sha256"] != expected["sha256"] or observed["size"] != expected["size"]
            or observed["stat"]["mode"] != (stat.S_IFREG | mode) or observed["stat"]["links"] != 1):
        raise refuse(BACKEND_CHANGED, f"{what} snapshot identity changed after copying")
    return observed


def cargo_records(transcript: str) -> list[dict]:
    records = []
    for line in transcript.splitlines():
        if not line.startswith("{"):
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            records.append(value)
    return records


def classify_build(returncode: int, transcript: str, backend: Path) -> dict:
    records = cargo_records(transcript)
    finished = [row for row in records if row.get("reason") == "build-finished"]
    artifacts = [
        row for row in records
        if row.get("reason") == "compiler-artifact" and row.get("manifest_path") == str(MANIFEST)
        and isinstance(row.get("target"), dict) and row["target"].get("name") == PACKAGE_TARGET
        and row["target"].get("kind") == ["dylib"]
    ]
    errors = []
    if returncode != 0:
        errors.append(f"release backend build exited {returncode}")
    if len(finished) != 1 or finished[0].get("success") is not True:
        errors.append("expected exactly one successful Cargo build-finished record")
    if len(artifacts) != 1 or artifacts[0].get("filenames") != [str(backend)]:
        errors.append("Cargo did not identify exactly the required release backend artifact")
    return {"status": "fail" if errors else "pass", "errors": errors,
            "cargo_artifact": artifacts[0] if len(artifacts) == 1 else None}


def classify_test_build(returncode: int, transcript: str, target_dir: Path,
                        names: Sequence[str]) -> dict:
    """Select exactly one release test executable per required target."""
    records = cargo_records(transcript)
    finished = [row for row in records if row.get("reason") == "build-finished"]
    errors = []
    if returncode != 0:
        errors.append(f"test build exited {returncode}")
    if len(finished) != 1 or finished[0].get("success") is not True:
        errors.append("expected exactly one successful Cargo test build-finished record")
    executables = {}
    for name in names:
        artifacts = [
            row for row in records
            if row.get("reason") == "compiler-artifact" and row.get("manifest_path") == str(MANIFEST)
            and isinstance(row.get("target"), dict) and row["target"].get("name") == name
            and row["target"].get("kind") == ["test"]
            and isinstance(row.get("profile"), dict) and row["profile"].get("test") is True
        ]
        if len(artifacts) != 1:
            errors.append(f"Cargo did not identify exactly one test executable for {name}")
            continue
        artifact = artifacts[0]
        executable = artifact.get("executable")
        path = Path(executable) if isinstance(executable, str) and executable else None
        # Cargo binds the package and source, not just a target with the same
        # name. Require the actual release profile before inspecting its bytes.
        package_prefix = "path+" + BRIDGE_DIR.as_uri() + "#" + PACKAGE_TARGET + "@"
        package = artifact.get("package_id")
        profile = artifact["profile"]
        identity_ok = (
            isinstance(package, str) and package.startswith(package_prefix)
            and re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+(?:[-+][0-9A-Za-z.+-]+)?",
                             package[len(package_prefix):]) is not None
            and artifact["target"].get("src_path") == str(TESTS_DIR / (name + ".rs"))
            and profile.get("opt_level") == "3" and profile.get("debuginfo") == 0
            and profile.get("debug_assertions") is False
            and profile.get("overflow_checks") is False
        )
        # Standard Cargo and Trust's package/unit layout both carry a 16-hex
        # unit suffix. In the latter, the directory and executable must agree.
        unit = None
        if path is not None and path.name.startswith(name + "-"):
            unit = path.name[len(name) + 1:]
        layout_ok = bool(unit and re.fullmatch(r"[0-9a-f]{16}", unit) and (
            path.parent == target_dir / "release" / "deps"
            or path.parent == target_dir / "release" / "build" / PACKAGE_TARGET / unit / "out"
        ))
        try:
            canonical = bool(identity_ok and layout_ok and path.is_absolute()
                             and path.resolve(strict=True) == path)
        except (OSError, RuntimeError):
            canonical = False
        if (not identity_ok or not layout_ok or not canonical
                or artifact.get("filenames") != [executable] or not os.access(path, os.X_OK)):
            errors.append(f"{name}: test executable is not the required release artifact")
            continue
        try:
            executables[name] = backend_identity(path)
        except (OSError, RuntimeError) as error:
            errors.append(f"{name}: {error}")
    return {"status": "fail" if errors else "pass", "errors": errors, "executables": executables}


def split_make_words(line: str) -> list[str]:
    """Split one Makefile dep-info line; Cargo escapes spaces in paths as '\\ '."""
    words, current, index = [], [], 0
    while index < len(line):
        char = line[index]
        if char == "\\" and index + 1 < len(line) and line[index + 1] == " ":
            current.append(" ")
            index += 2
            continue
        if char in " \t":
            if current:
                words.append("".join(current))
                current = []
        else:
            current.append(char)
        index += 1
    if current:
        words.append("".join(current))
    return words


def dep_info_sources(text: str, artifact: Path) -> list[Path]:
    """Return the dependencies of every dep-info rule whose target is artifact."""
    wanted = artifact.resolve()
    sources, matched = [], False
    for line in text.replace("\\\n", " ").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        words = split_make_words(line)
        for index, word in enumerate(words):
            if word.endswith(":"):
                targets = [*words[:index], word[:-1]]
                if any(target and Path(target).resolve() == wanted for target in targets):
                    matched = True
                    sources.extend(Path(dependency) for dependency in words[index + 1:])
                break
    if not matched:
        raise ValueError(f"dep-info has no rule for {artifact}")
    return sources


def backend_staleness(backend: Path, dep_info: Path) -> dict:
    """Compare the backend's mtime with every local source Cargo recorded for it."""
    record = {"backend": str(backend), "dep_info": str(dep_info), "stale": True, "errors": []}
    try:
        text = dep_info.read_text(encoding="utf-8", errors="replace")
        record["dep_info_sha256"] = hashlib.sha256(text.encode("utf-8")).hexdigest()
        sources = dep_info_sources(text, backend)
        backend_mtime = backend.lstat().st_mtime_ns
    except (OSError, ValueError) as error:
        record["code"] = STALENESS_UNDECIDABLE
        record["errors"].append(f"backend staleness cannot be decided: {error}")
        return record
    record["backend_mtime_ns"] = backend_mtime
    record["sources"] = len(sources)
    lib_rs = (BRIDGE_DIR / "src" / "lib.rs").resolve()
    if not sources or lib_rs not in {source.resolve() for source in sources}:
        record["code"] = STALENESS_UNDECIDABLE
        record["errors"].append(f"dep-info {dep_info} does not list the bridge's src/lib.rs")
        return record
    newer, missing, newest = [], [], None
    for source in sources:
        try:
            modified = source.stat().st_mtime_ns
        except OSError:
            missing.append(str(source))
            continue
        if newest is None or modified > newest[0]:
            newest = (modified, str(source))
        if modified > backend_mtime:
            newer.append(str(source))
    record.update({
        "newest_source": newest[1] if newest else None,
        "newest_source_mtime_ns": newest[0] if newest else None,
        "newer_source_count": len(newer), "newer_sources": newer[:20],
        "missing_source_count": len(missing), "missing_sources": missing[:20],
    })
    if newer or missing:
        record["code"] = STALE_BACKEND
        record["errors"].append(
            f"backend {backend} is older than {len(newer)} of its sources and {len(missing)} listed "
            f"sources are missing (first: {(newer + missing)[0]}); refusing to test a stale backend"
        )
        return record
    record["stale"] = False
    return record


def exempt_diagnostic(line: str) -> str | None:
    """The DIAGNOSTIC_EXEMPTIONS name the whole line fullmatches, or None."""
    for name, pattern in DIAGNOSTIC_EXEMPTIONS.items():
        if pattern.fullmatch(line):
            return name
    return None


def attribute_output(transcript: str) -> dict:
    """Attribute refusal lines, positive-evidence markers and TCG codes to the
    libtest test whose captured output holds them."""
    refusals, markers, codes, knobs = {}, {}, {}, {}
    unattributed, stray_markers, malformed_markers, stray_knobs = [], [], [], []
    native_summaries = []
    passed, failed = set(), set()
    exempted = collections.Counter()
    owner = None
    for raw in transcript.splitlines():
        line = raw.strip()
        header = MATRIX.STDOUT_HEADER.fullmatch(line)
        if header:
            owner = header[1]
            continue
        result = MATRIX.TEST_RESULT.fullmatch(line)
        if owner is None and result:
            if result[2] == "ok":
                passed.add(result[1])
            elif result[2] == "FAILED":
                failed.add(result[1])
            continue
        if line in ("successes:", "failures:") or MATRIX.ROLLUP.fullmatch(line):
            owner = None
            continue
        if owner is not None:
            codes.setdefault(owner, set()).update(TCG_CODE.findall(line))
        if line.startswith(STRICT_NATIVE_PREFIXES):
            native_summaries.append((owner, line))
        if POSITIVE_MARKER in line:
            marker = POSITIVE_LINE.fullmatch(line)
            if marker is None:
                malformed_markers.append(line)
            elif owner is None:
                stray_markers.append(line)
            else:
                markers.setdefault(owner, []).append(
                    {"kind": marker[1], "certs": marker[2], "test": marker[3]})
            continue
        if KNOB_TRACE in line:
            trace = KNOB_TRACE_LINE.fullmatch(line)
            if trace is None:
                malformed_markers.append(line)
            elif owner is None:
                stray_knobs.append(line)
            else:
                knobs.setdefault(owner, []).append(trace[1].split())
            continue
        if REFUSAL_LINE.search(line) or MATRIX.SKIP.match(raw):
            exemption = exempt_diagnostic(line)
            if exemption is not None:
                exempted[exemption] += 1
            elif owner is None:
                unattributed.append(line)
            else:
                lines = refusals.setdefault(owner, [])
                if line not in lines:
                    lines.append(line)
    return {
        "refusals": refusals, "unattributed": unattributed, "passed": passed, "failed": failed,
        "markers": markers, "stray_markers": stray_markers, "malformed_markers": malformed_markers,
        "knobs": knobs, "stray_knobs": stray_knobs,
        "native_summaries": native_summaries,
        "codes": {test: sorted(found) for test, found in codes.items()}, "exempted": dict(exempted),
    }


def disables_proof_certificates(knobs: Sequence[str]) -> bool:
    """Whether one traced knob list turns the backend's proof certificates off."""
    for item in knobs:
        key, separator, value = item.partition("=")
        if key == NO_PROOF_CERTS_KEY and (not separator or value.strip() not in BOOLEAN_OFF_VALUES):
            return True
    return False


def traced_certificates(traces: Sequence[Sequence[str]]) -> str:
    """The certificate state a test's knob traces establish: off, on, or none."""
    if any(disables_proof_certificates(knobs) for knobs in traces):
        return "off"
    return "on" if traces else "none"


def certificate_label_error(test: str, certs: str, traces: Sequence[Sequence[str]]) -> str | None:
    """Compare a marker's self-reported certs= with the knob arguments the test built.

    certs=off needs a traced no-proof-certs argument; certs=on and certs=none
    must have none, and certs=none (no backend compile) no knob argument at all.
    """
    traced = traced_certificates(traces)
    if certs == "off" and traced != "off":
        return (f"{test}: its marker says certs=off but it built no {NO_PROOF_CERTS_KEY} knob argument "
                f"({KNOB_TRACE} traces: {[' '.join(knobs) for knobs in traces]})")
    if certs in ("on", "none") and traced == "off":
        return (f"{test}: its marker says certs={certs} but it built a {NO_PROOF_CERTS_KEY} knob argument, "
                "so it compiled with proof certificates off")
    if certs == "none" and traces:
        return f"{test}: its marker says certs=none (no backend compile) but it built backend knob arguments"
    return None


def positive_evidence(target: Target, attributed: dict) -> tuple[dict, list[str]]:
    """Each test's one credited (kind, certs) marker, and the marker errors.

    A marker's certs= is checked against the knob arguments the test itself
    built (KNOB_TRACE), never taken on the test's word.
    """
    allowed = ALLOWED_EVIDENCE[target.kind]
    errors = [f"positive-evidence marker outside any test's captured output: {line}"
              for line in attributed["stray_markers"]]
    errors += [f"malformed positive-evidence marker or knob trace: {line}"
               for line in attributed["malformed_markers"]]
    errors += [f"backend knob trace outside any test's captured output: {line}"
               for line in attributed["stray_knobs"]]
    evidence = {}
    for test, entries in sorted(attributed["markers"].items()):
        valid = True
        for entry in entries:
            if entry["test"] != test:
                errors.append(f"{test}: its output carries a positive-evidence marker naming {entry['test']}")
                valid = False
            elif entry["kind"] not in allowed:
                errors.append(f"{test}: evidence kind {entry['kind']!r} is not credited for a "
                              f"{target.kind} target")
                valid = False
            elif entry["certs"] not in CERTS:
                errors.append(f"{test}: unknown certificate state {entry['certs']!r}")
                valid = False
        pairs = {(entry["kind"], entry["certs"]) for entry in entries}
        if valid and len(pairs) != 1:
            errors.append(f"{test}: conflicting positive-evidence markers {sorted(pairs)}")
            valid = False
        if valid:
            kind, certs = pairs.pop()
            mismatch = certificate_label_error(test, certs, attributed["knobs"].get(test, []))
            if mismatch is not None:
                errors.append(mismatch)
                continue
            evidence[test] = {"kind": kind, "certs": certs}
    return evidence, errors


def proof_certificate_opt_outs(tests_dir: Path = TESTS_DIR) -> list[str]:
    """Required targets whose fixture source passes the no-proof-certs knob."""
    names = []
    for target in TARGETS:
        try:
            text = (tests_dir / f"{target.name}.rs").read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if NO_PROOF_CERTS_KNOB in text:
            names.append(target.name)
    return names


def corpus_floor(path: Path = CORPUS_FLOOR) -> float:
    values = CORPUS_FLOOR_LINE.findall(path.read_text(encoding="utf-8"))
    if len(values) != 1:
        raise ValueError(f"{path} must contain exactly one a64_compile_floor_percent line")
    return float(values[0])


def corpus_verdict(transcript: str, floor_path: Path = CORPUS_FLOOR) -> tuple[dict | None, list[str]]:
    """Check the corpus's compile-verdict summary; it is never execution evidence."""
    lines = [line.strip() for line in transcript.splitlines()]
    summaries = [match for match in map(CORPUS_SUMMARY.fullmatch, lines) if match]
    rows = [match for match in map(CORPUS_ROW.fullmatch, lines) if match]
    if len(summaries) != 1:
        return None, ["expected exactly one '[a64 corpus row] N/M rows COMPILED' verdict summary"]
    compiled, total, printed, incomplete, hard = summaries[0].groups()
    compiled, total, incomplete, hard = int(compiled), int(total), int(incomplete), int(hard)
    errors = []
    outcomes = collections.Counter(match[2] for match in rows)
    names = [match[1] for match in rows]
    if total <= 0 or compiled + incomplete + hard != total:
        errors.append("corpus verdict counts do not add up to a nonempty row total")
    if hard:
        errors.append(f"corpus reported {hard} hard errors")
    if (len(rows) != total or len(set(names)) != total or outcomes["COMPILED"] != compiled
            or outcomes["INCOMPLETE"] != incomplete or outcomes["HARD ERROR"] != hard):
        errors.append("corpus row verdicts disagree with the summary")
    coverage = 100.0 * compiled / total if total > 0 else 0.0
    if total > 0 and f"{coverage:.1f}" != printed:
        errors.append("corpus coverage percentage disagrees with its row counts")
    try:
        floor = corpus_floor(floor_path)
    except (OSError, ValueError) as error:
        floor = None
        errors.append(f"corpus floor unreadable: {error}")
    if floor is not None and coverage < floor:
        errors.append(f"corpus coverage {coverage:.1f}% is below the committed floor {floor}%")
    return {
        "label": COMPILE_VERDICT_LABEL, "compiled": compiled, "total": total,
        "incomplete": incomplete, "hard_errors": hard, "coverage_percent": round(coverage, 1),
        "floor_percent": floor, "rows": dict(sorted((match[1], match[2]) for match in rows)),
    }, errors


def guarded_trap_profile(target: Target, transcript: str, credited_evidence: dict) -> tuple[dict, dict | None, list[str]]:
    """Bind the heap-drop test's evidence to all four recorded row outcomes.

    The two -O0 rows must have run natively (heap_image_glue lowers the
    vtable's drop glue there); the two -O2 rows may refuse or match.
    """
    required = dict(sorted(target.evidence))
    if target.name != "executable_trap_stub_routes_aarch64":
        return required, None, []
    expression = re.compile(
        r"^EXECUTABLE_TRAP_STUB_DYN rows=4 llvm_native=4 cg_native=(\d+) cg_refused=(\d+)$",
        re.MULTILINE,
    )
    rows = expression.findall(transcript)
    errors = []
    if len(rows) != 1:
        return required, None, ["expected exactly one complete four-row dyn-heap outcome marker"]
    native, refused = map(int, rows[0])
    record = {"rows": 4, "llvm_native": 4, "cg_native": native, "cg_refused": refused}
    if native + refused != 4 or native > 4 or refused > 4:
        errors.append("dyn-heap CG native/refusal counts must partition all four rows")
    if native < 2:
        errors.append("both -O0 dyn-heap rows must run natively (heap_image_glue lowers their drop glue)")
    kind = NATIVE_RUN if native else EXPECTED_REFUSAL
    test = "dyn_heap_glue_drop_fails_closed_aarch64"
    if credited_evidence.get(test, {}).get("kind") != kind:
        errors.append("dyn-heap positive evidence does not match its actual native/refusal outcomes")
    return required, record, errors


def strict_native_summary_errors(target: Target, attributed: dict) -> list[str]:
    """The two new native profiles require one complete, test-owned ledger.

    This is execution bookkeeping, not proof authority. In particular, a
    cached-key expected-refusal marker cannot substitute for four native runs.
    Other target ledgers retain their existing checks and evidence profiles.
    """
    test = STRICT_NATIVE_TESTS.get(target.name)
    if test is None:
        return []
    if len(target.markers) != 1:
        return ["strict native row requires exactly one complete summary contract"]
    expected = target.markers[0]
    prefix = expected.split(" ", 1)[0]
    summaries = [(owner, line) for owner, line in attributed["native_summaries"]
                 if line.startswith(prefix + " ")]
    if len(summaries) != 1:
        return [f"expected exactly one complete native summary for {test}, observed {len(summaries)}"]
    owner, line = summaries[0]
    errors = []
    if owner != test:
        errors.append(f"native summary for {test} is outside its own captured output")
    if re.fullmatch(re.escape(expected) + r" artifacts=/[^\r\n]+", line) is None:
        errors.append(f"native summary for {test} differs from its exact required cells/outcomes: {line}")
    return errors


def classify_target(target: Target, returncode: int, transcript: str,
                    named_refusals: dict | None = None, floor_path: Path = CORPUS_FLOOR) -> dict:
    """Classify one target: pass, an allowlisted named refusal, or fail."""
    named_refusals = NAMED_REFUSALS if named_refusals is None else named_refusals
    parsed = MATRIX.parse_log(transcript.splitlines(), mode="plain", rc=returncode, capture_available=True)
    structural = []
    if returncode != 0:
        structural.append(f"command exited {returncode}")
    if parsed["timeout_detected"]:
        structural.append("timeout detected")
    structural.extend(f"transcript problem: {problem}" for problem in parsed["parse_problems"])
    if parsed["suites"] != 1 or parsed["incomplete_suites"]:
        structural.append("expected exactly one started and completed test suite")
    if parsed["failed"] or parsed["ignored"] or parsed["filtered"]:
        structural.append("failed, ignored or filtered tests are not permitted")
    attributed = attribute_output(transcript)
    by_test, unattributed, ok_tests = attributed["refusals"], attributed["unattributed"], attributed["passed"]
    for detail in parsed["runtime_skip_details"]:
        lines = by_test.setdefault(detail["test"], [])
        lines.extend(message for message in detail["messages"] if message not in lines)
    credited_evidence, marker_errors = positive_evidence(target, attributed)
    # A TCG-PROOF-465 line without a skip word is data, not an early return, in
    # a test whose credited claim is itself a refusal or a refusal census.
    for test in list(by_test):
        if credited_evidence.get(test, {}).get("kind") in REFUSAL_BEARING_EVIDENCE:
            kept = [line for line in by_test[test] if SKIP_WORD.search(line) or MATRIX.SKIP.match(line)]
            if kept:
                by_test[test] = kept
            else:
                del by_test[test]
    refusal_lines = list(dict.fromkeys([*unattributed, *(line for lines in by_test.values() for line in lines)]))
    credited = {test for test in ok_tests if test in credited_evidence and test not in by_test}
    # A passed test with no marker at all; a rejected marker is its own error.
    unevidenced = sorted(test for test in ok_tests
                         if test not in credited_evidence and test not in attributed["markers"])
    executed = len(credited)
    evidence = list(marker_errors)
    evidence.extend(strict_native_summary_errors(target, attributed))
    if unevidenced:
        evidence.append(f"passed without a positive-evidence marker (an early return is "
                        f"indistinguishable from a pass): {unevidenced}")
    if executed < target.minimum:
        evidence.append(f"executed passes {executed} are below the required minimum {target.minimum}")
    for marker in target.markers:
        if marker not in transcript:
            evidence.append(f"required execution marker missing: {marker}")
    evidence_counts = dict(sorted(collections.Counter(
        credited_evidence[test]["kind"] for test in credited).items()))
    certs_counts = dict(sorted(collections.Counter(
        credited_evidence[test]["certs"] for test in credited).items()))
    required_evidence, guarded_execution, guarded_errors = guarded_trap_profile(
        target, transcript, credited_evidence,
    )
    evidence.extend(guarded_errors)
    if executed == target.minimum:
        # A complete pass must show the declared evidence profile: a test that
        # weakened from a native run to a compile, or to proofs off (its
        # certs=off marker checked against its own knob trace), fails.
        if evidence_counts != required_evidence:
            evidence.append(f"evidence profile {evidence_counts} differs from the required "
                            f"{required_evidence}")
        if certs_counts.get("off", 0) != target.certs_off:
            evidence.append(f"{certs_counts.get('off', 0)} proofs-off (certs=off) tests differ from the "
                            f"required {target.certs_off}")
    verdict = None
    if target.kind == COMPILE_VERDICT:
        verdict, verdict_errors = corpus_verdict(transcript, floor_path)
        evidence.extend(verdict_errors)
    counts = {key: parsed[key] for key in (
        "passed", "libtest_passed", "unclassified_passes", "failed", "ignored", "filtered",
        "runtime_skipped", "suites", "incomplete_suites",
    )}
    counts["executed"] = executed
    result = {
        "kind": target.kind, "minimum": target.minimum, "counts": counts,
        "matrix_status": parsed["status"], "timeout_detected": parsed["timeout_detected"],
        "refusal_lines": refusal_lines, "refused_tests": sorted(by_test),
        "compile_verdict": verdict, "named_refusal": None,
        "positive_evidence": {test: credited_evidence[test] for test in sorted(credited)},
        "evidence_counts": evidence_counts, "certs_counts": certs_counts,
        "required_evidence": required_evidence, "guarded_execution": guarded_execution,
        "required_certs_off": target.certs_off,
        "certs_off_tests": sorted(test for test in credited if credited_evidence[test]["certs"] == "off"),
        "backend_knob_traces": {test: sorted({" ".join(knobs) for knobs in traces})
                                for test, traces in sorted(attributed["knobs"].items())},
        "unevidenced_passes": unevidenced,
        "failed_tests": {test: attributed["codes"].get(test, []) for test in sorted(attributed["failed"])},
        "exempted_diagnostics": attributed["exempted"],
    }
    if not structural and not refusal_lines and not evidence:
        result.update(status="pass", errors=[])
        return result
    entry = named_refusals.get(target.name)
    allowlisted = (
        entry is not None and refusal_lines and not structural
        and all(any(re.fullmatch(marker, line) for marker in entry["markers"]) for line in refusal_lines)
    )
    if allowlisted:
        result.update(status="named-refusal", errors=[], counts={**counts, "executed": 0},
                      named_refusal={"gap": entry["gap"], "reason": entry["reason"],
                                     "lines": refusal_lines, "unmet_evidence": evidence})
        return result
    errors = structural + [f"refusal or early return: {line}" for line in refusal_lines] + evidence
    result.update(status="fail", errors=errors)
    return result


def runtime_entries(runtime_target: Path) -> list[str]:
    entries = []
    for directory, subdirectories, files in os.walk(runtime_target):
        for name in [*subdirectories, *files]:
            entries.append(str((Path(directory) / name).relative_to(runtime_target)))
    return sorted(entries)


def build_environment(base: dict, target_dir: Path, compiler: str) -> dict:
    environment = dict(base)
    environment.pop("CARGO_BUILD_TARGET_DIR", None)
    environment.update(CARGO_TARGET_DIR=str(target_dir), RUSTC=compiler, RUSTUP_AUTO_INSTALL="0")
    return environment


def test_environment(base: dict, runtime_target: Path) -> dict:
    """Point Cargo at the runtime target, where a fixture's stray write is detected.

    The fixtures do not read CARGO_TARGET_DIR to find their backend: each loads
    the library beside its own executable, which the runner copies there.
    """
    environment = dict(base)
    environment.pop("CARGO_BUILD_TARGET_DIR", None)
    environment.update(
        CARGO_TARGET_DIR=str(runtime_target), CARGO_MANIFEST_DIR=str(BRIDGE_DIR),
        RUSTUP_AUTO_INSTALL="0",
    )
    # The root Cargo config's [env] default; the executables run without Cargo.
    environment.setdefault("RUST_MIN_STACK", "16777216")
    return environment


def ensure_unchanged_source(report: dict, name: str) -> None:
    observed = current_source(report["provenance"]["tools"]["git"]["path"])
    report[name] = observed
    if observed["source_fingerprint"] != report["provenance"]["source_fingerprint"]:
        raise refuse(SOURCE_CHANGED, f"source changed during bridge qualification ({name})")


def run_step(command: Sequence[str], log: Path, timeout: float, environment: dict) -> dict:
    result = DARWIN.run_target(command, log, timeout, root=BRIDGE_DIR, environment=environment)
    for key in ("counts", "minimum", "matrix_status", "timeout_detected", "status", "errors"):
        result.pop(key, None)
    return result


def list_inventory() -> int:
    for target in TARGETS:
        profile = " ".join(f"{kind}={count}" for kind, count in target.evidence)
        print(f"{target.name} {target.minimum} {target.kind} [{profile} certs-off={target.certs_off}]")
    for name, reason in sorted(NOT_COVERED.items()):
        print(f"# not covered: {name}: {reason}")
    for name, reason in sorted(OUT_OF_SCOPE.items()):
        print(f"# out of scope: {name}: {reason}")
    problems = inventory_problems()
    for problem in problems:
        print(f"{INVENTORY_INCONSISTENT}: {problem}", file=sys.stderr)
    return 1 if problems else 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--list", action="store_true", help="print the required inventory; do not probe or build")
    parser.add_argument("--out", type=Path, help="new report directory outside the source tree; existing paths are rejected")
    parser.add_argument("--target-dir", type=Path, default=DEFAULT_TARGET_DIR,
                        help="dedicated Cargo target directory for the backend and test builds")
    parser.add_argument("--driver", help="explicit package trustc (default: the PATH trustc/targo pair)")
    parser.add_argument("--timeout-seconds", type=positive_seconds, default=3600.0,
                        help="bound for each build and each target process (default: 3600)")
    parser.add_argument("--jobs", type=positive_jobs, default=2, help="Cargo build jobs (default: 2)")
    parser.add_argument("--require-clean", action="store_true", help="refuse to run on a dirty source tree")
    args = parser.parse_args(argv)
    if args.list:
        return list_inventory()
    try:
        if args.out is None:
            output = Path(tempfile.mkdtemp(prefix="trust-cg-darwin-aarch64-bridge-"))
        else:
            output = args.out.absolute()
            if output.resolve().is_relative_to(ROOT):
                raise OSError("report directory must be outside the source tree")
            output.mkdir(mode=0o700)
    except OSError as error:
        print(f"Darwin AArch64 bridge gate: output error: {error}", file=sys.stderr)
        return 1
    proof_opt_outs = proof_certificate_opt_outs()
    report = {
        "schema": SCHEMA,
        "scope": (
            "Darwin AArch64 rustc-bridge native fixtures through the explicit unverified Trust lane; "
            "testing evidence only, not Darwin FnAbi completion, frontend qualification, proof "
            "authority, Trust-verified compilation or self-hosting"
        ),
        "host": HOST, "status": "incomplete",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "options": {"jobs": args.jobs, "timeout_seconds": args.timeout_seconds,
                    "require_clean": args.require_clean, "driver": args.driver},
        "required_targets": [
            dict(target._asdict(), markers=list(target.markers), evidence=dict(target.evidence))
            for target in TARGETS
        ],
        "required_minimum_passes": sum(target.minimum for target in TARGETS),
        "positive_evidence_marker": POSITIVE_MARKER,
        "diagnostic_exemptions": {name: pattern.pattern for name, pattern in DIAGNOSTIC_EXEMPTIONS.items()},
        "named_refusal_allowlist": {name: dict(entry) for name, entry in NAMED_REFUSALS.items()},
        "not_covered": dict(sorted(NOT_COVERED.items())),
        "out_of_scope": dict(sorted(OUT_OF_SCOPE.items())),
        "proof_certificates_disabled": proof_opt_outs,
        "not_established": [
            "no Darwin C FnAbi aggregate regression exists (twin of aarch64_c_fnabi_aggregate_linux)",
            "real_program_corpus_a64 is compile-verdict-only; no Darwin corpus execution",
            "fixed_cost_budget_aarch64 bounds counted start-up work (processes, digests); it times nothing",
            "unverified Trust lane; no Trust-verified compilation or self-host claim",
            "fixtures passing the no-proof-certs backend knob compile without proof certificates: "
            + (", ".join(proof_opt_outs) or "none")
            + "; each such test's marker says certs=off and the report lists it",
            "a certs=on pass is a default-lane compile the backend promoted; it is testing "
            "evidence, not a replayed proof or certificate check by this runner",
            "a certs= label is checked against the knob arguments a test BUILT "
            f"({KNOB_TRACE}); an argument built but not passed reads as proofs off",
            "that every knob argument comes from the traced constructor is a source-text scan of the "
            "required fixtures and every module they compile in (KNOB_OPTION_OWNERS); a knob string "
            "assembled at run time is outside it",
            "the runner sees only compiler output a test echoes: a certs=on compile that exits 0 "
            "can still have skipped an unreachable Rust-internal function with TCG-PROOF-465 "
            "(static_data_aarch64's immutable-statics crate asserts that its panic handler is "
            "the only one)",
            "diagnostic exemptions are the two lines ruling OD-06 admits "
            "(docs/decision-record.md): each reports a check run by another route",
        ],
        "targets": [], "findings": [], "errors": [],
    }
    report_path = output / "report.json"
    write_report(report_path, report)
    print(f"Darwin AArch64 bridge logs: {output}", flush=True)
    base_environment = dict(os.environ)
    try:
        target_dir = args.target_dir.resolve()
        report["provenance"] = preflight(target_dir, args.driver, base_environment)
        provenance = report["provenance"]
        write_report(report_path, report)
        if args.require_clean and provenance["dirty"]:
            raise refuse(DIRTY_TREE, "source tree is dirty; --require-clean refuses to run")
        toolchain = provenance["toolchain"]
        backend = target_dir / "release" / BACKEND_NAME
        environment = build_environment(base_environment, target_dir, toolchain["compiler"])
        cargo = [toolchain["targo"], "--unverified"]
        common = ["--manifest-path", str(MANIFEST), "--target-dir", str(target_dir), "--release",
                  "--locked", "--color", "never", "-j", str(args.jobs),
                  "--message-format=json-render-diagnostics"]
        report["backend_before_build"] = backend_identity(backend) if backend.exists() else None
        write_report(report_path, report)
        print("Building the current release backend with targo --unverified", flush=True)
        build_log = output / "build.log"
        build = run_step([*cargo, "build", *common], build_log, args.timeout_seconds, environment)
        build.update(classify_build(build["returncode"], build_log.read_text(errors="replace"), backend))
        if build["interrupted_signal"] is not None:
            build["status"] = "fail"
            build["errors"].append(f"build interrupted by signal {build['interrupted_signal']}")
        report["build"] = build
        ensure_unchanged_source(report, "source_after_build")
        write_report(report_path, report)
        if build["status"] != "pass":
            raise refuse(BUILD_FAILED, "required current-source backend build failed; a preexisting "
                                       "library is never reused: " + "; ".join(build["errors"]))
        report["backend_after_build"] = backend_identity(backend)
        report["staleness"] = backend_staleness(backend, target_dir / "release" / DEP_INFO_NAME)
        write_report(report_path, report)
        if report["staleness"]["stale"]:
            raise refuse(report["staleness"]["code"], "; ".join(report["staleness"]["errors"]))
        runtime_target = output / "runtime-target"
        runtime_deps = runtime_target / "release" / "deps"
        runtime_deps.mkdir(parents=True)
        snapshot = runtime_deps / BACKEND_NAME
        report["backend_snapshot"] = snapshot_backend(backend, snapshot, report["backend_after_build"])
        write_report(report_path, report)
        names = [target.name for target in TARGETS]
        test_build_log = output / "test-build.log"
        tests = [argument for name in names for argument in ("--test", name)]
        test_build = run_step([*cargo, "test", *common, *tests, "--no-run"], test_build_log,
                              args.timeout_seconds, environment)
        test_build.update(classify_test_build(test_build["returncode"],
                                              test_build_log.read_text(errors="replace"), target_dir, names))
        if test_build["interrupted_signal"] is not None:
            test_build["status"] = "fail"
            test_build["errors"].append(f"test build interrupted by signal {test_build['interrupted_signal']}")
        report["test_build"] = test_build
        ensure_unchanged_source(report, "source_after_test_build")
        write_report(report_path, report)
        if test_build["status"] != "pass":
            raise refuse(TEST_BUILD_FAILED, "; ".join(test_build["errors"]))
        # Each fixture loads the backend beside its own executable
        # (tests/support/backend_artifact.rs). Run an independent read-only copy
        # of every test executable from the snapshot's directory, so no fixture
        # can load the cache library the test build may have rebuilt.
        runtime_executables = {}
        for target in TARGETS:
            executable = test_build["executables"][target.name]
            copy = runtime_deps / Path(executable["path"]).name
            if copy == snapshot:
                raise refuse(TEST_BUILD_FAILED, f"{target.name}: test executable is named like the backend")
            runtime_executables[target.name] = snapshot_backend(
                Path(executable["path"]), copy, executable, mode=0o555,
                what=f"{target.name} test executable")
        report["runtime_executables"] = runtime_executables
        expected_entries = runtime_entries(runtime_target)
        write_report(report_path, report)
        run_environment = test_environment(base_environment, runtime_target)
        interrupted = False
        for target in TARGETS:
            executable = runtime_executables[target.name]
            if backend_identity(Path(executable["path"])) != executable:
                raise refuse(BACKEND_CHANGED, f"{target.name}: test executable changed before execution")
            if backend_identity(snapshot) != report["backend_snapshot"]:
                raise refuse(BACKEND_CHANGED, f"backend snapshot changed before {target.name}")
            print(f"Running {target.name} ({target.kind}) against backend "
                  f"{report['backend_snapshot']['sha256']}", flush=True)
            log = output / f"{target.name}.log"
            result = DARWIN.run_target(
                [executable["path"], "--show-output", "--test-threads=1"], log, args.timeout_seconds,
                minimum=target.minimum, root=BRIDGE_DIR, environment=run_environment,
            )
            result.update(classify_target(target, result["returncode"], log.read_text(errors="replace")))
            result["target"] = target.name
            if result["interrupted_signal"] is not None:
                result["status"] = "fail"
                result["errors"].append(f"interrupted by signal {result['interrupted_signal']}")
                interrupted = True
            report["targets"].append(result)
            write_report(report_path, report)
            print(f"{result['status'].upper()}: {target.name}", flush=True)
            if backend_identity(Path(executable["path"])) != executable:
                raise refuse(BACKEND_CHANGED, f"{target.name}: test executable changed during execution")
            if backend_identity(snapshot) != report["backend_snapshot"]:
                raise refuse(BACKEND_CHANGED, f"backend snapshot changed during {target.name}")
            entries = runtime_entries(runtime_target)
            if entries != expected_entries:
                raise refuse(FALLBACK_BUILD, f"{target.name} changed the runtime target directory "
                                             f"(a fixture fallback build or cache write): {entries}")
            if interrupted:
                report["errors"].append("interrupted; required target inventory is incomplete")
                break
        report["cache_backend_after_tests"] = backend_identity(backend) if backend.exists() else None
        ensure_unchanged_source(report, "source_after_tests")
        statuses = [row["status"] for row in report["targets"]]
        complete = len(report["targets"]) == len(TARGETS) and not interrupted
        if complete and all(status == "pass" for status in statuses):
            report["status"] = "pass"
        elif complete and all(status in ("pass", "named-refusal") for status in statuses):
            report["status"] = "named-refusal"
        else:
            report["status"] = "fail"
    except GateError as error:
        report["findings"].extend({"code": code, "message": message} for code, message in error.findings)
        report["errors"].append(str(error))
        report["status"] = "fail"
    except (OSError, RuntimeError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        report["errors"].append(str(error))
        report["status"] = "fail"
    except KeyboardInterrupt:
        report["errors"].append("interrupted; required bridge qualification is incomplete")
        report["status"] = "fail"
    rows = report["targets"]
    report["native_executed_passes"] = sum(
        row["counts"]["executed"] for row in rows if row.get("kind") == NATIVE and row["status"] == "pass")
    report["compile_verdict_passes"] = sum(
        row["counts"]["executed"] for row in rows if row.get("kind") == COMPILE_VERDICT and row["status"] == "pass")
    report["fixed_cost_passes"] = sum(
        row["counts"]["executed"] for row in rows if row.get("kind") == FIXED_COST and row["status"] == "pass")
    report["named_refusals"] = [row["target"] for row in rows if row["status"] == "named-refusal"]
    # Per-test positive accounting across every target that ran, passing or not:
    # a credited test passed AND printed its own positive-evidence marker. A
    # named refusal credits nothing.
    credited_rows = [row for row in rows if row["status"] != "named-refusal"]
    by_kind, by_certs = collections.Counter(), collections.Counter()
    for row in credited_rows:
        by_kind.update(row.get("evidence_counts") or {})
        by_certs.update(row.get("certs_counts") or {})
    report["positive_evidence_totals"] = {
        "required_tests": sum(target.minimum for target in TARGETS),
        "credited_tests": sum(row["counts"]["executed"] for row in credited_rows),
        "by_kind": dict(sorted(by_kind.items())), "by_certs": dict(sorted(by_certs.items())),
        "certs_off_tests": [f"{row['target']}::{test}"
                            for row in credited_rows for test in row.get("certs_off_tests", [])],
        "failed_tests": {row["target"]: row["failed_tests"] for row in rows if row.get("failed_tests")},
        "unevidenced_passes": {row["target"]: row["unevidenced_passes"]
                               for row in rows if row.get("unevidenced_passes")},
        "target_status": {row["target"]: row["status"] for row in rows},
    }
    report["finding_codes"] = sorted({finding["code"] for finding in report["findings"]})
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    write_report(report_path, report)
    label = report["status"].upper()
    if report["status"] == "named-refusal":
        label += " (open named refusals; not a pass)"
    print(f"Darwin AArch64 bridge gate: {label} ({report_path})")
    for error in report["errors"]:
        print(error, file=sys.stderr)
    if report["status"] == "pass":
        return 0
    return EXIT_NAMED_REFUSAL if report["status"] == "named-refusal" else 1


if __name__ == "__main__":
    raise SystemExit(main())
