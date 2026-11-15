#!/usr/bin/env python3
"""Run the required Linux AArch64 regression floor, not full qualification.

Each complete integration target runs in its own bounded process. Native
execution, ABI admission and source-binding controls are all required; this
floor does not establish full compiler completion, proof authority or release
readiness. See docs/linux-aarch64-completion.md for the remaining requirements.

--require-clean refuses to run when the source tree has any tracked
modification or untracked non-ignored file. Every run records, as
report.json's dependency_identity, the Git dependency identities the root
Cargo.lock resolves in the local Cargo home (scripts/dependency_identity.py),
and again after the targets as final_dependency_identity; a lockfile or
checkout tree that changes in between, or a checkout extracted during the run
that is not the unmodified pinned revision, fails the run. --require-offline-deps
refuses to run unless every pinned Git revision resolves in the local Cargo Git
database and no finished checkout differs from it, and passes --offline to
every Cargo invocation so nothing is fetched. --max-rss-gib enforces a sampled
process-group resident-set ceiling on every Cargo invocation through
scripts/run_with_timeout.py; a host that cannot supervise resident set records
"unsupported" and fails instead of running without the requested ceiling.

Proof-replay targets (source-bound frames, JIT certificates, certificate cache
identity) need the AY solver and the Clean checker exactly as the verifier's
child processes resolve them (scripts/release_gate_summary.py names these the
pinned routes): AY is an absolute AY_SOLVER_PATH, else the build toolchain's
<sysroot>/bin/ay, admitted by trust-cg-verify only by the SHA-256 of its bytes
(crates/trust-cg-verify/src/ay_identity.rs); Clean is an explicit
TCG_EXTERNAL_CLEAN_CHECKER override, or an aterm-style package prefix whose bin
directory is on PATH and whose store/clean/current/bin/clean exists. Every run
records both resolutions with executable hashes as report.json's proof_tools
before the first target and final_proof_tools after the last, and fails if
either identity changed in between. --require-proof-tools refuses to run
unless both resolve through a pinned route; without it an absent or unpinned
tool is labelled on stderr and in the report, because proof-replay targets
then fail with "needs independently replayed proof" for that reason alone,
which is a provisioning defect rather than a compiler regression. A pinned
route only names AY: the identity rule still has to admit its bytes and copy
them into `<cache>/trust-cg/ay-exec`, refusing any cache ancestor others may
write (a group-writable `<cache>/trust-cg` refused AY on every run). So
--require-proof-tools then builds the CLI with the floor's own build command
and, before any target, runs `trust-cg --print-ay-identity` in the targets'
runtime environment (report.json's ay_admission): the run fails unless the
rule admits exactly the resolved AY and its private copy exists, and the
failure carries the rule's own refusal, with the directory and remedy.

A required target whose native legs run through all three host linkers (GNU
ld, gold and LLD) runs with TCG_REQUIRE_LLD=1 and TCG_REQUIRE_GOLD=1
(TARGET_ENVIRONMENT), so a host without LLD or gold fails that target's leg by
assertion rather than only through the SKIP line it would otherwise print.
The LLVM importer's symbol_linkage_elf also runs with TCG_REQUIRE_LLC=1: its
llc twin legs need an llc, which the test finds through TCG_LLC, PATH or the
sysroot of the compiler that builds it (<sysroot>/lib/rustlib/<host>/bin/llc),
and whose LLVM major version must equal that compiler's. A Trust package ships
one there with its other LLVM tools. Preflight resolves it by the same rule (an
executable file; absolute PATH entries only), records its path, route, version,
SHA-256 and the compiler whose sysroot and LLVM version decided as
provenance.llc, and refuses to run without one, naming the remedy (a Trust
package that carries its LLVM tools, or TCG_LLC).
The runner sets exactly these variables for that target's invocation alone,
records them in report.json, and refuses to run when an entry names no
required target, a variable its test file does not read, or anything but
TCG_REQUIRE_<NAME>=1.

A required target whose test file is gated on a Cargo feature
(`#![cfg(feature = ...)]`, the LLVM IR importer's `driver` targets) would build
an empty suite without it. TARGET_FEATURES names each such target's features;
the runner passes them with `--features` to that target's invocation alone,
records them in report.json, and refuses to run when a required target's
file-level feature gate is covered neither by a default feature nor by its
entry, or when its entry names an undeclared feature.

Ambient PROPTEST_* variables, and the variables Cargo itself sets for build
scripts, rustc and tests (CARGO_MANIFEST_DIR, CARGO_PKG_*, CARGO_FEATURE_*,
...), are removed from every target's environment (an ambient PROPTEST_CASES
would silently shrink the panic-fuzz families); report.json records them as
provenance.scrubbed_environment and each target's scrubbed_environment. Each
of the seven panic-fuzz families must also print its case-count probe line
with its file's default count (PROPTEST_CASE_DEFAULTS).

Cargo config files and config variables bypass any environment scrub. Before
it runs any build tool (version probes included), every run records as
report.json's cargo_config each config path Cargo would read (with its
SHA-256) and each config variable under the selected build tool's prefixes
(CARGO_, and TARGO_ for Targo), audited by scripts/cargo_config_audit.py; it
records them again as final_cargo_config. The run refuses to start when a
config path is not a regular file, when a file other than a byte-identical
copy of the repository's committed .cargo/config.toml, or a variable, sets a
key outside that module's allowlist ([env], [build] rustflags, [profile],
[alias], a wrapper, [term] quiet, ...), and fails when the record changes
during the run.

Every target must report at least one executed pass. A target listed in
TARGET_MINIMUM_PASSES must report at least that many: its minimum is the
number of tests the file compiles on this host, so a test that vanishes
behind a cfg or is deleted fails the floor instead of silently shrinking the
suite. The runner refuses to start when a minimum exceeds the file's test
functions.

TARGETS is all-required. A target a recorded ruling (docs/decision-record.md)
takes out of the requirement is declared in DECIDED_ABSENT with its ruling id
and reason
instead of being deleted from the list: it is never run, but --list prints it,
every report.json records it under "decided_absent", and the summary prints one
refusal line per row before and after the run, so the omission stays visible in
the record. The runner refuses to start if a row also appears in TARGETS or its
test file is gone.

A required target may live in the rustc bridge (BRIDGE_PACKAGE), which is a
separate Cargo workspace on the pinned Trust toolchain. Such a target is run in
that directory by the pinned package's `targo --unverified test --release`, with
the package's `trustc` as RUSTC; --trust-driver names the package explicitly and
the pinned-package rules of scripts/trust_toolchain.py refuse a PATH shim, a
stock nightly, or a package built for another host. That lane is diagnostic: it
makes no Trust-verified-compilation claim. Its Cargo configuration is audited
from the bridge directory under the bridge build tool's own variable prefixes,
like the root workspace's.

Every target builds with PATH's coherent Trust compiler/build-tool package,
whose Targo runs with an explicit --unverified: the only lane (owner directive
2026-09-28; --trust-unverified, which named it, is still accepted). This is a
development compilation lane, not Trust-verified compilation. The selected
compiler also resolves the proof tools; their identity and acceptance checks
remain required.

--cpu-profile host+baseline-emulation additionally requires the bounded CPU
matrix in check_aarch64_cpu_profiles.py: native host, QEMU max and Cortex-A53,
including generated ELF children and the parent-only negative control. Its
profile fingerprint is recorded separately. --cpu-profile-only runs just that
matrix with its distinct report schema; it never claims this regression floor
passed. The default native floor and every required target stay mandatory.
"""

from __future__ import annotations

import argparse
import contextlib
import functools
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
TIMEOUT_RUNNER = ROOT / "scripts" / "run_with_timeout.py"
DEPENDENCY_RECORDER = ROOT / "scripts" / "dependency_identity.py"
# The rustc bridge is a separate Cargo workspace pinned to the Trust toolchain
# (`crates/rustc-codegen-trust-cg/rust-toolchain.toml`). A floor target in that
# package is built and run there by the pinned package's `targo`, in its
# explicit unverified build lane, with that package's `trustc` as RUSTC (the
# same lane the bridge's own tests and scripts/check_linux_x86_64_bridge.py
# use). A root-workspace `-p` cannot address the bridge, which is its own
# workspace, and a stock nightly cannot load the backend.
BRIDGE_PACKAGE = "rustc-codegen-trust-cg"
BRIDGE_DIR = ROOT / "crates" / BRIDGE_PACKAGE
TRUST_TOOLCHAIN_SCRIPT = ROOT / "scripts" / "trust_toolchain.py"
# The build tool every target runs, from PATH's Trust package (the only lane).
TRUST_BUILD_TOOL = "targo"
# The checkout's Cargo config directory, which Cargo reads from the root.
CARGO_CONFIG_DIRECTORY = ".cargo"
CARGO_CONFIG_AUDIT = ROOT / "scripts" / "cargo_config_audit.py"
PROOF_TOOL_RESOLVER = ROOT / "scripts" / "release_gate_summary.py"
PROOF_TOOLS = ("ay", "clean")
# The AArch64 arithmetic AOT runner's `ay_admission`: how a runner asks a
# trust-cg build (`trust-cg --print-ay-identity`) to apply the AY identity rule.
AY_ADMISSION_RUNNER = ROOT / "scripts" / "check_aarch64_aot_arithmetic.py"
# The binary --require-proof-tools builds, with this floor's build command, to
# ask that rule before any target runs.
AY_ADMISSION_PACKAGE = "trust-cg-cli"
AY_ADMISSION_BINARY = "trust-cg"
# Test-only tool selections must reach the target runner, never the Trust
# compiler process, which rejects ambient TCG_* controls.
RUNTIME_CHECKER_ENVIRONMENT = ("TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER", "TCG_LLC")
HOST = "aarch64-unknown-linux-gnu"
# The floor's own name, report schema and log-directory prefix. The Linux x86-64
# twin (scripts/check_linux_x86_64.py) loads this module and overrides these
# together with HOST and TARGETS; every message and record reads them from here.
FLOOR_NAME = "Linux AArch64"
SCHEMA = "trust-cg-linux-aarch64-regressions-v1"
OUTPUT_PREFIX = "trust-cg-linux-aarch64-"
# These are complete test targets, never substring filters. Additional Linux
# families must be added as their native implementations are qualified.
TARGETS = (
    ("trust-cg-lower", "aarch64_variadic_abi"),
    ("trust-cg-lower", "rust_empty_filter"),
    ("trust-cg-lower", "aarch64_adapter_target_abi"),
    ("trust-cg-lower", "aarch64_aggregate_stack_abi"),
    ("trust-cg-lower", "aarch64_hva_abi"),
    ("trust-cg-lower", "vector_type_admission"),
    ("trust-cg-lower", "container_pointer_metadata"),
    ("trust-cg-lower", "aggregate_constants"),
    ("trust-cg-lower", "packed_aggregate_constants"),
    ("trust-cg-lower", "niche_enum_codec"),
    ("trust-cg-lower", "abi_definition_refusals"),
    # L05-P2 trust-ir construct inventory: host-neutral lowering/refusal gate
    # added from a Darwin host and not yet run on a Linux floor host.
    ("trust-cg-lower", "trust_ir_construct_inventory"),
    # L05-P7 round-trip gate (the pinned trust-ir conformance corpus through
    # trust-cg's readers and writers) and the construct property generator:
    # host-neutral, added from a Darwin host; not yet run on a Linux host.
    ("trust-cg-codegen", "trust_ir_corpus_roundtrip"),
    ("trust-cg-codegen", "tmbc_roundtrip_prop"),
    # L13-P7 panic-fuzz: generated trust-ir through the lowering adapter must
    # translate or return a clean error, never panic.
    ("trust-cg-lower", "panic_fuzz_lower"),
    ("trust-cg-codegen", "canonical_bounds_assert_linux"),
    ("trust-cg-codegen", "aarch64_direct_cmp_branch"),
    ("trust-cg-codegen", "aarch64_select_flags_across_call"),
    ("trust-cg-codegen", "aarch64_unroll_trip_test_reader"),
    ("trust-cg-codegen", "aarch64_live_frame_effects"),
    ("trust-cg-codegen", "aarch64_shrink_wrap_region_exit"),
    ("trust-cg-codegen", "aarch64_call_result_liveness"),
    ("trust-cg-codegen", "aggregate_call_results"),
    ("trust-cg-codegen", "multi_result_call_abi"),
    ("trust-cg-codegen", "e2e_aarch64_variadic_linux"),
    ("trust-cg-codegen", "e2e_aarch64_aggregate_stack_linux"),
    ("trust-cg-codegen", "e2e_aarch64_hva_linux"),
    ("trust-cg-codegen", "e2e_aarch64_vector_types_linux"),
    # L04-P6 native differential of the newly admitted vector operations
    # against the host C compiler's NEON intrinsics at -O3; added from a
    # Darwin host and not yet run on a Linux host.
    ("trust-cg-codegen", "e2e_aarch64_neon_admission"),
    # L04-P3 TrustIR FP lowering differential (AOT with the explicit FP16
    # profile on Linux, and the host JIT; FEAT_FP16 required); added from a
    # Darwin host and not yet run on a Linux host.
    ("trust-cg-codegen", "e2e_aarch64_fp_ieee_lowering"),
    ("trust-cg-codegen", "e2e_aarch64_bool_atomics_linux"),
    ("trust-cg-codegen", "e2e_aarch64_llsc_atomics"),
    ("trust-cg-codegen", "e2e_aarch64_bool_abi_linux"),
    ("trust-cg-codegen", "e2e_aarch64_heap_dealloc_linux"),
    # L05-P3 ARC ops: Retain/Release/IsUnique through the declared Clean RC
    # triple, executed against a C counting runtime at O0-O3 and compared
    # with the trust-ir reference interpreter on the corpus's CleanHeap twin
    # (the interpreter refuses the corpus as compiled: its cells are not
    # reference-counted), with ELF CALL26 site counts.
    ("trust-cg-codegen", "e2e_aarch64_arc_ops_linux"),
    ("trust-cg-codegen", "e2e_aarch64_niche_enum_linux"),
    # L01-P5 hidden-result (sret) X8 convention: ELF twin of the Darwin
    # e2e_aarch64_sret fixture, both directions through function pointers and
    # variadic callees against the host cc; first run on the Linux floor host.
    ("trust-cg-codegen", "e2e_aarch64_sret_linux"),
    # L05-P5 direct-tag enums: ELF twin of the Darwin e2e_aarch64_direct_enums
    # fixture, C-driver and reference-interpreter agreement at O0-O3.
    ("trust-cg-codegen", "e2e_aarch64_direct_enums_linux"),
    # Aggregate InsertField/InsertElement value semantics: 27 shapes whose
    # source is still live after the insert (swap, parameters, loads, globals,
    # constants, calls, copies, selects, block parameters, nested fields,
    # stores and loop-carried values) against a C oracle at O0-O3, with the
    # reference interpreter and the adapter's copy/in-place LIR pinned.
    ("trust-cg-codegen", "e2e_aarch64_aggregate_insert_linux"),
    # AAPCS64 B.4 by-reference composites: every call passing a composite over
    # 16 bytes (not an HFA/HVA) passes storage the callee may own. 22 shapes
    # against C callees and 4 invoke shapes against throwing C++ callees that
    # write every by-reference parameter, at O0-O3; tail calls keep their BL
    # and the copies keep code size bounded.
    ("trust-cg-codegen", "e2e_aarch64_large_aggregate_args_linux"),
    # HFAs with zero-sized members: empty-struct and `()` members skipped and
    # zero-length arrays disqualifying, as GCC places them, in four directions
    # against a GCC-compiled oracle at O0-O3.
    ("trust-cg-codegen", "e2e_aarch64_hfa_zero_sized_linux"),
    ("trust-cg-codegen", "aarch64_exclusive_encoding"),
    ("trust-cg-codegen", "aarch64_cond_select"),
    ("trust-cg-codegen", "aarch64_fp_cond_select"),
    ("trust-cg-codegen", "aarch64_fp_memory_decode"),
    ("trust-cg-codegen", "aarch64_gpr_memory_decode"),
    ("trust-cg-codegen", "aarch64_scalar_writeback_decode"),
    ("trust-cg-codegen", "aarch64_register_offset_decode"),
    ("trust-cg-codegen", "aarch64_narrow_register_offset_decode"),
    ("trust-cg-codegen", "aarch64_pair_memory_decode"),
    # L10-P6: ENC-5's FP/SIMD and integer slices, the committed Darwin floor
    # census replay and the proof-grade refusal; host-neutral. Not yet run on
    # a Linux host.
    ("trust-cg-codegen", "aarch64_enc5_floor_census"),
    # L10-P5 machine-IR identity admission: the optimizer ladder corruption
    # controls and the generated/committed-corpus freshness property;
    # host-neutral (the property file is aarch64-gated, no OS gate). Added
    # from a Darwin host; not yet run on a Linux host.
    ("trust-cg-opt", "mach_id_admission"),
    ("trust-cg-codegen", "mach_id_admission_property"),
    # L07-P2 / X-OPCODES-P1 / L04-P7: the memory-effect decomposition bound to
    # the live encoder, ENC-5's refusal, native JIT programs at O0/O2 (the
    # Mach-O text check is Darwin-only) and the proof-required refusal;
    # aarch64-gated, no OS gate. Added from a Darwin host; not yet run on a
    # Linux host.
    ("trust-cg-codegen", "aarch64_memory_effect_binding"),
    # L04-P12: the trap-expansion obligations against the live expansion,
    # encoder and ENC-5, and the final encoder's refusal of a tampered or
    # partial recorded expansion; host-neutral. Added from a Darwin host; not
    # yet run on a Linux host.
    ("trust-cg-codegen", "aarch64_trap_expansion_binding"),
    # X-LEAN-P3: the Lean A64 golden corpus bound to the live encoder, the
    # field-level encoding helpers and ENC-5 (with every single-bit corruption
    # refused); host-neutral. Its execution is an enumerated encoder binding,
    # not a machine-semantics differential or full-floor qualification.
    ("trust-cg-codegen", "lean_a64_encode_golden_binding"),
    # L07-P2 / X-OPCODES-P1: source-bound memory rows on the proof-grade
    # pipeline's load/store leaves (binding, corruption controls, walk);
    # aarch64-gated, no OS gate. Added from a Darwin host; not yet run on a
    # Linux host.
    ("trust-cg-codegen", "aarch64_memory_source_binding"),
    ("trust-cg-codegen", "panic_fuzz_encode"),
    # L13-P7 panic-fuzz proptest families: the AArch64 compile pipeline, the
    # x86-64 pipeline and encoder (compiling for an explicit x86-64 target;
    # the x86-64-host JIT legs are compiled out here) and Mach-O fixups and
    # relocations must return a value or a typed error, never panic.
    ("trust-cg-codegen", "panic_fuzz_compile"),
    ("trust-cg-codegen", "panic_fuzz_compile_x86_64"),
    ("trust-cg-codegen", "panic_fuzz_encode_x86_64"),
    ("trust-cg-codegen", "panic_fuzz_macho_fixup"),
    ("trust-cg-codegen", "a64_fp_integer_conversion"),
    # aarch64-gated, no OS gate (aarch64_mem_pair_acquire_order's symbol-alias
    # test is macOS-only). Registered from a Darwin host; a64_refine_byte_invariance
    # also by the Linux batch, and run on a Linux host at its 2026-10-14
    # landing (6 passed).
    ("trust-cg-codegen", "a64_refine_byte_invariance"),
    ("trust-cg-codegen", "aarch64_mem_pair_acquire_order"),
    ("trust-cg-codegen", "e2e_fp_to_int_saturation"),
    ("trust-cg-codegen", "e2e_aarch64_exclusive_status_linux"),
    ("trust-cg-codegen", "e2e_aarch64_elf_tlsie"),
    ("trust-cg-codegen", "e2e_aarch64_elf_relocation_model"),
    # L05-P10/L03-P6 ELF twin of e2e_aarch64_globals_darwin: relocated TLS
    # templates (.rela.tdata) against a C pthread oracle in executables and a
    # dlopened shared object, the JIT data image, body SymbolAddr addends and
    # hidden/retained data attributes.
    ("trust-cg-codegen", "e2e_aarch64_globals_linux"),
    ("trust-cg-codegen", "e2e_aarch64_elf_link"),
    ("trust-cg-codegen", "e2e_aarch64_elf_stack_zero_fill"),
    ("trust-cg-codegen", "e2e_aarch64_elf_sections"),
    ("trust-cg-codegen", "e2e_aarch64_global_layout"),
    ("trust-cg-codegen", "aarch64_elf_symbol_binding"),
    # L02-P1 (2026-10-24 closure audit): function bindings off AArch64
    # (x86-64 ELF, Mach-O and COFF; RISC-V ELF) through Compiler::compile,
    # read back by the independent readers, and ld.lld link legs (GNU
    # flavour, cross-target, nothing executed).
    ("trust-cg-codegen", "module_local_binding_other_targets"),
    # trust-ir v41 ABI/linkage residue at the object level (ELF and Mach-O
    # reparsed on any host): ODR weak definitions, AvailableExternally,
    # ExternalWeak, definition and import visibility (its immutable `.rodata`
    # definition rows kill `.rodata` visibility mutants), retention, explicit
    # sections, naked/global_asm and target-feature refusals and the codegen
    # license.
    ("trust-cg-codegen", "v41_abi_residue_objects"),
    ("trust-cg-codegen", "e2e_aarch64_nested_bytes"),
    ("trust-cg-codegen", "e2e_aarch64_narrow_int_diff"),
    ("trust-cg-codegen", "e2e_aarch64_call_arg_signext"),
    ("trust-cg-codegen", "e2e_aarch64_i128_narrow_call"),
    ("trust-cg-codegen", "e2e_aarch64_stack_narrow_args"),
    ("trust-cg-codegen", "e2e_aarch64_callee_saved_fpr"),
    ("trust-cg-codegen", "e2e_aarch64_calling_conv"),
    ("trust-cg-codegen", "e2e_aarch64_tail_call_abi"),
    # Sited assertion delivery (TrustIR `PanicSite`) through
    # tests/common/aarch64_native.rs at O0-O3: a failing `Assert` calls the
    # site's entry with its payload and its value or global location and
    # traps if the entry returns; an `AssertInvoke`'s cleanup pad resumes to
    # the C++ driver's outer catch (LD-56).
    ("trust-cg-codegen", "sited_assert_delivery_native"),
    # Required nounwind EH frames: self/sibling calls at O0-O3, with final
    # Mach-O bytes and 32 Linux native stack walks / 64 source invocations.
    ("trust-cg-codegen", "aarch64_nounwind_tail_frame"),
    ("trust-cg-codegen", "aarch64_affine_bytes"),
    ("trust-cg-codegen", "aarch64_final_layout_crosscheck"),
    ("trust-cg-codegen", "aarch64_pseudo_boundary"),
    ("trust-cg-codegen", "aarch64_raw_dataflow_boundary"),
    ("trust-cg-codegen", "core_jit_planning"),
    # Since L07-P2 (OD-139) every framed source-bound leaf these two targets
    # and jit_cert_cache_identity_aarch64 publish also needs a Clean-checked
    # certificate of each of the twelve memory-effect parts of its two frame
    # records; no Linux AY/Clean pair has been measured on those parts, so
    # under that rule they are not yet run on a Linux host
    # (docs/jit-source-custody.md).
    ("trust-cg-codegen", "jit_fail_closed_proof_policy"),
    ("trust-cg-codegen", "jit_source_bound_arithmetic"),
    # L09-P6/L09-P1: the AArch64 whole-body owner on the real pipeline's
    # bodies (bind at O0-O3 in the AOT and JIT preparations, corruptions
    # refused by name and under Enforce, unreplayed rows uncredited), the
    # silicon differential of its row model, native JIT execution and AOT
    # objects linked against C references built by the host C compiler
    # (`cc`). Added from a Darwin host; not yet run on a Linux host.
    ("trust-cg-codegen", "aarch64_source_bound_body"),
    ("trust-cg-codegen", "jit_wx_refusal"),
    ("trust-cg-codegen", "jit_icache_coherence"),
    ("trust-cg-codegen", "jit_runtime_hardening"),
    ("trust-cg-codegen", "jit_cross_thread_execute_mode"),
    ("trust-cg-codegen", "jit_teardown_policy"),
    ("trust-cg-codegen", "jit_exception_handling"),
    ("trust-cg-codegen", "jit_cert_cache_identity_aarch64"),
    # L11-P2: the installed-artifact replay of the verifying JIT through the
    # public API (raw and proof-required publications, a CachedVerified warm
    # hit). aarch64-gated with no OS gate; added from a Darwin host and not
    # yet run on a Linux host.
    ("trust-cg-codegen", "jit_installed_artifact_replay"),
    ("trust-cg-verify", "aarch64_affine_lowering"),
    ("trust-cg-verify", "aarch64_trust_ir_affine_lowering"),
    ("trust-cg-verify", "bridge_copy_types"),
    ("trust-cg-verify", "aarch64_scalar_cell_bytes"),
    ("trust-cg-verify", "aarch64_scalar_cell_link"),
    ("trust-cg-verify", "aarch64_fcmp_binding"),
    # Per-compile switch-dispatch binding (L04-P11); host-neutral, added
    # from a Darwin host and not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_switch_binding"),
    ("trust-cg-verify", "aarch64_flag_consumer_gate"),
    ("trust-cg-verify", "aarch64_nzcv_silicon_bridge"),
    ("trust-cg-verify", "fp_normal_classification"),
    # L07-P2: the memory-effect decomposition of the Darwin census corpus's
    # memory words and its query size census; host-neutral, added from a
    # Darwin host and not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_memory_effect_queries"),
    # L04-P6 live NEON silicon differential (mmap/mprotect stubs on Linux);
    # added from a Darwin host and not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_neon_silicon_differential"),
    # L04-P3 scalar FP IEEE 754 differential (mmap/mprotect stubs on Linux;
    # FEAT_FP16 required); added from a Darwin host and not yet run on a
    # Linux host.
    ("trust-cg-verify", "aarch64_fp_ieee_differential"),
    # L04-P1 / X-OPCODES-P2 atomic and scalar memory-effect silicon
    # differentials (mmap/mprotect stubs on Linux); added from a Darwin host
    # and not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_atomic_silicon_differential"),
    ("trust-cg-verify", "aarch64_scalar_memory_silicon_differential"),
    # L04-P1 CRC32/CRC32C silicon differential (mmap/mprotect stubs on
    # Linux); added from a Darwin host and not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_crc32_silicon_differential"),
    # L04-P1 SUBS #imm silicon differential (mmap/mprotect stubs on Linux);
    # added from a Darwin host and not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_subs_imm_silicon_differential"),
    # L04-P1 NEON LD1/ST1 form-theorem silicon differential (mmap/mprotect
    # stubs on Linux); added from a Darwin host and not yet run on a Linux
    # host.
    ("trust-cg-verify", "aarch64_neon_structure_silicon_differential"),
    # L13-P7 panic-fuzz: the function verifier reports generated MachFunctions
    # (pseudos, out-of-range instruction ids) without panicking.
    ("trust-cg-verify", "panic_fuzz_verify"),
    # X-HOST-P13: process-level AY admission (what --require-proof-tools
    # asks), each function-verification request and the refusal note resolve
    # one AY cache root, whatever XDG_CACHE_HOME's spelling, HOME, the
    # working directory's mode or the umask; needs the recorded AY.
    ("trust-cg-verify", "ay_cache_root_agreement"),
    # L04-P12 trap-guard obligations: the shape catalog against the live
    # expand_trap_* output, degraded carriers, every pipeline guard window at
    # O0-O3 bound to its source, pipeline-function mutations (deleted,
    # displaced, dead, inverted, re-targeted windows; guard stamps forged onto
    # role traps; source traps moved, inverted or dropped), the certified
    # stack-limit trap, and the 32-bit-index bounds windows and narrow guard
    # operands run natively (the native legs are Linux AArch64 only).
    ("trust-cg-verify", "aarch64_trap_guard_obligations"),
    ("trust-cg-codegen", "aarch64_cmp_admission"),
    ("trust-cg-codegen", "aarch64_integer_predicate_binding"),
    ("trust-cg-codegen", "e2e_aarch64_link_runtime"),
    ("trust-cg-cli", "link_options"),
    ("trust-cg-codegen", "abi_definition_refusals"),
    ("trust-cg-codegen", "e2e_aarch64_host_target_authority_linux"),
    ("trust-cg-codegen", "aarch64_stack_probe_decode"),
    ("trust-cg-codegen", "e2e_aarch64_stack_probe_native"),
    ("trust-cg-codegen", "aarch64_value_decode_native"),
    # Final-stream frame dataflow net on real pipeline output (compile-only).
    ("trust-cg-codegen", "aarch64_frame_dataflow_net"),
    # L10-P10 Q-register spills, pair-spill refusal and LL/SC whole-window
    # spills (native O0-O3 through the shared native helper). Added from a
    # Darwin host and not yet run on a Linux host, so its Linux arm is required
    # here but unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_vector_spills"),
    # L10-P4 mac-reg-block on/off/C-reference differential at O2 and O3:
    # generated kernels (rewrite counts, negative controls, ported matmulfuzz
    # sweep) and the current rustc bridge's p4_matmul nest (rewrite count, and
    # a JIT run with a recording panic_bounds_check stub); the bridge's pre-v52
    # check triple and the p4_matmul nest captured in it are admission
    # fixtures that must be refused at the TrustIR v52 floor on the object
    # path and the JIT. Nine tests compile on aarch64-unknown-linux-gnu
    # (counted from the file on a Darwin host). Added from a Darwin host and
    # not yet run on a Linux host, so its Linux arm is required here but
    # unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_mac_reg_block_differential"),
    # LICM dereferenceable-frame speculation and the register-bound
    # trap-branch fold on/off/C-reference differential at O2 and O3 (fold and
    # neon-array counts, trapping negative controls), and the preheader-writer
    # rows for LICM's insertion point. Added from a Darwin host
    # and not yet run on a Linux host, so its Linux arm is required here but
    # unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_vec_len_guard_differential"),
    # L10-P3 per-pass translation validation (enforced compiles byte-equal to
    # validation off, dedicated-validator coverage, native C-reference rows
    # and the guarded-pair page-end trap). Added from a Darwin host and not
    # yet run on a Linux host, so its Linux arm is required here but
    # unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_pass_validation"),
    # L10-P1 post-allocation value-flow validation (both stage comparisons
    # validated under enforce, byte-equal to validation off, corruption
    # controls refused, native C-reference rows). Added from a Darwin host
    # and not yet run on a Linux host, so its Linux arm is required here but
    # unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_post_ra_value_flow"),
    # L09-P3 composed transition records (affine kernels composed from their
    # TrustIR source to their published bytes at O0-O3, recording byte-equal,
    # corruption controls refused by name, native C-reference rows). Added
    # from a Darwin host and not yet run on a Linux host, so its Linux arm is
    # required here but unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_composed_transition"),
    # Native families shared with macOS through tests/common/native_host.rs.
    # Their Linux arms are required here; LSE/FP16/DotProd families execute the
    # explicit-profile pipeline lane and fail (never skip) without host support.
    ("trust-cg-codegen", "aarch64_native_host_contract"),
    ("trust-cg-codegen", "v41_global_linkage"),
    ("trust-cg-codegen", "e2e_aarch64_switch"),
    ("trust-cg-codegen", "e2e_aarch64_indirect_call"),
    # Switch forms and function-pointer tables at O0-O3 (L04-P11). Compiles
    # for Linux GNU through the shared native helper; added from a Darwin
    # host and not yet run on a Linux host, so its Linux arm is required
    # here but unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_switch_forms"),
    # L05-P11 dialect legalization of the pinned corpus's dialect rows, AOT
    # (linked through the shared native helper) and JIT at O0-O3. Compiles for
    # Linux GNU; added from a Darwin host and not yet run on a Linux host, so
    # its Linux arm is required here but unmeasured until it runs.
    ("trust-cg-codegen", "dialect_legalization_corpus"),
    # First-class closure values (L05-P4). Compiles for Linux GNU through the
    # shared native helper; added from a Darwin host and not yet run on a Linux
    # host, so its Linux arm is required here but unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_closures"),
    # Sequences and boxed sets (L05-P8). Compiles for Linux GNU through the
    # shared native helper; added from a Darwin host and not yet run on a
    # Linux host, so its Linux arm is required here but unmeasured until it runs.
    ("trust-cg-codegen", "e2e_aarch64_sequences"),
    ("trust-cg-codegen", "e2e_aarch64_i128_icmp"),
    # The 128-bit division-by-zero guard (low-word-zero divisors): compiles for
    # Linux through the shared harness; added from a Darwin host and not yet
    # run on a Linux host.
    ("trust-cg-codegen", "e2e_aarch64_i128_div_zero_guard"),
    ("trust-cg-codegen", "e2e_aarch64_i128_overflow"),
    ("trust-cg-codegen", "e2e_aarch64_i128_shift"),
    # L04-P10 i128/u128 switch and checked-mul boundary controls: compiles for
    # Linux through the shared harness but has not yet been executed on the
    # Linux floor host (recorded Darwin run only).
    ("trust-cg-codegen", "e2e_aarch64_i128_switch"),
    ("trust-cg-codegen", "e2e_aarch64_u128_checked_mul"),
    ("trust-cg-codegen", "e2e_aarch64_i128_to_f16"),
    ("trust-cg-codegen", "e2e_aarch64_f16_to_i128"),
    ("trust-cg-codegen", "e2e_aarch64_fptosi_sat_i128"),
    ("trust-cg-codegen", "e2e_aarch64_fptosi_sat"),
    ("trust-cg-codegen", "e2e_aarch64_fp_rounding"),
    ("trust-cg-codegen", "e2e_aarch64_fp_minmax"),
    ("trust-cg-codegen", "e2e_aarch64_fp_to_int"),
    ("trust-cg-codegen", "e2e_aarch64_fcmp_nan"),
    ("trust-cg-codegen", "e2e_aarch64_fp_loop_carried_reduction"),
    ("trust-cg-codegen", "e2e_aarch64_int_to_float"),
    ("trust-cg-codegen", "e2e_aarch64_sitofp_signext"),
    ("trust-cg-codegen", "e2e_aarch64_f16_scalar"),
    ("trust-cg-codegen", "e2e_aarch64_f16_fcvt"),
    # L01-P7 f16 scalar and f16 HFA (1-4 members) arguments and returns in
    # both directions against GCC's _Float16 at O0-O3, baseline and explicit
    # fp16 lanes, bit-exact NaN payloads; decoded H-register/stack placement
    # against an independent AAPCS64 model, mutation and prototype controls,
    # and the FEAT_FP16 refusal for f16 arithmetic without the profile.
    ("trust-cg-codegen", "e2e_aarch64_f16_abi_linux"),
    ("trust-cg-codegen", "aarch64_volatile_access_preservation"),
    ("trust-cg-codegen", "e2e_aarch64_ctpop"),
    ("trust-cg-codegen", "e2e_aarch64_udot_popcount"),
    ("trust-cg-codegen", "e2e_aarch64_vector_binop"),
    ("trust-cg-codegen", "e2e_aarch64_vector_lane"),
    ("trust-cg-codegen", "e2e_aarch64_vector_fp_unary"),
    ("trust-cg-codegen", "aarch64_v4i32_vector_shift"),
    ("trust-cg-codegen", "neon_array_execution"),
    ("trust-cg-codegen", "neon_farray_execution"),
    # X-OPCODES-P11 NEON LD1/ST1 post-index: trust-ir maps vectorized by
    # neon_fmap at O2/O3, decoded word by word, run against a C oracle at
    # O0-O3, with scalar-only and mutated-word refusals and mutant runs.
    ("trust-cg-codegen", "neon_ld1_st1_post_execution"),
    # X-OPCODES-P11 live LD1/ST1 post-index writebacks: trust-ir FFT
    # butterflies vectorized by neon_butterfly at O2/O3 (walking pointers),
    # a decoded-stream liveness walk, a C oracle at O0-O3 and writeback-only
    # mutants that must fail it.
    ("trust-cg-codegen", "neon_butterfly_writeback_execution"),
    # AArch64 CEGIS superoptimizer (opt-in --cegis-superopt): solver-gated
    # budget, instruction-built obligations replayed by Clean, the operand-0
    # wrong-code regression and the tampered-cache refusal, run natively
    # against a C oracle.
    ("trust-cg-codegen", "e2e_cegis_superopt"),
    ("trust-cg-codegen", "e2e_aarch64_atomics"),
    ("trust-cg-codegen", "e2e_aarch64_narrow_atomics"),
    # Contended multi-thread atomics, litmus and TLS waves (shared with macOS).
    ("trust-cg-codegen", "e2e_aarch64_concurrency"),
    # L03-P3: the memory-order mapping checked on the words the selector emits
    # for aarch64-apple-darwin (object-only here; its Apple clang differential
    # is macOS-only). Added from a Darwin host; not yet run on a Linux host.
    # (The native litmus harness, e2e_aarch64_memory_order_litmus, runs on
    # macOS only.)
    ("trust-cg-codegen", "aarch64_memory_order_obligations"),
    ("trust-cg-codegen", "e2e_aarch64_global_var"),
    ("trust-cg-codegen", "e2e_aarch64_read_global"),
    ("trust-cg-codegen", "e2e_aarch64_data_reloc"),
    ("trust-cg-codegen", "e2e_aarch64_struct_byval"),
    ("trust-cg-codegen", "e2e_aarch64_call_arg_ptr_theft"),
    ("trust-cg-codegen", "e2e_aarch64_byte_gather_ro"),
    ("trust-cg-codegen", "e2e_aarch64_ext_stencil"),
    ("trust-cg-codegen", "e2e_aarch64_unit_return"),
    ("trust-cg-codegen", "e2e_aarch64_coroutine"),
    ("trust-cg-codegen", "e2e_aarch64_eh_catch"),
    ("trust-cg-codegen", "e2e_aarch64_eh_invoke_trust_ir"),
    ("trust-cg-codegen", "e2e_aarch64_eh_resume_trust_ir"),
    ("trust-cg-codegen", "e2e_aarch64_eh_o2_and_walkthrough_trust_ir"),
    # L03-P2: CG-owned catch-all and cleanup/resume pads and plain frames,
    # linked with libstdc++/libgcc_s and with Rust std and run at O0-O3
    # against an exact stage/payload/destructor model, read back by GNU
    # readelf, llvm-dwarfdump and llvm-objdump, with LSDA-row mutations and
    # missing-personality link controls.
    ("trust-cg-codegen", "e2e_aarch64_eh_linux"),
    # L03-P13: the certified relocation inventory's AArch64 ELF EH rows (CIE
    # personality, FDE pc-begin and LSDA, `DW.ref` slot) equal the emitted
    # object's records exactly by section and symbol index, read by the
    # reparse reader, an own `.eh_frame` walker and GNU readelf, at O0-O3
    # under static, PIE and PIC, with the post-emission row cross-check's
    # mutation controls, the named refusals, and the certified-compile
    # refusal of unproved exception tables ([TCG-EH-UNPROVED]).
    ("trust-cg-codegen", "aarch64_elf_eh_relocation_inventory"),
    # L03-P11 typed catches: compiles for Linux, but its native controls are
    # compiled only for AArch64 macOS (ELF typed catches and mixed
    # personalities are refused by name), so a Linux run executes the
    # object-level and refusal tests and prints no SKIP line; not yet run on a
    # Linux host.
    ("trust-cg-codegen", "e2e_aarch64_eh_typed"),
    ("trust-cg-codegen", "e2e_aarch64_p0_miscompiles"),
    ("trust-cg-codegen", "flat_gep_semantics"),
    ("trust-cg-codegen", "storage_geometry"),
    ("trust-cg-codegen", "e2e_aarch64_p1_p2_gaps"),
    ("trust-cg-codegen", "guard_kernel_gate_overflow_linkrun"),
    ("trust-cg-codegen", "guard_kernel_gate_overflow_mul_linkrun"),
    ("trust-cg-codegen", "overflow_inst_carrier_rewrite_linkrun"),
    # ELF DWARF and CFI read back by llvm-dwarfdump/llvm-readelf/llvm-objdump
    # (a required tool on this host), and gdb/lldb source correspondence.
    ("trust-cg-codegen", "aarch64_elf_dwarf"),
    ("trust-cg-codegen", "aarch64_elf_cfi_differential"),
    ("trust-cg-codegen", "e2e_aarch64_elf_debugger_linux"),
    # LLVM IR importer driver targets: clang -O0 IR through the full pipeline
    # for explicit aarch64-unknown-linux-gnu (and aarch64-apple-darwin object)
    # targets, ELF sections/symbols/relocations read back, and programs linked
    # with cc and run natively against pinned or C-reference output. They
    # build only with the crate's `driver` feature (TARGET_FEATURES).
    ("trust-cg-llvm-import", "ary3_init_o2_e2e"),
    ("trust-cg-llvm-import", "ary3_reverse_accum_proof_facts"),
    # Stack-slot bit-reverse ladders folded into RBIT (their private-slot
    # stores linked to it for the raw dataflow-integrity gate), frameless at
    # O2, and run against a C reference at O0-O3 with escaping, re-read and
    # width-mismatched slots that must keep their stores.
    ("trust-cg-llvm-import", "bitreverse_intrinsics"),
    ("trust-cg-llvm-import", "cast_e2e"),
    ("trust-cg-llvm-import", "casttest3_e2e"),
    ("trust-cg-llvm-import", "divtest_e2e"),
    ("trust-cg-llvm-import", "fp_e2e"),
    ("trust-cg-llvm-import", "intmm_o2_e2e"),
    ("trust-cg-llvm-import", "objectsize_intrinsic"),
    ("trust-cg-llvm-import", "printf_globals"),
    ("trust-cg-llvm-import", "switch_e2e"),
    # L02-P13 imported symbol facts: LLVM function and global linkage,
    # visibility, self-keyed COMDATs and extern_weak/available_externally
    # declarations read back from ELF objects at O0-O3 under static/pie/pic,
    # the COMDAT admission cross-checked against the backend's own grouping,
    # and native GNU ld/gold/LLD rows (a pic library's .dynsym and
    # LD_PRELOAD, ODR coalescing across objects and g++ twins, hidden
    # declarations binding locally, null-on-missing weak calls, weak calls
    # passing register-pair i128 and stack arguments like direct calls) each
    # compared with a gcc/g++ twin, and the named refusal of a weak call whose
    # address form would drop a stack-passed i128 half (L06-P15).
    ("trust-cg-llvm-import", "symbol_linkage_elf"),
    ("trust-cg-llvm-import", "ws2_stack_protector_target"),
    # L02-P14: both host-neutral rows and both native Linux rows are required.
    # The full 17-row escape corpus runs against llc at O0-O3 through GNU ld,
    # gold and LLD in non-PIE/PIE modes; both length refusals need LLVM's
    # semantic type-mismatch diagnostic and corrected-length controls.
    ("trust-cg-llvm-import", "c_string_escapes_e2e"),
    # L01-P11 `sret` carried onto trust-ir (and byval/inreg/... refused by
    # name): the host-neutral import/compile/refusal rows; the native legs
    # against clang are macOS-only. Added from a Darwin host; not yet run on a
    # Linux host.
    ("trust-cg-llvm-import", "sret_abi_e2e"),
    # L01-P11 `zeroext`/`signext` carried as the call edge's signedness: the
    # host-neutral import/compile/refusal rows; the native legs against clang
    # are macOS-only. Added from a Darwin host; not yet run on a Linux host.
    ("trust-cg-llvm-import", "int_ext_abi_e2e"),
    # L13-P7 differential JIT harness (crates/trust-cg-fuzz): generated and
    # hand-built trust-ir executed by the host JIT at O0-O3 in forked sandboxes
    # against the trust-ir interpreter (and native Rust arithmetic where a file
    # supplies it), the harness's own detection controls, the fuzz drivers'
    # report/diagnostic contract and the bridge differential engine. The
    # campaign-length runs are scripts/run_linux_fuzz_lane.py.
    ("trust-cg-fuzz", "bridge_diff"),
    ("trust-cg-fuzz", "cross_call_value_preserved"),
    ("trust-cg-fuzz", "ctpop_narrow"),
    ("trust-cg-fuzz", "dense_switch_blockarg_encode"),
    ("trust-cg-fuzz", "dense_switch_encode"),
    ("trust-cg-fuzz", "diff_cmp_overflow"),
    ("trust-cg-fuzz", "diff_int_divrem"),
    ("trust-cg-fuzz", "diff_narrow_int"),
    ("trust-cg-fuzz", "driver_output"),
    ("trust-cg-fuzz", "fp_const_and_fcmp"),
    ("trust-cg-fuzz", "generator_config"),
    ("trust-cg-fuzz", "jit_call_crossing_pressure_diff"),
    ("trust-cg-fuzz", "jit_diff_catches_miscompile"),
    ("trust-cg-fuzz", "jit_diff_consumer_shapes"),
    ("trust-cg-fuzz", "jump_table_in_loop"),
    ("trust-cg-fuzz", "sweep2_bitops"),
    ("trust-cg-fuzz", "sweep2_chained_casts"),
    ("trust-cg-fuzz", "sweep2_i128"),
    ("trust-cg-fuzz", "sweep2_large_pressure"),
    ("trust-cg-fuzz", "sweep3_cmp_branch_fusion"),
    ("trust-cg-fuzz", "sweep3_mem_aliasing"),
    ("trust-cg-fuzz", "sweep3_nested_calls_pressure"),
    ("trust-cg-fuzz", "sweep3_select_switch_calls"),
    ("trust-cg-fuzz", "sweep3_wide_shifts_bitops"),
    ("trust-cg-fuzz", "vector_v128_load_store_lane"),
    ("trust-cg-fuzz", "verify_narrow_int_0"),
    ("trust-cg-fuzz", "verify_narrow_int_1"),
    ("trust-cg-fuzz", "verify_narrow_int_2"),
)
# Cargo features a required target needs before its tests exist. Each of these
# files is `#![cfg(feature = ...)]`-gated, so without the feature Cargo builds
# an empty suite. The runner passes exactly these features, and only to that
# target's own invocation; feature_problems() reports a required target whose
# file-level feature gate is not covered, an undeclared feature, and an entry
# naming no required target.
# Targets a recorded ruling (docs/decision-record.md) has removed from this
# floor's requirement, as (package, target, ruling id, reason). They are never run here, but --list
# prints them and every report records them under "decided_absent", so an
# absent lane stays visible in the record instead of silently missing from
# TARGETS. TARGETS stays all-required; a target may not appear in both, and a
# decided-absent target must still exist as crates/<package>/tests/<target>.rs
# so the record cannot outlive the lane it describes. The architecture twin
# declares its own rows (scripts/check_linux_x86_64.py).
DECIDED_ABSENT: tuple[tuple[str, str, str, str], ...] = ()
TARGET_FEATURES = {
    ("trust-cg-llvm-import", target): ("driver",)
    for target in (
        "ary3_init_o2_e2e", "ary3_reverse_accum_proof_facts", "bitreverse_intrinsics",
        "cast_e2e", "casttest3_e2e", "divtest_e2e", "fp_e2e", "intmm_o2_e2e",
        "objectsize_intrinsic", "printf_globals", "switch_e2e", "symbol_linkage_elf",
        "ws2_stack_protector_target", "c_string_escapes_e2e", "sret_abi_e2e",
        "int_ext_abi_e2e",
    )
}
# The linker requirements of a target whose native legs run through GNU ld,
# gold and LLD: each leg asserts the variable is unset before it prints its
# SKIP line for a missing linker, so with it set a missing LLD or gold fails
# the leg itself.
LINKER_REQUIREMENTS = {"TCG_REQUIRE_LLD": "1", "TCG_REQUIRE_GOLD": "1"}
# Environment variables a required target runs with, set for that target's
# own invocation alone; environment_problems() checks each entry against the
# required rows and the variables the target's test file reads.
TARGET_ENVIRONMENT: dict[tuple[str, str], dict[str, str]] = {
    ("trust-cg-codegen", "e2e_aarch64_link_runtime"): LINKER_REQUIREMENTS,
    ("trust-cg-cli", "link_options"): LINKER_REQUIREMENTS,
    ("trust-cg-codegen", "e2e_aarch64_elf_tlsie"): {"TCG_REQUIRE_LLD": "1"},
    ("trust-cg-codegen", "e2e_aarch64_eh_catch"): LINKER_REQUIREMENTS,
    ("trust-cg-codegen", "e2e_aarch64_elf_sections"): {"TCG_REQUIRE_LLD": "1"},
    ("trust-cg-codegen", "aarch64_elf_symbol_binding"): LINKER_REQUIREMENTS,
    ("trust-cg-codegen", "module_local_binding_other_targets"): {"TCG_REQUIRE_LLD": "1"},
    # The three LLD link legs (the rust-lld of the toolchain, else an ld.lld)
    # print SKIP without an LLD unless this is set; the L02-P6 fifth closure
    # audit found the floor ran them unrequired.
    ("trust-cg-codegen", "e2e_aarch64_elf_relocation_model"): {"TCG_REQUIRE_LLD": "1"},
    # Its native rows also compile each LLVM text with llc and compare. The
    # test finds llc through TCG_LLC, PATH, or the sysroot of the compiler
    # that builds it (<sysroot>/lib/rustlib/<host>/bin/llc): a Trust package
    # ships one there. With TCG_REQUIRE_LLC a missing llc fails the leg
    # instead of printing the SKIP line the classifier would fail anyway.
    ("trust-cg-llvm-import", "symbol_linkage_elf"): {**LINKER_REQUIREMENTS, "TCG_REQUIRE_LLC": "1"},
    ("trust-cg-llvm-import", "c_string_escapes_e2e"): {**LINKER_REQUIREMENTS, "TCG_REQUIRE_LLC": "1"},
}
# A variable TARGET_ENVIRONMENT may set: a TCG_REQUIRE_<NAME> requirement.
REQUIREMENT_NAME = re.compile(r"TCG_REQUIRE_[A-Z0-9_]+")


def target_environment(package: str, target: str) -> dict[str, str]:
    """The environment variables required target `package`/`target` is run with."""
    return dict(TARGET_ENVIRONMENT.get((package, target), {}))


def environment_problems(
    rows: Sequence[tuple[str, str]] | None = None, root: Path = ROOT, *, stale_entries: bool = True,
) -> list[str]:
    """Check TARGET_ENVIRONMENT against the required rows and their test files.

    Every entry must name a required row (unless `stale_entries` is false, as
    in the runner's own pre-run check), set only TCG_REQUIRE_<NAME>=1, and
    name only variables the target's test file reads, so a requirement cannot
    outlive the legs it guards.
    """
    rows = TARGETS if rows is None else rows
    problems = []
    for (package, target), environment in sorted(TARGET_ENVIRONMENT.items()):
        if (package, target) not in rows:
            if stale_entries:
                problems.append(f"{package}/{target}: TARGET_ENVIRONMENT entry names no required target")
            continue
        if not isinstance(environment, dict) or not environment:
            problems.append(f"{package}/{target}: environment must be a nonempty mapping")
            continue
        path = root / "crates" / package / "tests" / f"{target}.rs"
        text = path.read_text() if path.is_file() else ""
        for name, value in sorted(environment.items()):
            if not isinstance(name, str) or not REQUIREMENT_NAME.fullmatch(name) or value != "1":
                problems.append(f"{package}/{target}: {name!r}={value!r} is not a TCG_REQUIRE_<NAME>=1 requirement")
            elif f'"{name}"' not in text:
                problems.append(f"{package}/{target}: {name} is not read by {path.relative_to(root)}")
    return problems


# Minimum executed passes for targets whose test census this floor pins; every
# other target needs at least one. Each minimum is the number of tests the
# file compiles on aarch64-unknown-linux-gnu, so a test that disappears behind
# a cfg or is deleted fails the floor. Lowering a minimum or removing an entry
# is a denominator change that needs an explicit, reviewed edit here. (The
# Darwin floor pins a minimum for every row.)
TARGET_MINIMUM_PASSES = {
    # L10-P1 post-allocation value flow: twenty host-neutral tests (the
    # enforced kernels byte-equal to validation off, sixteen corruption
    # controls, three pipeline-wiring tests) and two native C-reference rows;
    # counted from the file on a Darwin host, not yet run on a Linux host.
    ("trust-cg-codegen", "e2e_aarch64_post_ra_value_flow"): 22,
    # L09-P3 composed transition records: eight host-neutral tests and one
    # native C-reference row, counted from the file on a Darwin host; not yet
    # run on a Linux host.
    ("trust-cg-codegen", "e2e_aarch64_composed_transition"): 9,
    # L10-P6 ENC-5 slices and census replay: fourteen host-neutral tests
    # (twelve before the FRINTN dialect row, thirteen before the L03-P9 CRC32
    # row), counted from the file on a Darwin host; not yet run on a Linux
    # host.
    ("trust-cg-codegen", "aarch64_enc5_floor_census"): 14,
    # L10-P5 identity admission: six corruption/stale-counter controls and
    # five property tests, counted from the files on a Darwin host; not yet
    # run on a Linux host.
    ("trust-cg-opt", "mach_id_admission"): 6,
    ("trust-cg-codegen", "mach_id_admission_property"): 5,
    # L07-P2 memory-effect binding: four tests (the native one checks the JIT
    # programs on any AArch64 host and the Mach-O text only on Darwin) and the
    # corpus decomposition's two host-neutral tests; counted from the files on
    # a Darwin host, not yet run on a Linux host.
    ("trust-cg-codegen", "aarch64_memory_effect_binding"): 4,
    # Refined narrow returns (six tests: identical ELF and Mach-O text with and
    # without a refinement, poisoned register bits canonicalized, native C
    # differentials through tests/common/aarch64_native.rs; 6 passed on a
    # Linux host at the 2026-10-14 landing) and LDP formation after a
    # load-acquire (one test outside its macOS-only symbol-alias module;
    # counted from the file on a Darwin host, not yet run on a Linux host).
    ("trust-cg-codegen", "a64_refine_byte_invariance"): 6,
    ("trust-cg-codegen", "aarch64_mem_pair_acquire_order"): 1,
    # Sited assertion delivery: two native tests, both compiled on every
    # AArch64 host; 2 passed on a Linux host on 2026-10-15 (LD-56).
    ("trust-cg-codegen", "sited_assert_delivery_native"): 2,
    # L03-P3 memory-order mapping: four tests compile on
    # aarch64-unknown-linux-gnu (counted from the file on a Darwin host); not
    # yet run on a Linux host.
    ("trust-cg-codegen", "aarch64_memory_order_obligations"): 4,
    ("trust-cg-verify", "aarch64_memory_effect_queries"): 2,
    # L04-P6 NEON silicon differential: eleven tests, every one compiled for
    # aarch64-unknown-linux-gnu; counted from the file on a Darwin host, not
    # yet run on a Linux host.
    ("trust-cg-verify", "aarch64_neon_silicon_differential"): 11,
    # L04-P1 / X-OPCODES-P2 silicon differentials: two and one tests, compiled
    # for aarch64-unknown-linux-gnu; counted from the files on a Darwin host,
    # not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_atomic_silicon_differential"): 2,
    ("trust-cg-verify", "aarch64_scalar_memory_silicon_differential"): 1,
    # L04-P1 CRC32 silicon differential: two tests, compiled for
    # aarch64-unknown-linux-gnu; counted from the file on a Darwin host, not
    # yet run on a Linux host.
    ("trust-cg-verify", "aarch64_crc32_silicon_differential"): 2,
    # L04-P1 SUBS #imm silicon differential: two tests, compiled for
    # aarch64-unknown-linux-gnu; counted from the file on a Darwin host, not
    # yet run on a Linux host.
    ("trust-cg-verify", "aarch64_subs_imm_silicon_differential"): 2,
    # L04-P1 NEON LD1/ST1 form-theorem silicon differential: two tests,
    # compiled for aarch64-unknown-linux-gnu; counted from the file on a
    # Darwin host, not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_neon_structure_silicon_differential"): 2,
    # L04-P6 vector-admission differential: three tests, all compiled for
    # aarch64-unknown-linux-gnu; counted from the file on a Darwin host, not
    # yet run on a Linux host.
    ("trust-cg-codegen", "e2e_aarch64_neon_admission"): 3,
    # L04-P3 scalar FP IEEE 754 differentials: ten and five tests, every one
    # compiled for aarch64-unknown-linux-gnu; counted from the files on a
    # Darwin host, not yet run on a Linux host.
    ("trust-cg-verify", "aarch64_fp_ieee_differential"): 10,
    ("trust-cg-codegen", "e2e_aarch64_fp_ieee_lowering"): 5,
    # L04-P12 trap-expansion binding: four host-neutral tests, counted from
    # the file on a Darwin host; not yet run on a Linux host.
    ("trust-cg-codegen", "aarch64_trap_expansion_binding"): 4,
    # X-LEAN-P3 Lean A64 golden binding: all four host-neutral methods must
    # execute; compiling the target or skipping a method earns no pass.
    ("trust-cg-codegen", "lean_a64_encode_golden_binding"): 4,
    # L07-P2 source-bound memory rows: four tests, the outcome pinned only for
    # the Darwin tool digests measured (any other pair may give either);
    # counted from the file on a Darwin host, not yet run on a Linux host.
    ("trust-cg-codegen", "aarch64_memory_source_binding"): 4,
    # L11-P2 installed-artifact replay: three tests, counted from the file on
    # a Darwin host; not yet run on a Linux host.
    ("trust-cg-codegen", "jit_installed_artifact_replay"): 3,
    # L04-P12 trap-guard obligations: twenty-two tests, counted from the file
    # and run on the Linux AArch64 host (two run encoded functions natively
    # there and skip that leg loudly elsewhere).
    ("trust-cg-verify", "aarch64_trap_guard_obligations"): 22,
    # Static ELF caller/callback binding, relocation controls and call chains.
    ("trust-cg-verify", "aarch64_scalar_cell_link"): 7,
    # L09-P6/L09-P1 whole-body owner: nine tests, counted from the file on a
    # Darwin host; not yet run on a Linux host.
    ("trust-cg-codegen", "aarch64_source_bound_body"): 9,
    # Optimized live effects, native bounds ABI, entry-backedge stack stability,
    # and zero-storage leaves without a frame owner: ELF words equal to Mach-O
    # with no SP use, the owned and select-leaf envelopes kept, the A64 SP
    # decoder, and a native run checking callee-saved state and the unwinder's
    # CFA and return address at every leaf PC, with nine controls.
    ("trust-cg-codegen", "aarch64_live_frame_effects"): 7,
    ("trust-cg-codegen", "aarch64_shrink_wrap_region_exit"): 2,
    ("trust-cg-codegen", "aarch64_nounwind_tail_frame"): 2,
    ("trust-cg-codegen", "aarch64_select_flags_across_call"): 1,
    ("trust-cg-codegen", "aarch64_unroll_trip_test_reader"): 1,
    # Whole-pointee GEP arithmetic at O0-O3, including the interpreter boundary.
    ("trust-cg-codegen", "flat_gep_semantics"): 14,
    ("trust-cg-codegen", "storage_geometry"): 4,
    # L04-P11 switch controls at O0-O3: the dense/sparse and shared-arm
    # boolean legs and the selector-width/strategy matrix (i8-i64 and u8-u64
    # selectors, jump table/binary search/linear chain read back from the
    # code words and by binutils objdump, garbage upper argument bits).
    ("trust-cg-codegen", "e2e_aarch64_switch"): 3,
    # L04-P11 indirect-call controls at O0-O3: the C trampolines and the
    # function-pointer table, switch/call interplay and call-ABI module.
    ("trust-cg-codegen", "e2e_aarch64_indirect_call"): 2,
    # L02-P1/L02-P6 symbol-binding controls: 50 host-neutral object rows and
    # 33 native link-and-run rows (GNU ld, gold and LLD; .dynsym, LD_PRELOAD
    # interposition, IFUNC and weak declarations, the DW.ref slot, hidden
    # thread-locals, weak and COMDAT hidden/protected data and thread-locals,
    # the Pipeline route's TLS anchors, strong hidden/protected data in
    # .data, .bss, .rodata and .data.rel.ro, the visibility cross-product
    # table's shared library, declaration-only and identical-input merges and
    # the data SymbolAddr/stub address forms). 82 before the L02-P13 second
    # closure-audit repair's verifier round (one host-neutral row: the
    # declared-undefined set of ModuleSymbolLinkage through the Pipeline API,
    # written by all three ELF emitters, refused by name when inconsistent
    # and on Mach-O), 81 before the sixth closure
    # audit's host-neutral repeated-declaration row (visibility and linkage
    # pairs through the text, binary and JSON entries), 77 before the fifth
    # closure audit's two host-neutral and two native merge and address-form rows,
    # 70 before the fourth closure audit's six
    # host-neutral and one native visibility-table rows, 67 before the third closure
    # audit's two host-neutral and one native strong-data rows, 64 before the
    # second closure audit's verifier round (one host-neutral and two native
    # thread-local rows), 59 before that audit's two host-neutral and three
    # native rows.
    ("trust-cg-codegen", "aarch64_elf_symbol_binding"): 83,
    # L02-P1 (2026-10-24 closure audit): six host-neutral object rows and
    # four LLD link rows (ld.lld, and ld64.lld for x86-64 Mach-O). 7 before
    # the round-2 verifier's x86-64 Mach-O rows (references spelled `_x`
    # bound to `__x`, LSDA-label collisions refused, the ld64.lld link).
    ("trust-cg-codegen", "module_local_binding_other_targets"): 10,
    # Every Linux row of the AArch64 link runtime, GNU ld, gold and LLD
    # required: 39 at the L02-P2 round-2 repair (2026-10-24), whose native
    # row refuses a static object's default-visibility definitions in a
    # shared object before and after the link; 40 at its round-3 repair,
    # whose native row refuses a direct address of a linker-defined or
    # hidden name that --defsym, --wrap or a linker script exports or
    # redirects; 41 at the r1105 repair (2026-11-05), whose native row
    # refuses a conditional branch (CONDBR19, TSTBR14) to, and a
    # local-dynamic TLS access of, a default-visibility definition in a
    # shared object, which GNU ld and gold bind locally.
    ("trust-cg-codegen", "e2e_aarch64_link_runtime"): 41,
    # L02-P10 link driver: every Linux test of the CLI's link options and
    # staged image checks (the two Darwin ld64 signature rows are compiled
    # out here). 70 before the fifteenth closure audit's native row (LLD
    # links that compile nothing under --lto-partitions installed, what LLD
    # compiles under partitions read or refused). 69 before the fourteenth
    # closure audit's native row (code
    # LLD compiles from a loaded fat object read whatever the inputs are
    # named, with decoys named like LLD's compiled objects). 68 before the
    # thirteenth closure audit's native row (GOT-base
    # code LLD compiles from bitcode read through a ThinLTO cache, a user's
    # obj-path and fat LTO objects, and refused by name when unread), 65
    # before the twelfth closure audit's three native rows (the thread-local
    # template, read and execute permission, and LLVM bitcode through the
    # objects LLD compiles). 71 before the 2026-10-24 L02-P2 closure audit's
    # native row (a --shared link compiles pic; static and pie objects'
    # direct addresses of preemptible symbols refused on every linker), 72
    # before its round-2 native row (static and pie modules' default-visibility
    # definitions refused in a shared link; pic and protected twins run under
    # LD_PRELOAD).
    ("trust-cg-cli", "link_options"): 73,
    # L02-P13 imported symbol facts: 18 host-neutral rows and 13 native GNU
    # ld/gold/LLD rows. 29 before the third closure audit's repair
    # (LD-85): one host-neutral row (the linkage and
    # visibility of every global initializer shape in trust-ir and the
    # object) and one native llc- and gcc-twin row (hidden and protected data
    # of every image shape resisting LD_PRELOAD in a pic shared object).
    # 26 before the fifth round's three rows (integer
    # literals read at their type's width, host-neutral; the same literals
    # linked and run against llc, and static-model dso_local declarations
    # linked and run against llc, native). 25 before the second
    # closure-audit repair's third
    # verifier round: one host-neutral row (dso_local declarations whose
    # address the module's code takes refused by name). 23 before its second
    # verifier round: two host-neutral rows (hidden and protected
    # available_externally globals refused by name; unnamed_addr constants
    # LLVM makes mergeable refused by name in an explicit section). 17
    # before its first verifier
    # round: three host-neutral rows (named sections mixing COMDAT, used and
    # ordinary members in llc's creation order; x86-64 ELF per-global
    # retention, which only a lib unit test pinned; @llvm.used global
    # declarations written as llc's ELF writer writes them and refused by
    # name on Mach-O) and three native llc-twin rows (the walks and
    # constructor order through all three linkers with and without
    # --gc-sections; x86-64 ELF retention under LLD --gc-sections, linked,
    # not run; listed declarations linked and run). 10 before the second
    # closure-audit repair's five
    # host-neutral rows (every importer symbol fact and named refusal through
    # import_text, which the floor's targets did not pin because it runs no
    # lib unit tests; per-global @llvm.used retention; unreferenced
    # declarations; the coverage-mapping section refusal) and two native
    # llc-twin rows (unreferenced hidden/protected declarations under
    # LD_PRELOAD; --gc-sections retention, static/PIE/shared); 8 before the
    # weak-call refusal and weak-call argument rows of the first verifier
    # round.
    ("trust-cg-llvm-import", "symbol_linkage_elf"): 31,
    # L02-P14: two original host-neutral rows and two native Linux rows.
    ("trust-cg-llvm-import", "c_string_escapes_e2e"): 4,
    # L01-P11: two host-neutral rows (the two native rows are macOS-only);
    # counted from the file on a Darwin host, not yet run on a Linux host.
    ("trust-cg-llvm-import", "sret_abi_e2e"): 2,
    # L01-P11 extensions: two host-neutral rows (the two native rows are
    # macOS-only); counted from the file on a Darwin host, not yet run on a
    # Linux host.
    ("trust-cg-llvm-import", "int_ext_abi_e2e"): 2,
    # trust-ir v41 ABI/linkage residue: 18 host-neutral object rows.
    ("trust-cg-codegen", "v41_abi_residue_objects"): 18,
    # L05-P7: the four corpus round-trip tests and the six tMBC/construct
    # property tests, all host-neutral; counted from the files on a Darwin
    # host, not yet run on a Linux host.
    ("trust-cg-codegen", "trust_ir_corpus_roundtrip"): 4,
    ("trust-cg-codegen", "tmbc_roundtrip_prop"): 6,
    # L02-P6 relocation-model controls: 19 host-neutral rows (the three LLD
    # link legs and their lookup row among them) and the two native
    # pic/executable rows.
    ("trust-cg-codegen", "e2e_aarch64_elf_relocation_model"): 21,
    # L13-P7 panic-fuzz families: every proptest property, pinned shrink and
    # case-count probe compiled on this host (panic_fuzz_compile_x86_64's two
    # x86-64-host JIT legs are compiled out).
    ("trust-cg-lower", "panic_fuzz_lower"): 6,
    ("trust-cg-codegen", "panic_fuzz_compile"): 6,
    ("trust-cg-codegen", "panic_fuzz_compile_x86_64"): 3,
    ("trust-cg-codegen", "panic_fuzz_encode"): 12,
    ("trust-cg-codegen", "panic_fuzz_encode_x86_64"): 10,
    ("trust-cg-codegen", "panic_fuzz_macho_fixup"): 15,
    ("trust-cg-verify", "panic_fuzz_verify"): 7,
    # L13-P7 differential JIT harness: every test each file compiles here.
    ("trust-cg-fuzz", "bridge_diff"): 23,
    ("trust-cg-fuzz", "cross_call_value_preserved"): 2,
    ("trust-cg-fuzz", "ctpop_narrow"): 2,
    ("trust-cg-fuzz", "dense_switch_blockarg_encode"): 2,
    ("trust-cg-fuzz", "dense_switch_encode"): 1,
    ("trust-cg-fuzz", "diff_cmp_overflow"): 8,
    ("trust-cg-fuzz", "diff_int_divrem"): 1,
    ("trust-cg-fuzz", "diff_narrow_int"): 2,
    ("trust-cg-fuzz", "driver_output"): 6,
    ("trust-cg-fuzz", "fp_const_and_fcmp"): 2,
    ("trust-cg-fuzz", "generator_config"): 2,
    ("trust-cg-fuzz", "jit_call_crossing_pressure_diff"): 8,
    ("trust-cg-fuzz", "jit_diff_catches_miscompile"): 10,
    ("trust-cg-fuzz", "jit_diff_consumer_shapes"): 1,
    ("trust-cg-fuzz", "jump_table_in_loop"): 1,
    ("trust-cg-fuzz", "sweep2_bitops"): 8,
    ("trust-cg-fuzz", "sweep2_chained_casts"): 8,
    ("trust-cg-fuzz", "sweep2_i128"): 7,
    ("trust-cg-fuzz", "sweep2_large_pressure"): 5,
    ("trust-cg-fuzz", "sweep3_cmp_branch_fusion"): 14,
    ("trust-cg-fuzz", "sweep3_mem_aliasing"): 24,
    ("trust-cg-fuzz", "sweep3_nested_calls_pressure"): 7,
    ("trust-cg-fuzz", "sweep3_select_switch_calls"): 13,
    ("trust-cg-fuzz", "sweep3_wide_shifts_bitops"): 39,
    ("trust-cg-fuzz", "vector_v128_load_store_lane"): 1,
    ("trust-cg-fuzz", "verify_narrow_int_0"): 1,
    ("trust-cg-fuzz", "verify_narrow_int_1"): 1,
    ("trust-cg-fuzz", "verify_narrow_int_2"): 1,
    # L03-P13 EH relocation inventory: the mirror-equals-object matrix, the
    # COMDAT (shared section name)/local-personality matrix, the slot-named
    # data section, the shared reserved-section refusal, the rows-less
    # report, the row cross-check's mutants, the Darwin and
    # unenumerated-shape refusals, the certified-compile EH refusal, the
    # census-matches-the-object matrix (x86-64 walk-through filler tables),
    # the census-before-inventory order, the trusted-unwind disclosure and
    # the malformed-structure diagnostic under certificates.
    ("trust-cg-codegen", "aarch64_elf_eh_relocation_inventory"): 13,
}
# A test function attribute, counted the way the Darwin floor counts them.
TEST_ATTRIBUTE = re.compile(r"#\[(?:tokio::)?test\]|#\[cfg_attr\([^\[\]]*?,\s*test\s*\)\]")
# A file-level feature gate in its simple form: `#![cfg(feature = "name")]`.
FILE_FEATURE_GATE = re.compile(r'^#!\[cfg\(\s*feature\s*=\s*"([^"]+)"\s*\)\]', re.MULTILINE)
# A Cargo feature name as `--features` accepts it.
FEATURE_NAME = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_+.-]*")


def target_features(package: str, target: str) -> tuple[str, ...]:
    """The Cargo features required target `package`/`target` is built with."""
    return tuple(TARGET_FEATURES.get((package, target), ()))


def target_minimum_passes(package: str, target: str) -> int:
    """The executed passes required target `package`/`target` must report."""
    return TARGET_MINIMUM_PASSES.get((package, target), 1)


def minimum_problems(
    rows: Sequence[tuple[str, str]] | None = None, root: Path = ROOT, *, stale_entries: bool = True,
) -> list[str]:
    """Check TARGET_MINIMUM_PASSES against the required rows and their files.

    With `stale_entries` false (the runner's own pre-run check) an entry naming
    no required row is ignored instead of reported; the inventory tests keep
    reporting it.
    """
    rows = TARGETS if rows is None else rows
    problems = []
    for (package, target), minimum in sorted(TARGET_MINIMUM_PASSES.items()):
        if (package, target) not in rows:
            if stale_entries:
                problems.append(f"{package}/{target}: TARGET_MINIMUM_PASSES entry names no required target")
            continue
        if type(minimum) is not int or minimum < 1:
            problems.append(f"{package}/{target}: minimum must be a positive integer")
            continue
        path = root / "crates" / package / "tests" / f"{target}.rs"
        if not path.is_file():
            problems.append(f"{package}/{target}: missing test file for its minimum")
        elif len(TEST_ATTRIBUTE.findall(path.read_text())) < minimum:
            problems.append(f"{package}/{target}: minimum {minimum} exceeds its #[test] functions")
    return problems


def feature_arguments(package: str, target: str) -> list[str]:
    """`--features a,b` for a feature-gated target, nothing otherwise."""
    features = target_features(package, target)
    return ["--features", ",".join(features)] if features else []


def package_features(package: str, root: Path = ROOT) -> dict[str, tuple[str, ...]]:
    """The `[features]` table of crates/<package>/Cargo.toml: name -> entries.

    A deliberately small reader for flat `name = ["a", "b"]` entries (single-
    or multi-line), so this module keeps running on interpreters without
    tomllib; the Darwin floor loads it too.
    """
    manifest = root / "crates" / package / "Cargo.toml"
    if not manifest.is_file():
        return {}
    text = manifest.read_text()
    table = re.search(r"^\[features\][^\n]*\n(.*?)(?=^\[|\Z)", text, re.MULTILINE | re.DOTALL)
    if table is None:
        return {}
    body = re.sub(r"#[^\n]*", "", table.group(1))
    return {
        name: tuple(re.findall(r'"([^"]*)"', entries))
        for name, entries in re.findall(r"^\s*([A-Za-z0-9_][A-Za-z0-9_+.-]*)\s*=\s*\[(.*?)\]", body, re.MULTILINE | re.DOTALL)
    }


def enabled_features(package: str, requested: Sequence[str], root: Path = ROOT) -> set[str]:
    """Package features enabled by `requested` plus `default`, transitively."""
    table = package_features(package, root)
    enabled: set[str] = set()
    pending = ["default", *requested]
    while pending:
        feature = pending.pop()
        if feature in enabled or feature not in table:
            continue
        enabled.add(feature)
        pending.extend(entry for entry in table[feature] if "/" not in entry and not entry.startswith("dep:"))
    return enabled


def feature_problems(
    rows: Sequence[tuple[str, str]] | None = None, root: Path = ROOT, *, stale_entries: bool = True,
) -> list[str]:
    """Check TARGET_FEATURES against the required rows and their test files.

    With `stale_entries` false (the runner's own pre-run check) an entry naming
    no required row is ignored instead of reported; the inventory tests keep
    reporting it.
    """
    rows = TARGETS if rows is None else rows
    problems = []
    for (package, target), features in sorted(TARGET_FEATURES.items()):
        if (package, target) not in rows:
            if stale_entries:
                problems.append(f"{package}/{target}: TARGET_FEATURES entry names no required target")
            continue
        if (
            not isinstance(features, tuple) or not features
            or len(set(features)) != len(features)
            or not all(isinstance(feature, str) and FEATURE_NAME.fullmatch(feature) for feature in features)
        ):
            problems.append(f"{package}/{target}: features must be a nonempty tuple of distinct feature names")
            continue
        undeclared = sorted(set(features) - set(package_features(package, root)))
        if undeclared:
            problems.append(f"{package}/{target}: features {undeclared} are not declared by {package}")
    for package, target in rows:
        path = root / "crates" / package / "tests" / f"{target}.rs"
        if not path.is_file():
            continue
        gated = set(FILE_FEATURE_GATE.findall(path.read_text()))
        if not gated:
            continue
        missing = sorted(gated - enabled_features(package, target_features(package, target), root))
        if missing:
            problems.append(
                f"{package}/{target}: file-level cfg(feature) {missing} is neither a default feature "
                "nor in TARGET_FEATURES, so Cargo would build an empty suite"
            )
    return problems


def decided_absent_problems() -> list[str]:
    """Name every DECIDED_ABSENT row that overlaps TARGETS or has no test file."""
    problems = []
    required = set(TARGETS)
    for package, target, decision, _reason in DECIDED_ABSENT:
        if (package, target) in required:
            problems.append(
                f"decided-absent target {package}/{target} ({decision}) is also a required target"
            )
        source = ROOT / "crates" / package / "tests" / f"{target}.rs"
        if not source.is_file():
            problems.append(
                f"decided-absent target {package}/{target} ({decision}) has no test file at {source}"
            )
    return problems


def decided_absent_records() -> list[dict]:
    """The DECIDED_ABSENT rows as report.json records them."""
    return [
        {"package": package, "target": target, "decision": decision, "reason": reason}
        for package, target, decision, reason in DECIDED_ABSENT
    ]


def print_decided_absent(stream) -> None:
    """Print one refusal line per decided-absent row, before and after the run."""
    for package, target, decision, reason in DECIDED_ABSENT:
        print(
            f"{FLOOR_NAME} regression floor: decided absent, not run: {package}/{target} "
            f"({decision}): {reason}",
            file=stream,
        )


SUMMARY = re.compile(
    r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; "
    r"(\d+) ignored; (\d+) measured; (\d+) filtered out;[^\n]*$",
    re.MULTILINE,
)
START = re.compile(r"^running (\d+) tests?\s*$", re.MULTILINE)
SKIP = re.compile(
    r"(?:^|\.\.\.\s*|\[)\s*(?:skip|skipped|skipping)\b", re.MULTILINE | re.IGNORECASE
)
# trust-cg-verify's opcode evidence inventory renders each pseudo/trap row as
# "  [skip    ] <isa>::<opcode> <pad> pseudo/trap — no equivalence proof
# obligation" (OpcodeClass::PseudoOrTrap in coverage_gate.rs). That label is a
# static classification of an opcode that has no value obligation, not a test
# that skipped execution. Only a complete line of exactly that shape is exempt;
# "[SKIP]", "[skip]" with any other text, and every other skip spelling still
# fail the target.
INVENTORY_SKIP_LABEL = re.compile(
    r"  \[skip    \] [A-Za-z_][A-Za-z0-9_]*::[A-Za-z_][A-Za-z0-9_]* +"
    "pseudo/trap — no equivalence proof obligation"
)


def skip_lines(transcript: str) -> tuple[list[str], int]:
    """Return runtime-skip lines and the number of exempt inventory labels."""
    skipped = []
    inventory_labels = 0
    for line in transcript.splitlines():
        if INVENTORY_SKIP_LABEL.fullmatch(line):
            inventory_labels += 1
        elif SKIP.search(line):
            skipped.append(line)
    return skipped, inventory_labels


def classify_result(returncode: int, transcript: str, minimum: int = 1) -> dict:
    """Require one nonempty, complete integration suite and no skipped leg.

    The suite must report at least `minimum` (and always at least one)
    executed passes.
    """
    errors = []
    required = max(minimum, 1)
    summaries = list(SUMMARY.finditer(transcript))
    starts = list(START.finditer(transcript))
    counts = None
    if returncode != 0:
        errors.append(f"command exited {returncode}")
    skipped, inventory_labels = skip_lines(transcript)
    if skipped:
        errors.append(f"explicit skipped execution in transcript: {skipped[0].strip()[:200]}")
    if len(summaries) != 1 or len(starts) != 1:
        errors.append("expected exactly one started and completed test suite")
    if len(summaries) == 1:
        summary = summaries[0]
        counts = dict(zip(
            ("passed", "failed", "ignored", "measured", "filtered"),
            map(int, summary.groups()[1:]),
        ))
        if summary.group(1) != "ok" or counts["passed"] <= 0:
            errors.append("test suite did not report positive passing execution")
        elif counts["passed"] < required:
            errors.append(f"executed passes {counts['passed']} are below the required minimum {required}")
        if any(counts[key] != 0 for key in ("failed", "ignored", "measured", "filtered")):
            errors.append("failed, ignored, measured or filtered tests are not permitted")
        if len(starts) == 1:
            if int(starts[0].group(1)) != counts["passed"]:
                errors.append("started test count does not match passing test count")
            if starts[0].start() >= summary.start():
                errors.append("suite completion precedes its start")
    return {
        "status": "fail" if errors else "pass", "counts": counts, "errors": errors,
        "inventory_skip_labels": inventory_labels, "minimum": required,
    }


def positive_seconds(value: str) -> float:
    try:
        seconds = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a positive finite duration") from error
    if not math.isfinite(seconds) or seconds <= 0:
        raise argparse.ArgumentTypeError("expected a positive finite duration")
    return seconds


def positive_jobs(value: str) -> int:
    try:
        jobs = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a positive job count") from error
    if jobs <= 0:
        raise argparse.ArgumentTypeError("expected a positive job count")
    return jobs


def positive_gib(value: str) -> float:
    try:
        gib = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a positive finite GiB ceiling") from error
    if not math.isfinite(gib) or gib <= 0:
        raise argparse.ArgumentTypeError("expected a positive finite GiB ceiling")
    return gib


def timeout_runner_module():
    """Load the shared runner so the host-support rule has one source."""
    spec = importlib.util.spec_from_file_location("_linux_aarch64_timeout_runner", TIMEOUT_RUNNER)
    if spec is None or spec.loader is None or not TIMEOUT_RUNNER.is_file():
        raise RuntimeError(f"required timeout runner is missing: {TIMEOUT_RUNNER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@functools.cache
def cargo_config_auditor():
    """Load the shared Cargo config audit (scripts/cargo_config_audit.py)."""
    spec = importlib.util.spec_from_file_location("_aarch64_cargo_config_audit", CARGO_CONFIG_AUDIT)
    if spec is None or spec.loader is None or not CARGO_CONFIG_AUDIT.is_file():
        raise RuntimeError(f"required Cargo config audit is missing: {CARGO_CONFIG_AUDIT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def cargo_config_record(
    git: str = "git", environment: dict | None = None, tool: str = TRUST_BUILD_TOOL, cwd: Path = ROOT,
) -> dict:
    """Every Cargo config path and config variable the targets' build tool
    `tool` reads from `cwd`, audited.

    `cwd` is the directory the build tool will run in: ROOT for the root
    workspace, BRIDGE_DIR for a bridge target. The ancestor walk starts there,
    so a config the bridge workspace holds of its own is audited too, and the
    repository's committed root config stays exempt in either walk.
    """
    auditor = cargo_config_auditor()
    return auditor.audit(
        cwd, os.environ if environment is None else environment, auditor.committed_config(ROOT, git), tool,
    )


def selected_build_tool() -> str:
    """The build tool this run will invoke, found on PATH without running it."""
    found = shutil.which(TRUST_BUILD_TOOL)
    if found is None:
        raise RuntimeError(f"required tool is missing: {TRUST_BUILD_TOOL}")
    return found


def dependency_recorder():
    """Load the shared recorder so both AArch64 floors record identities one way."""
    spec = importlib.util.spec_from_file_location("_aarch64_dependency_identity", DEPENDENCY_RECORDER)
    if spec is None or spec.loader is None or not DEPENDENCY_RECORDER.is_file():
        raise RuntimeError(f"required dependency identity recorder is missing: {DEPENDENCY_RECORDER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def dependency_identity(git: str, environment: dict | None = None) -> dict:
    """Record the Git dependencies the root Cargo.lock resolves in Cargo's home."""
    recorder = dependency_recorder()
    cargo_home, origin = recorder.cargo_home_from(os.environ if environment is None else environment, ROOT)
    return recorder.collect(ROOT / "Cargo.lock", cargo_home, git=git, cargo_home_source=origin)


def proof_tool_resolver():
    """Load the release-gate resolver so every AArch64 lane names AY/Clean one way."""
    spec = importlib.util.spec_from_file_location("_aarch64_proof_tool_resolver", PROOF_TOOL_RESOLVER)
    if spec is None or spec.loader is None or not PROOF_TOOL_RESOLVER.is_file():
        raise RuntimeError(f"required proof-tool resolver is missing: {PROOF_TOOL_RESOLVER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def executable_digest(path: Path) -> dict:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return {"sha256": digest.hexdigest(), "bytes": path.stat().st_size}


def proof_tool_identities(environment: dict | None = None) -> dict:
    """Resolve AY and Clean as the verifier's child processes will, and bind their bytes.

    The record is identity only. For AY the pinned routes are an absolute
    AY_SOLVER_PATH and the build toolchain's bin/ay (nothing else is
    consulted); for Clean an explicit override or an aterm-style package prefix
    on PATH. An absent or unpinned tool is reported so that a proof-replay
    failure can be attributed to provisioning rather than to the compiler.
    """
    resolver = proof_tool_resolver()
    environ = dict(os.environ if environment is None else environment)
    record = {}
    for tool in PROOF_TOOLS:
        try:
            # Finding AY asks the build compiler for its sysroot. Clean's
            # runtime selection is not a compiler/codegen option; Trust rejects
            # such TCG_* variables even on a --print sysroot probe.
            compiler_environ = {k: v for k, v in environ.items()
                                if k not in RUNTIME_CHECKER_ENVIRONMENT}
            found = resolver.resolve_tool(tool, HOST, compiler_environ if tool == "ay" else environ, sys.platform)
        except resolver.ResolveError as error:
            record[tool] = {"resolved": None, "route": None, "pinned": False, "error": str(error)}
            continue
        if found is None:
            record[tool] = {"resolved": None, "route": None, "pinned": False}
            continue
        path, route = found
        record[tool] = {
            "resolved": str(path), "route": route,
            "pinned": resolver.route_pinning(route) == "pinned", **executable_digest(path),
        }
    return record


def proof_tool_problems(record: dict) -> list[str]:
    """Name every tool that is absent, broken or resolved only through an unpinned route."""
    problems = []
    for tool in PROOF_TOOLS:
        entry = record.get(tool) or {}
        if entry.get("error"):
            problems.append(f"{tool}: {entry['error']}")
        elif entry.get("resolved") is None:
            problems.append(
                f"{tool}: no executable resolves ("
                + ("build with a Trust toolchain that ships its bin/ay, or set an absolute AY_SOLVER_PATH "
                   "to a byte copy of it" if tool == "ay" else
                   "set an explicit override or put an aterm-style package prefix's bin directory on PATH")
                + ")"
            )
        elif not entry.get("pinned"):
            problems.append(f"{tool}: only the unpinned route {entry['route']} resolves ({entry['resolved']})")
    return problems


def proof_tool_changes(before: dict, after: dict) -> list[str]:
    return [
        f"{tool}: {json.dumps(before.get(tool), sort_keys=True)} -> {json.dumps(after.get(tool), sort_keys=True)}"
        for tool in PROOF_TOOLS
        if (before.get(tool) or {}) != (after.get(tool) or {})
    ]


@functools.cache
def ay_admission_runner():
    """Load the AOT runner's admission check so every lane asks the CLI one way."""
    spec = importlib.util.spec_from_file_location("_floor_ay_admission", AY_ADMISSION_RUNNER)
    if spec is None or spec.loader is None or not AY_ADMISSION_RUNNER.is_file():
        raise RuntimeError(f"required AY admission check is missing: {AY_ADMISSION_RUNNER}")
    module = importlib.util.module_from_spec(spec)
    # Registered before it runs: its dataclasses resolve their module by name.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def built_executable(messages: str, binary: str) -> str | None:
    """The executable Cargo's JSON messages report for bin target `binary`."""
    found = None
    for line in messages.splitlines():
        try:
            message = json.loads(line)
        except ValueError:
            continue
        if not isinstance(message, dict):
            continue
        target = message.get("target")
        if (message.get("reason") == "compiler-artifact" and isinstance(target, dict)
                and target.get("name") == binary and "bin" in (target.get("kind") or [])
                and isinstance(message.get("executable"), str)):
            found = message["executable"]
    return found


def ay_admission_preflight(
    provenance: dict, ay: dict, output: Path, *, jobs: int, offline: bool,
    timeout_seconds: float, max_rss_gib: float | None,
) -> tuple[dict, list[str]]:
    """Have the real AY identity rule admit the resolved AY where the targets will run.

    A pinned route only NAMES an AY. The rule (crates/trust-cg-verify/src/
    ay_identity.rs) admits it by the digest compiled into the build, then
    copies it into `<cache>/trust-cg/ay-exec` and refuses any ancestor of that
    directory others may write. An AY can therefore resolve and still never
    run: a group-writable `<cache>/trust-cg`, which `create_dir_all` made
    under umask 0002, refused it in every process, and each proof-replay
    target then failed as if it were a proof gap. This builds the CLI with the
    floor's own build command and runs `trust-cg --print-ay-identity` (it
    executes no AY) in the targets' runtime environment, through
    `ay_admission` of scripts/check_aarch64_aot_arithmetic.py: the admitted
    path and digest must be the resolved AY's, and the private copy must exist
    and pass, by its canonical path, the private-cache rule (every canonical
    ancestor renamable by nobody else); that canonical path is recorded as
    `exec_canonical`.
    """
    record: dict = {"package": AY_ADMISSION_PACKAGE, "binary": AY_ADMISSION_BINARY}
    command = [
        *target_build_command(provenance, RUNTIME_CHECKER_ENVIRONMENT),
        "build", "--locked", *(["--offline"] if offline else []), "--color", "never",
        "-j", str(jobs), "-p", AY_ADMISSION_PACKAGE, "--bin", AY_ADMISSION_BINARY,
        "--message-format", "json-render-diagnostics",
    ]
    log, messages = output / "ay-admission-build.log", output / "ay-admission-build.json"
    build = run_bounded(command, log, timeout_seconds, max_rss_gib=max_rss_gib, stdout_path=messages)
    record["build"] = {"command": command, "log": log.name, "returncode": build["returncode"]}
    if build["returncode"] != 0 or build["interrupted_signal"] is not None:
        return record, [f"AY admission: building {AY_ADMISSION_PACKAGE} to ask the AY identity rule failed "
                        f"(exit {build['returncode']}; see {log.name})"]
    executable = built_executable(messages.read_text(encoding="utf-8", errors="replace"), AY_ADMISSION_BINARY)
    record["executable"] = executable
    if executable is None:
        return record, [f"AY admission: Cargo reported no {AY_ADMISSION_BINARY} executable (see {messages.name})"]
    environment = {name: value for name, value in os.environ.items()
                   if name not in scrubbed_environment(os.environ)}
    admission, problems = ay_admission_runner().ay_admission(executable, ay, environment)
    record["admission"] = admission
    record["admitted"] = not problems
    return record, [f"AY admission: {problem}" for problem in problems]


def rss_supervision(max_rss_gib: float | None) -> str:
    """Name the enforced resident-set supervision, or "unsupported"."""
    if max_rss_gib is None:
        return "not-requested"
    return timeout_runner_module().rss_supervision_support() or "unsupported"


# Must equal run_with_timeout.RSS_RECEIPT; the gate tests pin the two together.
RSS_RECEIPT_PREFIX = "run_with_timeout: RSS_RECEIPT"
RSS_RECEIPT_LINE = re.compile(
    re.escape(RSS_RECEIPT_PREFIX)
    + r" ceiling_gib=(\S+) peak_mib=(\d+) samples=(\d+) outcome=(within|exceeded|unmeasurable)"
)


def rss_receipt(transcript: str, max_rss_gib: float) -> tuple[dict | None, list[str]]:
    """Require the runner's single resident-set receipt for the requested ceiling."""
    lines = [line for line in transcript.splitlines() if line.startswith(RSS_RECEIPT_PREFIX)]
    if len(lines) != 1:
        return None, [f"expected exactly one resident-set supervision receipt, observed {len(lines)}"]
    match = RSS_RECEIPT_LINE.fullmatch(lines[0])
    if match is None:
        return None, ["malformed resident-set supervision receipt"]
    try:
        ceiling = float(match.group(1))
    except ValueError:
        return None, ["malformed resident-set supervision receipt"]
    receipt = {
        "ceiling_gib": ceiling, "sampled_peak_mib": int(match.group(2)),
        "samples": int(match.group(3)), "outcome": match.group(4),
    }
    errors = []
    if not math.isclose(ceiling, max_rss_gib, rel_tol=1e-5):
        errors.append(f"resident-set receipt ceiling {ceiling:g} GiB differs from requested {max_rss_gib:g} GiB")
    if receipt["outcome"] != "within":
        errors.append(f"resident-set ceiling {max_rss_gib:g} GiB {receipt['outcome']}")
    elif receipt["samples"] == 0:
        # The runner samples before its first wait, so a within receipt without
        # a single sample records no supervision at all.
        errors.append("resident-set receipt records no sample; the ceiling was never observed")
    elif receipt["sampled_peak_mib"] > max_rss_gib * 1024:
        errors.append("resident-set receipt reports a peak above its ceiling as within")
    return receipt, errors


def run_target(
    command: Sequence[str], log_path: Path, timeout_seconds: float,
    *, root: Path = ROOT, grace_seconds: float = 5,
    unset_environment: Sequence[str] = (), max_rss_gib: float | None = None,
    set_environment: dict[str, str] | None = None,
    minimum: int = 1, required_lines: Sequence[str] = (),
) -> dict:
    """Run a real process through the shared process-group timeout boundary.

    `unset_environment` and every scrubbed variable are removed from the
    inherited environment, then `set_environment` is set over it. Each of
    `required_lines` must appear as a complete transcript line.
    """
    started = time.monotonic()
    run = run_bounded(
        command, log_path, timeout_seconds, root=root, grace_seconds=grace_seconds,
        unset_environment=unset_environment, max_rss_gib=max_rss_gib, set_environment=set_environment,
    )
    bounded, returncode = run["bounded_command"], run["returncode"]
    interrupted_signal, scrubbed = run["interrupted_signal"], run["scrubbed_environment"]
    data = log_path.read_bytes()
    transcript = data.decode("utf-8", errors="replace")
    verdict = classify_result(returncode, transcript, minimum)
    for line in required_lines:
        if not transcript_has_line(transcript, line):
            verdict["errors"].append(f"required transcript line is missing: {line!r}")
            verdict["status"] = "fail"
    if interrupted_signal is not None:
        verdict["errors"].append(f"interrupted by signal {interrupted_signal}")
        verdict["status"] = "fail"
    receipt = None
    if max_rss_gib is not None:
        receipt, receipt_errors = rss_receipt(transcript, max_rss_gib)
        if receipt_errors:
            verdict["errors"].extend(receipt_errors)
            verdict["status"] = "fail"
    return {
        "command": list(command), "bounded_command": bounded, "cwd": str(root),
        "timeout_seconds": timeout_seconds, "elapsed_seconds": time.monotonic() - started,
        "max_rss_gib": max_rss_gib, "rss": receipt,
        "returncode": returncode, "log": log_path.name,
        "interrupted_signal": interrupted_signal,
        "unset_environment": list(unset_environment), "scrubbed_environment": scrubbed,
        "required_lines": list(required_lines),
        "set_environment": dict(set_environment or {}),
        "log_sha256": hashlib.sha256(data).hexdigest(), **verdict,
    }


def run_bounded(
    command: Sequence[str], log_path: Path, timeout_seconds: float,
    *, root: Path = ROOT, grace_seconds: float = 5,
    unset_environment: Sequence[str] = (), max_rss_gib: float | None = None,
    set_environment: dict[str, str] | None = None, stdout_path: Path | None = None,
) -> dict:
    """Run `command` under the timeout supervisor with the targets' environment.

    Its output goes to the new file `log_path`; with `stdout_path`, standard
    output goes to that new file instead and standard error stays in the log.
    Returns the bounded command, its exit status, a forwarded interrupt and the
    scrubbed variable names.
    """
    ceiling = [] if max_rss_gib is None else ["--max-rss-gib", repr(max_rss_gib)]
    bounded = [
        sys.executable, str(TIMEOUT_RUNNER), "--grace-seconds", str(grace_seconds),
        *ceiling, str(timeout_seconds), *command,
    ]
    environment = os.environ.copy()
    scrubbed = scrubbed_environment(environment)
    for name in (*unset_environment, *scrubbed):
        environment.pop(name, None)
    environment.update(set_environment or {})
    process = None
    interrupted_signal = None

    def forward(signum: int, _frame: object) -> None:
        nonlocal interrupted_signal
        if interrupted_signal is None:
            interrupted_signal = signum
        if process is not None:
            try:
                process.send_signal(signum)
            except ProcessLookupError:
                pass

    previous_handlers = {}
    with contextlib.ExitStack() as files:
        log = files.enter_context(log_path.open("x", encoding="utf-8"))
        stdout = log if stdout_path is None else files.enter_context(stdout_path.open("x", encoding="utf-8"))
        try:
            # subprocess.run kills its immediate child on KeyboardInterrupt,
            # which would destroy the timeout supervisor before it can clean
            # up the command's separate process group. Forward cancellation
            # and let the bounded supervisor finish that cleanup instead.
            for signum in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
                previous_handlers[signum] = signal.signal(signum, forward)
            process = subprocess.Popen(
                bounded, cwd=root, stdout=stdout,
                stderr=subprocess.STDOUT if stdout_path is None else log,
                start_new_session=True, env=environment,
            )
            if interrupted_signal is not None:
                forward(interrupted_signal, None)
            returncode = process.wait()
        except OSError as error:
            log.write(f"{FLOOR_NAME} gate launch error: {error}\n")
            returncode = 125
        finally:
            for signum, handler in previous_handlers.items():
                signal.signal(signum, handler)
    return {
        "bounded_command": bounded, "returncode": returncode,
        "interrupted_signal": interrupted_signal, "scrubbed_environment": scrubbed,
    }


def probe(command: Sequence[str]) -> str:
    result = subprocess.run(
        command, cwd=ROOT, capture_output=True, text=True, timeout=20, check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(f"probe {list(command)!r} exited {result.returncode}: {result.stderr.strip()}")
    return result.stdout.strip()


def source_provenance(git: str) -> dict:
    source_root = probe([git, "rev-parse", "--show-toplevel"])
    if Path(source_root).resolve() != ROOT:
        raise RuntimeError(f"Git environment selects another source tree: {source_root}")
    # HEAD plus a complete binary tracked diff and content hashes of every
    # nonignored untracked file identify new source files as well as edits.
    # Hash symlink text, never the external file it might point at.
    def git_bytes(*args: str) -> bytes:
        result = subprocess.run([git, *args], cwd=ROOT, capture_output=True, timeout=20, check=False)
        if result.returncode:
            raise RuntimeError(f"Git source inventory failed: {result.stderr.decode(errors='replace')}")
        return result.stdout

    # Keep porcelain lines verbatim: stripping the output would turn the first
    # " M" (unstaged) entry into "M" (staged).
    status = git_bytes("status", "--porcelain=v1", "--untracked-files=normal").decode("utf-8", errors="replace")

    diff = git_bytes("diff", "--binary", "--no-ext-diff", "--no-textconv", "HEAD", "--")
    untracked = []
    for raw_name in sorted(git_bytes("ls-files", "--others", "--exclude-standard", "-z").split(b"\0")):
        if not raw_name:
            continue
        name = os.fsdecode(raw_name)
        path = ROOT / name
        before = path.lstat()
        digest = hashlib.sha256()
        if stat.S_ISLNK(before.st_mode):
            kind = "symlink"
            digest.update(os.fsencode(os.readlink(path)))
        elif stat.S_ISREG(before.st_mode):
            kind = "file"
            with path.open("rb") as source:
                for chunk in iter(lambda: source.read(1024 * 1024), b""):
                    digest.update(chunk)
        else:
            raise RuntimeError(f"unsupported untracked source file kind: {name}")
        after = path.lstat()
        identity = lambda info: (info.st_ino, info.st_size, info.st_mode, info.st_mtime_ns, info.st_ctime_ns)
        if identity(before) != identity(after):
            raise RuntimeError(f"untracked source changed during hashing: {name}")
        untracked.append({
            "path": name, "kind": kind, "mode": stat.S_IMODE(before.st_mode),
            "sha256": digest.hexdigest(),
        })
    # Cargo reads .cargo/config and .cargo/config.toml whatever Git thinks of
    # them, but git status lists no FIFO, socket or device and no ignored
    # file. Every entry of .cargo that Git neither tracks nor lists above is
    # untracked source here too, named with its kind.
    listed = {entry["path"] for entry in untracked}
    tracked_cargo = {
        os.fsdecode(name) for name in git_bytes("ls-files", "-z", "--", CARGO_CONFIG_DIRECTORY).split(b"\0") if name
    }
    unlisted = []
    cargo_directory = ROOT / CARGO_CONFIG_DIRECTORY
    if os.path.lexists(cargo_directory):
        info = cargo_directory.lstat()
        entries = ([(CARGO_CONFIG_DIRECTORY, info)] if not stat.S_ISDIR(info.st_mode) else [
            (f"{CARGO_CONFIG_DIRECTORY}/{entry.name}", entry.stat(follow_symlinks=False))
            for entry in os.scandir(cargo_directory)
        ])
        for name, entry_info in sorted(entries, key=lambda row: row[0]):
            if name in tracked_cargo or name in listed:
                continue
            unlisted.append({"path": name, "kind": cargo_config_auditor().file_kind(entry_info.st_mode)})
    status_lines = status.splitlines() + [
        f"!! {entry['path']} ({entry['kind']}, not listed by git status)" for entry in unlisted
    ]
    state = {
        "source_sha": probe([git, "rev-parse", "HEAD"]), "source_root": source_root,
        "dirty": bool(status_lines), "git_status": status_lines,
        "tracked_diff_sha256": hashlib.sha256(diff).hexdigest(),
        "untracked_files": untracked, "unlisted_cargo_config_entries": unlisted,
    }
    state["source_fingerprint"] = hashlib.sha256(
        json.dumps(state, sort_keys=True).encode("utf-8")
    ).hexdigest()
    return state


def _trust_toolchain_module():
    spec = importlib.util.spec_from_file_location(
        "_linux_aarch64_trust_toolchain", ROOT / "scripts" / "trust_toolchain.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def trust_development_toolchain() -> dict:
    """Bind a development build to one real Trust package, without a shim."""
    tools = {}
    launcher_target = _trust_toolchain_module().launcher_target
    for name in ("trustc", "trustdoc", "targo", "env"):
        found = shutil.which(name)
        if found is None:
            raise RuntimeError(f"required Trust development tool is missing: {name}")
        path = Path(found).resolve(strict=True)
        # An atpkg launcher shim is followed to the package file it execs
        # (scripts/trust_toolchain.py); any other wrapper stays refused below.
        target = launcher_target(path) if name != "env" else None
        if target is not None:
            path = target.resolve(strict=True)
        if not path.is_file() or not os.access(path, os.X_OK):
            raise RuntimeError(f"Trust development tool is not executable: {path}")
        tools[name] = str(path)
    package_bin = Path(tools["trustc"]).parent
    if any(Path(tools[name]).parent != package_bin for name in ("trustdoc", "targo")):
        raise RuntimeError("trustc, trustdoc and targo must resolve to the same package")
    wrappers = (
        "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    )
    if any(os.environ.get(name) for name in wrappers):
        raise RuntimeError("Trust development compilation requires the selected compiler without wrappers")
    compiler_prefix = [tools["env"], *(argument for name in RUNTIME_CHECKER_ENVIRONMENT
                                     for argument in ("-u", name))]
    rustc = probe([*compiler_prefix, tools["trustc"], "-vV"])
    if not re.search(r"^binary: trustc$", rustc, re.MULTILINE):
        raise RuntimeError("Trust development compilation requires the branded trustc driver")
    if not re.search(r"^commit-hash: [0-9a-f]{40}$", rustc, re.MULTILINE):
        raise RuntimeError("Trust compiler did not provide a commit identity")
    sysroot = Path(probe([*compiler_prefix, tools["trustc"], "--print", "sysroot"])).resolve(strict=True)
    if sysroot != package_bin.parent:
        raise RuntimeError("Trust compiler/sysroot package mismatch")
    if not (sysroot / "lib/rustlib" / HOST / "lib").is_dir():
        raise RuntimeError("Trust package lacks the native target libraries")
    environment = {
        "RUSTC": tools["trustc"], "RUSTDOC": tools["trustdoc"],
        "PATH": str(package_bin) + os.pathsep + os.environ.get("PATH", ""),
    }
    command = [*compiler_prefix, *(f"{k}={v}" for k, v in environment.items()),
               tools["targo"], "--unverified"]
    version = probe([*command, "--version"])
    if not version.startswith("targo "):
        raise RuntimeError("Trust development compilation requires the branded Targo build tool")
    identities = {tools[name]: executable_digest(Path(tools[name]))
                  for name in ("trustc", "trustdoc", "targo")}
    return {
        "lane": "trust-unverified", "tools": tools, "rustc": rustc, "cargo": version,
        "sysroot": str(sysroot), "build_command": command,
        "compiler_environment": environment, "compiler_tool_identities": identities,
        "runtime_checker_environment": {key: os.environ[key] for key in RUNTIME_CHECKER_ENVIRONMENT
                                        if key in os.environ},
    }


def target_build_command(
    provenance: dict, unset_environment: Sequence[str], runner_environment: dict | None = None,
) -> list[str]:
    """The Trust package's `targo --unverified` prefix for a root-workspace
    target, with any runtime environment delivered through a Cargo target
    runner.

    The Trust compiler refuses TCG_* variables as untracked compiler controls,
    so the checker selections (less `unset_environment`) and a target's
    TARGET_ENVIRONMENT (`runner_environment`) reach only the test executable.
    """
    command = list(provenance["build_command"])
    runtime = {k: v for k, v in provenance["runtime_checker_environment"].items()
               if k not in unset_environment}
    runtime.update(runner_environment or {})
    if runtime:
        # Cargo still owns test discovery, execution and its native library
        # search path. Only the test receives these checker selections; no
        # wrapper or unchecked semantic environment enters the compiler.
        runner = [provenance["tools"]["env"], *(f"{k}={v}" for k, v in runtime.items())]
        command += ["--config", f"target.{HOST}.runner={json.dumps(runner)}"]
    return command


def bridge_toolchain(driver: str | None) -> dict:
    """Resolve the pinned Trust package that builds and runs bridge targets.

    `scripts/trust_toolchain.py` identifies the package `trustc` named by
    `--trust-driver` (or, without it, the PATH `trustc`/`targo` pair) against
    the bridge's own pin and refuses the retired stock nightly, an unidentified
    compiler, or a PATH shim that is not the package driver; its record
    (compiler, targo, commit, lane) goes into the provenance. A missing or
    incoherent package is a floor error, like any other missing required tool,
    and so is a package built for another host.
    """
    spec = importlib.util.spec_from_file_location("_trust_toolchain", TRUST_TOOLCHAIN_SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"required helper is missing: {TRUST_TOOLCHAIN_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    try:
        record = module.resolve(driver)
    except module.ToolchainError as error:
        raise RuntimeError(
            f"bridge targets need the pinned Trust package (name it with --trust-driver "
            f"<package>/bin/trustc): {error}"
        ) from error
    if record["host"] != HOST:
        raise RuntimeError(
            f"pinned Trust compiler host must be {HOST}, observed {record['host']}"
        )
    return record


def target_command(
    package: str, target: str, provenance: dict, jobs: int, offline: bool,
    *, unset_environment: Sequence[str] = (), runner_environment: dict | None = None,
) -> tuple[list[str], Path, dict[str, str]]:
    """The test command for one floor target, its working directory and env.

    The ROOT-workspace spelling is exactly the one the gate tests pin, argument
    for argument: any `--features` sits directly before `--test`, so a feature
    can only ever reach the target it was declared for. A BRIDGE_PACKAGE target
    instead runs in the bridge workspace, built by the pinned Trust package's
    own build tool in its explicit unverified lane.
    """
    head = ["--color", "never", "-j", str(jobs)]
    tail = ["--test", target, "--", "--nocapture", "--test-threads=1"]
    if package == BRIDGE_PACKAGE:
        trust = provenance.get("trust_bridge")
        if trust is None:
            # Unreachable through main(), which resolves the package before the
            # first target; raised rather than asserted so `python3 -O` cannot
            # turn a missing Trust package into a bare `targo` on PATH.
            raise RuntimeError(
                f"{package}/{target} is a bridge target but no pinned Trust package was resolved"
            )
        if target_environment(package, target) or runner_environment:
            # TARGET_ENVIRONMENT reaches a root-workspace target through a
            # Cargo target runner. This lane has no route: `trustc` refuses
            # TCG_* variables on the process, and the runner config belongs to
            # the bridge workspace. Refuse rather than drop a requirement a row
            # asked for. No bridge row declares one today.
            raise RuntimeError(
                f"{package}/{target} is a bridge target, for which this runner has no "
                "TARGET_ENVIRONMENT delivery route"
            )
        # The bridge package is its own workspace, so `-p` does not name it and
        # TARGET_FEATURES / TARGET_MINIMUM_PASSES read crates/<package> paths
        # that exist for it; the inventory checks therefore cover it unchanged.
        command = [
            trust["targo"], "--unverified", "test", "--release", "--locked",
            *(["--offline"] if offline else []), *head, *tail,
        ]
        return command, BRIDGE_DIR, {"RUSTC": trust["compiler"]}
    command = [
        *target_build_command(provenance, unset_environment, runner_environment),
        "test", "--locked", *(["--offline"] if offline else []), *head,
        "-p", package, *feature_arguments(package, target), *tail,
    ]
    return command, ROOT, {}


def llc_required() -> bool:
    """Whether a required target runs llc twin legs (TCG_REQUIRE_LLC)."""
    return any(environment.get("TCG_REQUIRE_LLC") == "1" for environment in TARGET_ENVIRONMENT.values())


def executable_file(path: Path) -> bool:
    """An existing regular file with an execute bit: the rule symbol_linkage_elf's
    llc lookup applies too (is_executable_file)."""
    try:
        return path.is_file() and (path.stat().st_mode & 0o111) != 0
    except OSError:
        return False


def llvm_major(text: str) -> int | None:
    """The major version of an `LLVM version 22.1.6...` (llc --version) or
    `LLVM version: 22.1.6` (rustc -vV) line."""
    found = re.search(r"LLVM version:? *(\d+)", text)
    return int(found.group(1)) if found else None


def resolve_llc(
    sysroot: Path, *, search_path: str, compiler: str, compiler_version: str,
    environ: dict | None = None,
) -> dict:
    """The llc a required target's llc twin legs will use, by the rule the test
    applies: TCG_LLC, the first llc in an absolute entry of the lane's PATH
    (a relative entry would resolve against the test's working directory, not
    this process's, so neither searches it), then
    <sysroot>/lib/rustlib/<host>/bin/llc of the Trust package's compiler. The
    llc must be an executable file whose LLVM major version equals the
    compiler's (`compiler_version` is its -vV). Anything else is refused with
    the remedy: a Trust package that ships its LLVM tools.
    """
    environ = os.environ if environ is None else environ
    sysroot_llc = sysroot / "lib/rustlib" / HOST / "bin/llc"
    remedy = (
        f"the Trust package {sysroot} ships its LLVM tools at lib/rustlib/{HOST}/bin/llc; use a Trust "
        "package that carries them"
    )

    def refuse(problem: str) -> RuntimeError:
        return RuntimeError(
            f"required tool is missing: llc (a required target's llc twin legs, TCG_REQUIRE_LLC): {problem}; {remedy}"
        )

    explicit = environ.get("TCG_LLC")
    on_path = next((
        Path(entry) / "llc" for entry in search_path.split(os.pathsep)
        if os.path.isabs(entry) and executable_file(Path(entry) / "llc")
    ), None)
    if explicit:
        path, route = Path(explicit), "TCG_LLC"
    elif on_path is not None:
        path, route = on_path, "PATH"
    elif executable_file(sysroot_llc):
        path, route = sysroot_llc, "sysroot"
    else:
        raise refuse(f"none through TCG_LLC, an absolute PATH entry or {sysroot_llc}")
    if not executable_file(path):
        raise refuse(f"{route} names {path}, which is not an executable file")
    wanted = llvm_major(compiler_version)
    if wanted is None:
        raise refuse(f"the lane compiler {compiler} reports no LLVM version to match")
    version = next(
        (line.strip() for line in probe([str(path), "--version"]).splitlines() if "LLVM version" in line),
        "no LLVM version line",
    )
    if llvm_major(version) != wanted:
        raise refuse(f"{path} ({route}) reports {version!r}, but the lane compiler {compiler} is LLVM {wanted}")
    release = next((line.split(": ", 1)[1] for line in compiler_version.splitlines()
                    if line.startswith("release: ")), "no release line")
    return {
        "path": str(path), "route": route, "version": version, "llvm_major": wanted,
        "compiler": compiler, "compiler_release": release, "sysroot": str(sysroot),
        **executable_digest(path),
    }


def preflight() -> dict:
    """Probe the host tools and PATH's Trust package, the floor's only lane."""
    executables = {}
    selected = trust_development_toolchain()
    for name in ("git", "cc", "c++", "readelf"):
        path = shutil.which(name)
        if path is None:
            raise RuntimeError(f"required tool is missing: {name}")
        executables[name] = path
    if not TIMEOUT_RUNNER.is_file():
        raise RuntimeError(f"required timeout runner is missing: {TIMEOUT_RUNNER}")
    executables.update(selected["tools"])
    rustc = selected["rustc"]
    hosts = re.findall(r"^host: (\S+)$", rustc, re.MULTILINE)
    if sys.platform != "linux" or hosts != [HOST]:
        raise RuntimeError(f"required Linux host is {HOST}, observed {hosts!r} on {sys.platform}")
    configured_target = os.environ.get("CARGO_BUILD_TARGET")
    if configured_target and configured_target != HOST:
        raise RuntimeError(f"CARGO_BUILD_TARGET selects a different target: {configured_target}")
    llc = None
    if llc_required():
        # The llc a required target's llc twin legs will find: the Trust
        # package's compiler is the one whose sysroot they search, and the one
        # recorded in provenance.llc with the LLVM version that decided.
        llc = resolve_llc(
            Path(selected["sysroot"]), search_path=selected["compiler_environment"]["PATH"],
            compiler=selected["tools"]["trustc"], compiler_version=selected["rustc"],
        )
        executables["llc"] = llc["path"]
    result = {
        **source_provenance(executables["git"]),
        "host": hosts[0], "tools": executables,
        "rustc": rustc,
        "cargo": selected["cargo"],
        "cc": probe([executables["cc"], "--version"]),
        "cxx": probe([executables["c++"], "--version"]),
        "readelf": probe([executables["readelf"], "--version"]),
        "llc": llc,
        "configuration": {
            name: os.environ[name]
            for name in (
                "RUSTUP_TOOLCHAIN", "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET", "CARGO_TARGET_DIR",
                "AY_SOLVER_PATH", "TCG_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER",
                "TRUST_ROOT", "TCG_JIT_UNCHECKED", "TCG_NO_PROOF_CERTS", "TCG_REFINE_SOLVER",
                "TCG_NO_PROOF_CACHE", "TCG_NO_CERT_STORE", "TCG_PROOF_CERT_STORE", "XDG_CACHE_HOME",
            )
            if name in os.environ
        },
        # Removed from every target's environment (SCRUBBED_ENVIRONMENT_PREFIXES).
        "scrubbed_environment": {name: os.environ[name] for name in scrubbed_environment(os.environ)},
    }
    result.update({key: value for key, value in selected.items() if key != "tools"})
    return result


def write_report(path: Path, report: dict) -> None:
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


# Ambient controls that would silently change what a required target
# executes: proptest reads PROPTEST_* (an ambient PROPTEST_CASES=1 would shrink
# every panic-fuzz family to one case). They are removed from every target's
# environment, with the variables Cargo sets for its children (see
# scrubbed_environment), and each removal is recorded with the target.
SCRUBBED_ENVIRONMENT_PREFIXES = ("PROPTEST_",)

# The proptest case-count positive control: each panic-fuzz family's
# panic_fuzz_runs_its_configured_case_count prints the count its properties
# are configured with and the count it actually ran. With PROPTEST_* scrubbed
# both must be that file's default, so a count shrunk by any other route (a
# Cargo `[env]` entry, a changed default) fails the floor.
PROPTEST_CASE_DEFAULTS = {
    ("trust-cg-lower", "panic_fuzz_lower"): 256,
    ("trust-cg-codegen", "panic_fuzz_compile"): 64,
    ("trust-cg-codegen", "panic_fuzz_compile_x86_64"): 64,
    ("trust-cg-codegen", "panic_fuzz_encode"): 256,
    ("trust-cg-codegen", "panic_fuzz_encode_x86_64"): 256,
    ("trust-cg-codegen", "panic_fuzz_macho_fixup"): 256,
    ("trust-cg-verify", "panic_fuzz_verify"): 64,
}


def proptest_case_line(cases: int) -> str:
    """The probe's transcript line for `cases` configured and run."""
    return f"panic-fuzz proptest cases: configured={cases} run={cases}"


def transcript_has_line(transcript: str, required: str) -> bool:
    """Whether `required` is a whole transcript line, or ends libtest's
    `test <name> ... ` line (--nocapture prints a test's output after it)."""
    return any(
        line == required or line.endswith(f" ... {required}") for line in transcript.splitlines()
    )


def target_required_lines(package: str, target: str) -> tuple[str, ...]:
    """Transcript lines required target `package`/`target` must print."""
    if (package, target) == ("trust-cg-codegen", "aarch64_shrink_wrap_region_exit"):
        return ("SHRINK_WRAP_REGION_EXIT_NATIVE levels=4 checked_per_level=24",)
    default = PROPTEST_CASE_DEFAULTS.get((package, target))
    return () if default is None else (proptest_case_line(default),)


def scrubbed_environment(environment: dict) -> list[str]:
    """The ambient names every target runs without: PROPTEST_*, and the
    variables Cargo sets for build scripts, rustc and tests under either floor
    build tool's prefixes (an ambient one Cargo does not overwrite, such as a
    CARGO_FEATURE_* for a disabled feature, would reach build scripts)."""
    auditor = cargo_config_auditor()
    prefixes = auditor.environment_prefixes(TRUST_BUILD_TOOL)
    return sorted(
        name for name in environment
        if name.startswith(SCRUBBED_ENVIRONMENT_PREFIXES) or auditor.child_variable(name, prefixes)
        or name in ("TCG_TEST_AARCH64_EMULATOR", "TCG_TEST_AARCH64_CPU")
    )


def target_unset_environment(package: str, target: str) -> tuple[str, ...]:
    if package == BRIDGE_PACKAGE:
        # The bridge lane compiles with the pinned `trustc`, which refuses the
        # whole TCG_*/TRUST_CG_* family as untracked compiler controls. Remove
        # the two checker selections this runner itself may be given, exactly as
        # the Trust development lane's compiler prefix does; an ambient one would
        # fail the build rather than change the reading.
        return RUNTIME_CHECKER_ENVIRONMENT
    if (package, target) == ("trust-cg-codegen", "core_jit_planning"):
        # This suite only tests pure sealed-plan admission, which deliberately
        # rejects ambient checker overrides. It does not compile or authorize
        # executable code, nor invoke the external solver/checker. Give it its
        # intended clean planning context while preserving its negative tests.
        # Every executable/proof suite keeps the user's exact checker choice.
        return ("TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER")
    return ()


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--list", action="store_true", help="print required targets without probing or executing")
    parser.add_argument(
        "--trust-unverified", action="store_true",
        help="use PATH's coherent Trust package and explicit targo --unverified; development compilation "
             "only. This is the default and the only lane: the stock cargo/rustc lane is retired "
             "(owner directive 2026-09-28), so the flag is accepted for compatibility",
    )
    parser.add_argument("--out", type=Path, help="new output directory outside the source tree; existing paths are rejected")
    parser.add_argument("--timeout-seconds", type=positive_seconds, default=1200.0, help="bound for each Cargo invocation (default: 1200)")
    parser.add_argument("--jobs", type=positive_jobs, default=2, help="Cargo build jobs (default: 2)")
    parser.add_argument("--cpu-profile", choices=("native", "host+baseline-emulation"), default="native",
                        help="add the full native/max/Cortex-A53 CPU matrix to the unchanged native floor")
    parser.add_argument("--cpu-profile-only", action="store_true",
                        help="run only the distinct CPU-matrix qualification; grants no native-floor credit")
    parser.add_argument("--aarch64-emulator", type=Path, help="absolute qemu-aarch64 for the CPU matrix")
    parser.add_argument("--cpu-profile-driver", help="Trust workspace compiler for the CPU matrix")
    parser.add_argument(
        "--trust-driver", metavar="TRUSTC",
        help="the pinned Trust package's trustc for bridge-package targets (default: the PATH trustc/targo pair)",
    )
    parser.add_argument(
        "--require-clean", action="store_true",
        help="refuse to run unless git status --porcelain is empty (no tracked edits or untracked non-ignored files)",
    )
    parser.add_argument(
        "--max-rss-gib", type=positive_gib, metavar="GIB",
        help="kill any Cargo invocation whose process group exceeds GIB resident (Linux /proc supervision; fails where unsupported)",
    )
    parser.add_argument(
        "--require-offline-deps", action="store_true",
        help="refuse to run unless every Git revision Cargo.lock pins resolves in the local Cargo Git database "
             "and no finished checkout differs from it; run Cargo with --offline",
    )
    parser.add_argument(
        "--require-proof-tools", action="store_true",
        help="refuse to run unless the AY solver and the Clean checker both resolve through a pinned route "
             "(AY: an absolute AY_SOLVER_PATH or the build toolchain's bin/ay; Clean: an explicit "
             "TCG_EXTERNAL_CLEAN_CHECKER override, or an aterm-style package prefix whose bin directory is "
             "on PATH) and the CLI built by this floor (trust-cg --print-ay-identity) admits exactly the "
             "resolved AY and materializes its private copy under the effective cache root; without it an "
             "absent or unpinned tool is labelled and proof-replay targets may fail for that reason alone",
    )
    # The Trust lane is the only lane (owner directive 2026-09-28): the stock
    # cargo/rustc floor is retired, and --trust-unverified changes nothing.
    args = parser.parse_args(argv)
    profile_requested = args.cpu_profile == "host+baseline-emulation"
    if args.cpu_profile_only and not profile_requested:
        parser.error("--cpu-profile-only requires --cpu-profile host+baseline-emulation")
    if not profile_requested and (args.aarch64_emulator or args.cpu_profile_driver):
        parser.error("CPU matrix controls require --cpu-profile host+baseline-emulation")
    if profile_requested and not args.aarch64_emulator:
        parser.error("--cpu-profile host+baseline-emulation requires --aarch64-emulator")
    if args.cpu_profile_only and args.require_proof_tools:
        parser.error("--cpu-profile-only has no proof-tool qualification; use the complete floor for --require-proof-tools")
    profile_command = [sys.executable, str(ROOT / "scripts/check_aarch64_cpu_profiles.py")]
    if profile_requested:
        profile_command += ["--emulator", str(args.aarch64_emulator), "--jobs", str(args.jobs),
                            "--timeout-seconds", str(args.timeout_seconds)]
        if args.cpu_profile_driver:
            profile_command += ["--trust-driver", args.cpu_profile_driver]
        if args.max_rss_gib is not None:
            profile_command += ["--max-rss-gib", str(args.max_rss_gib)]
    if args.list:
        if profile_requested:
            print("cpu-profile-matrix native-host qemu-max qemu-cortex-a53 (emulated evidence labelled separately)")
        if args.cpu_profile_only:
            return 0
        for package, target in TARGETS:
            environment = [f"{name}={value}" for name, value in sorted(target_environment(package, target).items())]
            print(" ".join((package, target, *feature_arguments(package, target), *environment)))
        for package, target, decision, reason in DECIDED_ABSENT:
            print(f"decided-absent {package} {target} ({decision}): {reason}")
        problems = decided_absent_problems()
        for problem in problems:
            print(problem, file=sys.stderr)
        return 1 if problems else 0
    if args.cpu_profile_only:
        if args.out is not None:
            profile_command += ["--out", str(args.out)]
        return subprocess.call(profile_command, cwd=ROOT)
    try:
        if args.out is None:
            output = Path(tempfile.mkdtemp(prefix=OUTPUT_PREFIX))
        else:
            output = args.out.absolute()
            if output.resolve().is_relative_to(ROOT):
                raise OSError("output must be outside the source tree so logs cannot change source provenance")
            output.mkdir(mode=0o700)
    except OSError as error:
        print(f"{FLOOR_NAME} regression floor: output directory error: {error}", file=sys.stderr)
        return 1
    report = {
        "schema": SCHEMA,
        "host": HOST,
        "scope": "required regression floor; not full completion, proof or release qualification",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "status": "incomplete", "required_targets": [list(row) for row in TARGETS],
        "decided_absent": decided_absent_records(),
        "required_target_minimum_passes": {
            f"{package}/{target}": target_minimum_passes(package, target)
            for package, target in TARGETS
        },
        "required_minimum_passes": sum(
            target_minimum_passes(package, target) for package, target in TARGETS
        ),
        "required_target_features": {
            f"{package}/{target}": list(target_features(package, target))
            for package, target in TARGETS if target_features(package, target)
        },
        "required_target_environment": {
            f"{package}/{target}": target_environment(package, target)
            for package, target in TARGETS if target_environment(package, target)
        },
        "controls": {
            "require_clean": args.require_clean, "max_rss_gib": args.max_rss_gib,
            "rss_supervision": None, "require_offline_deps": args.require_offline_deps,
            "require_proof_tools": args.require_proof_tools,
            "trust_driver": args.trust_driver,
        },
        "targets": [], "errors": [],
    }
    if profile_requested:
        report["controls"]["cpu_profile"] = args.cpu_profile
    report_path = output / "report.json"
    write_report(report_path, report)
    print(f"{FLOOR_NAME} regression logs: {output}", flush=True)
    print_decided_absent(sys.stdout)
    try:
        report["controls"]["rss_supervision"] = rss_supervision(args.max_rss_gib)
        write_report(report_path, report)
        # Cargo applies its config files and config variables to every
        # invocation, version probes included, and a config [alias] can run
        # any command; an [env], [build] rustflags, [profile] or wrapper would
        # change what the floor builds and runs without any ambient variable.
        # Audit them before running any build tool.
        git = shutil.which("git")
        if git is None:
            raise RuntimeError("required tool is missing: git")
        build_tool = selected_build_tool()
        report["cargo_config"] = cargo_config_record(git, tool=build_tool)
        write_report(report_path, report)
        if report["cargo_config"]["problems"]:
            report["errors"].extend(f"cargo config: {problem}" for problem in report["cargo_config"]["problems"])
            print(f"{FLOOR_NAME} regression floor: a Cargo config would change the targets; see cargo_config:",
                  file=sys.stderr)
            for problem in report["cargo_config"]["problems"]:
                print(f"  {problem}", file=sys.stderr)
            raise RuntimeError("refusing to run any build tool: the Cargo configuration did not audit clean")
        # A bridge target runs another build tool in another workspace, so that
        # workspace's Cargo configuration is audited under the bridge build
        # tool's own variable prefixes before the pinned package is probed.
        bridge = any(package == BRIDGE_PACKAGE for package, _ in TARGETS)
        if bridge:
            report["bridge_cargo_config"] = cargo_config_record(
                git, tool=TRUST_BUILD_TOOL, cwd=BRIDGE_DIR,
            )
            write_report(report_path, report)
            if report["bridge_cargo_config"]["problems"]:
                report["errors"].extend(
                    f"bridge cargo config: {problem}"
                    for problem in report["bridge_cargo_config"]["problems"]
                )
                print(f"{FLOOR_NAME} regression floor: a Cargo config would change the bridge "
                      "target; see bridge_cargo_config:", file=sys.stderr)
                for problem in report["bridge_cargo_config"]["problems"]:
                    print(f"  {problem}", file=sys.stderr)
                raise RuntimeError(
                    "refusing to run any build tool: the bridge Cargo configuration did not audit clean"
                )
        report["provenance"] = preflight()
        provenance = report["provenance"]
        if bridge:
            provenance["trust_bridge"] = bridge_toolchain(args.trust_driver)
        proof_environment = {**os.environ, **provenance["compiler_environment"]}
        write_report(report_path, report)
        refused = False
        absent_errors = decided_absent_problems()
        if absent_errors:
            report["errors"].extend(absent_errors)
            refused = True
        inventory_errors = feature_problems(stale_entries=False)
        if inventory_errors:
            report["errors"].extend(f"required target features: {problem}" for problem in inventory_errors)
            refused = True
        environment_errors = environment_problems(stale_entries=False)
        if environment_errors:
            report["errors"].extend(f"required target environment: {problem}" for problem in environment_errors)
            refused = True
        minimum_errors = minimum_problems(stale_entries=False)
        if minimum_errors:
            report["errors"].extend(f"required target minimums: {problem}" for problem in minimum_errors)
            refused = True
        if report["controls"]["rss_supervision"] == "unsupported":
            report["errors"].append(
                f"--max-rss-gib {args.max_rss_gib:g}: resident-set supervision is unsupported on this host; "
                "refusing to run without the requested ceiling"
            )
            refused = True
        # A provenance record without a cleanliness verdict is treated as dirty.
        if report["provenance"].get("dirty") is not False:
            if args.require_clean:
                report["errors"].append(
                    "--require-clean: source tree has tracked modifications or untracked non-ignored "
                    "files; see provenance.git_status"
                )
                refused = True
                print(f"{FLOOR_NAME} regression floor: --require-clean refuses this source tree; "
                      "git status --porcelain:", file=sys.stderr)
            else:
                print(f"{FLOOR_NAME} regression floor: source tree is dirty; this run is not a "
                      "clean-source qualification (see --require-clean). git status --porcelain:",
                      file=sys.stderr)
            for line in report["provenance"].get("git_status", []):
                print(f"  {line}", file=sys.stderr)
        report["dependency_identity"] = dependency_identity(report["provenance"]["tools"]["git"])
        offline_problems = dependency_recorder().offline_problems(report["dependency_identity"])
        if offline_problems and args.require_offline_deps:
            report["errors"].extend(f"--require-offline-deps: {problem}" for problem in offline_problems)
            refused = True
            print(f"{FLOOR_NAME} regression floor: --require-offline-deps refuses this Cargo home; "
                  "see dependency_identity:", file=sys.stderr)
        elif offline_problems:
            print(f"{FLOOR_NAME} regression floor: pinned Git dependencies are not all local, so Cargo "
                  "may fetch them (see --require-offline-deps and dependency_identity):", file=sys.stderr)
        for problem in offline_problems:
            print(f"  {problem}", file=sys.stderr)
        report["proof_tools"] = proof_tool_identities(proof_environment)
        tool_problems = proof_tool_problems(report["proof_tools"])
        if tool_problems and args.require_proof_tools:
            report["errors"].extend(f"--require-proof-tools: {problem}" for problem in tool_problems)
            refused = True
            print(f"{FLOOR_NAME} regression floor: --require-proof-tools refuses this environment; "
                  "see proof_tools:", file=sys.stderr)
        elif tool_problems:
            print(f"{FLOOR_NAME} regression floor: the AY solver and Clean checker are not both pinned, so "
                  "proof-replay targets may fail for that reason alone (see --require-proof-tools and "
                  "proof_tools):", file=sys.stderr)
        for problem in tool_problems:
            print(f"  {problem}", file=sys.stderr)
        write_report(report_path, report)
        if args.require_proof_tools and not refused:
            report["ay_admission"], admission_problems = ay_admission_preflight(
                provenance, report["proof_tools"]["ay"], output, jobs=args.jobs,
                offline=args.require_offline_deps, timeout_seconds=args.timeout_seconds,
                max_rss_gib=args.max_rss_gib,
            )
            if admission_problems:
                report["errors"].extend(f"--require-proof-tools: {problem}" for problem in admission_problems)
                refused = True
                print(f"{FLOOR_NAME} regression floor: --require-proof-tools refuses this environment: "
                      "the AY identity rule does not admit the resolved AY (see ay_admission):",
                      file=sys.stderr)
                for problem in admission_problems:
                    print(f"  {problem}", file=sys.stderr)
            write_report(report_path, report)
        if profile_requested and not refused:
            cpu_output = output / "cpu-profiles"
            result = subprocess.run([*profile_command, "--out", str(cpu_output)], cwd=ROOT, check=False)
            cpu_report = json.loads((cpu_output / "report.json").read_text())
            report["cpu_profiles"] = {
                "report": str(cpu_output / "report.json"), "status": cpu_report.get("status"),
                "profile_fingerprint": cpu_report.get("profile_fingerprint"),
            }
            write_report(report_path, report)
            if (result.returncode != 0 or cpu_report.get("schema") != "trust-cg-aarch64-cpu-profiles-v1"
                    or cpu_report.get("status") != "pass" or not cpu_report.get("profile_fingerprint")):
                raise RuntimeError("required CPU profile matrix failed; see cpu_profiles report")
        for package, target in () if refused else TARGETS:
            print(f"Running {package}/{target}", flush=True)
            unset_environment = target_unset_environment(package, target)
            # A target's TARGET_ENVIRONMENT reaches only its test executable,
            # through the Cargo target runner: the Trust compiler refuses TCG_*
            # variables as untracked compiler controls.
            command, root, bridge_environment = target_command(
                package, target, provenance, args.jobs, args.require_offline_deps,
                unset_environment=unset_environment,
                runner_environment=target_environment(package, target),
            )
            result = run_target(
                command, output / f"{package}--{target}.log", args.timeout_seconds,
                root=root, unset_environment=unset_environment,
                max_rss_gib=args.max_rss_gib, minimum=target_minimum_passes(package, target),
                required_lines=target_required_lines(package, target),
                set_environment=bridge_environment,
            )
            result.update({
                "package": package, "target": target,
                "features": list(target_features(package, target)),
                "environment": target_environment(package, target),
            })
            report["targets"].append(result)
            write_report(report_path, report)
            print(f"{result['status'].upper()}: {package}/{target}", flush=True)
            if result["interrupted_signal"] is not None:
                report["errors"].append("interrupted; required target inventory is incomplete")
                break
        complete = len(report["targets"]) == len(TARGETS) and bool(TARGETS)
        report["status"] = "pass" if (
            complete and not report["errors"]
            and all(row["status"] == "pass" for row in report["targets"])
        ) else "fail"
        report["final_source"] = source_provenance(report["provenance"]["tools"]["git"])
        if report["final_source"]["source_fingerprint"] != report["provenance"]["source_fingerprint"]:
            report["errors"].append("source changed while required targets were running")
            report["status"] = "fail"
        report["final_cargo_config"] = cargo_config_record(git, tool=build_tool)
        config_changes = cargo_config_auditor().changes(report["cargo_config"], report["final_cargo_config"])
        if config_changes:
            report["errors"].extend(
                f"Cargo config changed while the floor was running: {change}" for change in config_changes
            )
            report["status"] = "fail"
        if bridge:
            report["final_bridge_cargo_config"] = cargo_config_record(
                git, tool=TRUST_BUILD_TOOL, cwd=BRIDGE_DIR,
            )
            bridge_changes = cargo_config_auditor().changes(
                report["bridge_cargo_config"], report["final_bridge_cargo_config"],
            )
            if bridge_changes:
                report["errors"].extend(
                    f"bridge Cargo config changed while the floor was running: {change}"
                    for change in bridge_changes
                )
                report["status"] = "fail"
        if report["targets"]:
            # The trees Cargo extracted and compiled, compared with the record
            # taken before the first target.
            report["final_dependency_identity"] = dependency_identity(report["provenance"]["tools"]["git"])
            changes = dependency_recorder().identity_changes(
                report["dependency_identity"], report["final_dependency_identity"],
            )
            if changes:
                report["errors"].extend(
                    f"dependency identity changed while required targets were running: {change}"
                    for change in changes
                )
                report["status"] = "fail"
            report["final_proof_tools"] = proof_tool_identities(proof_environment)
            tool_changes = proof_tool_changes(report["proof_tools"], report["final_proof_tools"])
            if tool_changes:
                report["errors"].extend(
                    f"proof tool identity changed while required targets were running: {change}"
                    for change in tool_changes
                )
                report["status"] = "fail"
        identities = provenance["compiler_tool_identities"]
        report["final_compiler_tool_identities"] = {
            path: executable_digest(Path(path)) for path in identities
        }
        if report["final_compiler_tool_identities"] != identities:
            report["errors"].append("Trust compiler/build-tool bytes changed during the regression floor")
            report["status"] = "fail"
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        report["errors"].append(str(error))
        report["status"] = "fail"
    except KeyboardInterrupt:
        report["errors"].append("interrupted; required target inventory is incomplete")
        report["status"] = "fail"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    write_report(report_path, report)
    print(f"{FLOOR_NAME} regression floor: {report['status'].upper()} ({report_path})")
    print_decided_absent(sys.stdout)
    for error in report["errors"]:
        print(error, file=sys.stderr)
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
