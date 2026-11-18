#!/usr/bin/env python3
"""Run the required Darwin AArch64 execution floor, not full qualification.

Each complete integration target runs in its own bounded process on an
aarch64-apple-darwin host with the installed Trust package
(scripts/trust_toolchain.py; `targo --unverified test` through
scripts/trust_cargo.sh). ALab systems build with Trust (owner directive
2026-09-28); there is no stock rustup lane.
Transcripts are captured with --show-output and classified by
scripts/matrix_results.py, so a runtime SKIP line, an ignored or filtered test,
a timeout or an incomplete suite fails the target, and every target must report
at least its required minimum of executed passes.

The required inventory is every trust-cg-codegen test file carrying a
target_os = "macos" guard or using tests/common/aarch64_native.rs (except the
x86-64 files named in OUT_OF_SCOPE), every Linux-floor target that compiles a
nonempty suite on Darwin, and two unguarded AArch64 JIT canaries. Linux-floor
targets compiled out on Darwin are reported, never counted. Other AArch64 JIT
suites without an OS guard belong to the release and full-matrix runners. A
target gated on a Cargo feature is built with the features the Linux floor's
TARGET_FEATURES names for it, and the same file-level feature-gate check
applies.

Every run records, as report.json's dependency_identity, the Git dependency
identities the root Cargo.lock resolves in the local Cargo home (shared with
the Linux floor through scripts/dependency_identity.py), and again after the
targets as final_dependency_identity; a lockfile or checkout tree that changes
in between, or a checkout extracted during the run that is not the unmodified
pinned revision, fails the run. --require-offline-deps refuses to run unless every
pinned Git revision resolves in the local Cargo Git database and no finished
checkout differs from it, and passes --offline to every Cargo invocation.

Each target runs with TMPDIR set to a new directory of its own; an entry left
there after the target exits (other than a named host-tool cache) fails the
target and is recorded in report.json as temporary_leftovers, and the runner
then removes that directory. Only the runner's own per-target directories are
ever removed.

This floor is testing evidence. It does not establish full compiler completion,
proof authority, Trust-verified compilation or release readiness. See
docs/linux-aarch64-completion.md and scripts/check_linux_aarch64.py.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
TIMEOUT_RUNNER = ROOT / "scripts" / "run_with_timeout.py"
MATRIX_RESULTS = ROOT / "scripts" / "matrix_results.py"
LINUX_FLOOR = ROOT / "scripts" / "check_linux_aarch64.py"
TRUST_TOOLCHAIN = ROOT / "scripts" / "trust_toolchain.py"
TRUST_CARGO = ROOT / "scripts" / "trust_cargo.sh"
TOOLCHAIN_FILE = ROOT / "rust-toolchain.toml"
CODEGEN_TESTS = ROOT / "crates" / "trust-cg-codegen" / "tests"
HOST = "aarch64-apple-darwin"
MACHINE = "arm64"
# Every host tool the required targets invoke, with its identity probe.
HOST_TOOL_PROBES = {
    "git": ("--version",), "cc": ("--version",), "c++": ("--version",),
    "clang": ("--version",), "ld": ("-v",), "otool": ("--version",),
    "nm": ("--version",), "objdump": ("--version",), "dwarfdump": ("--version",),
    "lldb": ("--version",), "xcrun": ("--show-sdk-version",), "sw_vers": (),
    "uname": ("-m",),
}
# The Trust sysroot's proof tools, recorded by digest in the report's
# provenance (see preflight).
PROOF_TOOL_FILES = {
    "sysroot_ay": "bin/ay", "sysroot_clean": "bin/clean", "overlay_manifest": "overlay.json",
}
# Host tools with no version flag, identified by the SCCS strings /usr/bin/what
# reads from the resolved binary. codesign re-signs the code-signing and
# MAP_JIT entitlement controls' binaries.
WHAT = "/usr/bin/what"
WHAT_PROBED_TOOLS = ("codesign",)
# These route Cargo around the pinned Trust compiler, or run the test binaries
# through another program, and are refused rather than recorded.
REFUSED_ENVIRONMENT = (
    "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER",
)
# The same reroutes spelled as keys in a Cargo config file Cargo would load
# (build.rustc, build.rustc-wrapper, build.rustc-workspace-wrapper and any
# target runner, in table or dotted-key form).
CARGO_CONFIG_REROUTE = re.compile(
    r"^\s*(?:[\w.'\"()=, -]*\.)?(rustc|rustc-wrapper|rustc-workspace-wrapper|runner)\s*=",
    re.MULTILINE,
)
# libtest capture must stay on so matrix_results can attribute runtime SKIPs
# to the test that printed them. The tests' keep-scratch knobs are a developer's
# post-mortem aid; under them a target would leave its scratch directories in
# its TMPDIR by request, so the floor never passes them on.
CHILD_UNSET_ENVIRONMENT = ("RUST_TEST_NOCAPTURE", "TRUST_CG_KEEP_TEST_OBJECTS", "TRUST_CG_KEEP_LINKRUN")
RECORDED_CONFIGURATION = (
    "RUSTUP_TOOLCHAIN", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET",
    "CARGO_TARGET_DIR", "CARGO_HOME", "RUSTUP_HOME", "AY_SOLVER_PATH", "TCG_SOLVER_PATH",
    "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER", "TRUST_ROOT", "TCG_JIT_UNCHECKED",
    "TCG_NO_PROOF_CERTS", "TCG_REFINE_SOLVER", "TCG_NO_PROOF_CACHE", "TCG_NO_CERT_STORE",
    "TCG_PROOF_CERT_STORE", "XDG_CACHE_HOME", "RUST_TEST_NOCAPTURE", "RUST_TEST_THREADS",
    "DEVELOPER_DIR", "SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "PROPTEST_CASES",
    "CARGO_BUILD_RUSTFLAGS", "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS",
    "CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER", "RUST_MIN_STACK",
)

# Complete test targets and the minimum number of executed passes each must
# report; never substring filters. Each minimum is the number of tests the
# file compiles on aarch64-apple-darwin with default features, so a test that
# vanishes behind a cfg fails the floor. A target whose tests partly live in
# `#[path]` helper modules is pinned at its own file's test census (the
# inventory's upper bound), below its executed count. Lowering a minimum or
# removing a row is a denominator change that needs an explicit, reviewed edit
# here.
TARGETS = (
    # Linux-floor lowering and verification controls; host-neutral.
    ("trust-cg-lower", "aarch64_variadic_abi", 3),
    ("trust-cg-lower", "aarch64_adapter_target_abi", 4),
    ("trust-cg-lower", "aarch64_aggregate_stack_abi", 4),
    ("trust-cg-lower", "aarch64_hva_abi", 4),
    # Six since L04-P6 pinned the unsigned-lane operation partition and the
    # unsigned select on a same-shape compare.
    ("trust-cg-lower", "vector_type_admission", 6),
    ("trust-cg-lower", "container_pointer_metadata", 12),
    ("trust-cg-lower", "aggregate_constants", 13),
    ("trust-cg-lower", "packed_aggregate_constants", 8),
    ("trust-cg-lower", "abi_definition_refusals", 4),
    ("trust-cg-lower", "niche_enum_codec", 17),
    # Empty Rust exception filters are checked by the host-neutral adapter.
    ("trust-cg-lower", "rust_empty_filter", 2),
    # L05-P2: versioned trust-ir construct inventory (every Ty/Inst/Constant/
    # CastOp variant and Module table with an executed/model-only/refused
    # disposition and re-driven refusals).
    ("trust-cg-lower", "trust_ir_construct_inventory", 11),
    # L05-P7: the pinned trust-ir conformance corpus (live, compat,
    # v41-reader-compat and must-refuse goldens in tmbc/JSON/text/msgpack)
    # through trust-cg's readers and writers, with trust-ir's reader and the
    # MessagePack codec as oracles, and the construct property generator
    # (aggregates, enums, records, closures, collections, globals/TLS,
    # handles, refinements, dialect, proof/lineage tables, v41-v50 metadata)
    # beside the scalar one; host-neutral.
    ("trust-cg-codegen", "trust_ir_corpus_roundtrip", 4),
    ("trust-cg-codegen", "tmbc_roundtrip_prop", 6),
    ("trust-cg-verify", "aarch64_affine_lowering", 39),
    ("trust-cg-verify", "aarch64_trust_ir_affine_lowering", 38),
    # Per-compile switch-dispatch binding on real pipeline output at O0-O3
    # (jump-table entries, bounds check, BR register chain, compare groups,
    # fused branches) with its word and intent-consistent corruption
    # batteries and a spilled, reloaded selector (L04-P11); host-neutral.
    ("trust-cg-verify", "aarch64_switch_binding", 7),
    ("trust-cg-verify", "aarch64_fcmp_binding", 15),
    ("trust-cg-verify", "bridge_copy_types", 8),
    ("trust-cg-verify", "aarch64_scalar_cell_bytes", 4),
    ("trust-cg-codegen", "aarch64_direct_cmp_branch", 1),
    # Four host-neutral tests: emitted frame effects, the ELF/Mach-O leaf-frame
    # word pins (unowned, owned and select-leaf boundary) and the SP decoder.
    ("trust-cg-codegen", "aarch64_live_frame_effects", 4),
    ("trust-cg-codegen", "aarch64_shrink_wrap_region_exit", 2),
    ("trust-cg-verify", "aarch64_flag_consumer_gate", 7),
    ("trust-cg-verify", "aarch64_nzcv_silicon_bridge", 9),
    ("trust-cg-verify", "fp_normal_classification", 5),
    # L07-P2 / X-OPCODES-P1 / L04-P7: the word-bound memory-effect
    # decomposition of every admitted memory word of the Darwin census corpus
    # (each re-derived from its disassembly, every part holding, every
    # corruption refuted) and the size census of its queries against the
    # obligations it replaces; host-neutral.
    ("trust-cg-verify", "aarch64_memory_effect_queries", 2),
    # L04-P6: the live NEON silicon differential. Every modeled encoder form
    # of every audited NEON value opcode runs on this CPU against the
    # neon_semantics model the obligations use (exhaustive byte lanes, edge
    # triples, random vectors), the encoder-only forms against their
    # lane-effect parts, the post-index transfers against their word-bound
    # memory-effect parts, the inventory, wrong-model and corrupted-word
    # controls: eleven tests, all native (MAP_JIT).
    ("trust-cg-verify", "aarch64_neon_silicon_differential", 11),
    # L04-P3: the three-way IEEE 754 differential of every emitted scalar FP
    # conversion, rounding and arithmetic form (72 encoder words plus 15
    # assembler-only forms): the CPU (result, untouched registers, FPSR flags)
    # and the verifier model against the independent integer-only reference;
    # every binary16 source exhaustive, the rest statistical, and the
    # committed record of the exhaustive release run checked, and the two
    # named single-NaN model boundaries pinned; ten tests, all native
    # (MAP_JIT).
    ("trust-cg-verify", "aarch64_fp_ieee_differential", 10),
    # L04-P1 / X-OPCODES-P2: the live atomic silicon differential (every
    # LDAR/STLR/CAS/SWP/LD<op> opcode at every emitted width: live encoder
    # word == verified word, ENC-5 refusing every flip, the CPU against the
    # word-bound decomposition and both sides of the form theorem, with
    # neighbouring-model controls) and the scalar memory-effect differential
    # (every scalar load/store form: H/S/D/Q, sign-extending, writeback,
    # register offset); all native (MAP_JIT).
    ("trust-cg-verify", "aarch64_atomic_silicon_differential", 2),
    ("trust-cg-verify", "aarch64_scalar_memory_silicon_differential", 1),
    # L04-P1: the live CRC32/CRC32C silicon differential (every form at
    # seven register assignments: live encoder word == verified word, ENC-5
    # refusing every flip, the CPU against the decoded word's pseudocode, the
    # reflected-CRC intent and a host reference, with neighbouring-model
    # controls); native (MAP_JIT).
    ("trust-cg-verify", "aarch64_crc32_silicon_differential", 2),
    # L04-P1: the live SUBS #imm silicon differential (both widths, five
    # immediates, five register assignments: live encoder word == verified
    # word, ENC-5 refusing every flip, destination and NZCV read with MRS
    # against the machine model, the intent and a host reference, with
    # neighbouring-model controls); native (MAP_JIT).
    ("trust-cg-verify", "aarch64_subs_imm_silicon_differential", 2),
    # L04-P1: the NEON LD1/ST1 post-index form-theorem silicon differential
    # (all fourteen forms: live encoder word == verified word, ENC-5 refusing
    # every flip, both sides of every form theorem against the CPU at every
    # register or buffer byte and the writeback, every machine defect
    # disagreeing with the CPU); native (MAP_JIT).
    ("trust-cg-verify", "aarch64_neon_structure_silicon_differential", 2),
    # Linux-floor codegen, JIT-policy and binding targets. Those listed by
    # linux_only_leg_targets() also carry Linux-only native legs that are
    # compiled out here; only their remaining tests run on Darwin.
    ("trust-cg-codegen", "aarch64_call_result_liveness", 2),
    ("trust-cg-codegen", "aggregate_call_results", 1),
    ("trust-cg-codegen", "multi_result_call_abi", 1),
    ("trust-cg-codegen", "e2e_aarch64_vector_types_linux", 2),
    ("trust-cg-codegen", "e2e_aarch64_bool_abi_linux", 2),
    ("trust-cg-codegen", "e2e_aarch64_heap_dealloc_linux", 2),
    # L05-P3: the ELF CALL26 site, refusal, interpreter-oracle (CleanHeap
    # twin) and as-compiled interpreter-refusal rows run here; the two native
    # rows are Linux-only.
    ("trust-cg-codegen", "e2e_aarch64_arc_ops_linux", 5),
    ("trust-cg-codegen", "e2e_aarch64_niche_enum_linux", 2),
    ("trust-cg-codegen", "e2e_aarch64_direct_enums_linux", 4),
    ("trust-cg-codegen", "e2e_aarch64_sret_linux", 6),
    # Aggregate insert value semantics: eight host-neutral rows (canonical
    # corpus, interpreter model, pinned copy/in-place and block-parameter LIR,
    # the bridge's store-through form, Linux and Darwin objects at O0-O3, and
    # the zero-sized values' LIR and objects); the two C-oracle execution rows
    # are Linux-only. Counted from the cfg gates on a Linux host, not yet run
    # on a Darwin floor host.
    ("trust-cg-codegen", "e2e_aarch64_aggregate_insert_linux", 8),
    # By-reference composite arguments: six host-neutral rows (canonical
    # corpora; Linux and Darwin objects at O0-O3 with the Darwin variadic
    # refusal; BL kept in tail position; bounded code size; invoke block
    # shape; the adapter's copy decisions); the C and C++ oracle rows are
    # Linux-only. Counted from the cfg gates on a Linux host, not yet run on a
    # Darwin floor host.
    ("trust-cg-codegen", "e2e_aarch64_large_aggregate_args_linux", 6),
    # HFAs with zero-sized members: three host-neutral rows (canonical corpus,
    # classification of the translated types, Linux and Darwin objects at
    # O0-O3); the GCC-oracle row is Linux-only.
    ("trust-cg-codegen", "e2e_aarch64_hfa_zero_sized_linux", 3),
    ("trust-cg-codegen", "aarch64_exclusive_encoding", 6),
    # Host-dual native control: forces the BASELINE profile and runs natively
    # on either host, so it is required on both floors.
    ("trust-cg-codegen", "e2e_aarch64_llsc_atomics", 12),
    ("trust-cg-codegen", "aarch64_cond_select", 4),
    ("trust-cg-codegen", "aarch64_fp_cond_select", 6),
    ("trust-cg-codegen", "aarch64_fp_memory_decode", 19),
    ("trust-cg-codegen", "aarch64_gpr_memory_decode", 8),
    ("trust-cg-codegen", "aarch64_scalar_writeback_decode", 8),
    ("trust-cg-codegen", "aarch64_register_offset_decode", 7),
    ("trust-cg-codegen", "aarch64_narrow_register_offset_decode", 8),
    ("trust-cg-codegen", "aarch64_pair_memory_decode", 8),
    # L10-P6: ENC-5's FP/SIMD and integer slices against assembler words,
    # the live encoder (including every W/X view assignment of the integer
    # forms) and the committed Darwin floor census (replayed with every-bit
    # corruption), TrustIR lowerings with mixed views, an F16 compare, the
    # FRINTN dialect or a FEAT_CRC32 intrinsic on both routes, plus the
    # proof-grade refusal of an undecoded word; host-neutral.
    ("trust-cg-codegen", "aarch64_enc5_floor_census", 14),
    # L10-P5: the machine-IR identity admission. Every pass of the O1/O2/O3
    # ladders sits behind the entry admission that refuses six injected
    # stale-counter or dangling-reference corruptions; an allocating pass is
    # refused at its first allocation when the pass before it left the
    # counter far below or a near miss below a live register (fixtures and,
    # at O2, 194 committed-corpus functions); SROA is refused before it writes
    # a shadow register and promotes a memcpy fill at O1-O3; generated and
    # corpus functions keep every optimizer boundary admitted with every new
    # register inside the range the counter advanced over during its pass;
    # host-neutral (the property file is aarch64-gated, no OS gate).
    ("trust-cg-opt", "mach_id_admission", 6),
    ("trust-cg-codegen", "mach_id_admission_property", 5),
    # L07-P2: the verifier's instruction-derived obligations bound to the live
    # encoder over every enumerated admitted shape, ENC-5's refusal of a word
    # the verifier did not re-derive, native programs of the admitted families
    # checked against the host, and the proof-required refusal that names the
    # instruction-derived row; aarch64-gated, no OS gate.
    ("trust-cg-codegen", "aarch64_instruction_word_binding", 4),
    # L07-P2 / X-OPCODES-P1 / L04-P7: the word-bound memory-effect
    # decomposition against the live encoder over every enumerated admitted
    # scalar and pair shape, ENC-5's refusal of a pair word the parts do not
    # carry, frame- and pointer-heavy programs at O0 and O2 checked against
    # the host (their Mach-O text read back on Darwin), and the proof-required
    # refusal that names the memory-effect row; aarch64-gated, no OS gate.
    ("trust-cg-codegen", "aarch64_memory_effect_binding", 4),
    # L04-P12: the trap-expansion obligations against the live expansion,
    # encoder and ENC-5 for every modeled carrier form, ENC-5's refusal of an
    # unexpanded carrier word, and the final encoder's refusal of a tampered
    # or partial recorded expansion; host-neutral.
    ("trust-cg-codegen", "aarch64_trap_expansion_binding", 4),
    # X-LEAN-P3: the Lean A64 instruction-word model's generated golden corpus
    # (formal/lean/Trust/A64/EncoderGolden.lean, 831 emitter rows) bound to the
    # live encoder, the field-level encoding helpers and ENC-5, ENC-5's refusal
    # of every single-bit corruption of a golden word, and the corrupted-golden
    # text controls; host-neutral.
    ("trust-cg-codegen", "lean_a64_encode_golden_binding", 4),
    # L07-P2 / X-OPCODES-P1: the memory-leaf checker binds every access of
    # the proof-grade pipeline's load/store leaves at O0-O3 to its LIR access,
    # binds nothing once an access is corrupted (slot, source operand, width,
    # stored register), the walk credits a bound access only under the
    # source-bound route's proof name (every part Clean-checked), and the
    # verifying JIT publishes and runs a leaf only when every access is
    # credited. The outcome is pinned for the measured tool digests (package
    # 9192's AY: all refused by name; an AY 2657db47c/Clean ed21fee39 overlay:
    # all credited, published and run); another pair may give either.
    # aarch64-gated, no OS gate.
    ("trust-cg-codegen", "aarch64_memory_source_binding", 4),
    ("trust-cg-codegen", "panic_fuzz_encode", 12),
    # L13-P7 fuzz families, added to the Linux floor from the Linux host. None
    # has a target_os gate, so each compiles the same tests on
    # aarch64-apple-darwin (the x86-64-host JIT legs of
    # panic_fuzz_compile_x86_64 are compiled out on any AArch64 host); not yet
    # run on a Darwin floor host.
    ("trust-cg-lower", "panic_fuzz_lower", 6),
    ("trust-cg-codegen", "panic_fuzz_compile", 6),
    ("trust-cg-codegen", "panic_fuzz_compile_x86_64", 3),
    ("trust-cg-codegen", "panic_fuzz_encode_x86_64", 10),
    ("trust-cg-codegen", "panic_fuzz_macho_fixup", 15),
    ("trust-cg-verify", "panic_fuzz_verify", 7),
    # X-HOST-P13: process-level AY admission, each function-verification
    # request and the refusal note resolve one AY cache root whatever
    # XDG_CACHE_HOME's spelling, HOME, the working directory or the umask;
    # one unix test, needs the recorded AY. Added from a Linux host; not yet
    # run on a Darwin floor host.
    ("trust-cg-verify", "ay_cache_root_agreement", 1),
    # L04-P12 trap-guard obligations: twenty-two tests (the shape catalog
    # against the live expansions, degraded carriers, pipeline guard windows
    # bound to their source, pipeline-function mutations, forged role traps,
    # the certified stack-limit trap, source traps; the native runs of
    # encoded functions are Linux-only and skip loudly here).
    # Added from a Linux host; not yet run on a Darwin floor host.
    ("trust-cg-verify", "aarch64_trap_guard_obligations", 22),
    # The trust-cg-fuzz differential JIT harness: aarch64/unix-gated files that
    # JIT-execute through the host JIT, and host-neutral harness unit targets.
    ("trust-cg-fuzz", "bridge_diff", 23),
    ("trust-cg-fuzz", "cross_call_value_preserved", 2),
    ("trust-cg-fuzz", "ctpop_narrow", 2),
    ("trust-cg-fuzz", "dense_switch_blockarg_encode", 2),
    ("trust-cg-fuzz", "dense_switch_encode", 1),
    ("trust-cg-fuzz", "diff_cmp_overflow", 8),
    ("trust-cg-fuzz", "diff_int_divrem", 1),
    ("trust-cg-fuzz", "diff_narrow_int", 2),
    ("trust-cg-fuzz", "driver_output", 6),
    ("trust-cg-fuzz", "fp_const_and_fcmp", 2),
    ("trust-cg-fuzz", "generator_config", 2),
    ("trust-cg-fuzz", "jit_call_crossing_pressure_diff", 8),
    ("trust-cg-fuzz", "jit_diff_catches_miscompile", 10),
    ("trust-cg-fuzz", "jit_diff_consumer_shapes", 1),
    ("trust-cg-fuzz", "jump_table_in_loop", 1),
    ("trust-cg-fuzz", "sweep2_bitops", 8),
    ("trust-cg-fuzz", "sweep2_chained_casts", 8),
    ("trust-cg-fuzz", "sweep2_i128", 7),
    ("trust-cg-fuzz", "sweep2_large_pressure", 5),
    ("trust-cg-fuzz", "sweep3_cmp_branch_fusion", 14),
    ("trust-cg-fuzz", "sweep3_mem_aliasing", 24),
    ("trust-cg-fuzz", "sweep3_nested_calls_pressure", 7),
    ("trust-cg-fuzz", "sweep3_select_switch_calls", 13),
    ("trust-cg-fuzz", "sweep3_wide_shifts_bitops", 39),
    ("trust-cg-fuzz", "vector_v128_load_store_lane", 1),
    ("trust-cg-fuzz", "verify_narrow_int_0", 1),
    ("trust-cg-fuzz", "verify_narrow_int_1", 1),
    ("trust-cg-fuzz", "verify_narrow_int_2", 1),
    ("trust-cg-codegen", "a64_fp_integer_conversion", 8),
    ("trust-cg-codegen", "e2e_fp_to_int_saturation", 5),
    ("trust-cg-codegen", "e2e_aarch64_exclusive_status_linux", 2),
    ("trust-cg-codegen", "e2e_aarch64_elf_tlsie", 3),
    # 19 host-neutral rows; the two `native` rows are Linux-only.
    ("trust-cg-codegen", "e2e_aarch64_elf_relocation_model", 19),
    # L05-P10/L03-P6 ELF globals twin: its six object/refusal rows are
    # host-neutral (ELF and Mach-O emission); the pthread/dlopen, JIT, addend
    # and attribute legs are Linux-only. Added from a Linux host, where the
    # target was also compiled with its native legs switched off; not yet run
    # on a Darwin floor host.
    ("trust-cg-codegen", "e2e_aarch64_globals_linux", 6),
    # 7 host-neutral rows; the five `native` rows are Linux-only. Counted from
    # the cfg gates on a Linux host, not yet run on a Darwin floor host.
    ("trust-cg-codegen", "e2e_aarch64_elf_stack_zero_fill", 7),
    # 50 host-neutral rows (declaration and data visibility, module-local
    # binding, TLS anchor, merge, repeated-declaration, declared-undefined,
    # refusal and JIT rows); the 33 `native` rows are Linux-only. Counted
    # from the cfg gates on a Linux host, not yet run on a Darwin floor host
    # (49 before the L02-P13 second closure-audit repair's verifier round).
    ("trust-cg-codegen", "aarch64_elf_symbol_binding", 50),
    # AArch64 Mach-O module-local function binding: four object rows (any
    # host) and three macOS AArch64 native rows (ld64 executables, dyld
    # interposition into dylibs, the linked-image replay). All seven passed
    # on this host before being required.
    ("trust-cg-codegen", "aarch64_macho_module_local_binding", 7),
    # L02-P1 (2026-10-24 closure audit): function bindings off AArch64
    # (x86-64 ELF, Mach-O and COFF; RISC-V ELF): six object rows and four
    # LLD link rows (ld.lld, ld64.lld), all host-neutral (the link legs print
    # SKIP without an LLD, which the Darwin runner does not require, so they
    # count as passes there without linking). 7 before the round-2
    # verifier's x86-64 Mach-O rows. Counted from the file on a Linux host,
    # not yet run on a Darwin floor host.
    ("trust-cg-codegen", "module_local_binding_other_targets", 10),
    # trust-ir v41 ABI/linkage residue: 18 host-neutral object rows (ELF and
    # Mach-O reparsed on any host), on the Linux floor since the L02-P6 third
    # closure audit. Counted from the file on a Linux host, not yet run on a
    # Darwin floor host.
    ("trust-cg-codegen", "v41_abi_residue_objects", 18),
    ("trust-cg-codegen", "aarch64_affine_bytes", 13),
    ("trust-cg-codegen", "aarch64_final_layout_crosscheck", 6),
    ("trust-cg-codegen", "aarch64_pseudo_boundary", 6),
    ("trust-cg-codegen", "core_jit_planning", 13),
    # L11-P8/L08-P9: the source-bound JIT chain on this host's own triple,
    # MAP_JIT publication and proof tools. The Trust toolchain's AY must
    # discharge the queries and independent Clean must replay them; the tests
    # fail naming the tools they resolved. Historical qualification is recorded
    # in reports/2026-09-29-darwin-source-bound-jit-qualification/. The current
    # arithmetic matrix requires all 160 publications plus constant/body
    # authority controls; missing replay authority is a failure, never a skip.
    ("trust-cg-codegen", "jit_fail_closed_proof_policy", 9),
    ("trust-cg-codegen", "jit_source_bound_arithmetic", 4),
    # L09-P6/L09-P1: the AArch64 whole-body owner (Boolean, bitwise, shift,
    # select and acyclic control-flow bodies) on this host's own triple: every
    # family binds at O0-O3 in the AOT and JIT preparations (the JIT one
    # byte-identical to the published JIT code), corruptions of the real
    # bodies are refused by name and rejected by the verifier under Enforce,
    # every admitted row's machine model agrees with this CPU on probe bodies
    # (with mis-model decoys refuted), unreplayed rows stay uncredited, and
    # the code runs natively through the MAP_JIT JIT and as Mach-O objects
    # linked against clang-compiled C references. Tool-independent; the
    # opt-in solver-lane qualification is
    # aarch64_source_bound_body_qualification.
    ("trust-cg-codegen", "aarch64_source_bound_body", 9),
    ("trust-cg-codegen", "aarch64_cmp_admission", 7),
    ("trust-cg-codegen", "aarch64_integer_predicate_binding", 8),
    ("trust-cg-codegen", "e2e_aarch64_link_runtime", 18),
    ("trust-cg-cli", "macos_deployment_target", 5),
    ("trust-cg-cli", "link_options", 10),
    # L02-P5: `--linked-image-evidence` refusals (host-neutral) and, through
    # the real binary (native): ld64 records, a replay refusal removing the
    # output, stale records removed by every relink, and `-Wl` objects,
    # unused dylibs and the flat namespace refused.
    ("trust-cg-cli", "linked_image_evidence", 5),
    # 19 on Darwin: 18 host-neutral rows plus the Mach-O constructor run; the
    # seven `linux_native` rows are Linux-only. Counted from the cfg gates on
    # a Linux host, not yet run on a Darwin floor host.
    ("trust-cg-codegen", "e2e_aarch64_elf_sections", 19),
    ("trust-cg-codegen", "abi_definition_refusals", 6),
    ("trust-cg-codegen", "aarch64_stack_probe_decode", 15),
    # 5 on Darwin: the geometry row, the two republication rows and the two
    # host-neutral structural rows (publisher walk, empty range). The two
    # in-place rows (`in_place::*`) are cfg-gated to Linux. Counted from the
    # cfg gates on a Linux host, not yet run on a Darwin floor host.
    ("trust-cg-codegen", "jit_icache_coherence", 5),
    ("trust-cg-codegen", "jit_teardown_policy", 5),
    # 6 on Darwin: the four W^X refusal rows plus the two host-neutral
    # installed-witness rows (recorded-only source there, and the sealed
    # witness forgery refusal); the four kernel-witness rows are Linux-only.
    # Counted from the cfg gates on a Linux host, not yet run on a Darwin
    # floor host.
    ("trust-cg-codegen", "jit_wx_refusal", 6),
    ("trust-cg-codegen", "jit_exception_handling", 11),
    # 9 on this host with either proof-tool pair (its certified function is
    # exhaustive; it needs the discovered authority, not a formal proof).
    ("trust-cg-codegen", "jit_cert_cache_identity_aarch64", 9),
    # L11-P2: the installed-artifact replay through the public API. A
    # verifying raw publication re-reads its sealed MAP_JIT mapping and
    # replays every certified word, both branch targets and the veneer before
    # hand-out; a non-verifying one carries no replay; the proof-required route
    # (AlwaysVerify, and a CachedVerified warm hit) publishes only with a
    # replay covering every function. 3 with either proof-tool pair: its
    # certified function is exhaustive, it needs the discovered authority, not
    # a formal proof. The tamper controls (a flipped byte, a retargeted
    # branch, a moved veneer literal after the seal) are crate unit tests
    # (`jit::jit_installed_replay_tests`); aarch64-gated, no OS gate.
    ("trust-cg-codegen", "jit_installed_artifact_replay", 3),
    # The shared runner (tests/common/rosetta.rs) behind the native rows here:
    # its exit, signal and timeout contracts, and the Darwin launch-hold rows
    # (a run deadline starts once the child has executed code, a child that
    # never starts is bounded separately, and a fresh executable that hangs
    # after it starts is still ended).
    ("trust-cg-codegen", "command_timeout", 18),
    # Linux-floor families that were compiled out here until they moved to
    # the shared tests/common/native_host.rs harness; each now runs its
    # Darwin arm natively.
    ("trust-cg-codegen", "aarch64_native_host_contract", 12),
    ("trust-cg-codegen", "e2e_aarch64_hva_linux", 2),
    ("trust-cg-codegen", "e2e_aarch64_bool_atomics_linux", 2),
    ("trust-cg-codegen", "e2e_aarch64_global_layout", 3),
    ("trust-cg-codegen", "e2e_aarch64_nested_bytes", 8),
    ("trust-cg-codegen", "aarch64_raw_dataflow_boundary", 5),
    ("trust-cg-codegen", "v41_global_linkage", 3),
    ("trust-cg-codegen", "e2e_aarch64_stack_probe_native", 3),
    ("trust-cg-codegen", "aarch64_value_decode_native", 1),
    ("trust-cg-codegen", "aarch64_frame_dataflow_net", 9),
    # WS7.7: v42 declared tuple layouts consumed when a row equals the byte
    # path's declaration-order layout — the producer's c13 tuple module runs
    # to 1002 at O0-O3 against the interpreter, disagreeing rows (swapped
    # offsets, padded size, rustc's reordered tuple, a reordered global) are
    # refused by name, and the default build carries no mutation knob.
    ("trust-cg-codegen", "declared_tuple_layout", 7),
    # L14-P6: compile cost grows linearly with module size (heap and, on
    # macOS, instructions-retired growth per 4x step; the call block, the
    # loop functions, the stack-tuple block and the fill-loop chain), the
    # fixed-cost budget of a trivial compile, plus the call-heavy module
    # against a C reference.
    ("trust-cg-codegen", "aarch64_compile_scaling", 7),
    # L10-P10: Q-register spills (vector, mixed, across-call and dynamic-frame
    # pressure), the pair-spill refusal and the LL/SC whole-window spill
    # strategy (including a borrowed register live only in successor blocks),
    # natively at O0-O3 against C models, with corruption controls.
    ("trust-cg-codegen", "e2e_aarch64_vector_spills", 14),
    # L10-P4: mac-reg-block at O2/O3, pass on and off through the in-process
    # disable list, natively against a C reference. Generated kernels whose
    # failed check returns -1: admitted nests rewritten exactly once, negative
    # controls left unrewritten with identical code, and the ported
    # matmulfuzz sweep. The current rustc bridge's p4_matmul nest (a failed
    # check calls panic_bounds_check): rewritten exactly once, run through the
    # JIT with a recording panic stub, and a one-short copy that must call it.
    # The bridge's pre-v52 check triple (`const` + `icmp ult` + kindless
    # `assert`), kept as a fixture with the p4_matmul nest captured in it, is
    # refused at the shared TrustIR v52 admission floor on the object path and
    # the JIT. Nine tests: four host-neutral (three rewrite-count, one
    # object-path admission) and five native (four differentials, one JIT
    # admission).
    ("trust-cg-codegen", "e2e_aarch64_mac_reg_block_differential", 9),
    # h1_vec_push_sum: LICM's dereferenceable-frame speculation and the
    # register-bound trap-branch fold at O2/O3, on and off through the
    # in-process disable list, natively against a C reference with trapping
    # negative controls, plus the preheader-writer rows pinning LICM's
    # insertion point after preheader stores and trap carriers (four
    # host-neutral compile tests, two native differentials).
    ("trust-cg-codegen", "e2e_aarch64_vec_len_guard_differential", 6),
    # L10-P3: per-pass translation validation through the public Pipeline.
    # Every kernel compiles at O1-O3 under the enforcing policy, byte-equal
    # to validation off, with every dedicated validator checking real changed
    # runs (two host-neutral tests); the enforce-built kernels run against a
    # C reference, and the guarded pair traps (not faults) one element short
    # at a page end, the mem-pair defect the region validator found (one
    # native row).
    ("trust-cg-codegen", "e2e_aarch64_pass_validation", 5),
    # L10-P1: post-allocation value-flow validation through the public
    # Pipeline. Ten kernels (values across calls, spill pressure, a
    # jump-table switch, stack arguments both ways, FP across calls, a stack
    # array, a 32 KiB frame probed by a counted loop, a stack-protected
    # array, a 32-bit array sum whose loop late post-index formation turns
    # into a post-indexed pointer, spill pressure beside a live stack array)
    # compile at O0-O3 under the enforcing policy with the composed
    # comparison and both split stage comparisons validated for every
    # function, byte-equal to validation off (one host-neutral test);
    # sixteen corruption controls on the real stage inputs are refused
    # (sixteen host-neutral tests, one of them on an AArch64 ELF compile for
    # the lo12 fusion, six judging the composed comparison too); three
    # wiring tests (an unmodeled function refused by name under enforce and
    # reported under the diagnostic policy, the default tier's uncovered
    # record); two native rows (the enforce-built kernels against a C
    # reference, and the outgoing-area corruptions disagreeing with it while
    # the uncorrupted stream agrees). Twenty-two tests.
    ("trust-cg-codegen", "e2e_aarch64_post_ra_value_flow", 22),
    # L09-P3: the composed transition record (TrustIR -> LIR -> raw MachIR
    # -> validated optimizer runs -> post-allocation comparison -> proof-grade
    # encoding) through the public Pipeline and Compiler. Eight affine
    # kernels compose at O0-O3 from their exact TrustIR source to the bytes
    # their object carries; recording never changes an emitted byte;
    # out-of-domain functions are named and not required; dropped links,
    # swapped interfaces, unvalidated rewrites (AOT instrumentation, a
    # reported and a silent result change) and every flipped published byte
    # are refused by name; the JIT publishes exactly the composed bytes; the
    # proof-required routes require the composition before proof promotion
    # (real AOT instrumentation refused by composition on both, a composing
    # function never); a whole-body family census; the proof-grade objects
    # against a C reference natively. Nine tests.
    ("trust-cg-codegen", "e2e_aarch64_composed_transition", 9),
    # OD-127 (main 53006040e), classified here so the floor runs: LDP
    # formation keeps a plain load after a load-acquire at O0-O3 (JIT values
    # and code shape), and integer addresses of two distinct globals may
    # alias an earlier store (macOS typed-module JIT). Two tests.
    ("trust-cg-codegen", "aarch64_mem_pair_acquire_order", 2),
    # The trust-ir must-refuse corpus through every admission lane, the host
    # JIT lane macOS-guarded (main 9f1eb65a4), classified here so the floor
    # runs: every row refused, the control row's bound, and the three default
    # WASM entry-policy tests. Five tests.
    ("trust-cg-codegen", "must_refuse_corpus", 5),
    # Refined narrow calls and returns (main c298d74e1): Mach-O text and ELF
    # objects identical to the unrefined signatures, poisoned register bits
    # canonicalized, the legal Darwin ABI for loaded narrow returns, and
    # native C drivers checking the extensions (16 drivers). Six tests.
    ("trust-cg-codegen", "a64_refine_byte_invariance", 6),
    # Shared NZCV observation (main 7ec11048d), classified here so the floor
    # runs: an MRS NZCV after a compare keeps AndCmpFuse from fusing it, and
    # the original, the pass result and the historical TST mutant (negative
    # control) run through the pipeline and the JIT at O0-O3. One test.
    ("trust-cg-codegen", "jit_nzcv_observation", 1),
    ("trust-cg-codegen", "e2e_aarch64_f16_fcvt", 2),
    # L01-P7: the six host-neutral rows (ELF placement against the AAPCS64
    # model, FEAT_FP16 classifier, profile refusal, mutations, C oracle
    # wiring). Its three native rows are Linux GNU only: DarwinPCS packs HFA
    # stack members, so the Linux corpus is not a Darwin oracle.
    ("trust-cg-codegen", "e2e_aarch64_f16_abi_linux", 6),
    ("trust-cg-codegen", "aarch64_volatile_access_preservation", 4),
    # Native C differentials through tests/common/aarch64_native.rs, which
    # selects the Darwin triple and links with the host cc on this host.
    ("trust-cg-codegen", "e2e_aarch64_narrow_int_diff", 1),
    ("trust-cg-codegen", "e2e_aarch64_call_arg_signext", 1),
    ("trust-cg-codegen", "e2e_aarch64_i128_narrow_call", 1),
    ("trust-cg-codegen", "e2e_aarch64_stack_narrow_args", 2),
    ("trust-cg-codegen", "e2e_aarch64_callee_saved_fpr", 2),
    ("trust-cg-codegen", "e2e_aarch64_calling_conv", 2),
    ("trust-cg-codegen", "e2e_aarch64_tail_call_abi", 6),
    # Sited assertion delivery at O0-O3 through the same helper: the payload,
    # location, trap-if-the-entry-returns and AssertInvoke cleanup/rethrow
    # rows. Two tests, no cfg (the file's census); 2 passed on a Linux host
    # on 2026-10-15, not yet run on a Darwin host (LD-56).
    ("trust-cg-codegen", "sited_assert_delivery_native", 2),
    # One host-neutral Mach-O call/frame matrix. The stack-walk execution
    # test is Linux-only; this row supplies no Darwin native frame credit.
    ("trust-cg-codegen", "aarch64_nounwind_tail_frame", 1),
    # First-class closure values (L05-P4): closure literals, capture spreading
    # through CallIndirect and nested closure/FnDef/SymbolAddr constants, run
    # against the trust-ir reference interpreter and a C model at O0-O3, plus
    # named-refusal controls.
    ("trust-cg-codegen", "e2e_aarch64_closures", 8),
    # Sequences and boxed sets (L05-P8): the trust_cg_lower::sequence_layout
    # image through constants, parameters, results, calls, selects and loops
    # (including loop-carried images), the SeqMap family as counted loops with
    # a fresh cell per element, run against the trust-ir reference interpreter
    # and a C model at O0-O3; every run-time length witness trapping in a
    # forked child; plus named refusals (replaceable callees included).
    ("trust-cg-codegen", "e2e_aarch64_sequences", 14),
    # Branch relaxation (dcb2accf2): far B.cond/CBZ/TBZ branches relax in
    # the production pipeline; both rows decode-and-interpret the object and
    # run it natively through the raw JIT on this host.
    ("trust-cg-codegen", "aarch64_branch_relaxation", 2),
    # A loaded bool is its byte read as `!= 0` (bb4bbac08): the reference
    # interpreter, the host JIT natively at O0-O3 and the AArch64 Mach-O
    # object decoded and interpreted.
    ("trust-cg-codegen", "bool_load_semantics", 3),
    # A select on a bool loaded before an indirect call re-tests the bool
    # after it (select-fuse stops at calls), run through the JIT at O0-O3.
    ("trust-cg-codegen", "aarch64_select_flags_across_call", 1),
    # A fully unrolled counted loop whose select reads the loop's own exit
    # test keeps that reader defined, run through the JIT at O0-O3.
    ("trust-cg-codegen", "aarch64_unroll_trip_test_reader", 1),
    # A descending map whose count passes i32 range stays scalar (neon_map's
    # 32-bit index would land 2^32 elements low): 2^31+21 elements of address
    # space over one file mapped repeatedly, run through the JIT at O2/O3.
    ("trust-cg-codegen", "aarch64_neon_map_reverse_wide_count", 1),
    # Rotated FP maps (neon_fmap) enter the vector code only below their
    # bound, from an i32-range start on the MIXED path (interior bases of one
    # large reservation), and stay scalar under a negative zero-extended bound
    # (2^32 scalar iterations over one file mapped repeatedly), O0-O3.
    ("trust-cg-codegen", "aarch64_neon_fmap_rotated_entry", 1),
    ("trust-cg-codegen", "aarch64_neon_fmap_zext_bound", 1),
    # AArch64 JIT canaries without a host-OS guard.
    ("trust-cg-codegen", "aarch64_incoming_arg_zero_offset_load", 1),
    ("trust-cg-codegen", "aarch64_petri_o2_o3_incoming_arg_canary", 1),
    # macOS-guarded native link-and-run families: each test prints SKIP and
    # returns on any other host, so a Darwin run is their only execution.
    ("trust-cg-codegen", "e2e_aarch64_atomics", 3),
    ("trust-cg-codegen", "e2e_aarch64_byte_gather_ro", 1),
    ("trust-cg-codegen", "e2e_aarch64_call_arg_ptr_theft", 2),
    ("trust-cg-codegen", "e2e_aarch64_coroutine", 4),
    ("trust-cg-codegen", "e2e_aarch64_ctpop", 1),
    # trust-ir WS3.20: rotates, bit counts, byte/bit reversal, copySign and
    # the MemCopy/MemSet bulk-memory pair against a C reference at O0-O3,
    # plus the named no-wire-image refusal.
    ("trust-cg-codegen", "e2e_aarch64_bit_intrinsics_bulk_memory", 2),
    ("trust-cg-codegen", "e2e_aarch64_data_reloc", 3),
    ("trust-cg-codegen", "e2e_aarch64_eh_catch", 7),
    # Eight since 2026-10-10: two rows run an invoke whose normal destination
    # is a loop header, with a landing pad that uses its own constant (the O3
    # LICM/CSE/GVN pad-value reproducers), and one runs a catch-and-retry loop
    # whose header is the landing pad (the O2/O3 reproducer only LICM's
    # invoke-block refusal closes), all at O0-O3 against a source model.
    ("trust-cg-codegen", "e2e_aarch64_eh_invoke_trust_ir", 8),
    ("trust-cg-codegen", "e2e_aarch64_eh_o2_and_walkthrough_trust_ir", 6),
    ("trust-cg-codegen", "e2e_aarch64_eh_resume_trust_ir", 5),
    # L03-P2: 6 host-neutral rows (Linux-object EH table decode at O0-O3,
    # LSDA mutation tooling, the adapter moving an invoke that follows another
    # call into a block of its own, which calls before an invoke split or stay
    # refused, and the selection-introduced-call and missing-personality
    # refusals); the six link/run/readback/mutation rows are Linux-only.
    # Counted from the cfg gates on a Linux host, not yet run on a Darwin
    # floor host.
    ("trust-cg-codegen", "e2e_aarch64_eh_linux", 6),
    # L03-P11: typed catches through GOT-relocated TType slots (identity
    # slots, catch-all slot fixed at lowering across O0-O3 pad pruning), a
    # typed catch with a cleanup, catch-all after typed, a module mixing the
    # C++ and Rust personalities (rustc-linked driver) through compact-unwind
    # and through DWARF-fallback frames (one zPLR CIE per personality),
    # standalone-linker GOT binds, and named refusals (including typed
    # catches under the Rust personality and the JIT's typed-catch and
    # mixed-personality refusals).
    ("trust-cg-codegen", "e2e_aarch64_eh_typed", 13),
    # X-DARWIN-P7: the mixed-codegen exception/RAII/destructor-count
    # campaign. C++ throwers and catchers and Rust panics through CG
    # compact-unwind and DWARF-fallback frames (cleanup pads running C++
    # destructors and Rust drop glue, catch-all and typed pads, rethrow,
    # nesting, a throw inside a cleanup), and the Linux 768-case campaign's
    # frame (memory words, a throw through a function-pointer slot, 64-bit
    # edge inputs): 632 chain, 1,152 touch and 184 Rust cases per build, each
    # equal to the C++-only or Rust-only reference build and the models, AOT
    # at O0-O3 (executables and a CG dylib; linked __unwind_info read back)
    # and through the unchecked JIT at O0-O3 (typed chains refused by name),
    # with mutated-frame negative controls; plus the host-neutral object rows.
    # L03-P14: every campaign object and JIT image passes the exception-table
    # obligations (testing grade), and corrupted objects, IR sides and JIT
    # images are refused by the obligation they break (three more rows).
    # Darwin-only: the Linux floor admits only Linux-native files
    # (native_test_host_matrix.py).
    ("trust-cg-codegen", "e2e_aarch64_eh_raii_darwin", 12),
    ("trust-cg-codegen", "e2e_aarch64_ext_stencil", 1),
    ("trust-cg-codegen", "e2e_aarch64_f16_scalar", 4),
    ("trust-cg-codegen", "e2e_aarch64_f16_to_i128", 1),
    ("trust-cg-codegen", "e2e_aarch64_fcmp_nan", 1),
    ("trust-cg-codegen", "e2e_aarch64_fp_loop_carried_reduction", 2),
    ("trust-cg-codegen", "e2e_aarch64_fp_minmax", 1),
    ("trust-cg-codegen", "e2e_aarch64_fp_rounding", 1),
    ("trust-cg-codegen", "e2e_aarch64_fp_to_int", 1),
    ("trust-cg-codegen", "e2e_aarch64_fptosi_sat", 4),
    ("trust-cg-codegen", "e2e_aarch64_fptosi_sat_i128", 1),
    ("trust-cg-codegen", "e2e_aarch64_global_var", 1),
    # L05-P10: relocated Mach-O TLS templates, the JIT data image, SymbolAddr
    # addends and data-symbol attributes against a C driver at O0-O3, linked by
    # ld64 and the standalone linker, plus the refusals that stay.
    ("trust-cg-codegen", "e2e_aarch64_globals_darwin", 7),
    ("trust-cg-codegen", "e2e_aarch64_heap_dealloc", 2),
    ("trust-cg-codegen", "e2e_aarch64_niche_enum", 2),
    # L05-P5: direct-tag enums beyond the canonical shape (explicit and signed
    # discriminants, producer layouts, enum/record/relocation globals) against
    # a C driver and the trust-ir interpreter at O0-O3, plus named refusals.
    ("trust-cg-codegen", "e2e_aarch64_direct_enums", 4),
    # L05-P9: borrows, binding frames and Undef through the named legalization
    # stage (value-copy borrows with recorded roots, in-place frame slots,
    # NoUndef zero materialization) against a C driver and the trust-ir
    # interpreter at O0-O3, plus the strict entry, the receipts and the named
    # refusals (four host-neutral tests and one native).
    ("trust-cg-codegen", "e2e_aarch64_borrows_frames", 5),
    # L05-P2 (D05) construct sweep: trust-ir types, instructions, constants,
    # casts (the MakeAggregate, v50 ArraySplat / Splat and Transmute
    # lowerings included) and module
    # tables the inventory held model-only or refused, run at O0-O3 against
    # the trust-ir interpreter (or its stated twin) and C models, plus the
    # named refusals that stay.
    ("trust-cg-codegen", "e2e_aarch64_construct_sweep_types", 6),
    ("trust-cg-codegen", "e2e_aarch64_construct_sweep_insts", 7),
    # Actual direct-THIR Result constructors, complete payload/aliasing and
    # layout/tag/domain controls through canonical Compiler::compile.
    ("trust-cg-codegen", "result_aggregate_native", 5),
    ("trust-cg-codegen", "e2e_aarch64_construct_sweep_casts", 4),
    ("trust-cg-codegen", "e2e_aarch64_construct_sweep_tables", 2),
    ("trust-cg-codegen", "e2e_aarch64_i128_icmp", 1),
    # A 128-bit divisor whose low word is zero, constant and runtime, through
    # the division-by-zero guard at O0/O2/O3 against the __int128 reference.
    ("trust-cg-codegen", "e2e_aarch64_i128_div_zero_guard", 1),
    ("trust-cg-codegen", "e2e_aarch64_i128_overflow", 5),
    ("trust-cg-codegen", "e2e_aarch64_i128_shift", 1),
    ("trust-cg-codegen", "e2e_aarch64_i128_switch", 2),
    ("trust-cg-codegen", "e2e_aarch64_i128_to_f16", 1),
    # L04-P11: the C trampolines plus the function-pointer table, switch/call
    # interplay and call-ABI module at O0-O3. Counted from the file on a Linux
    # host; the second test has not yet run on a Darwin floor host.
    ("trust-cg-codegen", "e2e_aarch64_indirect_call", 2),
    ("trust-cg-codegen", "e2e_aarch64_int_to_float", 1),
    ("trust-cg-codegen", "e2e_aarch64_narrow_atomics", 3),
    ("trust-cg-codegen", "e2e_aarch64_concurrency", 7),
    # L03-P3: the C11/Rust -> AArch64 memory-order mapping checked on the
    # words the selector emits for every atomic request (Darwin AOT, LSE and
    # baseline profiles, O0-O3) with named refusals of weakened words, plus the
    # Apple clang barrier differential (macOS-only); and the native
    # MP/SB/LB/IRIW/2+2W litmus harness over trust-cg-compiled thread bodies.
    ("trust-cg-codegen", "aarch64_memory_order_obligations", 5),
    ("trust-cg-codegen", "e2e_aarch64_memory_order_litmus", 2),
    ("trust-cg-codegen", "e2e_aarch64_narrow_signed_cmp", 1),
    ("trust-cg-codegen", "e2e_aarch64_p0_miscompiles", 6),
    ("trust-cg-codegen", "e2e_aarch64_p1_p2_gaps", 9),
    ("trust-cg-codegen", "e2e_aarch64_read_global", 2),
    ("trust-cg-codegen", "e2e_aarch64_sitofp_signext", 1),
    ("trust-cg-codegen", "e2e_aarch64_struct_byval", 1),
    # The Darwin swiftcall aggregate run plus the host-neutral refusals: each
    # shape by name under AAPCS64, and the budget>=5 and packed shapes.
    ("trust-cg-codegen", "e2e_aarch64_swift_aggregate", 4),
    ("trust-cg-codegen", "e2e_aarch64_swift_scalar", 1),
    # Whole-pointee GEP arithmetic at O0-O3 against the pinned trust-ir
    # interpreter, through the host JIT (the file compiles on Linux and macOS
    # AArch64 and x86-64), shared with the Linux floor since `4ec1eee16`. All
    # 14 rows compile on Darwin. Counted from the file on a Linux host; not
    # yet run on a Darwin floor host.
    ("trust-cg-codegen", "flat_gep_semantics", 14),
    ("trust-cg-codegen", "storage_geometry", 4),
    # Captured proof-required framed/narrow bodies and the actual singleton
    # reference/native differential belong to the required Darwin denominator.
    ("trust-cg-codegen", "aarch64_framed_identity_control", 6),
    ("trust-cg-codegen", "aarch64_narrow_return_body", 2),
    ("trust-cg-codegen", "single_inhabited_native", 1),
    ("trust-cg-codegen", "aarch64_darwin_signed_tail", 2),
    ("trust-cg-codegen", "e2e_aarch64_make_closure", 2),
    # Shared compiler consumers: actual Mach-O link/run, host JIT helper-body
    # authentication and tiered JIT execution. Keep these in the required
    # Darwin denominator, not the x86-only exclusions below.
    ("trust-cg-codegen", "aot_inline_only_bodies", 6),
    ("trust-cg-codegen", "inline_only_authentication", 7),
    ("trust-cg-codegen", "tier_up", 6),
    # L04-P11: the dense/sparse and shared-arm legs plus the selector-width
    # and strategy matrix (its objdump read-back and garbage-upper-bits legs
    # are Linux-only). Counted from the file on a Linux host; the matrix test
    # has not yet run on a Darwin floor host.
    ("trust-cg-codegen", "e2e_aarch64_switch", 3),
    # Every switch strategy and selector width, a selector spilled under
    # register pressure, and indirect calls through function-pointer tables,
    # at O0-O3 against the host C compiler (L04-P11).
    ("trust-cg-codegen", "e2e_aarch64_switch_forms", 3),
    ("trust-cg-codegen", "e2e_aarch64_u128_checked_mul", 2),
    ("trust-cg-codegen", "e2e_aarch64_udot_popcount", 3),
    ("trust-cg-codegen", "e2e_aarch64_unit_return", 1),
    ("trust-cg-codegen", "e2e_aarch64_variadic_call", 1),
    ("trust-cg-codegen", "e2e_aarch64_vector_binop", 1),
    ("trust-cg-codegen", "e2e_aarch64_vector_fp_unary", 1),
    ("trust-cg-codegen", "e2e_aarch64_vector_lane", 1),
    # L04-P6: the unsigned-lane, V64-constant and vector OR-NOT lowerings at
    # O0-O3 against clang -O3 NEON intrinsics (93 functions x 4096 vectors;
    # vornq/vorn), and the remaining refusals by name.
    ("trust-cg-codegen", "e2e_aarch64_neon_admission", 3),
    # L04-P3: 121 TrustIR FP conversion, rounding and arithmetic functions on
    # the proof-grade AOT route at O0-O3 (ENC-5-checked words, dlopen) and the
    # JIT at O1/O2 against the independent reference, and the committed
    # record of the exhaustive release run checked; five tests.
    ("trust-cg-codegen", "e2e_aarch64_fp_ieee_lowering", 5),
    ("trust-cg-codegen", "aarch64_v4i32_vector_shift", 3),
    ("trust-cg-codegen", "neon_array_execution", 3),
    ("trust-cg-codegen", "neon_farray_execution", 3),
    # X-OPCODES-P11: two host-neutral object tests (ELF and Mach-O) and two
    # native tests that link and run the Mach-O object on this host.
    ("trust-cg-codegen", "neon_ld1_st1_post_execution", 4),
    # X-OPCODES-P11 live writebacks: two host-neutral object tests (ELF and
    # Mach-O) and two native tests that link and run the Mach-O object here.
    ("trust-cg-codegen", "neon_butterfly_writeback_execution", 4),
    # AArch64 CEGIS superoptimizer: every row is host-neutral (the native
    # rows use the shared aarch64_native helper). Counted from the cfg gates
    # on a Linux host, not yet run on a Darwin floor host.
    ("trust-cg-codegen", "e2e_cegis_superopt", 10),
    ("trust-cg-codegen", "guard_kernel_gate_overflow_linkrun", 2),
    ("trust-cg-codegen", "guard_kernel_gate_overflow_mul_linkrun", 3),
    ("trust-cg-codegen", "overflow_inst_carrier_rewrite_linkrun", 2),
    ("trust-cg-codegen", "e2e_native_link", 6),
    ("trust-cg-codegen", "e2e_macho_deployment_target", 4),
    ("trust-cg-codegen", "macho_code_signature_native", 7),
    ("trust-cg-codegen", "e2e_aarch64_darwin_variadic_wide", 3),
    # X-DARWIN-P4: DarwinPCS twins of the Linux L01 aggregate-stack, variadic
    # and Bool corpora through tests/common/darwin_c_boundary.rs, against Apple
    # clang at O0-O3 (both directions where TrustCG can be the callee), with
    # the named refusals that stay.
    ("trust-cg-codegen", "e2e_aarch64_aggregate_stack_darwin", 2),
    ("trust-cg-codegen", "e2e_aarch64_variadic_darwin", 3),
    ("trust-cg-codegen", "e2e_aarch64_bool_abi_darwin", 1),
    # L01-P5: X8 hidden-result (sret) results through function pointers and
    # variadic callees, C caller -> CG callee and CG caller -> C callee.
    ("trust-cg-codegen", "e2e_aarch64_sret", 6),
    ("trust-cg-codegen", "e2e_macho_standalone_got_tlv", 14),
    ("trust-cg-codegen", "e2e_aarch64_macho_dylib", 8),
    # L02-P5: linked-image evidence records (macho::linked_image) for CG
    # Mach-O executables and dylibs. Seven host-neutral rows (standalone-linker
    # records at O0-O3, a program importing from a CG dylib, the image and
    # object corruption controls, malformed inputs, the record file and the
    # TAPI stub reader) and nine native rows (ld64 images with chained fixups
    # and LC_DYLD_INFO, run to exit 42; the -no_data_const, direct-weak and
    # exported-symbols-list rows; -dead_strip; ld64 corruption controls;
    # unnamed link inputs and unused dylibs; SUBTRACTOR differences and
    # optimization-hint objects).
    ("trust-cg-codegen", "macho_linked_image_evidence", 16),
    ("trust-cg-codegen", "stack_guard_admission", 4),
    ("trust-cg-codegen", "dialect_machine_execution", 10),
    # L05-P11: the pinned trust-ir corpus's dialect rows legalized by the
    # registry (ty_dialect_v39, inst_dialect, inst_vector_crosslane,
    # inst_vector_dialect) and a per-op vector sweep, run as AOT objects linked
    # with a C driver and through the JIT at O0-O3 against trust-ir's
    # interpreter or a source-payload reference, a runtime call over a
    # registered nominal type (its carrier ABI, AOT and JIT), plus the named
    # refusals and the proof policy (including a verifying JIT validation mode
    # on its own). All ten passed on this host before being required.
    ("trust-cg-codegen", "dialect_legalization_corpus", 10),
    ("trust-cg-codegen", "aot_profile_execution", 3),
    # macOS-guarded JIT execution on the Darwin host.
    ("trust-cg-codegen", "jit_crash_replay", 3),
    # L04-P12: every trap carrier's expansion through the O0 pipeline (its
    # stated expansion judged before allocation) and the JIT: 49 inputs inside
    # the 25 guards return, 52 outside them die of SIGTRAP from BRK #1 (ESR
    # EC 0x3C, ISS 1, the BRK word at the faulting PC); W cases run with
    # garbage upper halves; macOS-guarded.
    ("trust-cg-codegen", "e2e_aarch64_trap_expansion_native", 1),
    ("trust-cg-codegen", "jit_cross_thread_execute_mode", 1),
    ("trust-cg-codegen", "local_function_address_jit", 3),
    # L03-P9: the Darwin hw.optional sysctl host truth, per-function LSE and
    # FP16 under the baseline profile (AOT, linked and run), FEAT_CRC32
    # intrinsics as one CRC32 word or the baseline expansion (run through the
    # JIT at O0-O3 against the LLVM intrinsic; Apple AOT O2 words counted),
    # the serialized-replay contract naming `crc`, runtime dispatch choosing
    # the fast path here and the fallback without `crc`, the refusals of an
    # unmodeled feature by name, and the CRC32 coverage-gate rows staying RED
    # beside credited controls; macOS-guarded.
    ("trust-cg-codegen", "aarch64_function_target_features", 12),
    ("trust-cg-codegen", "jit_mrs_tpidr", 2),
    ("trust-cg-codegen", "jit_runtime_hardening", 4),
    ("trust-cg-codegen", "jit_map_jit_entitlement", 5),
    ("trust-cg-codegen", "jit_external_symbol_resolution_policy", 6),
    ("trust-cg-codegen", "jit_integration", 59),
    ("trust-cg-codegen", "jit_ay_widened_overflow_regression", 3),
    ("trust-cg-codegen", "jit_sparse_substitute_regression", 29),
    # WS7.6: by-value direct-tag enum ExtractField (F-112), JIT-run against
    # the Part A-Lean kernel-certified values and the trust-ir interpreter,
    # plus the review adversarials (enum fields of structs, nested enums, ...).
    ("trust-cg-codegen", "enum_field_projection", 13),
    # WS7.2: the trust-ir -> native differential over the vendored
    # trust_ir_exec corpus and the pinned-seed aggregate generator, JIT at
    # O0-O3 against the trust-ir interpreter (the adapter step no certificate
    # covers); six tests in the default build.
    ("trust-cg-codegen", "trust_ir_interp_differential", 6),
    # WS7.5: the codegen license bound to evidence (F-006) and claim-less
    # bodies refused by default (DG-73), on every lane, with the real Clean
    # `addmul` JIT-run against the trust-ir interpreter (its `host_jit` rows
    # are the macOS/Linux-gnu AArch64 guard). The mutation-knobs control is
    # feature-gated and not counted.
    ("trust-cg-codegen", "codegen_license_evidence", 9),
    # WS7.1: InsertField / InsertElement value semantics (F-111), JIT-run
    # against closed forms and the trust-ir reference interpreter.
    ("trust-cg-codegen", "insert_field_value_semantics", 9),
    # macOS-guarded Mach-O link-and-run suites that skip without an AArch64
    # host cc.
    ("trust-cg-codegen", "abi_many_args_e2e", 20),
    ("trust-cg-codegen", "e2e_correctness", 4),
    ("trust-cg-codegen", "e2e_cse_movz_movn", 1),
    ("trust-cg-codegen", "e2e_full_pipeline", 30),
    ("trust-cg-codegen", "e2e_multiblock_builder", 7),
    ("trust-cg-codegen", "e2e_opt_levels", 6),
    ("trust-cg-codegen", "e2e_run", 15),
    ("trust-cg-codegen", "e2e_stack_alloc", 5),
    ("trust-cg-codegen", "e2e_bridge", 7),
    ("trust-cg-codegen", "xxh3_trust_ir", 16),
    ("trust-cg-codegen", "xxh3_main_loop_trust_ir", 13),
    ("trust-cg-codegen", "xxh3_medium_long_trust_ir", 3),
    ("trust-cg-codegen", "ty_bfs_minimal", 9),
    # Linux-floor AArch64 ELF DWARF/CFI object checks read back by the LLVM
    # tools; the DWARF target's lldb ELF-object leg is macOS-only.
    ("trust-cg-codegen", "aarch64_elf_dwarf", 13),
    ("trust-cg-codegen", "aarch64_elf_cfi_differential", 3),
    # L03-P13: all thirteen rows are host-neutral (ELF objects read back by the
    # reparse reader and the file's own walker, and certified AArch64/x86-64
    # ELF and Mach-O compiles); the GNU readelf leg inside the matrix rows is
    # Linux-only. Counted from the cfg gates on a Linux host, not yet run on a
    # Darwin floor host.
    ("trust-cg-codegen", "aarch64_elf_eh_relocation_inventory", 13),
    # Mach-O inspection and debugger legs (otool, nm, objdump, dwarfdump,
    # lldb) that skip on Linux. The lldb leg needs an authorized debugserver.
    ("trust-cg-codegen", "e2e_aarch64_link", 33),
    ("trust-cg-codegen", "aarch64_encoding", 113),
    ("trust-cg-codegen", "compact_unwind_integration", 5),
    ("trust-cg-codegen", "dwarf_dwarfdump", 2),
    ("trust-cg-codegen", "e2e_macho_link", 9),
    ("trust-cg-codegen", "e2e_macho_validation", 20),
    ("trust-cg-codegen", "macho_integration", 7),
    ("trust-cg-codegen", "e2e_abi_dual_target", 4),
    ("trust-cg-codegen", "o3_debug_lldb_line_200loc", 2),
    # Linux-floor LLVM IR importer targets, built with the `driver` feature the
    # Linux floor's TARGET_FEATURES names: host-triple Mach-O programs linked
    # with cc and run natively (IntMM IR from the host clang), and explicit
    # Mach-O/ELF object checks.
    ("trust-cg-llvm-import", "ary3_init_o2_e2e", 2),
    ("trust-cg-llvm-import", "ary3_reverse_accum_proof_facts", 2),
    # The revertBits vectorizer rows run each variant at O0 and O2 natively:
    # the trip shapes the coverage clause refuses (odd, nonzero-start,
    # run-time and inclusive trips) and those `clause_gap` refuses beside it
    # (a mid-tested loop, an argc-keyed trip, and the side-effect rows: a
    # store of the induction in the latch and in the body, plain and
    # volatile), beside the RBIT selection and frame-shape rows.
    ("trust-cg-llvm-import", "bitreverse_intrinsics", 15),
    ("trust-cg-llvm-import", "cast_e2e", 1),
    ("trust-cg-llvm-import", "casttest3_e2e", 1),
    ("trust-cg-llvm-import", "divtest_e2e", 1),
    ("trust-cg-llvm-import", "fp_e2e", 9),
    ("trust-cg-llvm-import", "intmm_o2_e2e", 2),
    ("trust-cg-llvm-import", "objectsize_intrinsic", 1),
    ("trust-cg-llvm-import", "printf_globals", 5),
    ("trust-cg-llvm-import", "switch_e2e", 4),
    # L02-P13: the seventeen host-neutral rows (ELF symbol facts, the
    # extern_weak call spelling, the named refusal of weak calls whose
    # address form this backend would change, COMDAT admission vs backend
    # grouping, the Mach-O weak definitions and named refusals, the second
    # closure-audit repair's five: importer symbol facts and named refusals
    # through import_text, per-global @llvm.used retention, unreferenced
    # declarations, and the coverage-mapping section refusal, its first
    # verifier round's three: placed-section creation order, x86-64 ELF
    # retention, and @llvm.used declarations, its second verifier round's
    # two: hidden/protected available_externally globals and mergeable
    # unnamed_addr constants in explicit sections refused by name, and its
    # third verifier round's one: dso_local declarations whose address the
    # module's code takes refused by name, the fifth round's one:
    # integer literals read at their type's width, and the third closure
    # audit's repair's one: the linkage and visibility of every global
    # initializer shape); the thirteen GNU ld/gold/LLD native rows are
    # compiled only for AArch64 Linux GNU. The thirteen rows of the repairs
    # were counted from the file on a Linux host and are not yet run on a
    # Darwin host (5 before the repair, 10 before its first verifier round,
    # 13 before its second, 15 before its third, 16 before the fifth round,
    # 17 before the third closure audit's repair).
    ("trust-cg-llvm-import", "symbol_linkage_elf", 18),
    ("trust-cg-llvm-import", "ws2_stack_protector_target", 6),
    # L02-P14: c-string escapes decoded as LLVM decodes them (a corpus of
    # every escape rule and every byte value), and length mismatches refused
    # by name; the two native rows compare trust-cg's bytes with clang reading
    # the same IR, through ld64, and require clang to reject what is refused.
    ("trust-cg-llvm-import", "c_string_escapes_e2e", 4),
    # L01-P11: `sret` carried onto trust-ir; the native rows run clang's IR of
    # C sret callers and callees (-O0..-O3) through trust-cg against clang,
    # linked by ld64, and refuse clang's indirect sret call by name.
    ("trust-cg-llvm-import", "sret_abi_e2e", 4),
    # L01-P11: `zeroext`/`signext` carried as the call edge's signedness; the
    # native rows run clang's IR of C callee and caller units (-O0..-O3, and
    # `_Bool` at -O1..-O3) through trust-cg against clang, linked by ld64.
    ("trust-cg-llvm-import", "int_ext_abi_e2e", 4),
)
# Linux-floor targets whose every test is compiled out on Darwin by a
# file-level Linux cfg. An empty suite can never satisfy the floor, so they are
# reported as uncovered here; their Darwin ports are open work.
DARWIN_COMPILED_OUT = {
    ("trust-cg-codegen", "canonical_bounds_assert_linux"):
        "Linux canonical bounds trap execution; no Darwin native port",
    ("trust-cg-codegen", "e2e_aarch64_variadic_linux"):
        "Linux AAPCS64 variadic native corpus; its DarwinPCS twin is the required "
        "target e2e_aarch64_variadic_darwin",
    ("trust-cg-codegen", "e2e_aarch64_aggregate_stack_linux"):
        "Linux aligned-aggregate stack native corpus; its DarwinPCS twin is the "
        "required target e2e_aarch64_aggregate_stack_darwin",
    ("trust-cg-codegen", "e2e_aarch64_elf_link"):
        "ELF object/link native corpus; Mach-O equivalents are separate targets",
    ("trust-cg-codegen", "e2e_aarch64_host_target_authority_linux"):
        "Linux GNU host-derived target authority (AAPCS64/ELF selection and JIT "
        "stack-argument placement); its every test is Linux-only by design",
    ("trust-cg-codegen", "e2e_aarch64_elf_debugger_linux"):
        "Linux ELF gdb/lldb correspondence; Darwin debugger legs are o3_debug_lldb_line_200loc and aarch64_elf_dwarf",
    ("trust-cg-verify", "aarch64_scalar_cell_link"):
        "Linux static ELF scalar-cell caller/callback link and relocation controls "
        "(check_aarch64_scalar_cell_elf/_link read ELF objects); no Mach-O port",
}
# macOS-guarded files that are not AArch64 execution controls.
OUT_OF_SCOPE = {
    "e2e_x86_64_internal_multi_result": (
        "x86 System V native/Rosetta/JIT controls; the AArch64 parity row only "
        "compiles and does not execute an AArch64 image"
    ),
    **{
        name: "x86-64 code generation; not an AArch64 control"
        for name in (
            "e2e_x86_64_atomics", "e2e_x86_64_callee_saved", "e2e_x86_64_calling_conv", "e2e_x86_64_checked_arith",
            "e2e_x86_64_correctness",
            "e2e_x86_64_data_reloc", "e2e_x86_64_dispatcher", "e2e_x86_64_eh_catch",
            "e2e_x86_64_eh_invoke_trust_ir_run", "e2e_x86_64_eh_resume_trust_ir",
            "e2e_x86_64_fp", "e2e_x86_64_heap_alloc", "e2e_x86_64_i128_stack_abi",
            "e2e_x86_64_indirect_calls", "e2e_x86_64_jump_table_selector_width", "e2e_x86_64_link", "e2e_x86_64_module_batch_fnptr",
            "e2e_x86_64_module_batch_globals", "e2e_x86_64_opt_correctness", "e2e_x86_64_pair_bool_lane",
            "e2e_x86_64_recursion", "e2e_x86_64_scale_emergent",
            "e2e_x86_64_sib_rmw", "e2e_x86_64_swiftcc", "e2e_x86_64_symbol_address", "e2e_x86_64_vector_fp",
            "guard_kernel_gate_x86_linkrun", "jit_integration_x86_64", "weak_linkage_x86",
            "x86_64_macho_module_local_binding",
        )
    },
}
MACOS_GUARD = re.compile(r'target_os\s*=\s*"macos"')
# A test function: `#[test]`, `#[tokio::test]`, or a host-gated
# `#[cfg_attr(<predicate>, test)]` (single- or multi-line).
TEST_ATTRIBUTE = re.compile(r"#\[(?:tokio::)?test\]|#\[cfg_attr\([^\[\]]*?,\s*test\s*\)\]")
NATIVE_HELPER = re.compile(r'#\[path\s*=\s*"common/aarch64_native\.rs"\]')
CFG_ATTRIBUTE = re.compile(r"#!?\[\s*cfg\s*\(")
LINUX_OS = re.compile(r'target_os\s*=\s*"linux"')
# matrix_results only recognizes explicit upper-case SKIP spellings; the
# "Skipping ..." and "skipping ..." guards in older suites are caught here so
# neither can pass.
SKIP_LINE = re.compile(
    r"(?:^|\.\.\.\s*|\[)\s*(?:skip|skipped|skipping)\b", re.MULTILINE | re.IGNORECASE
)


def load_helper(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"required helper is missing: {path}")
    module = importlib.util.module_from_spec(spec)
    # Dataclasses resolve their module through sys.modules while executing.
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


MATRIX = load_helper("_darwin_aarch64_matrix_results", MATRIX_RESULTS)
# Share the Linux floor's argument parsing, report writing, source-content
# fingerprint, dependency identity recording and planning-environment
# isolation, as its bridge twin does.
SHARED = load_helper("_darwin_aarch64_linux_shared", LINUX_FLOOR)
positive_seconds = SHARED.positive_seconds
positive_jobs = SHARED.positive_jobs
write_report = SHARED.write_report
source_provenance = SHARED.source_provenance
target_unset_environment = SHARED.target_unset_environment
dependency_identity = SHARED.dependency_identity
dependency_recorder = SHARED.dependency_recorder


def target_path(package: str, target: str) -> Path:
    return ROOT / "crates" / package / "tests" / f"{target}.rs"


def cfg_predicates(text: str) -> list[tuple[bool, str]]:
    """Return (inner, predicate) for every cfg attribute in Rust source text."""
    predicates = []
    for match in CFG_ATTRIBUTE.finditer(text):
        depth, start = 0, match.end() - 1
        for index in range(start, len(text)):
            depth += {"(": 1, ")": -1}.get(text[index], 0)
            if depth == 0:
                predicates.append((match.group(0).startswith("#!"), text[start + 1:index]))
                break
    return predicates


def linux_only(predicate: str) -> bool:
    return bool(LINUX_OS.search(predicate)) and not MACOS_GUARD.search(predicate)


def linux_only_leg_targets() -> list[str]:
    """Required targets whose source also carries Linux-only cfg'd legs."""
    return [
        f"{package}/{target}" for package, target, _ in TARGETS
        if any(linux_only(predicate) for _, predicate in cfg_predicates(target_path(package, target).read_text()))
    ]


def inventory_problems() -> list[str]:
    """Check the inventory against the source tree and the Linux floor."""
    problems = []
    rows = [(package, target) for package, target, _ in TARGETS]
    if len(set(rows)) != len(rows):
        problems.append("duplicate required target")
    for package, target, minimum in TARGETS:
        path = target_path(package, target)
        if type(minimum) is not int or minimum < 1:
            problems.append(f"{package}/{target}: minimum must be a positive integer")
        if not path.is_file():
            problems.append(f"{package}/{target}: missing test file {path.relative_to(ROOT)}")
            continue
        text = path.read_text()
        if len(TEST_ATTRIBUTE.findall(text)) < minimum:
            problems.append(f"{package}/{target}: minimum {minimum} exceeds its #[test] functions")
        if any(inner and linux_only(predicate) for inner, predicate in cfg_predicates(text)):
            problems.append(f"{package}/{target}: file-level Linux cfg compiles it out on Darwin")
    for (package, target), reason in DARWIN_COMPILED_OUT.items():
        path = target_path(package, target)
        if (package, target) in rows:
            problems.append(f"{package}/{target}: both required and compiled out")
        if not reason or not path.is_file() or not any(
            inner and linux_only(predicate) for inner, predicate in cfg_predicates(path.read_text())
        ):
            problems.append(f"{package}/{target}: compiled-out entry has no file-level Linux cfg")
    # Darwin runs each row with the Linux floor's TARGET_FEATURES, so the same
    # file-level feature-gate check covers every Darwin row too.
    problems.extend(SHARED.feature_problems(rows=rows + [
        row for row in SHARED.TARGETS if row not in rows
    ]))
    # The Linux floor's TARGET_ENVIRONMENT (TCG_REQUIRE_LLD/GOLD, and
    # TCG_REQUIRE_LLC for the LLVM importer's llc twin legs) guards native
    # legs of ELF targets. The Darwin runner sets no target environment: most
    # of those legs are compiled out on Darwin, and
    # e2e_aarch64_elf_relocation_model's three host-neutral LLD link legs run
    # here unrequired (with the toolchain's rust-lld; without an LLD they
    # print SKIP). The table is still checked against both floors' rows, so
    # an entry the two share cannot go stale unnoticed.
    problems.extend(SHARED.environment_problems(rows=rows + [
        row for row in SHARED.TARGETS if row not in rows
    ]))
    linux_rows = set(SHARED.TARGETS)
    for row in sorted(linux_rows - set(rows) - set(DARWIN_COMPILED_OUT)):
        problems.append(f"Linux floor target {row[0]}/{row[1]} is neither required nor reported compiled out")
    for row in sorted(set(DARWIN_COMPILED_OUT) - linux_rows):
        problems.append(f"{row[0]}/{row[1]}: compiled-out entry is not a Linux floor target")
    # Every macOS-guarded or native-helper codegen test file must be classified,
    # so a new Darwin-only native family cannot silently stay outside the floor.
    classified = {target for package, target in rows if package == "trust-cg-codegen"}
    classified |= {target for package, target in DARWIN_COMPILED_OUT if package == "trust-cg-codegen"}
    for name in sorted(set(OUT_OF_SCOPE) & classified):
        problems.append(f"trust-cg-codegen/{name}: both required and out of scope")
    for path in sorted(CODEGEN_TESTS.glob("*.rs")):
        text = path.read_text()
        if (MACOS_GUARD.search(text) or NATIVE_HELPER.search(text)) and path.stem not in classified | set(OUT_OF_SCOPE):
            problems.append(f"trust-cg-codegen/{path.stem}: macOS-guarded or native-helper target is unclassified")
    for name in sorted(OUT_OF_SCOPE):
        if not (CODEGEN_TESTS / f"{name}.rs").is_file():
            problems.append(f"trust-cg-codegen/{name}: out-of-scope entry has no test file")
    return problems


def classify_result(returncode: int, transcript: str, minimum: int = 1) -> dict:
    """Require one complete, captured suite with no skip and enough passes."""
    errors = []
    parsed = MATRIX.parse_log(
        transcript.splitlines(), mode="plain", rc=returncode, capture_available=True,
    )
    required = max(minimum, 1)
    if returncode != 0:
        errors.append(f"command exited {returncode}")
    if parsed["status"] != "pass":
        errors.append(f"matrix classification is {parsed['status']}, not pass")
    for problem in parsed["parse_problems"]:
        errors.append(f"transcript problem: {problem}")
    for skip in parsed["runtime_skip_details"]:
        errors.append(f"runtime SKIP in {skip['test']}: {'; '.join(skip['messages'])}")
    for line in parsed["unattributed_skips"]:
        errors.append(f"unattributed runtime SKIP: {line}")
    skip_line = SKIP_LINE.search(transcript)
    if skip_line is not None:
        line_start = transcript.rfind("\n", 0, skip_line.start()) + 1
        line_end = transcript.find("\n", skip_line.end())
        errors.append(f"skip line in transcript: {transcript[line_start:line_end if line_end >= 0 else None].strip()}")
    if parsed["suites"] != 1 or parsed["incomplete_suites"]:
        errors.append("expected exactly one started and completed test suite")
    if parsed["failed"] or parsed["ignored"] or parsed["filtered"]:
        errors.append("failed, ignored or filtered tests are not permitted")
    if parsed["passed"] < required:
        errors.append(f"executed passes {parsed['passed']} are below the required minimum {required}")
    counts = {
        key: parsed[key]
        for key in (
            "passed", "libtest_passed", "unclassified_passes", "failed", "ignored", "filtered",
            "runtime_skipped", "suites", "incomplete_suites",
        )
    }
    return {
        "status": "fail" if errors else "pass", "counts": counts, "minimum": required,
        "matrix_status": parsed["status"], "timeout_detected": parsed["timeout_detected"],
        "errors": errors,
    }


def child_environment(base: dict | None = None) -> dict:
    """The caller's environment; the Trust package comes from its PATH."""
    environment = dict(os.environ if base is None else base)
    environment["RUSTUP_AUTO_INSTALL"] = "0"
    return environment


def trust_probe_environment(environment: dict) -> dict:
    """trustc refuses to run at all under any TRUST_CG_*/TCG_* control."""
    return {key: value for key, value in environment.items()
            if not key.startswith(("TRUST_CG_", "TCG_"))}


def trust_package(environment: dict) -> dict:
    """The installed Trust package on PATH (atpkg launchers followed)."""
    toolchain = load_helper("_darwin_aarch64_trust_toolchain", TRUST_TOOLCHAIN)
    try:
        return toolchain.resolve(path=environment.get("PATH"))
    except toolchain.ToolchainError as error:
        raise RuntimeError(f"no installed Trust package resolves (no stock fallback): {error}") from error


def run_target(
    command: Sequence[str], log_path: Path, timeout_seconds: float,
    *, minimum: int = 1, root: Path = ROOT, grace_seconds: float = 5,
    environment: dict | None = None, unset_environment: Sequence[str] = (),
    required_lines: Sequence[str] = (),
) -> dict:
    """Run a real process through the shared process-group timeout boundary."""
    bounded = [
        sys.executable, str(TIMEOUT_RUNNER), "--grace-seconds", str(grace_seconds),
        str(timeout_seconds), *command,
    ]
    started = time.monotonic()
    environment = dict(os.environ if environment is None else environment)
    removed = tuple(dict.fromkeys((*unset_environment, *CHILD_UNSET_ENVIRONMENT)))
    for name in removed:
        environment.pop(name, None)
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
    with log_path.open("x", encoding="utf-8") as log:
        try:
            # subprocess.run kills its immediate child on KeyboardInterrupt,
            # which would destroy the timeout supervisor before it can clean
            # up the command's separate process group. Forward cancellation
            # and let the bounded supervisor finish that cleanup instead.
            for signum in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
                previous_handlers[signum] = signal.signal(signum, forward)
            process = subprocess.Popen(
                bounded, cwd=root, stdout=log, stderr=subprocess.STDOUT,
                start_new_session=True, env=environment,
            )
            if interrupted_signal is not None:
                forward(interrupted_signal, None)
            returncode = process.wait()
        except OSError as error:
            log.write(f"Darwin AArch64 floor launch error: {error}\n")
            returncode = 125
        finally:
            for signum, handler in previous_handlers.items():
                signal.signal(signum, handler)
    data = log_path.read_bytes()
    verdict = classify_result(returncode, data.decode("utf-8", errors="replace"), minimum)
    for required in required_lines:
        if not SHARED.transcript_has_line(data.decode("utf-8", errors="replace"), required):
            verdict["errors"].append(f"required transcript line missing: {required}")
            verdict["status"] = "fail"
    if interrupted_signal is not None:
        verdict["errors"].append(f"interrupted by signal {interrupted_signal}")
        verdict["status"] = "fail"
    return {
        "command": list(command), "bounded_command": bounded,
        "timeout_seconds": timeout_seconds, "elapsed_seconds": time.monotonic() - started,
        "returncode": returncode, "log": log_path.name,
        "interrupted_signal": interrupted_signal, "unset_environment": list(removed),
        "log_sha256": hashlib.sha256(data).hexdigest(),
        "required_lines": list(required_lines), **verdict,
    }


def probe(command: Sequence[str], environment: dict | None = None, *, stdout_only: bool = False) -> str:
    result = subprocess.run(
        command, cwd=ROOT, capture_output=True, text=True, timeout=30, check=False,
        env=environment,
    )
    if result.returncode != 0:
        raise RuntimeError(f"probe {list(command)!r} exited {result.returncode}: {result.stderr.strip()}")
    if stdout_only:
        return result.stdout.strip()
    # Apple ld reports its version on stderr; keep both streams as identity.
    return "\n".join(part.strip() for part in (result.stdout, result.stderr) if part.strip())


def cargo_config_files(environment: dict) -> list[Path]:
    """Config files Cargo loads for a command started in ROOT, nearest first."""
    home, _ = dependency_recorder().cargo_home_from(environment, ROOT, native_targo=True)
    candidates = [
        directory / ".cargo" / name
        for directory in (ROOT, *ROOT.parents) for name in ("config.toml", "config")
    ]
    candidates += [home / name for name in ("config.toml", "config")]
    files, seen = [], set()
    for path in candidates:
        if path.is_file() and path.resolve() not in seen:
            seen.add(path.resolve())
            files.append(path)
    return files


def cargo_config_identity(environment: dict) -> dict:
    """Hash every loaded Cargo config; refuse compiler or test-runner reroutes."""
    identities = {}
    for path in cargo_config_files(environment):
        data = path.read_bytes()
        match = CARGO_CONFIG_REROUTE.search(data.decode("utf-8", errors="replace"))
        if match is not None:
            raise RuntimeError(
                f"Cargo config {path} sets {match.group(1)}, which would bypass the pinned "
                "compiler or run test binaries through another program; remove it"
            )
        identities[str(path)] = hashlib.sha256(data).hexdigest()
    return identities


def file_sha256(path: Path) -> str | None:
    if not path.is_file():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def toolchain_channel() -> str:
    text = TOOLCHAIN_FILE.read_text(encoding="utf-8")
    channels = re.findall(r'^\s*channel\s*=\s*"([^"]+)"', text, re.MULTILINE)
    if len(channels) != 1:
        raise RuntimeError(f"expected exactly one channel in {TOOLCHAIN_FILE}")
    return channels[0]


def require_darwin_host() -> str:
    """Refuse every host but native aarch64-apple-darwin before probing tools."""
    machine = platform.machine()
    if sys.platform != "darwin" or machine != MACHINE:
        raise RuntimeError(f"required Darwin host is {HOST}, observed {sys.platform}/{machine}")
    return machine


def preflight(environment: dict | None = None) -> dict:
    require_darwin_host()
    environment = child_environment() if environment is None else environment
    for name in REFUSED_ENVIRONMENT:
        if environment.get(name):
            raise RuntimeError(f"{name} would bypass the pinned Trust compiler; unset it")
    channel = toolchain_channel()
    if channel != "trust":
        raise RuntimeError(f"{TOOLCHAIN_FILE} must pin channel = \"trust\", found {channel!r}")
    override = environment.get("RUSTUP_TOOLCHAIN")
    if override and override != channel:
        raise RuntimeError(f"RUSTUP_TOOLCHAIN selects {override!r}, not the pinned {channel}")
    configured_target = environment.get("CARGO_BUILD_TARGET")
    if configured_target and configured_target != HOST:
        raise RuntimeError(f"CARGO_BUILD_TARGET selects a different target: {configured_target}")
    executables = {}
    for name in (*HOST_TOOL_PROBES, *WHAT_PROBED_TOOLS):
        path = shutil.which(name, path=environment.get("PATH"))
        if path is None:
            raise RuntimeError(f"required tool is missing: {name}")
        executables[name] = path
    for path in (TIMEOUT_RUNNER, MATRIX_RESULTS, LINUX_FLOOR, TRUST_TOOLCHAIN, TRUST_CARGO):
        if not path.is_file():
            raise RuntimeError(f"required helper is missing: {path}")
    package = trust_package(environment)
    executables["trustc"] = package["compiler"]
    executables["targo"] = package["targo"]
    cargo_configs = cargo_config_identity(environment)
    compiler_environment = trust_probe_environment(environment)
    rustc = probe([executables["trustc"], "-vV"], compiler_environment)
    hosts = re.findall(r"^host: (\S+)$", rustc, re.MULTILINE)
    if hosts != [HOST]:
        raise RuntimeError(f"required Darwin host is {HOST}, observed trustc host {hosts!r}")
    if re.findall(r"^binary: (\S+)$", rustc, re.MULTILINE) != ["trustc"]:
        raise RuntimeError("the Trust package did not identify as the branded trustc driver")
    # `targo --unverified` is the one discriminator between targo and upstream
    # cargo shipped under its name (upstream rejects the flag).
    cargo = probe([executables["targo"], "--unverified", "-vV"], compiler_environment)
    if not cargo.startswith("targo "):
        raise RuntimeError(f"required targo, observed {cargo.splitlines()[:1]!r}")
    machine = probe([executables["uname"], "-m"], environment)
    if machine != MACHINE:
        raise RuntimeError(f"required {MACHINE} machine, observed {machine!r}")
    sysroot = Path(package["sysroot"])
    sysroot_hashes = {name: file_sha256(sysroot / "bin" / name) for name in ("trustc", "targo")}
    missing = sorted(name for name, digest in sysroot_hashes.items() if digest is None)
    if missing:
        raise RuntimeError(f"pinned Trust sysroot {sysroot} lacks bin/{', bin/'.join(missing)}")
    # Proof-tool files shipped in this sysroot, hashed at preflight (an overlay
    # replaces bin/ay and bin/clean and names both in overlay.json). Runtime
    # admission can resolve an overridden or managed checker; these file hashes
    # describe the shipped inputs, while its resolved identity is separate.
    # An absent shipped file is recorded as null.
    proof_tools = {
        name: file_sha256(sysroot / relative)
        for name, relative in PROOF_TOOL_FILES.items()
    }
    tool_identities = {
        name: {
            "command": [name, *arguments],
            "identity": probe([executables[name], *arguments], environment),
        }
        for name, arguments in HOST_TOOL_PROBES.items()
    }
    for name in WHAT_PROBED_TOOLS:
        tool_identities[name] = {
            "command": [WHAT, name], "identity": probe([WHAT, executables[name]], environment),
        }
    return {
        **source_provenance(executables["git"]),
        "host": HOST, "channel": channel, "machine": machine, "tools": executables,
        "rustc": rustc, "cargo": cargo,
        "trust_package": {
            key: package.get(key) for key in ("compiler", "targo", "sysroot", "commit", "launchers", "lane")
        },
        "rustc_sysroot": str(sysroot),
        "rustc_sha256": sysroot_hashes["trustc"],
        "cargo_sha256": sysroot_hashes["targo"],
        "proof_tools": proof_tools,
        "cargo_configs": cargo_configs,
        "tool_identities": tool_identities,
        "configuration": {
            name: environment[name] for name in RECORDED_CONFIGURATION if name in environment
        },
    }


# Each required target runs with TMPDIR naming its own new, empty directory,
# created by this runner under the caller's temporary directory with a short
# name (an AF_UNIX socket a test binds there must fit sun_path's 104 bytes).
# Everything left in it when the target's process group has exited was made by
# that target's build or tests and not removed, so the target fails and the
# entries are recorded (TEMPORARY_LEFTOVERS_SHOWN of them by name, plus the
# count and bytes). The runner then removes that directory, which is its own;
# it never lists or removes anything else in the caller's temporary directory.
# Caches a host tool re-creates under whatever TMPDIR it runs with are recorded
# as such and do not fail the target.
TEMPORARY_TOOL_CACHES = {
    "xcrun_db": "xcrun's SDK lookup cache, written on first use under any TMPDIR (a regular file)",
    # Measured 2026-09-30: `TMPDIR=<empty> lldb --batch -o run -- /bin/echo`
    # leaves an empty `lldb` directory (the root of lldb's per-process
    # temporary directories; it removes its own subdirectory at exit).
    "lldb": "lldb's per-process temporary-directory root, left (empty) by every lldb that runs a process",
}


def is_tool_cache(entry: Path) -> bool:
    """Whether `entry` is a tool cache in exactly the shape the tool leaves it.

    Only the name AND the shape admit an entry: `xcrun_db` must be a regular
    file, and `lldb` an empty directory. Anything under `lldb` (a crashed
    lldb's per-process subdirectory, or a file a target wrote there) makes the
    whole entry a leak, so a target cannot hide output under a cache's name.
    """
    try:
        if entry.name == "xcrun_db":
            return not entry.is_symlink() and entry.is_file()
        if entry.name == "lldb":
            return not entry.is_symlink() and entry.is_dir() and not any(entry.iterdir())
    except OSError:
        return False
    return False
TEMPORARY_DIRECTORY_PREFIX = "tcg-floor-"
TEMPORARY_LEFTOVERS_SHOWN = 20


def target_temporary_directory() -> Path:
    """A new, empty, private directory for one target's TMPDIR."""
    return Path(tempfile.mkdtemp(prefix=TEMPORARY_DIRECTORY_PREFIX))


def entry_bytes(path: Path) -> int:
    """Apparent size of a file, or of every file under a directory; links are not followed."""
    try:
        if path.is_symlink() or not path.is_dir():
            return path.lstat().st_size
        total = 0
        for directory, _, files in os.walk(path, onerror=lambda _error: None):
            for name in files:
                try:
                    total += (Path(directory) / name).lstat().st_size
                except OSError:
                    pass
        return total
    except OSError:
        return 0


def temporary_leftovers(directory: Path) -> dict:
    """The entries a target left in its own TMPDIR, split into leaks and tool caches."""
    leaked, caches = [], []
    for entry in sorted(directory.iterdir(), key=lambda path: path.name):
        (caches if is_tool_cache(entry) else leaked).append(entry)
    return {
        "leaked": [entry.name for entry in leaked],
        "leaked_bytes": sum(entry_bytes(entry) for entry in leaked),
        "tool_caches": [entry.name for entry in caches],
    }


def check_temporary_leftovers(result: dict, directory: Path) -> None:
    """Record what the target left in `directory`, fail it on a leak, then remove `directory`."""
    try:
        leftovers = temporary_leftovers(directory)
    except OSError as error:
        leftovers = {"leaked": [], "leaked_bytes": 0, "tool_caches": []}
        result["errors"].append(f"its TMPDIR {directory} could not be listed: {error}")
        result["status"] = "fail"
    result["temporary_leftovers"] = leftovers["leaked"]
    result["temporary_leftover_bytes"] = leftovers["leaked_bytes"]
    result["temporary_tool_caches"] = leftovers["tool_caches"]
    if leftovers["leaked"]:
        shown = leftovers["leaked"][:TEMPORARY_LEFTOVERS_SHOWN]
        more = len(leftovers["leaked"]) - len(shown)
        result["errors"].append(
            f"left {len(leftovers['leaked'])} temporary entr{'y' if len(leftovers['leaked']) == 1 else 'ies'} "
            f"({leftovers['leaked_bytes']} bytes) in its own TMPDIR: {', '.join(shown)}"
            + (f" and {more} more" if more else "")
        )
        result["status"] = "fail"
    shutil.rmtree(directory, ignore_errors=True)
    if directory.exists():
        result["errors"].append(f"its TMPDIR {directory} could not be removed")
        result["status"] = "fail"


def select_targets(only: Sequence[str] | None) -> tuple[tuple[str, str, int], ...]:
    """Resolve --only names to complete inventory rows; unknown names are errors."""
    if not only:
        return TARGETS
    selected = []
    for name in only:
        matches = [row for row in TARGETS if name in (row[1], f"{row[0]}/{row[1]}")]
        if len(matches) != 1:
            raise ValueError(f"--only {name!r} does not name exactly one required target")
        if matches[0] not in selected:
            selected.append(matches[0])
    return tuple(selected)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--list", action="store_true", help="print required targets and minimum passes without probing or executing")
    parser.add_argument("--out", type=Path, help="new output directory outside the source tree; existing paths are rejected")
    parser.add_argument("--timeout-seconds", type=positive_seconds, default=1200.0, help="bound for each Cargo invocation (default: 1200)")
    parser.add_argument("--jobs", type=positive_jobs, default=2, help="Cargo build jobs (default: 2)")
    parser.add_argument("--only", action="append", metavar="TARGET", help="run only this required target (package/target or target); repeatable; never a floor pass")
    parser.add_argument("--require-clean", action="store_true", help="refuse to run on a dirty source tree")
    parser.add_argument(
        "--require-offline-deps", action="store_true",
        help="refuse to run unless every Git revision Cargo.lock pins resolves in the local Cargo Git database "
             "and no finished checkout differs from it; run Cargo with --offline",
    )
    args = parser.parse_args(argv)
    try:
        selected = select_targets(args.only)
    except ValueError as error:
        parser.error(str(error))
    if args.list:
        for package, target, minimum in selected:
            print(" ".join((package, target, str(minimum), *SHARED.feature_arguments(package, target))))
        return 0
    try:
        if args.out is None:
            output = Path(tempfile.mkdtemp(prefix="trust-cg-darwin-aarch64-"))
        else:
            output = args.out.absolute()
            if output.resolve().is_relative_to(ROOT):
                raise OSError("output must be outside the source tree so logs cannot change source provenance")
            output.mkdir(mode=0o700)
    except OSError as error:
        print(f"Darwin AArch64 execution floor: output directory error: {error}", file=sys.stderr)
        return 1
    complete_floor = args.only is None
    report = {
        "schema": "trust-cg-darwin-aarch64-floor-v1",
        "scope": "required Darwin execution floor; testing evidence, not full completion, proof or release qualification",
        "host": HOST,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "status": "incomplete",
        "complete_floor": complete_floor,
        "options": {
            "jobs": args.jobs, "timeout_seconds": args.timeout_seconds,
            "require_clean": args.require_clean, "only": list(args.only or []),
            "require_offline_deps": args.require_offline_deps,
        },
        "required_targets": [list(row) for row in TARGETS],
        "required_target_features": {
            f"{package}/{target}": list(SHARED.target_features(package, target))
            for package, target, _ in TARGETS if SHARED.target_features(package, target)
        },
        "required_minimum_passes": sum(row[2] for row in TARGETS),
        "selected_targets": [list(row) for row in selected],
        "not_executed_on_darwin": {
            "compiled_out_linux_floor_targets": {
                f"{package}/{target}": reason for (package, target), reason in sorted(DARWIN_COMPILED_OUT.items())
            },
            "out_of_scope_macos_guarded": dict(sorted(OUT_OF_SCOPE.items())),
        },
        "targets": [], "errors": [],
    }
    report_path = output / "report.json"
    write_report(report_path, report)
    print(f"Darwin AArch64 execution floor logs: {output}", flush=True)
    environment = child_environment()
    try:
        problems = inventory_problems()
        if problems:
            raise RuntimeError("required inventory is inconsistent: " + "; ".join(problems))
        report["not_executed_on_darwin"]["linux_only_legs_of_required_targets"] = linux_only_leg_targets()
        report["provenance"] = preflight(environment)
        # Every Cargo run uses exactly the package preflight identified.
        environment["TRUST_TARGO"] = report["provenance"]["tools"]["targo"]
        write_report(report_path, report)
        if args.require_clean and report["provenance"]["dirty"]:
            raise RuntimeError("source tree is dirty; --require-clean refuses to run")
        report["dependency_identity"] = dependency_identity(report["provenance"]["tools"]["git"], environment)
        write_report(report_path, report)
        offline_problems = dependency_recorder().offline_problems(report["dependency_identity"])
        if offline_problems and args.require_offline_deps:
            report["errors"].extend(f"--require-offline-deps: {problem}" for problem in offline_problems)
            raise RuntimeError("--require-offline-deps refuses this Cargo home; see dependency_identity")
        if offline_problems:
            print("Darwin AArch64 execution floor: pinned Git dependencies are not all local, so Cargo "
                  "may fetch them (see --require-offline-deps and dependency_identity):", file=sys.stderr)
            for problem in offline_problems:
                print(f"  {problem}", file=sys.stderr)
        for package, target, minimum in selected:
            print(f"Running {package}/{target}", flush=True)
            # targo --unverified through the wrapper: TRUST_CG_*/TCG_* reach the
            # test binary but never trustc, which refuses to run under them.
            command = [
                str(TRUST_CARGO), "test", "--locked",
                *(["--offline"] if args.require_offline_deps else []), "--color", "never",
                "-j", str(args.jobs), "-p", package, *SHARED.feature_arguments(package, target),
                "--test", target, "--", "--show-output", "--test-threads=1",
            ]
            temporary = target_temporary_directory()
            result = run_target(
                command, output / f"{package}--{target}.log", args.timeout_seconds,
                minimum=minimum, environment={**environment, "TMPDIR": f"{temporary}/"},
                required_lines=SHARED.target_required_lines(package, target),
                unset_environment=target_unset_environment(package, target),
            )
            check_temporary_leftovers(result, temporary)
            result.update({
                "package": package, "target": target,
                "features": list(SHARED.target_features(package, target)),
            })
            report["targets"].append(result)
            write_report(report_path, report)
            print(f"{result['status'].upper()}: {package}/{target}", flush=True)
            if result["interrupted_signal"] is not None:
                report["errors"].append("interrupted; required target inventory is incomplete")
                break
        report["executed_passes"] = sum(row["counts"]["passed"] for row in report["targets"])
        complete = len(report["targets"]) == len(selected) and bool(selected)
        passed = complete and all(row["status"] == "pass" for row in report["targets"])
        report["status"] = ("pass" if complete_floor else "partial-pass") if passed else "fail"
        report["final_source"] = source_provenance(report["provenance"]["tools"]["git"])
        if report["final_source"]["source_fingerprint"] != report["provenance"]["source_fingerprint"]:
            report["errors"].append("source changed while required targets were running")
            report["status"] = "fail"
        if report["targets"]:
            # The trees Cargo extracted and compiled, compared with the record
            # taken before the first target.
            report["final_dependency_identity"] = dependency_identity(report["provenance"]["tools"]["git"], environment)
            changes = dependency_recorder().identity_changes(
                report["dependency_identity"], report["final_dependency_identity"],
            )
            if changes:
                report["errors"].extend(
                    f"dependency identity changed while required targets were running: {change}"
                    for change in changes
                )
                report["status"] = "fail"
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        report["errors"].append(str(error))
        report["status"] = "fail"
    except KeyboardInterrupt:
        report["errors"].append("interrupted; required target inventory is incomplete")
        report["status"] = "fail"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    write_report(report_path, report)
    label = report["status"].upper()
    if report["status"] == "partial-pass":
        label += " (selected targets only; not the required floor)"
    print(f"Darwin AArch64 execution floor: {label} ({report_path})")
    for error in report["errors"]:
        print(error, file=sys.stderr)
    return 0 if report["status"] in ("pass", "partial-pass") else 1


if __name__ == "__main__":
    raise SystemExit(main())
