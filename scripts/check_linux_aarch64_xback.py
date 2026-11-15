#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Require the Linux AArch64 cross-backend ABI differential (ledger L06-P9).

Every call in the four suites below crosses a codegen boundary: a callee crate
and a caller crate are each built twice, once by LLVM and once by the
Trust-built rustc bridge (`-Zcodegen-backend=<backend>`), under the pinned
Trust compiler, and linked four ways at O0, O1, O2 and O3:

    caller llvm x callee llvm   the ORACLE
    caller llvm x callee tcg    trust-cg as callee: does it READ its arguments
    caller tcg  x callee llvm   trust-cg as caller: does it WRITE them
    caller tcg  x callee tcg    self-consistency

Suites: `abi-xback` (benchmarks/abi-xback/gen.py seeds 1-40, one crate pair),
`abi-families` (benchmarks/abi-xback/families.py: the named AAPCS64 placement
families), `regclass-xback` and `sret-xback` (their committed program pairs).

The oracle must itself print the line its generator computed without any
compiler (or, for regclass/sret, exit with the fixture's 42); only then is each
cross cell compared with it, byte for byte, by exit status and output. Every
case runs in its own process. A wrong value, a crash, a timeout, a build or
link failure, an oracle failure or a missing case fails the gate. A trust-cg
refusal (exit 1, every error carrying a `[TCG-...]` tag) is a DECLINE: it is
counted and listed by case, side and level, and must equal the committed
EXPECTED_DECLINES table exactly, each declined cell with exactly its row's tag
set; an unlisted decline and a listed one that no longer occurs both fail.
When one function of a group refuses, the group is rebuilt one case per crate
pair; every cell the whole-group attempt executed is judged as well, and its
refusal must be reproduced, side and tags, by that rebuild. There is no skip.

The trust-cg halves run in Trust's unverified frontend lane
(`-Ztrust-verify=off`) with proof certificates and the refinement solver off
through the backend's tracked knob option: this is ABI execution evidence, not
proof evidence and not a Trust-verified compilation.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from typing import Sequence

ROOT = Path(__file__).resolve().parents[1]
HOST = "aarch64-unknown-linux-gnu"
SCHEMA = "trust-cg-linux-aarch64-xback-v1"
TIMEOUT_RUNNER = ROOT / "scripts/run_with_timeout.py"
GEN = ROOT / "benchmarks/abi-xback/gen.py"
FAMILIES = ROOT / "benchmarks/abi-xback/families.py"
REGCLASS_PROGS = ROOT / "benchmarks/regclass-xback/progs"
SRET_PROGS = ROOT / "benchmarks/sret-xback/progs"

OPT_LEVELS = (0, 1, 2, 3)
# (caller backend, callee backend)
CELLS = (("llvm", "llvm"), ("llvm", "tcg"), ("tcg", "llvm"), ("tcg", "tcg"))
SUITES = ("abi-xback", "abi-families", "regclass-xback", "sret-xback")
ABI_XBACK_FIRST, ABI_XBACK_COUNT = 1, 40
REGCLASS_SHAPES = ("fret", "farg", "iret", "iarg", "barg", "harg", "earg", "marg", "qarg")
FIXTURE_EXIT = 42

BASE_FLAGS = (
    "-Ztrust-verify=off", "--edition=2021", "-Cpanic=abort", "-Ccodegen-units=1",
    "--error-format=json", "-Awarnings",
)
TCG_KNOBS = ("-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args=refine-solver=0")

# Pinned inventory. A suite or family that shrinks below its floor fails the
# gate even if every remaining cell matches.
SUITE_MIN_CASES = {"abi-xback": 40, "abi-families": 346, "regclass-xback": 9, "sret-xback": 1}
FAMILY_MIN_CASES = {
    "integer": 20, "float": 6, "hfa": 23, "hva": 15, "composite": 13, "i128": 6, "sret": 10,
    "byref": 8, "bool": 6, "varargs": 20, "callback": 8, "exhaustion": 12, "spill": 6,
    "overalign": 95, "packed": 16, "union": 16, "enum": 14, "niche": 12, "random": 40,
}
# Minimum cross cells (the three non-oracle cells) that EXECUTED and MATCHED,
# per suite, over O0-O3. Declines are subtracted from the complete matrix only
# through EXPECTED_DECLINES, and this floor keeps the executed count itself
# from shrinking.
SUITE_MIN_CROSS_MATCHES = {"abi-xback": 480, "abi-families": 3328, "regclass-xback": 108, "sret-xback": 12}

# (suite, case, side) -> the committed refusal: the exact `[TCG-...]` tag set
# trust-cg reports and the optimization levels at which it declines (a row's
# `level_tags`, where present, gives the exact set per level instead; every
# declined cell must carry exactly its level's set). A side is the half that
# trust-cg compiled ("callee" or "caller"); when both halves of a case refuse,
# the tcg x tcg cell is counted on the callee's row. Each row says why the
# decline is a refusal by name (never a wrong value) and what is left
# unsupported; measured 2026-10-14 on Linux AArch64, the variadic rows
# 2026-10-15 (reports/perf/2026-10-14-linux-cross-backend-abi). Re-measured
# 2026-10-15 after main's WS7.3 ingestion admission (trust-ir validation of
# every module the bridge emits) merged with its bridge repairs: the same rows,
# no row added or removed; the variadic-definition rows and `comp_mixfi_c` are
# refused by an earlier gate, so their tags changed (decision record LD-27).
ALL_LEVELS = (0, 1, 2, 3)
_MIR = "[TCG-MIR-UNSUPPORTED]"
_RUST_SINGLE_FLOAT = ("Rust-ABI struct of one f32/f64 (H1f/H1d): rustc's FnAbi casts it to a general-purpose "
                      "register, the bridge types it as the float scalar and refuses ([TCG-ARG-ABI])")
_SHORT_VECTOR = ("C-ABI 128-bit short vector, bare or as a one-member HVA: the bridge's lane builder cannot "
                 "place it and refuses under the System V tag name ([TCG-SYSV-SSE-AGGREGATE]); AArch64 HVA "
                 "and bare-vector arguments are unsupported")
_VARIADIC_DEFINITION = ("a C-variadic DEFINITION compiled by trust-cg: va_start/va_arg lowering of the AAPCS64 "
                        "va_list is absent and refused, at O0/O1 as the definition, at O2/O3, where "
                        "`VaList::next_arg` is inlined into it, as the `va_arg` intrinsic (the generic "
                        "[TCG-MIR-UNSUPPORTED] only). Since WS7.3 trust-ir's validator, which runs before the "
                        "native adapter, refuses the O0/O1 definition first ([TCG-IR-LOWER], `EntryParamsMismatch`: "
                        "the entry block holds the `VaList` the variadic signature does not list), where the adapter "
                        "refused it as [TCG-VARIADIC-DEFINITION]; calls INTO an LLVM-built variadic callee are judged "
                        "on their own rows (the scalar-argument ones execute)")
_SRET_POINTER = ("an x8 indirect result through a fn pointer: the indirect-result marker is keyed by a callee "
                 "symbol, which an indirect call lacks, so the call is refused ([TCG-SRET-ABI])")
_OVERALIGNED_HFA = ("C-ABI over-aligned HFA (`#[repr(C, align(16))] {f64, f64}`, alone, at d0-d7 or inside a "
                    "repr(C) struct): rustc's float cast does not tile the bridge's 16-aligned lane storage, "
                    "refused [TCG-AAPCS64-HFA]")
_PACKED_HFA = ("C-ABI packed HFA `#[repr(C, packed)] {f32, f32}` (alignment 1): rustc's float cast does not tile "
               "the bridge's byte lane storage, refused [TCG-AAPCS64-HFA]")
_PADDED_NARROW = ("over-aligned single-scalar newtype of at most 8 bytes (`#[repr(C, align(2))] {u8}`, `#[repr(C, "
                  "align(8))] {u16}`, Rust-ABI `#[repr(align(4))] {u16}`): rustc casts its padded bytes to one "
                  "integer, the bridge declares the scalar and the whole-signature check refuses it "
                  "([TCG-ARG-ABI])")
_PADDED_INDIRECT = ("padded single-scalar newtype that rustc passes or returns through a caller-made copy "
                    "(a 32-aligned C-ABI argument or result, a 16- or 32-aligned Rust-ABI result through x8): the "
                    "bridge types it as its scalar and refuses ([TCG-ARG-ABI] / [TCG-RET-ABI])")
_WIDE_ALIGN = ("32- or 64-aligned composite (`#[repr(C, align(32))] {f32 x4}`, `align(64) {u8, u32}`): the bridge "
               "has no memory slot of that alignment (`memory slot alignment N unsupported`, the generic "
               "[TCG-MIR-UNSUPPORTED])")
_PACKED_MISALIGNED = ("C-ABI `#[repr(C, packed)]` / `packed(2)` composite with a misaligned field, argument or "
                      "result: refused under the System V tag name ([TCG-SYSV-PACKED-AGGREGATE])")
_UNION_RESULT = ("a union RESULT whose members have different types (`union {u64, u32}`, `union {u16, u8}`), "
                 "received by a trust-cg caller: the caller's union construct is refused (`field 1 type ... "
                 "differs from field 0`, the generic [TCG-MIR-UNSUPPORTED]); the callee side compiles")
_ENUM_FLOAT_PAYLOAD = ("C-ABI `#[repr(C, u32)]` enum with an f32 payload (`Ecr32`), argument or result: the "
                       "bridge's C-ABI lane builder sees a floating-point eightbyte it cannot model and refuses "
                       "under the System V tag name ([TCG-SYSV-SSE-AGGREGATE])")
_VARIADIC_DEFINITION_NO_ARG = ("a C-variadic DEFINITION that reads no anonymous argument, compiled by trust-cg: "
                               "nothing inlines `va_arg` into it, so at every level the definition itself is "
                               "refused, since WS7.3 by trust-ir's validator ahead of the native adapter "
                               "([TCG-IR-LOWER], `EntryParamsMismatch`: the entry block holds the `VaList` the "
                               "variadic signature does not list; the adapter's [TCG-VARIADIC-DEFINITION] is not "
                               "reached); calls INTO an LLVM-built variadic callee are judged on their own rows")
_VARIADIC_FIXED_PADDED = ("over-aligned single-scalar newtype (`#[repr(C, align(16))] {u64}` / `{u8}`, "
                          "`#[repr(C, align(2))] {u8}`) or repr(C) struct around a 16-aligned member as a FIXED "
                          "argument of a C-variadic function, passed by a trust-cg CALLER: rustc's FnAbi casts it "
                          "to [2 x i64], one integer or i128; on the variadic route the bridge declares its one "
                          "scalar (the variadic aggregate scope admits no two-unit carrier) and the whole-call "
                          "check of the direct variadic call refuses it ([TCG-ARG-ABI]) (LD-29; until 2026-10-15 "
                          "a silent wrong value or a crash)")
_VARIADIC_POINTER_PADDED = ("the same over-aligned FIXED arguments passed by a trust-cg CALLER through a "
                            "C-variadic `fn` pointer with no anonymous argument (the ordinary fn-pointer call "
                            "route): the whole-signature check of the pointer's signature refuses them "
                            "([TCG-ARG-ABI]) (LD-29; on 395954590's backend a silent wrong value)")
_VARIADIC_NESTED_DEFINITION = ("a C-variadic DEFINITION whose fixed argument is a repr(C) struct around a "
                               "16-aligned member, compiled by trust-cg: reading its scalar (`a.a.a`) is a `Place "
                               "projection` refused in MIR lowering (the generic [TCG-MIR-UNSUPPORTED]) before the "
                               "native adapter would refuse the variadic definition")
_VARIADIC_POINTER_ANON = ("a trust-cg CALLER passing anonymous arguments through a C-variadic `fn` pointer: the "
                          "fn-pointer call route has no variadic lane and refuses the call by its argument count "
                          "(`argument count 3 does not match callee input count 1`, the generic "
                          "[TCG-MIR-UNSUPPORTED])")
_VARIADIC_FIXED_AGGREGATE = ("C composite `#[repr(C, align(16))] {u64, u64}` as a FIXED argument of a C-variadic "
                             "function, directly or through a C-variadic fn pointer: an aggregate carrier in a "
                             "variadic signature is outside the bridge's aggregate ABI scope, refused "
                             "([TCG-AGGREGATE-ABI-SCOPE]) on both sides")


def _declines(case: str, sides: Sequence[str], tags: Sequence[str], reason: str,
              level_tags: dict | None = None) -> dict:
    rows = {}
    for side in sides:
        row = {"tags": sorted([_MIR, *tags]), "opt_levels": list(ALL_LEVELS), "reason": reason}
        if level_tags is not None:
            exact = {level: sorted([_MIR, *level_tags[level]]) for level in ALL_LEVELS}
            row["level_tags"] = exact
            row["tags"] = sorted({tag for tags_at in exact.values() for tag in tags_at})
        rows[("abi-families", case, side)] = row
    return rows


def expected_cell_tags(row: dict, level: int) -> list[str]:
    """The exact tag set a declined cell of `row` must carry at `level`."""
    return sorted(row.get("level_tags", {}).get(level, row["tags"]))


_BOTH = ("callee", "caller")
_VARIADIC_LEVEL_TAGS = {0: ("[TCG-IR-LOWER]",), 1: ("[TCG-IR-LOWER]",), 2: (), 3: ()}

EXPECTED_DECLINES: dict[tuple[str, str, str], dict] = {
    **_declines("cb_hfa_rust", ("callee",), ("[TCG-RET-ABI]",),
                "Rust-ABI fn-pointer callback returning a 12-byte H3f: rustc returns it through an x8 buffer, "
                "the bridge would use two register lanes and refuses ([TCG-RET-ABI])"),
    **_declines("cb_sret_c", ("callee",), ("[TCG-RET-ABI]", "[TCG-SRET-ABI]"), _SRET_POINTER),
    **_declines("cb_sret_rust", ("callee",), ("[TCG-RET-ABI]", "[TCG-SRET-ABI]"), _SRET_POINTER),
    **_declines("comp_a16_at_x5_rust", _BOTH, ("[TCG-RET-ABI]",),
                "Rust-ABI A16 { i128 } result: rustc returns the 16-aligned Memory aggregate through an x8 "
                "buffer, the bridge types it as one i128 and refuses ([TCG-RET-ABI])"),
    **_declines("comp_small_c", _BOTH, ("[TCG-ARG-ABI]",),
                "C-ABI MixF { f32, f64 } (16 bytes, not an HFA): rustc passes two integer lanes, the bridge's "
                "lane plan disagrees and refuses ([TCG-ARG-ABI]); the case also holds MixFI, refused on its "
                "own in comp_mixfi_c"),
    **_declines("comp_mixfi_c", ("callee",), ("[TCG-FIELD-STORE-TYPE]",),
                "C-ABI MixFI { f64, u64 } DEFINITION: the bridge reads the (f64, i64) parameter's lanes through "
                "its slot's lane image with an element read, which trust-ir defines over arrays only; the "
                "bridge's field-store gate types that read as unknown and refuses the lane's store by name "
                "([TCG-FIELD-STORE-TYPE], main's d3a3cddea; before it trust-ir's validator refused the read, "
                "[TCG-IR-LOWER]); a trust-cg CALLER of it compiles and matches"),
    **_declines("hfa_after_full_rust", _BOTH, ("[TCG-ARG-ABI]",), _RUST_SINGLE_FLOAT),
    **_declines("hfa_args_rust", _BOTH, ("[TCG-ARG-ABI]",), _RUST_SINGLE_FLOAT),
    **_declines("hfa_stack_align_rust", _BOTH, ("[TCG-ARG-ABI]",), _RUST_SINGLE_FLOAT),
    **_declines("hva_after7_c", _BOTH, ("[TCG-SYSV-SSE-AGGREGATE]",), _SHORT_VECTOR),
    **_declines("hva_args_c", _BOTH, ("[TCG-SYSV-SSE-AGGREGATE]",), _SHORT_VECTOR),
    **_declines("hva_ret_v1_c", _BOTH, ("[TCG-SYSV-SSE-AGGREGATE]",), _SHORT_VECTOR),
    **_declines("hva_spill_c", _BOTH, ("[TCG-SYSV-SSE-AGGREGATE]",), _SHORT_VECTOR),
    **_declines("spill_all_c", _BOTH, ("[TCG-SYSV-SSE-AGGREGATE]",),
                _SHORT_VECTOR + "; the case's float32x4_t is refused first; it also holds V2 (a two-vector HVA "
                "argument, the same refused class) and MixF (refused on its own in comp_small_c), and "
                "spill_all_exec_c runs its thirty-two positions with those three shapes replaced"),
    **_declines("vec_bare_c", _BOTH, ("[TCG-SYSV-SSE-AGGREGATE]",),
                _SHORT_VECTOR + "; the case's 64-bit vectors are refused on their own in vec64_bare_c"),
    **_declines("vec64_bare_c", _BOTH, ("[TCG-ARG-ABI]",),
                "C-ABI bare 64-bit vector arguments (float32x2_t, int16x4_t): rustc passes each in one vector "
                "register, the bridge's lanes disagree and refuse ([TCG-ARG-ABI])"),
    **_declines("vec64_ret_c", _BOTH, ("[TCG-RET-ABI]",),
                "C-ABI bare 64-bit vector result (float32x2_t): rustc returns it in one vector register, the "
                "bridge's return lanes disagree and refuse ([TCG-RET-ABI])"),
    **_declines("hva_ret_vs2_c", _BOTH, ("[TCG-RET-ABI]",),
                "C-ABI VS2 (two 64-bit vectors) result: rustc returns it in two vector registers, the bridge's "
                "return lanes disagree and refuse ([TCG-RET-ABI])"),
    **_declines("hva_vs2_arg_c", _BOTH, ("[TCG-ARG-ABI]",),
                "C-ABI VS2 (two 64-bit vectors) argument: rustc passes it in two vector registers, the bridge's "
                "lanes disagree and refuse ([TCG-ARG-ABI])"),
    **{key: row for case in ("va_after_fixed_c", "va_f64_c", "va_ints_regs_c", "va_ints_stack_c",
                             "va_oa16u64_x1_c", "va_oa16u8_x1_c", "va_oa2_x1_c", "va_ptr_anon_c")
       for key, row in _declines(case, ("callee",), (), _VARIADIC_DEFINITION,
                                 level_tags=_VARIADIC_LEVEL_TAGS).items()},
    **{key: row for case in ("va_none_c", "va_ptr_none_c", "va_ptr_oa16u64_x1_c", "va_ptr_oa16u8_x1_c",
                             "va_ptr_oa2_x1_c")
       for key, row in _declines(case, ("callee",), ("[TCG-IR-LOWER]",),
                                 _VARIADIC_DEFINITION_NO_ARG).items()},
    **{key: row for case in ("va_oawrap16_x1_c", "va_oawrap16_s8_c", "va_ptr_oawrap16_x1_c",
                             "va_ptr_oawrap16_s8_c")
       for key, row in _declines(case, ("callee",), (), _VARIADIC_NESTED_DEFINITION).items()},
    # Over-aligned fixed arguments of a C-variadic function (2026-10-15).
    **{key: row for case in ("va_oa16u64_x1_c", "va_oa16u8_x1_c", "va_oa2_x1_c", "va_oawrap16_x1_c",
                             "va_oawrap16_s8_c")
       for key, row in _declines(case, ("caller",), ("[TCG-ARG-ABI]",), _VARIADIC_FIXED_PADDED).items()},
    **{key: row for case in ("va_ptr_oa16u64_x1_c", "va_ptr_oa16u8_x1_c", "va_ptr_oa2_x1_c",
                             "va_ptr_oawrap16_x1_c", "va_ptr_oawrap16_s8_c")
       for key, row in _declines(case, ("caller",), ("[TCG-ARG-ABI]",), _VARIADIC_POINTER_PADDED).items()},
    **_declines("va_ptr_anon_c", ("caller",), (), _VARIADIC_POINTER_ANON),
    **{key: row for case in ("va_oa16_x1_c", "va_ptr_oa16_x1_c")
       for key, row in _declines(case, _BOTH, ("[TCG-AGGREGATE-ABI-SCOPE]",),
                                 _VARIADIC_FIXED_AGGREGATE).items()},
    # The layout families (2026-10-14).
    **{key: row for case in ("ov_oa16f64x2_c", "ov_oa16f64x2_d0_c", "ov_oa16f64x2_d1_c", "ov_oa16f64x2_d5_c",
                             "ov_oa16f64x2_d6_c", "ov_oa16f64x2_d7_c", "ov_oawraphfa_c", "ov_ret_oa16f64x2_c")
       for key, row in _declines(case, _BOTH, ("[TCG-AAPCS64-HFA]",), _OVERALIGNED_HFA).items()},
    **{key: row for case in ("pa_pkf_c", "pa_ret_pkf_c")
       for key, row in _declines(case, _BOTH, ("[TCG-AAPCS64-HFA]",), _PACKED_HFA).items()},
    **{key: row for case in ("ov_oa2_c", "ov_oa8_c", "ov_oa2_rust", "ov_roa4u16_rust")
       for key, row in _declines(case, _BOTH, ("[TCG-ARG-ABI]",), _PADDED_NARROW).items()},
    **_declines("ov_oawrap16_c", _BOTH, ("[TCG-ARG-ABI]",),
                "C-ABI repr(C) struct around a 16-aligned member (natural alignment 16): rustc casts it to "
                "i128, from an even register; the bridge declares its one scalar and the whole-signature check "
                "refuses it ([TCG-ARG-ABI])"),
    **_declines("ov_oawrap16_rust", ("callee",), (),
                "Rust-ABI callee reading the scalar of a nested over-aligned newtype (`a.a.a`): `Place "
                "projection` is refused in MIR lowering (the generic [TCG-MIR-UNSUPPORTED]); the caller side "
                "compiles and matches"),
    **_declines("ov_oa32_c", _BOTH, ("[TCG-ARG-ABI]",), _PADDED_INDIRECT),
    **{key: row for case in ("ov_ret_oa32_c", "ov_ret_roa16u32_rust", "ov_ret_roa32_rust")
       for key, row in _declines(case, _BOTH, ("[TCG-RET-ABI]",), _PADDED_INDIRECT).items()},
    **{key: row for case in ("ov_oa32f32x4_c", "ov_oa64_c", "ov_oa64_rust")
       for key, row in _declines(case, _BOTH, (), _WIDE_ALIGN).items()},
    **_declines("ov_oawrap8_c", _BOTH, (),
                "C-ABI repr(C) struct holding an over-aligned `#[repr(C, align(8))] {u16}` member: the bridge's "
                "memory layout cannot model the member as a leaf (`memory aggregate leaf ... is not a single "
                "scalar`, the generic [TCG-MIR-UNSUPPORTED])"),
    **_declines("ov_ret_oa16f32x2_c", _BOTH, ("[TCG-SYSV-SSE-AGGREGATE]",),
                "C-ABI `#[repr(C, align(16))] {f32, f32}` RESULT (padded, so not an HFA): the bridge's return "
                "lane builder sees a floating-point eightbyte it cannot model and refuses under the System V "
                "tag name ([TCG-SYSV-SSE-AGGREGATE]); as an argument it executes"),
    **{key: row for case in ("pa_pk_c", "pa_pk2_c", "pa_pkbig_c", "pa_ret_pk_c", "pa_ret_pk2_c")
       for key, row in _declines(case, _BOTH, ("[TCG-SYSV-PACKED-AGGREGATE]",), _PACKED_MISALIGNED).items()},
    **_declines("un_unmix_c", _BOTH, ("[TCG-SYSV-MIXED-UNION]",),
                "C-ABI union of an integer and a float member (`union {u64, f64}`): refused under the System V "
                "tag name ([TCG-SYSV-MIXED-UNION])"),
    **{key: row for case in ("un_ret_runint_rust", "un_ret_unsmall_c")
       for key, row in _declines(case, ("caller",), (), _UNION_RESULT).items()},
    **{key: row for case in ("en_ecr32_c", "en_ret_ecr32_c")
       for key, row in _declines(case, _BOTH, ("[TCG-SYSV-SSE-AGGREGATE]",), _ENUM_FLOAT_PAYLOAD).items()},
}

ERROR_TAG = re.compile(r"\[TCG-[A-Z0-9-]+\]")
FOOTER = re.compile(r"aborting due to (\d+) previous errors?(?:; \d+ warnings? emitted)?")
ICE_MARKERS = ("internal compiler error", "panicked at", "thread 'rustc' panicked", "query stack during panic")
COMPILE_TIMEOUT_EXIT = 124

# Child processes never inherit codegen/proof/compiler overrides; trustc
# refuses untracked TCG_*/TRUST_CG_* controls outright.
SCRUBBED_PREFIXES = ("TCG_", "TRUST_CG_", "CARGO_", "RUSTC", "RUSTFLAGS", "RUSTDOC")


class GateError(RuntimeError):
    pass


def child_environment() -> tuple[dict, list[str]]:
    environment = dict(os.environ)
    removed = sorted(name for name in environment if name.startswith(SCRUBBED_PREFIXES))
    for name in removed:
        environment.pop(name)
    environment["LC_ALL"] = "C"
    return environment, removed


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def file_identity(path: Path) -> dict:
    info = path.lstat()
    if not stat.S_ISREG(info.st_mode):
        raise GateError(f"must be a regular file, not a symlink or special file: {path}")
    return {"path": str(path), "sha256": sha256_file(path), "size": info.st_size,
            "modified_ns": info.st_mtime_ns}


# --- compile classification ----------------------------------------------

def classify_compile(returncode: int, stderr: str) -> dict:
    """A failed trust-cg compile is a decline only when it is a clean refusal.

    A decline: exit status 1, no compiler panic, every error diagnostic other
    than the count footer carries at least one `[TCG-...]` tag, and the footer
    (if present) counts exactly those errors. Anything else is a build failure.
    """
    if returncode == 0:
        return {"kind": "built"}
    lowered = stderr.lower()
    if any(marker in lowered for marker in ICE_MARKERS):
        return {"kind": "build-failure", "reason": "compiler panic", "returncode": returncode}
    if returncode == COMPILE_TIMEOUT_EXIT:
        return {"kind": "build-failure", "reason": "compile timeout", "returncode": returncode}
    if returncode != 1:
        return {"kind": "build-failure", "reason": f"compiler exit {returncode}", "returncode": returncode}
    errors = []
    footer = None
    for line in stderr.splitlines():
        if not line.startswith("{"):
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            return {"kind": "build-failure", "reason": "malformed JSON diagnostic", "returncode": returncode}
        if not isinstance(record, dict) or record.get("$message_type") != "diagnostic":
            continue
        if record.get("level") != "error":
            continue
        message = record.get("message")
        if not isinstance(message, str):
            return {"kind": "build-failure", "reason": "error diagnostic without a message", "returncode": 1}
        summary = FOOTER.fullmatch(message)
        if summary is not None:
            footer = int(summary[1])
            continue
        errors.append(message)
    if not errors:
        return {"kind": "build-failure", "reason": "exit 1 without an error diagnostic", "returncode": 1}
    tags = set()
    for message in errors:
        found = ERROR_TAG.findall(message)
        if not found:
            first = message.splitlines()[0][:200]
            return {"kind": "build-failure", "reason": f"untagged error: {first}", "returncode": 1}
        tags.update(found)
    if footer is not None and footer != len(errors):
        return {"kind": "build-failure", "reason": "error count footer disagrees", "returncode": 1}
    symbols = sorted({symbol for message in errors for symbol in SYMBOL.findall(message)})
    return {"kind": "decline", "tags": sorted(tags), "message": decline_reason(errors[0]),
            "functions": symbols, "returncode": 1}


SYMBOL = re.compile(r"^\s*- (_R[0-9A-Za-z_]+)", re.MULTILINE)


def decline_reason(message: str) -> str:
    """The specific refusal: from the first tag that is not the generic wrapper."""
    positions = [match for match in ERROR_TAG.finditer(message) if match[0] != "[TCG-MIR-UNSUPPORTED]"]
    start = positions[0].start() if positions else 0
    return " ".join(message[start:].split())[:600]


# --- sources ----------------------------------------------------------------

def generate_sources(out: Path, environment: dict, suites: Sequence[str], groups: set | None) -> list[dict]:
    """Write every suite's sources under out/sources and return its units."""
    units = []
    sources = out / "sources"
    sources.mkdir()
    if "abi-xback" in suites:
        directory = sources / "abi-xback"
        directory.mkdir()
        group = directory / f"seeds{ABI_XBACK_FIRST}-{ABI_XBACK_FIRST + ABI_XBACK_COUNT - 1}"
        run_generator([sys.executable, str(GEN), "--emit-group", str(group),
                       str(ABI_XBACK_FIRST), str(ABI_XBACK_COUNT)], environment)
        units.append(generated_unit("abi-xback", group))
    if "abi-families" in suites:
        directory = sources / "abi-families"
        run_generator([sys.executable, str(FAMILIES), "--emit", str(directory)], environment)
        for group in sorted(path for path in directory.iterdir() if path.is_dir()):
            if groups is None or group.name in groups:
                units.append(generated_unit("abi-families", group))
    for suite, progs, shapes in (
            ("regclass-xback", REGCLASS_PROGS, REGCLASS_SHAPES),
            ("sret-xback", SRET_PROGS, ("argty",))):
        if suite not in suites:
            continue
        directory = sources / suite
        directory.mkdir()
        for shape in shapes:
            unit_dir = directory / shape
            unit_dir.mkdir()
            shutil.copyfile(progs / f"{shape}_callee.rs", unit_dir / "callee.rs")
            shutil.copyfile(progs / f"{shape}_caller.rs", unit_dir / "caller.rs")
            units.append({
                "suite": suite, "unit": shape, "dir": str(unit_dir),
                "cases": [{"name": shape, "family": suite, "abi": "Rust", "argc": None, "sides": "both",
                           "rule": f"{suite} {shape}", "expected": None, "expected_exit": FIXTURE_EXIT}],
            })
    return units


def run_generator(command: list[str], environment: dict) -> None:
    result = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, text=True, timeout=300)
    if result.returncode != 0:
        raise GateError(f"generator failed ({result.returncode}): {' '.join(command)}: {result.stderr.strip()}")


def generated_unit(suite: str, directory: Path) -> dict:
    expected = json.loads((directory / "expected.json").read_text())
    cases = []
    for case in expected["cases"]:
        cases.append({**case, "expected_exit": 0})
    return {"suite": suite, "unit": expected["group"], "dir": str(directory), "cases": cases}


SINGLE_CASE_LOCK = threading.Lock()


def single_case_unit(unit: dict, case: dict, out: Path, environment: dict) -> dict:
    """Regenerate one case of a generated unit as its own crate pair.

    Levels run concurrently and share the regenerated sources, so generation
    is serialized; every level then compiles the same bytes.
    """
    with SINGLE_CASE_LOCK:
        return _single_case_unit(unit, case, out, environment)


def _single_case_unit(unit: dict, case: dict, out: Path, environment: dict) -> dict:
    if unit["suite"] not in ("abi-xback", "abi-families"):
        raise GateError(f"{unit['suite']} has no per-case regeneration")
    directory = out / "single" / unit["suite"] / unit["unit"]
    directory.mkdir(parents=True, exist_ok=True)
    target = directory / case["name"]
    if not target.exists():
        if unit["suite"] == "abi-xback":
            seed = int(case["name"].removeprefix("seed"))
            run_generator([sys.executable, str(GEN), "--emit-group", str(target), str(seed), "1"], environment)
        else:
            staging = directory / f".{case['name']}"
            run_generator([sys.executable, str(FAMILIES), "--emit", str(staging), "--case", case["name"]],
                          environment)
            (staging / case["name"]).rename(target)
    return generated_unit(unit["suite"], target)


# --- execution --------------------------------------------------------------

class Runner:
    def __init__(self, trustc: str, backend: Path, environment: dict, compile_timeout: float,
                 run_timeout: float):
        self.trustc, self.backend, self.environment = trustc, backend, environment
        self.compile_timeout, self.run_timeout = compile_timeout, run_timeout
        self.lock = threading.Lock()
        self.counts = {"compiles": 0, "runs": 0}

    def compile(self, source: Path, backend: str, opt: int, crate_type: str, output: Path,
                library_dir: Path | None, log: Path) -> dict:
        command = [self.trustc, *BASE_FLAGS, f"-Copt-level={opt}", "--crate-type", crate_type]
        if backend == "tcg":
            command += [f"-Zcodegen-backend={self.backend}", *TCG_KNOBS]
        if crate_type == "rlib":
            command += ["--out-dir", str(output)]
        else:
            command += ["-o", str(output)]
        if library_dir is not None:
            command += ["-L", str(library_dir)]
        command.append(str(source))
        bounded = [sys.executable, str(TIMEOUT_RUNNER), "--grace-seconds", "5", str(self.compile_timeout),
                   *command]
        with log.open("x") as stream:
            result = subprocess.run(bounded, cwd=log.parent, env=self.environment, stdout=stream,
                                    stderr=subprocess.PIPE, text=True, errors="replace")
            stream.write(result.stderr)
        with self.lock:
            self.counts["compiles"] += 1
        verdict = classify_compile(result.returncode, result.stderr)
        if verdict["kind"] == "built":
            built = output if crate_type == "bin" else next(output.glob("lib*.rlib"), None)
            if built is None or not built.is_file():
                verdict = {"kind": "build-failure", "reason": "compiler exited 0 without its artifact",
                           "returncode": 0}
        verdict["log"] = str(log)
        if backend == "tcg" and verdict["kind"] == "build-failure" and backend_knob_refused(result.stderr):
            verdict["reason"] += " (the backend refused a knob)"
        return verdict

    def execute(self, binary: Path, argc: int | None) -> dict:
        arguments = [] if argc is None else ["case"] * (argc - 1)
        try:
            process = subprocess.Popen([str(binary), *arguments], cwd=binary.parent, env=self.environment,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       start_new_session=True)
        except OSError as error:
            return {"status": "launch-error", "error": str(error)}
        try:
            stdout, stderr = process.communicate(timeout=self.run_timeout)
            timed_out = False
        except subprocess.TimeoutExpired:
            # The child is this runner's own process; it is killed by its pid.
            process.kill()
            stdout, stderr = process.communicate()
            timed_out = True
        with self.lock:
            self.counts["runs"] += 1
        returncode = process.returncode
        status = "timeout" if timed_out else ("signal" if returncode < 0 else "exited")
        result = {"status": status, "returncode": returncode,
                  "stdout": stdout.decode("utf-8", errors="replace"),
                  "stderr": stderr.decode("utf-8", errors="replace")[-400:]}
        if returncode < 0:
            try:
                result["signal"] = signal.Signals(-returncode).name
            except ValueError:
                result["signal"] = str(-returncode)
        return result


def backend_knob_refused(stderr: str) -> bool:
    return "trust-ir-cg-args" in stderr and "unknown" in stderr.lower()


def expected_text(case: dict) -> str:
    return "" if case["expected"] is None else case["expected"] + "\n"


def run_unit_level(runner: Runner, unit: dict, opt: int, work: Path, mode: str) -> tuple[list[dict], bool]:
    """Build one crate pair at one level, all four cells, and run every case.

    Returns the cell records and whether any trust-cg half failed to build.
    """
    work.mkdir(parents=True)
    source = Path(unit["dir"])
    callees = {}
    for backend in ("llvm", "tcg"):
        directory = work / f"callee-{backend}"
        directory.mkdir()
        callees[backend] = runner.compile(source / "callee.rs", backend, opt, "rlib", directory, None,
                                          work / f"callee-{backend}.log")
    builds = {}
    for caller, callee in CELLS:
        binary = work / f"bin-{caller}-{callee}"
        if callees[callee]["kind"] != "built":
            builds[(caller, callee)] = {"kind": "not-built", "because": f"callee-{callee}"}
            continue
        builds[(caller, callee)] = runner.compile(source / "caller.rs", caller, opt, "bin", binary,
                                                  work / f"callee-{callee}", work / f"bin-{caller}-{callee}.log")
    tcg_failed = callees["tcg"]["kind"] != "built" or any(
        builds[cell]["kind"] not in ("built", "not-built") for cell in CELLS if cell[0] == "tcg")
    records = []
    for case in unit["cases"]:
        oracle = None
        for caller, callee in CELLS:
            record = {
                "suite": unit["suite"], "unit": unit["unit"], "case": case["name"],
                "family": case["family"], "abi": case["abi"], "sides": case["sides"], "opt": opt,
                "caller": caller, "callee": callee, "mode": mode,
            }
            callee_build, build = callees[callee], builds[(caller, callee)]
            if callee_build["kind"] != "built":
                record.update(outcome_for_build(callee_build, "callee"))
            elif build["kind"] != "built":
                record.update(outcome_for_build(build, "caller"))
            else:
                execution = runner.execute(work / f"bin-{caller}-{callee}", case["argc"])
                record["execution"] = {key: execution.get(key) for key in
                                       ("status", "returncode", "signal", "stdout", "stderr")}
                record.update(compare(case, (caller, callee), execution, oracle))
                if (caller, callee) == ("llvm", "llvm"):
                    oracle = execution if record["outcome"] == "oracle-ok" else None
            records.append(record)
    return records, tcg_failed


def outcome_for_build(build: dict, side: str) -> dict:
    if build["kind"] == "decline":
        return {"outcome": "decline", "decline": {"side": side, "tags": build["tags"],
                                                    "message": build["message"],
                                                    "functions": build.get("functions", [])},
                "log": build.get("log")}
    return {"outcome": "build-failure", "failure": {"side": side, "reason": build.get("reason"),
                                                      "returncode": build.get("returncode")},
            "log": build.get("log")}


def compare(case: dict, cell: tuple[str, str], execution: dict, oracle: dict | None) -> dict:
    expected_stdout = expected_text(case)
    if cell == ("llvm", "llvm"):
        if execution["status"] != "exited":
            return {"outcome": "oracle-failure", "reason": f"oracle {execution['status']}"}
        if execution["returncode"] != case["expected_exit"]:
            return {"outcome": "oracle-failure",
                    "reason": f"oracle exit {execution['returncode']}, fixture expects {case['expected_exit']}"}
        if execution["stdout"] != expected_stdout:
            return {"outcome": "oracle-failure", "reason": "oracle output differs from the generator's value"}
        return {"outcome": "oracle-ok"}
    if oracle is None:
        return {"outcome": "no-oracle"}
    if execution["status"] in ("signal", "timeout", "launch-error"):
        return {"outcome": "crash", "reason": execution.get("signal") or execution["status"]}
    if execution["returncode"] != oracle["returncode"] or execution["stdout"] != oracle["stdout"]:
        return {"outcome": "mismatch",
                "reason": f"exit {execution['returncode']} vs oracle {oracle['returncode']}; "
                          f"output {execution['stdout'].strip()[:200]!r} vs {oracle['stdout'].strip()[:200]!r}"}
    return {"outcome": "match"}


def run_unit(runner: Runner, unit: dict, opt: int, out: Path, environment: dict) -> list[dict]:
    work = out / "work" / unit["suite"] / unit["unit"] / f"O{opt}"
    records, tcg_failed = run_unit_level(runner, unit, opt, work, "group")
    if not tcg_failed or len(unit["cases"]) == 1:
        return records
    # A trust-cg half of the group did not build: one refused function would
    # hide every other case of the crate. Rebuild each case as its own pair so
    # every case is executed or declined on its own. The group attempt's rows
    # are kept as `group_attempt` records: the cells it did execute (the
    # halves that built) are judged by `verdict_errors` like every other cell,
    # and its refusal must be one the per-case rebuild reproduces.
    singles = []
    for case in unit["cases"]:
        single = single_case_unit(unit, case, out, environment)
        case_records, _ = run_unit_level(runner, single, opt, work / "per-case" / case["name"], "per-case")
        for record in case_records:
            record["unit"] = unit["unit"]
        singles.extend(case_records)
    for record in records:
        record["superseded"] = True
    return singles + [{"group_attempt": record} for record in records]


# --- verdict ------------------------------------------------------------------

def cell_records(report: dict) -> list[dict]:
    """The cells of the matrix: one per case, level and pairing."""
    return [record for record in report.get("cells", []) if "group_attempt" not in record]


def group_attempt_records(report: dict) -> list[dict]:
    """The rows of whole-group attempts that a per-case rebuild superseded.

    They are not matrix cells (each case's cell is its per-case row), but every
    one of them that executed is still a run of trust-cg code against the
    oracle, so `verdict_errors` judges it.
    """
    return [record["group_attempt"] for record in report.get("cells", []) if "group_attempt" in record]


def cell_outcome_error(row: dict, where: str) -> str | None:
    """The error one recorded cell carries, or None when its outcome is admissible.

    A decline is admissible here only as a refusal of a half trust-cg built;
    whether it is LISTED is the decline table's question.
    """
    outcome = row.get("outcome")
    oracle_cell = (row.get("caller"), row.get("callee")) == ("llvm", "llvm")
    if outcome == "oracle-ok" and oracle_cell or outcome == "match" and not oracle_cell:
        return None
    if outcome == "decline":
        side = row.get("decline", {}).get("side")
        if side not in ("callee", "caller") or row.get(side) != "tcg":
            return f"decline recorded on a half trust-cg did not compile: {where}"
        return None
    if outcome in ("match", "oracle-ok"):
        return f"{outcome} recorded on the wrong cell: {where}"
    if outcome == "mismatch":
        return f"WRONG VALUE {where}: {row.get('reason')}"
    if outcome == "crash":
        return f"CRASH {where}: {row.get('reason')}"
    if outcome == "build-failure":
        return f"build failure {where}: {row.get('failure')}"
    return f"{outcome} {where}: {row.get('reason')}"


def summarize(cells: list[dict]) -> dict:
    summary = {}
    for suite in SUITES:
        rows = [row for row in cells if row["suite"] == suite]
        if not rows:
            continue
        outcomes = {}
        for row in rows:
            outcomes[row["outcome"]] = outcomes.get(row["outcome"], 0) + 1
        cases = sorted({row["case"] for row in rows})
        families = {}
        for row in rows:
            families.setdefault(row["family"], set()).add(row["case"])
        cross = [row for row in rows if (row["caller"], row["callee"]) != ("llvm", "llvm")]
        summary[suite] = {
            "cases": len(cases), "cells": len(rows), "outcomes": dict(sorted(outcomes.items())),
            "cross_cells": len(cross),
            "cross_matches": sum(1 for row in cross if row["outcome"] == "match"),
            "families": {name: len(members) for name, members in sorted(families.items())},
            "opt_levels": sorted({row["opt"] for row in rows}),
        }
    return summary


def decline_rows(cells: list[dict]) -> list[dict]:
    rows = {}
    for row in cells:
        if row["outcome"] != "decline":
            continue
        key = (row["suite"], row["case"], row["decline"]["side"])
        entry = rows.setdefault(key, {
            "suite": row["suite"], "case": row["case"], "family": row["family"], "abi": row["abi"],
            "side": row["decline"]["side"], "tags": row["decline"]["tags"], "opt_levels": set(),
            "cells": 0, "message": row["decline"]["message"],
        })
        entry["opt_levels"].add(row["opt"])
        entry["cells"] += 1
        if row["decline"]["tags"] != entry["tags"]:
            entry["tags"] = sorted(set(entry["tags"]) | set(row["decline"]["tags"]))
    return [{**entry, "opt_levels": sorted(entry["opt_levels"])}
            for _, entry in sorted(rows.items())]


def verdict_errors(report: dict, backend_sha256: str | None = None, *, complete: bool = True) -> list[str]:
    """Every reason this report cannot pass. Shared by the bridge lane."""
    errors = []
    if report.get("schema") != SCHEMA:
        return [f"expected cross-backend report schema {SCHEMA}"]
    if backend_sha256 is not None and report.get("backend", {}).get("sha256") != backend_sha256:
        errors.append("cross-backend report does not bind the qualified backend hash")
    levels = report.get("opt_levels")
    if complete and levels != list(OPT_LEVELS):
        errors.append("cross-backend run must cover exactly O0-O3")
    if not isinstance(levels, list) or not levels or any(level not in OPT_LEVELS for level in levels):
        return errors + ["cross-backend report names no valid optimization levels"]
    if report.get("knobs") != list(TCG_KNOBS) or report.get("base_flags") != list(BASE_FLAGS):
        errors.append("cross-backend run must use the pinned compile flags")
    cells = cell_records(report)
    if not cells:
        errors.append("cross-backend run executed no cell")
        return errors
    if complete and report.get("selection") is not None:
        errors.append("a subset run is not the required cross-backend matrix")
    # Matrix completeness: every case at every level in every cell, exactly once.
    seen = {}
    for row in cells:
        key = (row["suite"], row["case"], row["opt"], row["caller"], row["callee"])
        seen[key] = seen.get(key, 0) + 1
    for key, count in seen.items():
        if count != 1:
            errors.append(f"cell recorded {count} times: {key}")
    cases = {(row["suite"], row["case"]) for row in cells}
    for suite, case in sorted(cases):
        for opt in levels:
            for caller, callee in CELLS:
                if (suite, case, opt, caller, callee) not in seen:
                    errors.append(f"missing cell {suite}/{case} O{opt} caller={caller} callee={callee}")
    for row in cells:
        where = f"{row['suite']}/{row['case']} O{row['opt']} caller={row['caller']} callee={row['callee']}"
        error = cell_outcome_error(row, where)
        if error is not None:
            errors.append(error)
    # Superseded whole-group attempts: every cell they executed is judged, and
    # their refusal must be one the per-case rebuild of the same unit, level
    # and side reproduced (tags included), so a refusal that exists only in
    # group form cannot stand in for the cells it kept from running.
    per_case = {}
    rebuilt = set()
    for row in cells:
        if row.get("mode") != "per-case":
            continue
        rebuilt.add((row["suite"], row.get("unit"), row["opt"]))
        if row["outcome"] == "decline":
            per_case.setdefault((row["suite"], row.get("unit"), row["opt"], row["decline"]["side"]),
                                set()).update(row["decline"]["tags"])
    for row in group_attempt_records(report):
        where = (f"{row.get('suite')}/{row.get('case')} O{row.get('opt')} caller={row.get('caller')} "
                 f"callee={row.get('callee')} (superseded group attempt {row.get('unit')})")
        if (row.get("suite"), row.get("unit"), row.get("opt")) not in rebuilt:
            errors.append(f"group attempt without a per-case rebuild: {where}")
        error = cell_outcome_error(row, where)
        if error is not None:
            errors.append(error)
            continue
        if row["outcome"] == "decline":
            side = row["decline"]["side"]
            reproduced = per_case.get((row["suite"], row.get("unit"), row["opt"], side))
            if reproduced is None or not set(row["decline"]["tags"]) <= reproduced:
                errors.append(f"group refusal {row['decline']['tags']} on the {side} not reproduced by any "
                              f"per-case rebuild: {where}")
    # Declines must equal the committed table exactly: per (suite, case, side)
    # its levels, and per declined cell its exact tag set (so a tag that
    # changes at one level cannot hide behind the others).
    observed = {(row["suite"], row["case"], row["side"]): row for row in decline_rows(cells)}
    for key, row in observed.items():
        expected = EXPECTED_DECLINES.get(key)
        if expected is None:
            errors.append(f"unlisted decline {key[0]}/{key[1]} {key[2]} at O{row['opt_levels']}: "
                          f"{row['tags']} {row['message'][:160]}")
            continue
        if list(expected["opt_levels"]) != row["opt_levels"]:
            errors.append(f"decline {key} changed: expected {expected['tags']} at {expected['opt_levels']}, "
                          f"observed {row['tags']} at {row['opt_levels']}")
    for row in cells:
        if row["outcome"] != "decline":
            continue
        expected = EXPECTED_DECLINES.get((row["suite"], row["case"], row["decline"]["side"]))
        if expected is None:
            continue
        want = expected_cell_tags(expected, row["opt"])
        if sorted(row["decline"]["tags"]) != want:
            errors.append(f"decline tags changed at O{row['opt']} caller={row['caller']} callee={row['callee']}: "
                          f"{row['suite']}/{row['case']} {row['decline']['side']} expected {want}, "
                          f"observed {sorted(row['decline']['tags'])}")
    if complete:
        for key in EXPECTED_DECLINES:
            if key not in observed:
                errors.append(f"stale expected decline (no longer declines; remove it): {key}")
    if complete:
        summary = summarize(cells)
        for suite, minimum in SUITE_MIN_CASES.items():
            row = summary.get(suite)
            if row is None:
                errors.append(f"suite {suite} did not run")
                continue
            if row["cases"] < minimum:
                errors.append(f"suite {suite} ran {row['cases']} cases, below its pinned {minimum}")
            if row["cross_matches"] < SUITE_MIN_CROSS_MATCHES[suite]:
                errors.append(f"suite {suite} matched {row['cross_matches']} executed cross cells, below its "
                              f"pinned {SUITE_MIN_CROSS_MATCHES[suite]}")
        families = summary.get("abi-families", {}).get("families", {})
        for family, minimum in FAMILY_MIN_CASES.items():
            if families.get(family, 0) < minimum:
                errors.append(f"family {family} has {families.get(family, 0)} cases, below its pinned {minimum}")
    return errors


# --- preflight and main ---------------------------------------------------------

def resolve_trustc(explicit: str | None) -> str:
    path = explicit or shutil.which("trustc")
    if path is None:
        raise GateError("the pinned Trust compiler (trustc) is not on PATH; name it with --trustc")
    resolved = Path(path).resolve(strict=True)
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise GateError(f"trustc is not an executable file: {resolved}")
    return str(resolved)


def compiler_identity(trustc: str, environment: dict) -> dict:
    result = subprocess.run([trustc, "-vV"], env=environment, capture_output=True, text=True, timeout=60)
    if result.returncode != 0:
        raise GateError(f"trustc -vV failed: {result.stderr.strip()}")
    text = result.stdout
    hosts = re.findall(r"^host: (\S+)$", text, re.MULTILINE)
    if sys.platform != "linux" or hosts != [HOST]:
        raise GateError(f"the cross-backend gate runs on {HOST}; trustc reports {hosts!r} on {sys.platform}")
    if not re.search(r"^binary: trustc$", text, re.MULTILINE):
        raise GateError("the compiler is not the branded Trust driver (binary: trustc)")
    commit = re.search(r"^commit-hash: ([0-9a-f]{40})$", text, re.MULTILINE)
    if commit is None:
        raise GateError("the Trust compiler reports no commit identity")
    sysroot = subprocess.run([trustc, "--print", "sysroot"], env=environment, capture_output=True,
                             text=True, timeout=60).stdout.strip()
    return {"path": trustc, "sha256": sha256_file(Path(trustc)), "version": text.strip(),
            "commit": commit[1], "sysroot": sysroot}


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
                                     allow_abbrev=False)
    parser.add_argument("--backend", type=Path, required=True, help="the bridge backend (.so) under test")
    parser.add_argument("--backend-sha256", help="refuse to run unless the backend has this SHA-256")
    parser.add_argument("--trustc", help="the pinned Trust compiler (default: PATH trustc)")
    parser.add_argument("--out", type=Path, help="new report directory outside the source tree")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--compile-timeout", type=float, default=300.0)
    parser.add_argument("--run-timeout", type=float, default=30.0)
    parser.add_argument("--suites", help="development subset: comma-separated suites (never a pass)")
    parser.add_argument("--groups", help="development subset: comma-separated abi-families groups")
    parser.add_argument("--opt-levels", help="development subset: comma-separated levels (never a pass)")
    args = parser.parse_args(argv)
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    try:
        if args.out is None:
            out = Path(tempfile.mkdtemp(prefix="trust-cg-linux-aarch64-xback-"))
        else:
            out = args.out.absolute()
            if out.resolve().is_relative_to(ROOT):
                raise OSError("report directory must be outside the source tree")
            out.mkdir(mode=0o700)
    except OSError as error:
        print(f"cross-backend ABI gate: output error: {error}", file=sys.stderr)
        return 1
    suites = SUITES if args.suites is None else tuple(args.suites.split(","))
    groups = None if args.groups is None else set(args.groups.split(","))
    levels = OPT_LEVELS if args.opt_levels is None else tuple(int(level) for level in args.opt_levels.split(","))
    selection = None
    if args.suites is not None or args.groups is not None or args.opt_levels is not None:
        selection = {"suites": list(suites), "groups": sorted(groups) if groups else None, "opt_levels": list(levels)}
    report = {
        "schema": SCHEMA, "status": "incomplete", "errors": [], "selection": selection,
        "scope": ("Linux AArch64 cross-backend ABI execution (LLVM and the Trust-built bridge on either side of "
                  "each call); unverified frontend lane, proof certificates off; not proof evidence"),
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "opt_levels": list(levels), "cells_per_case": [list(cell) for cell in CELLS],
        "base_flags": list(BASE_FLAGS), "knobs": list(TCG_KNOBS),
        "expected_declines": [
            {"suite": suite, "case": case, "side": side, **row}
            for (suite, case, side), row in sorted(EXPECTED_DECLINES.items())
        ],
    }
    report_path = out / "report.json"
    write_report(report_path, report)
    print(f"cross-backend ABI gate: report {report_path}", flush=True)
    try:
        environment, scrubbed = child_environment()
        report["scrubbed_environment"] = scrubbed
        trustc = resolve_trustc(args.trustc)
        report["compiler"] = compiler_identity(trustc, environment)
        backend = args.backend.absolute()
        report["backend"] = file_identity(backend)
        if args.backend_sha256 is not None and report["backend"]["sha256"] != args.backend_sha256:
            raise GateError("backend SHA-256 differs from --backend-sha256")
        report["generators"] = {
            str(path.relative_to(ROOT)): sha256_file(path)
            for path in (GEN, FAMILIES, *sorted(REGCLASS_PROGS.glob("*.rs")), *sorted(SRET_PROGS.glob("*.rs")))
        }
        report["runner_sha256"] = sha256_file(Path(__file__).resolve())
        units = generate_sources(out, environment, suites, groups)
        report["units"] = [{"suite": unit["suite"], "unit": unit["unit"], "cases": len(unit["cases"])}
                           for unit in units]
        write_report(report_path, report)
        runner = Runner(trustc, backend, environment, args.compile_timeout, args.run_timeout)
        tasks = [(unit, opt) for unit in units for opt in levels]
        print(f"cross-backend ABI gate: {len(units)} crate pairs x {len(levels)} levels, "
              f"{sum(len(unit['cases']) for unit in units)} cases, jobs {args.jobs}", flush=True)
        cells = []
        started = time.monotonic()
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = [pool.submit(run_unit, runner, unit, opt, out, environment) for unit, opt in tasks]
            for done, future in enumerate(futures, 1):
                rows = future.result()
                cells.extend(rows)
                bad = [row for row in rows if row.get("outcome") not in (None, "match", "oracle-ok")]
                unit, opt = tasks[done - 1]
                print(f"  [{done}/{len(tasks)}] {unit['suite']}/{unit['unit']} O{opt}: "
                      f"{sum(1 for row in rows if row.get('outcome') == 'match')} match"
                      + (f", {len(bad)} other" if bad else ""), flush=True)
        report["elapsed_seconds"] = round(time.monotonic() - started, 1)
        report["counts"] = dict(runner.counts)
        report["cells"] = cells
        report["backend_after"] = file_identity(backend)
        if report["backend_after"] != report["backend"]:
            raise GateError("backend changed during the cross-backend run")
        live = cell_records(report)
        report["summary"] = summarize(live)
        report["declines"] = decline_rows(live)
        attempts = group_attempt_records(report)
        report["group_attempt_summary"] = {
            "cells": len(attempts),
            "executed": sum(1 for row in attempts if "execution" in row),
            "outcomes": {outcome: sum(1 for row in attempts if row["outcome"] == outcome)
                         for outcome in sorted({row["outcome"] for row in attempts})},
        }
        report["errors"] = verdict_errors(report, complete=selection is None)
        if selection is not None:
            report["status"] = "subset-fail" if report["errors"] else "subset-ok"
        else:
            report["status"] = "fail" if report["errors"] else "pass"
    except (GateError, OSError, subprocess.SubprocessError, ValueError, KeyError) as error:
        report["errors"].append(str(error))
        report["status"] = "fail"
    except KeyboardInterrupt:
        report["errors"].append("interrupted")
        report["status"] = "fail"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    write_report(report_path, report)
    print_summary(report)
    return 0 if report["status"] in ("pass", "subset-ok") else 1


def print_summary(report: dict) -> None:
    for suite, row in report.get("summary", {}).items():
        print(f"{suite}: {row['cases']} cases, {row['cells']} cells, {row['cross_matches']}/{row['cross_cells']} "
              f"cross cells matched; outcomes {row['outcomes']}")
    for row in report.get("declines", []):
        print(f"DECLINE {row['suite']}/{row['case']} {row['side']} O{row['opt_levels']}: {row['tags']} "
              f"{row['message'][:200]}")
    for error in report.get("errors", [])[:200]:
        print(f"ERROR {error}")
    print(f"cross-backend ABI gate: {report['status'].upper()}")


def write_report(path: Path, report: dict) -> None:
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=1, sort_keys=False) + "\n", encoding="utf-8")
    temporary.replace(path)


if __name__ == "__main__":
    raise SystemExit(main())
