#!/usr/bin/env python3
# scripts/eqsat_corpus.py - generate the interim trust-cg-eqsat corpus (PKG-U1)
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Generate the INTERIM e-graph corpus of docs/eqsat-tier-e.md section 9.

The plan's corpus is the trust-ir dumped from the rustc ladder by
``-Ztrust-dump=ir`` on the stage-1 compiler (PKG-C0). That dump does not exist
yet, so this script assembles an interim one from trust-ir modules already
committed:

* in trust-ir, at exactly the revision the root ``Cargo.toml`` committed at
  ``HEAD`` pins (``git show HEAD:Cargo.toml``; the modules are read with
  ``git ls-tree`` / ``git cat-file`` from ``--trust-ir-repo``, never from a
  worktree checkout);
* in trust-cg, at ``HEAD`` (committed blobs only; no candidate is read from
  the working tree, so an uncommitted edit never reaches the corpus).

The probe that reads the candidates is built by Cargo from the working tree
(``--locked``: ``Cargo.lock`` must already resolve the manifest). Its trust-ir
is therefore the one the working-tree ``Cargo.toml`` pins, and generation
refuses when that pin differs from the committed one, so the revision the
manifest header names is the one that validated every taken module.

It writes ``crates/trust-cg-eqsat/tests/corpus/MANIFEST.tsv`` and
``crates/trust-cg-eqsat/tests/corpus/modules/*.trust_ir``. The manifest names
EVERY candidate with a reason: every file in either tree whose name marks a
trust-ir module transport, plus the binary/JSON/MessagePack files of the
fixture families listed in ``CODEC_FAMILIES``, except files of the engine's
and the checker's own crates (``crates/trust-cg-eqsat*``: the corpus itself
and fixtures written for those crates would make the measurement circular).
Each candidate is classified by the first matching rule of ``RULES``; a
candidate no rule names is left out as unreviewed (fail-closed: a new fixture
is never taken without review).

A candidate a rule sends to the probe is read by
``crates/trust-cg-eqsat/examples/eqsat_corpus_probe.rs``: decoded (text or
the TRUST_IR binary codec), validated with ``trust_ir_build::validate_module``,
printed back with ``trust_ir::format::text_checked`` and re-parsed to a
structurally equal module. It is taken when that holds, the module has a
function body, its printed text is neither a duplicate nor a near-duplicate
(equal once the module name and Rust mangled symbols are blanked:
``shape_key``) of a candidate preferred before it, and it fits the size
limits: ``PER_FILE_CAP`` per module, ``FAMILY_BUDGET`` per family and
``CORPUS_BUDGET`` in all, consumed in preference order (family rank, then
source). Generation fails rather than write a directory of
``DIRECTORY_LIMIT`` bytes or more. Every corpus file is TEXT: the consumers
parse it with ``trust_ir::parser::parse_module`` only.

Consumers read only MANIFEST.tsv (rows whose status is ``taken``) and the
module files it names. PKG-C0 replaces this corpus by regenerating that
directory from the ladder dump in the same manifest format (comment lines,
the header ``status<TAB>file<TAB>source<TAB>reason``, one row per candidate);
no consumer changes.

What the corpus establishes, and what not: a taken module is read, validated
and text-round-tripped by the pinned trust-ir. It is NOT a sample of
production code (the hand-written goldens over-represent unusual constructs,
the benchmark dumps were collected at older wire versions and re-read by the
current reader), and nothing here says what the engine does with it.

Usage::

    python3 -I scripts/eqsat_corpus.py [--trust-ir-repo PATH] [--probe-cmd CMD]
    python3 -I scripts/eqsat_corpus.py --check [...]

``--check`` regenerates into a temporary directory and compares it with the
committed corpus directory byte for byte; it exits 1 on any difference.
``--probe-cmd`` replaces the command that runs the probe (the script appends
``--out DIR LIST``); the default runs the example through
``scripts/trust_cargo.sh run --locked --offline`` behind ``build-slot`` when
that gate is installed, with the caller's ``CARGO_TARGET_DIR``.

Exit status: 0 success (and, with --check, no difference); 1 a --check
difference; 2 an error (missing pinned revision, probe failure, an
unexpected exception, ...), reported on one line of standard error. Status 1
means only a difference: no failure is ever reported as one.
"""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unicodedata

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "crates" / "trust-cg-eqsat" / "tests" / "corpus"
MANIFEST_HEADER = "status\tfile\tsource\treason"

# Size limits on the printed text of taken modules. A module over the per-file
# cap is left out as oversize; candidates are then taken in preference order
# (family rank, then source) while the running totals stay within the family
# budget (so no one generator dominates the corpus) and the corpus budget.
# Generation fails when the whole directory (modules plus manifest) would
# reach DIRECTORY_LIMIT bytes.
PER_FILE_CAP = 256 * 1024
FAMILY_BUDGET = 1_500_000
CORPUS_BUDGET = 4_000_000
DIRECTORY_LIMIT = 6_000_000

# File-name endings that mark a trust-ir module transport (or a near relative
# a reader must refuse by name: templates, proof-lineage sidecars). Every file
# with one of these endings in either tree is a candidate.
MODULE_SUFFIXES = (
    ".trust_ir",
    ".trust-ir",
    ".tir",
    ".tmbc",
    ".trust_irbin",
    ".trust-ir.txt",
    ".trust-ir.bin",
    ".trust-ir.json",
    ".trust_ir.json",
    ".trust_irs",
    ".tmbs",
    ".trust_irpl",
)

# Fixture families whose generic-codec files (.bin, .json, .msgpack) are also
# candidates. (repo, directory prefix, regex on the rest of the path)
CODEC_FAMILIES = (
    ("ir", "crates/trust-ir-conformance/tests/fixtures/", r"[^\n]*\.(bin|json|msgpack)"),
    ("ir", "crates/trust-ir-build/tests/fixtures/source_value_equations/", r"[^\n]*\.bin"),
    ("ir", "lean/semr/fixtures/", r"[^\n]*\.bin"),
    ("cg", "tests/fixtures/", r"[^/\n]+\.json"),
    ("cg", "tests/fixtures/trust_ir_binary_container/", r"[^\n]*\.json"),
)

# Basenames that are indexes beside modules, never modules.
NOT_MODULES = {"MANIFEST.json", "ORIGIN.json"}


class Left:
    """Leave the candidate out with a fixed reason."""

    def __init__(self, reason: str) -> None:
        self.reason = reason


class Probe:
    """Send the candidate to the probe; take it if it passes.

    ``family`` names the module file prefix, ``rank`` orders duplicates and the
    size budget (lower first), ``base`` is the directory the file-name stem is
    taken relative to, ``note`` says what a taken module exercises.
    """

    def __init__(self, family: str, rank: int, base: str, note: str) -> None:
        self.family = family
        self.rank = rank
        self.base = base
        self.note = note


class TwinOf:
    """A binary/JSON twin of a sibling in another format.

    Left as a twin when the sibling with ``suffix`` exists in the same tree;
    otherwise handled by ``fallback``.
    """

    def __init__(self, suffix: str, fallback: Left | Probe) -> None:
        self.suffix = suffix
        self.fallback = fallback


class VendoredFrom:
    """A trust-cg copy of a trust-ir fixture: compared with the pinned blob."""

    def __init__(self, ir_dir: str) -> None:
        self.ir_dir = ir_dir


# Directory prefixes, used both literally (as a Probe base) and as the start of
# a rule pattern (they hold no regex metacharacter).
CF = "crates/trust-ir-conformance/tests/fixtures/"
TF = "crates/trust-cg-codegen/tests/fixtures/"
COMPILE_CORPUS = "benchmarks/compile-corpus/modules/"

REASON_TWIN = "format twin of {twin} (that form is the candidate)"
REASON_UNREVIEWED = "unreviewed location (no corpus rule names it)"
REASON_NO_BODY = "no function with a body (nothing for the engine)"

# Ordered classification rules: (repo, regex anchored at the path start,
# action). The first match wins; a candidate no rule matches is left out as
# unreviewed. "ir" is trust-ir at the pinned revision, "cg" is trust-cg HEAD.
RULES: tuple[tuple[str, str, object], ...] = (
    # trust-ir
    ("ir", r"reports/", Left("report artifact (not held by a test; includes deliberate negatives)")),
    ("ir", CF + r"refuse/", Left("refusal fixture (must-refuse corpus)")),
    ("ir", CF + r"refuse_templates/", Left("refusal template (must-refuse corpus), not a module")),
    ("ir", CF + r"templates/", Left("level-S template, not a module")),
    ("ir", CF + r"compat/", Left("compat reader fixture (older wire version of a live family)")),
    ("ir", CF + r"v41-reader-compat/", Left("legacy reader fixture (frozen v41 shapes of live families)")),
    ("ir", CF + r"frame-cfg/stale_generation_loop\.trust_ir$",
     Left("negative fixture (invalid by design: binding use after close)")),
    ("ir", CF + r"frame-cfg/mixed_origin_join\.trust_ir$",
     Left("negative fixture (invalid by design: binding slot type mismatch)")),
    ("ir", CF + r"frame-cfg/[^/]+\.trust_ir$",
     Probe("frame_cfg", 21, CF + "frame-cfg/", "binding-frame loop fixture")),
    ("ir", CF + r"semr_compiled/[^/]+\.bin$",
     Probe("semr_compiled", 50, CF + "semr_compiled/",
           "rustc -Ztrust-dump=ir crate module (body-gated, proof-annotated)")),
    ("ir", CF + r"proof_lineage_", Left("not a module (proof-lineage sidecar)")),
    ("ir", CF + r"native_request_trust_bundle\.", Left("not a module (native request trust bundle)")),
    ("ir", CF + r"vector_mask_oracles\.json$", Left("not a module (vector mask oracle table)")),
    ("ir", CF + r"[^/]+\.trust_ir$",
     Probe("conformance", 20, CF, "trust-ir conformance golden")),
    ("ir", CF + r"[^/]+\.(tmbc|json|msgpack)$",
     TwinOf(".trust_ir", Left("binary/JSON golden without a text twin (not read)"))),
    ("ir", r"crates/trust-ir-build/tests/fixtures/source_value_equations/",
     Left("certificate-bound (source-value equation evidence)")),
    ("ir", r"lean/semr/fixtures/law-proof-ref-body-mutant\.tmbc$",
     Left("negative fixture (body mutant of a kernel-checked byte image)")),
    ("ir", r"lean/semr/fixtures/",
     Left("certificate-bound (byte image a Lean kernel check names)")),
    ("ir", r"crates/trust-ir-ay/tests/fixtures/[^/]+\.trust-ir\.txt$",
     Probe("ay", 51, "crates/trust-ir-ay/tests/fixtures/", "trustc text dump")),
    # trust-cg. The engine's and the checker's own crates are never
    # candidates: the corpus itself, and fixtures written for those crates,
    # would make the measurement circular.
    ("cg", r"crates/trust-cg-eqsat/", None),
    ("cg", r"crates/trust-cg-eqsat-check/", None),
    ("cg", r"reports/", Left("report artifact (not held by a test)")),
    ("cg", TF + r"ae9-linux/",
     Left("platform twin (Linux-target dump of a module the macOS dumps cover)")),
    ("cg", TF + r"trust_ir_exec/",
     Probe("cg_exec", 10, TF + "trust_ir_exec/",
           "interpreter-differential program (argument vectors in its MANIFEST.tsv)")),
    ("cg", TF + r"insert_field/store_form\.trust_ir$",
     Left("negative fixture (store form: FieldAccessInvalid)")),
    ("cg", TF + r"enum_projection/[^/]*tag_write[^/]*$",
     Left("negative fixture (enum re-tag write is undefined behaviour)")),
    ("cg", TF + r"(insert_field|enum_projection|declared_tuple_layout)/",
     Probe("cg_values", 30, TF, "aggregate value-semantics fixture")),
    ("cg", TF + r"(aggregate_insert|hfa_zero_sized|large_aggregate_args)/",
     Probe("cg_abi", 31, TF, "aggregate ABI fixture")),
    ("cg", TF + r"(aarch64_nonleaf_frame|x86_split_copy_replay|aarch64_framed_identity"
     r"|aarch64_local_address)/",
     Probe("cg_backend", 32, TF, "backend regression input")),
    ("cg", TF + r"trust_ir_conformance/", VendoredFrom(CF)),
    ("cg", TF + r"mir_[^/]+\.tir$",
     Probe("cg_mir", 61, TF, "MIR dump")),
    ("cg", r"crates/trust-cg-codegen/tests/slices/[^/]+\.tir$",
     Probe("cg_slices", 60, "crates/trust-cg-codegen/tests/slices/",
           "MIR closure dump of one real function")),
    ("cg", r"crates/trust-cg-codegen/tests/[^/]+\.tir$",
     Probe("cg_dumps", 90, "crates/trust-cg-codegen/tests/", "whole-crate MIR dump")),
    ("cg", r"crates/trust-cg-jit-matrix/fixtures/",
     Probe("cg_bcp", 42, "crates/trust-cg-jit-matrix/fixtures/", "hand-written BCP kernel")),
    ("cg", r"scripts/fuzz/[^/]+\.trust_ir$",
     Probe("cg_fuzz", 40, "scripts/fuzz/", "fuzz-campaign loop kernel")),
    ("cg", r"examples/[^/]+\.trust_ir$",
     Probe("cg_examples", 41, "examples/", "quickstart example")),
    ("cg", r"tests/fixtures/trust_ir_binary_container/conformance/compat_",
     Left("compat reader fixture (wire version below the read floor)")),
    ("cg", r"tests/fixtures/trust_ir_binary_container/conformance/", VendoredFrom(CF)),
    ("cg", r"tests/fixtures/trust_ir_binary_container/clean/",
     Left("certificate-bound (gated Clean library body)")),
    ("cg", r"tests/fixtures/trust_ir_binary_container/pinned_writer/[^/]+\.json$",
     TwinOf(".tmbc", Left("JSON module (not read: no JSON reader among the probe's dependencies)"))),
    ("cg", r"tests/fixtures/trust_ir_binary_container/pinned_writer/",
     Probe("cg_pinned_writer", 33, "tests/fixtures/trust_ir_binary_container/pinned_writer/",
           "binary writer pin")),
    ("cg", r"tests/fixtures/[^/]+\.json$", Left("legacy JSON format")),
    ("cg", r"crates/trust-cg-verify/tests/fixtures/",
     Left("JSON module (not read: no JSON reader among the probe's dependencies)")),
    ("cg", COMPILE_CORPUS + r"fixtures/",
     Probe("bench_fixtures", 70, COMPILE_CORPUS + "fixtures/",
           "compile-corpus binary of a trust-cg fixture")),
    ("cg", COMPILE_CORPUS + r"jit-matrix/",
     Probe("bench_jit", 71, COMPILE_CORPUS + "jit-matrix/", "compile-corpus BCP/parent-loop kernel")),
    ("cg", COMPILE_CORPUS + r"bridge/",
     Probe("bench_bridge", 80, COMPILE_CORPUS + "bridge/", "rustc-bridge codegen-unit dump")),
    ("cg", COMPILE_CORPUS + r"ty/",
     Probe("bench_ty", 81, COMPILE_CORPUS + "ty/", "TY-generated state-machine module")),
)

# Endings stripped from a file name to form a module file stem (longest first).
STEM_SUFFIXES = tuple(
    sorted(
        set(MODULE_SUFFIXES) | {".trust.tir", ".bin", ".json", ".msgpack"},
        key=len,
        reverse=True,
    )
)


class GenerationError(Exception):
    """A failure that stops generation (exit status 2)."""


def git(args: list[str], *, input_bytes: bytes | None = None) -> bytes:
    result = subprocess.run(
        ["git", *args],
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode != 0:
        raise GenerationError(
            f"git {' '.join(args[:4])} ... failed: {result.stderr.decode(errors='replace').strip()}"
        )
    return result.stdout


def pinned_revision_in(text: str, where: str) -> str:
    """The trust-ir revision a root Cargo.toml text pins (all trust-ir* lines agree)."""
    revs = set(
        re.findall(
            r'^trust-ir[a-z-]*\s*=\s*\{[^}\n]*\brev\s*=\s*"([0-9a-f]{40})"', text, re.MULTILINE
        )
    )
    main = re.findall(
        r'^trust-ir\s*=\s*\{[^}\n]*\brev\s*=\s*"([0-9a-f]{40})"', text, re.MULTILINE
    )
    if len(main) != 1 or revs != set(main):
        raise GenerationError(
            f"the root Cargo.toml ({where}) must pin exactly one trust-ir revision on every"
            " trust-ir* line"
        )
    return main[0]


def pinned_revision() -> str:
    """The trust-ir revision ``HEAD:Cargo.toml`` pins.

    The probe is built from the working tree, so a working-tree ``Cargo.toml``
    that pins another revision is refused: the probe would validate the
    modules with a trust-ir other than the one the manifest names.
    """
    committed = git(["-C", str(ROOT), "show", "HEAD:Cargo.toml"]).decode("utf-8")
    rev = pinned_revision_in(committed, "HEAD")
    working = pinned_revision_in((ROOT / "Cargo.toml").read_text(encoding="utf-8"), "working tree")
    if working != rev:
        raise GenerationError(
            f"the working-tree Cargo.toml pins trust-ir {working}, HEAD pins {rev}; the probe"
            " would read the corpus with an uncommitted pin (commit or revert the pin move)"
        )
    return rev


def ls_tree(repo: Path, rev: str) -> dict[str, str]:
    """Path -> blob id of every regular file in ``rev`` of ``repo``."""
    out = git(["-C", str(repo), "ls-tree", "-r", "-z", "--full-tree", rev])
    files: dict[str, str] = {}
    for record in out.split(b"\0"):
        if not record:
            continue
        meta, _, path = record.partition(b"\t")
        mode, kind, blob = meta.decode().split(" ")
        if kind == "blob" and mode in ("100644", "100755"):
            files[path.decode("utf-8")] = blob
    return files


def cat_blobs(repo: Path, blobs: list[str]) -> dict[str, bytes]:
    """Blob id -> contents, read in one ``git cat-file --batch``."""
    unique = sorted(set(blobs))
    if not unique:
        return {}
    out = git(
        ["-C", str(repo), "cat-file", "--batch"],
        input_bytes="".join(f"{b}\n" for b in unique).encode(),
    )
    contents: dict[str, bytes] = {}
    position = 0
    for blob in unique:
        newline = out.index(b"\n", position)
        header = out[position:newline].decode().split(" ")
        if len(header) != 3 or header[0] != blob or header[1] != "blob":
            raise GenerationError(f"git cat-file returned {header!r} for {blob}")
        size = int(header[2])
        start = newline + 1
        contents[blob] = out[start : start + size]
        position = start + size + 1
    return contents


def in_universe(repo: str, path: str) -> bool:
    name = path.rsplit("/", 1)[-1]
    if name in NOT_MODULES:
        return False
    if path.endswith(MODULE_SUFFIXES):
        return True
    for family_repo, prefix, rest in CODEC_FAMILIES:
        if repo == family_repo and path.startswith(prefix) and re.fullmatch(rest, path[len(prefix):]):
            return True
    return False


def classify(repo: str, path: str) -> object:
    for rule_repo, pattern, action in RULES:
        if rule_repo == repo and re.match(pattern, path):
            return action
    return Left(REASON_UNREVIEWED)


def stem(path: str, base: str) -> str:
    relative = path[len(base):] if path.startswith(base) else path.rsplit("/", 1)[-1]
    for suffix in STEM_SUFFIXES:
        if relative.endswith(suffix):
            relative = relative[: -len(suffix)]
            break
    return relative.replace("/", "__")


def shape_key(text: bytes) -> bytes:
    """``text`` with the module name and every Rust v0 mangled symbol blanked.

    Codegen-unit dumps of different crates repeat the same standard-library
    shims (``lang_start`` closures, ``Termination::report``) whose texts differ
    only in the crate disambiguators inside those names; two modules with one
    shape key give the engine the same bodies, so only the first is taken.
    """
    blanked = re.sub(rb'^module "[^"\n]*"', b'module ""', text, count=1, flags=re.MULTILINE)
    return re.sub(rb"_R[0-9A-Za-z_]+", b"_R", blanked)


def module_file(family: str, path: str, base: str, source: str) -> str:
    name = re.sub(r"[^A-Za-z0-9._-]", "_", f"{family}__{stem(path, base)}")
    if len(name) > 120:
        name = name[:100] + "-" + hashlib.sha256(source.encode()).hexdigest()[:8]
    return f"modules/{name}.trust_ir"


class Candidate:
    def __init__(self, repo: str, path: str, blob: str, source: str) -> None:
        self.repo = repo
        self.path = path
        self.blob = blob
        self.source = source
        self.status = "left"
        self.file = "-"
        self.reason = ""
        self.probe: Probe | None = None
        self.text = b""
        self.summary: dict[str, str] = {}


def default_probe_command() -> list[str]:
    slot = shutil.which("build-slot")
    if slot is None:
        home_slot = Path.home() / "trust" / "scripts" / "build-slot"
        if home_slot.is_file() and os.access(home_slot, os.X_OK):
            slot = str(home_slot)
    command = [slot, "--"] if slot else []
    command += [
        str(ROOT / "scripts" / "trust_cargo.sh"),
        "run",
        "--locked",
        "--offline",
        "--quiet",
        "-p",
        "trust-cg-eqsat",
        "--example",
        "eqsat_corpus_probe",
        "--",
    ]
    return command


def run_probe(command: list[str], probed: list[Candidate], blobs: dict[tuple[str, str], bytes]) -> None:
    """Probe every candidate in ``probed`` and record its verdict on it."""
    with tempfile.TemporaryDirectory(prefix="eqsat-corpus-probe-") as scratch:
        scratch_path = Path(scratch)
        inputs = scratch_path / "in"
        outputs = scratch_path / "out"
        inputs.mkdir()
        keys: dict[str, Candidate] = {}
        lines = []
        for index, candidate in enumerate(probed):
            key = f"c{index:05d}"
            keys[key] = candidate
            target = inputs / key
            target.write_bytes(blobs[(candidate.repo, candidate.blob)])
            lines.append(f"{key}\t{target}\n")
        listing = scratch_path / "list.tsv"
        listing.write_text("".join(lines), encoding="utf-8")
        result = subprocess.run(
            [*command, "--out", str(outputs), str(listing)],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            check=False,
        )
        if result.returncode != 0:
            raise GenerationError(f"the probe exited with status {result.returncode}")
        seen: set[str] = set()
        for line in result.stdout.decode("utf-8").splitlines():
            fields = line.split("\t")
            if fields[0] not in keys:
                continue
            key = fields[0]
            if key in seen:
                raise GenerationError(f"the probe reported {key} twice")
            seen.add(key)
            candidate = keys[key]
            if fields[1:2] == ["ok"] and len(fields) == 8:
                candidate.text = (outputs / f"{key}.trust_ir").read_bytes()
                if len(candidate.text) != int(fields[7]):
                    raise GenerationError(f"the probe's text for {key} has the wrong length")
                candidate.summary = dict(
                    zip(("format", "functions", "bodies", "instructions", "scalar_ops"), fields[2:7])
                )
            elif fields[1:2] == ["left"] and len(fields) == 3:
                candidate.reason = fields[2]
            else:
                raise GenerationError(f"unexpected probe line: {line!r}")
        missing = sorted(set(keys) - seen)
        if missing:
            raise GenerationError(f"the probe reported no verdict for {len(missing)} candidates")


def taken_reason(candidate: Candidate) -> str:
    assert candidate.probe is not None
    summary = candidate.summary
    read_from = "" if summary["format"] == "text" else f"read from {summary['format'].replace('-', ' ')}; "
    return (
        f"{candidate.probe.note}; {read_from}{summary['bodies']} bodies of "
        f"{summary['functions']} functions, {summary['instructions']} instructions "
        f"({summary['scalar_ops']} integer/bool scalar ops)"
    )


def generate(trust_ir_repo: Path, probe_command: list[str], destination: Path) -> None:
    rev = pinned_revision()
    try:
        git(["-C", str(trust_ir_repo), "cat-file", "-e", f"{rev}^{{commit}}"])
    except GenerationError as error:
        raise GenerationError(
            f"trust-ir revision {rev} is not in {trust_ir_repo}; "
            f"fetch it (git -C {trust_ir_repo} fetch origin {rev}) or pass --trust-ir-repo"
        ) from error
    trees = {"ir": ls_tree(trust_ir_repo, rev), "cg": ls_tree(ROOT, "HEAD")}
    repos = {"ir": trust_ir_repo, "cg": ROOT}
    prefix = {"ir": f"trust-ir@{rev[:12]}:", "cg": "trust-cg:"}

    candidates: list[Candidate] = []
    for repo in ("ir", "cg"):
        for path, blob in trees[repo].items():
            if not in_universe(repo, path):
                continue
            action = classify(repo, path)
            if action is None:
                continue
            candidate = Candidate(repo, path, blob, prefix[repo] + path)
            if isinstance(action, TwinOf):
                twin = None
                for suffix in STEM_SUFFIXES:
                    if path.endswith(suffix):
                        twin = path[: -len(suffix)] + action.suffix
                        break
                if twin is not None and twin != path and twin in trees[repo]:
                    action = Left(REASON_TWIN.format(twin=twin.rsplit("/", 1)[-1]))
                else:
                    action = action.fallback
            if isinstance(action, VendoredFrom):
                ir_path = action.ir_dir + path.rsplit("/", 1)[-1]
                if trees["ir"].get(ir_path) == blob:
                    action = Left(f"byte-identical copy of {prefix['ir']}{ir_path}")
                else:
                    action = Left(
                        "stale vendored copy of a trust-ir conformance golden (differs from the pin)"
                    )
            if isinstance(action, Left):
                candidate.reason = action.reason
            elif isinstance(action, Probe):
                candidate.probe = action
            else:
                raise GenerationError(f"no action for {candidate.source}")
            candidates.append(candidate)
    candidates.sort(key=lambda c: c.source)

    probed = [c for c in candidates if c.probe is not None]
    blobs: dict[tuple[str, str], bytes] = {}
    for repo in ("ir", "cg"):
        wanted = [c.blob for c in probed if c.repo == repo]
        for blob, data in cat_blobs(repos[repo], wanted).items():
            blobs[(repo, blob)] = data
    run_probe(probe_command, probed, blobs)

    # Preference order: family rank, then source. Duplicates and the size
    # budget are resolved in this order.
    probed.sort(key=lambda c: (c.probe.rank if c.probe else 0, c.source))
    first_with_text: dict[bytes, Candidate] = {}
    first_with_shape: dict[bytes, Candidate] = {}
    family_totals: dict[str, int] = {}
    total = 0
    names: dict[str, str] = {}
    for candidate in probed:
        probe = candidate.probe
        assert probe is not None
        if not candidate.summary:
            continue  # the probe left it; its reason is set
        if int(candidate.summary["bodies"]) == 0:
            candidate.reason = REASON_NO_BODY
            continue
        original = first_with_text.get(candidate.text)
        if original is not None:
            candidate.reason = f"duplicate of {original.source}"
            continue
        first_with_text[candidate.text] = candidate
        key = shape_key(candidate.text)
        original = first_with_shape.get(key)
        if original is not None:
            candidate.reason = (
                f"near-duplicate of {original.source} (same text up to Rust symbol and module names)"
            )
            continue
        first_with_shape[key] = candidate
        size = len(candidate.text)
        if size > PER_FILE_CAP:
            candidate.reason = f"oversize: {size} bytes of text (per-file cap {PER_FILE_CAP})"
            continue
        family_total = family_totals.get(probe.family, 0)
        if family_total + size > FAMILY_BUDGET:
            candidate.reason = f"family size budget ({probe.family}: {FAMILY_BUDGET} bytes of text) exhausted"
            continue
        if total + size > CORPUS_BUDGET:
            candidate.reason = f"corpus size budget ({CORPUS_BUDGET} bytes of text) exhausted"
            continue
        file = module_file(probe.family, candidate.path, probe.base, candidate.source)
        folded = unicodedata.normalize("NFC", file).casefold()
        if folded in names:
            raise GenerationError(f"module file {file} collides with {names[folded]}")
        names[folded] = file
        total += size
        family_totals[probe.family] = family_total + size
        candidate.status = "taken"
        candidate.file = file
        candidate.reason = taken_reason(candidate)

    rows = []
    for candidate in candidates:
        fields = (candidate.status, candidate.file, candidate.source, candidate.reason)
        for field in fields:
            if not field or any(ch in field for ch in "\t\r\n"):
                raise GenerationError(f"bad manifest field {field!r} for {candidate.source}")
        rows.append("\t".join(fields))
    taken = [c for c in candidates if c.status == "taken"]
    header = [
        "# trust-cg-eqsat e-graph corpus (docs/eqsat-tier-e.md section 9): one row per candidate"
        " module, taken or left out, with the reason. Generated; do not edit.",
        "# Generator: python3 -I scripts/eqsat_corpus.py [--trust-ir-repo PATH]; verify with --check.",
        f"# trust-ir pinned revision: {rev} (root Cargo.toml); trust-cg candidates are read at HEAD.",
        "# INTERIM: replace with the PKG-C0 ladder dump.",
        "# Taken: parses, validates (trust_ir_build::validate_module), prints back with"
        " trust_ir::format::text_checked and re-parses to an equal module, has a function body,"
        " is no duplicate or near-duplicate (same text up to the module name and Rust mangled"
        " symbols) and fits the size limits. Modules are trust-ir text.",
        f"# Size limits: {PER_FILE_CAP} bytes of text per module, {FAMILY_BUDGET} per family,"
        f" {CORPUS_BUDGET} in all;"
        " duplicates and the budget go by family rank (scripts/eqsat_corpus.py RULES), then source.",
        f"# Candidates: {len(candidates)}; taken {len(taken)} ({total} bytes of text);"
        f" left {len(candidates) - len(taken)}.",
        MANIFEST_HEADER,
    ]
    manifest = "\n".join(header + rows) + "\n"
    directory_bytes = total + len(manifest.encode("utf-8"))
    if directory_bytes >= DIRECTORY_LIMIT:
        raise GenerationError(
            f"the corpus would hold {directory_bytes} bytes (limit {DIRECTORY_LIMIT}); lower CORPUS_BUDGET"
        )

    modules = destination / "modules"
    if modules.exists():
        shutil.rmtree(modules)
    modules.mkdir(parents=True)
    for candidate in taken:
        (destination / candidate.file).write_bytes(candidate.text)
    (destination / "MANIFEST.tsv").write_text(manifest, encoding="utf-8")


def tree_files(directory: Path) -> dict[str, bytes]:
    files: dict[str, bytes] = {}
    if not directory.is_dir():
        return files
    for path in sorted(directory.rglob("*")):
        if path.is_file():
            files[path.relative_to(directory).as_posix()] = path.read_bytes()
    return files


def run(args: argparse.Namespace) -> int:
    probe_command = shlex.split(args.probe_cmd) if args.probe_cmd else default_probe_command()
    trust_ir_repo = args.trust_ir_repo.expanduser().resolve()
    if not args.check:
        CORPUS.mkdir(parents=True, exist_ok=True)
        generate(trust_ir_repo, probe_command, CORPUS)
        manifest = (CORPUS / "MANIFEST.tsv").read_text(encoding="utf-8")
        summary = [line for line in manifest.splitlines() if line.startswith("# Candidates:")]
        print(f"eqsat_corpus: wrote {CORPUS.relative_to(ROOT)} ({summary[0][2:] if summary else ''})")
        return 0
    with tempfile.TemporaryDirectory(prefix="eqsat-corpus-check-") as scratch:
        fresh = Path(scratch) / "corpus"
        fresh.mkdir()
        generate(trust_ir_repo, probe_command, fresh)
        expected = tree_files(fresh)
        actual = tree_files(CORPUS)
    differences = []
    for name in sorted(set(expected) | set(actual)):
        if name not in actual:
            differences.append(f"missing: {name}")
        elif name not in expected:
            differences.append(f"not generated: {name}")
        elif expected[name] != actual[name]:
            differences.append(f"differs: {name}")
    if differences:
        print(
            f"eqsat_corpus: {CORPUS.relative_to(ROOT)} is stale ({len(differences)} differences);"
            " regenerate with python3 -I scripts/eqsat_corpus.py",
            file=sys.stderr,
        )
        for line in differences[:40]:
            print(f"  {line}", file=sys.stderr)
        return 1
    print(f"eqsat_corpus: {CORPUS.relative_to(ROOT)} matches a fresh generation ({len(actual)} files)")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "--trust-ir-repo",
        type=Path,
        default=Path.home() / "trust-ir",
        help="a trust-ir git repository holding the pinned revision (default: $HOME/trust-ir)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="regenerate into a temporary directory and compare with the committed corpus",
    )
    parser.add_argument(
        "--probe-cmd",
        help="command that runs eqsat_corpus_probe (the script appends --out DIR LIST)",
    )
    args = parser.parse_args(argv)
    try:
        return run(args)
    except GenerationError as error:
        print(f"eqsat_corpus: {error}", file=sys.stderr)
        return 2
    except Exception as error:  # noqa: BLE001 - every other failure is exit 2, never 1
        detail = " ".join(str(error).split())
        print(f"eqsat_corpus: internal error: {type(error).__name__}: {detail}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
