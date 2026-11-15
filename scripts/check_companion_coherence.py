#!/usr/bin/env python3
"""Report whether the committed TrustIr, Clean and AY identities agree.

For each companion, the revision the root Cargo.lock pins (what a
root-workspace build compiles) must equal the one revision the companion
resolves to across every manifest, lockfile and compile-artifact cache identity
(the tree tuple, derived from the same files scripts/bump_trust_ir_pin.py
owns); a split, mutable or unpinned tree is reported as a disagreement.

The soundness gate derives its Clean and AY checkouts from these same Cargo
locks (scripts/soundness_check.sh candidate_dependency_rev) and records them in
each per-commit attestation; there is no separate hand-kept revision lock to
compare. Every disagreement is reported with each source's revision and
location. The gate's --attest preflight runs this check.

Agreement is bookkeeping. It does not show that a revision was audited, tested,
published or fetched, nor does it name installed executables. This check is not
part of scripts/check_documentation.py; SOUNDNESS_CHECK.md records its current
result.

Exit status: 0 when every present source agrees, 1 on any disagreement or
malformed source, 2 when a required file cannot be read.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
from typing import Optional, Sequence
from urllib.parse import urlsplit


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "trust-cg-companion-coherence-v1"
CARGO_LOCK = "Cargo.lock"
TREE = "tree (manifests, lockfiles, cache identities)"
FULL_REVISION = re.compile(r"[0-9a-f]{40}\Z")


def sibling(name: str):
    path = Path(__file__).resolve().parent / f"{name}.py"
    spec = importlib.util.spec_from_file_location(f"_companion_coherence_{name}", path)
    if spec is None or spec.loader is None:
        raise ImportError(f"required helper is missing: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


DEPS = sibling("dependency_identity")
# These mirror scripts/bump_trust_ir_pin.py's MANIFESTS, REGALLOC, LOCKS and
# CACHE; scripts/tests/test_companion_coherence.py pins the agreement.
MANIFESTS = ("Cargo.toml", "crates/rustc-codegen-trust-cg/Cargo.toml")
REGALLOC = "crates/trust-cg-regalloc/Cargo.toml"
LOCKS = (
    "Cargo.lock",
    "crates/rustc-codegen-trust-cg/Cargo.lock",
    "fuzz/Cargo.lock",
)
# The cargo-fuzz package resolves no AY package; if it ever does, it must agree.
AY_LOCKS = LOCKS[:2]
CACHE = "crates/trust-cg-codegen/src/compile_artifact_cache_profile.rs"
LABELS = ("TrustIr", "Clean", "AY")
REPOSITORIES = {"TrustIr": "trust-ir", "Clean": "clean", "AY": "ay"}
CACHE_CONSTANTS = {
    "TrustIr": ("COMPILE_ARTIFACT_DEFAULT_TRUST_IR_IDENTITY", "trust_ir"),
    "AY": ("COMPILE_ARTIFACT_DEFAULT_AY_IDENTITY", "ay"),
}
EXACT_SHA = re.compile(r"[0-9a-f]{40}\Z")
LOCK_SOURCE = re.compile(
    r'^source = "git\+https://github\.com/[^/"]+/(trust-ir|clean|ay)\.git([^"]*)"$',
    re.MULTILINE,
)


def manifest_pins(relative: str, text: str, repository: str) -> tuple[list[str], list[str]]:
    """Return (revisions, errors) for single-line `git = ...` dependencies."""
    dependency = re.compile(
        r'\bgit\s*=\s*"https://github\.com/[^/"]+/' + re.escape(repository) + r'\.git"'
    )
    revisions, errors = [], []
    for number, line in enumerate(text.splitlines(), 1):
        if line.lstrip().startswith("#") or not dependency.search(line):
            continue
        where = f"{relative}:{number}"
        if re.search(r'\b(branch|tag|path)\s*=', line):
            errors.append(f"{where}: {repository} dependency uses a mutable or local selector")
            continue
        match = re.search(r'\brev\s*=\s*"([^"]*)"', line)
        if match is None or EXACT_SHA.match(match[1]) is None:
            errors.append(f"{where}: {repository} dependency lacks an exact 40-hex rev")
            continue
        revisions.append(match[1])
    if not revisions and not errors:
        errors.append(f"{relative}: no pinned {repository} dependency")
    return revisions, errors


def tree_tuple(root: Path) -> tuple[dict[str, str], list[str]]:
    """Derive the single TrustIr/Clean/AY revision each companion resolves to."""
    found: dict[str, list[tuple[str, str]]] = {label: [] for label in LABELS}
    errors: list[str] = []

    for relative, label in [(name, "TrustIr") for name in MANIFESTS] + [(REGALLOC, "AY")]:
        revisions, problems = manifest_pins(relative, (root / relative).read_text(), REPOSITORIES[label])
        errors.extend(problems)
        found[label].extend((relative, revision) for revision in revisions)

    cache = (root / CACHE).read_text()
    for label, (constant, prefix) in CACHE_CONSTANTS.items():
        matches = re.findall(
            r"pub const " + constant + r': &str =\s*"' + prefix + r':([^"]*)";', cache
        )
        if len(matches) != 1 or EXACT_SHA.match(matches[0]) is None:
            errors.append(f"{CACHE}: {constant} must be defined once with an exact 40-hex identity")
        else:
            found[label].append((CACHE, matches[0]))

    for relative in LOCKS:
        seen = {label: 0 for label in LABELS}
        for repository, suffix in LOCK_SOURCE.findall((root / relative).read_text()):
            label = next(name for name, repo in REPOSITORIES.items() if repo == repository)
            match = re.fullmatch(r"\?rev=([0-9a-f]{40})#([0-9a-f]{40})", suffix)
            if match is None or match[1] != match[2]:
                errors.append(f"{relative}: {repository} source is not an exact rev#rev identity: {suffix}")
                continue
            seen[label] += 1
            found[label].append((relative, match[1]))
        required = ("TrustIr", "Clean") + (("AY",) if relative in AY_LOCKS else ())
        for label in required:
            if seen[label] == 0:
                errors.append(f"{relative}: resolves no {REPOSITORIES[label]} package")

    resolved: dict[str, str] = {}
    for label in LABELS:
        revisions = sorted({revision for _, revision in found[label]})
        if len(revisions) == 1:
            resolved[label] = revisions[0]
        elif revisions:
            places = ", ".join(
                f"{revision[:8]} in {', '.join(sorted({where for where, rev in found[label] if rev == revision}))}"
                for revision in revisions
            )
            errors.append(f"tree resolves split {label} revisions: {places}")
        else:
            errors.append(f"tree resolves no {label} revision")
    return resolved, errors




def cargo_lock_revisions(text: str) -> tuple[dict[str, list[tuple[str, int]]], list[str]]:
    """(revision, line) of every companion Git source in the root lock."""
    sources, errors = DEPS.parse_lock_git_sources(text, CARGO_LOCK)
    found: dict[str, list[tuple[str, int]]] = {label: [] for label in LABELS}
    for source in sources:
        try:
            name = urlsplit(DEPS.canonical_url(source["url"])).path.rsplit("/", 1)[-1]
        except ValueError as error:
            errors.append(f"{CARGO_LOCK}:{source['lock_line']}: {error}")
            continue
        for label, repository in REPOSITORIES.items():
            if name == repository:
                found[label].append((source["revision"], source["lock_line"]))
    return found, errors


def coherence(root: Path) -> dict:
    """Compare every companion's revision across the committed records."""
    report: dict = {
        "schema": SCHEMA,
        "scope": "committed identity agreement only; not audit, test, publication or executable identity",
        "companions": {}, "context": {}, "disagreements": [], "errors": [],
    }
    lock_text = (root / CARGO_LOCK).read_text(encoding="utf-8")
    cargo, errors = cargo_lock_revisions(lock_text)
    report["errors"].extend(errors)
    tree, tree_errors = tree_tuple(root)
    report["disagreements"].extend(f"{TREE}: {error}" for error in tree_errors)

    for label in LABELS:
        sources: dict[str, Optional[dict]] = {}
        pins = cargo[label]
        revisions = sorted({revision for revision, _ in pins})
        if not pins:
            report["errors"].append(f"{label}: {CARGO_LOCK} pins no {REPOSITORIES[label]} source")
            reference = None
        else:
            if len(revisions) > 1:
                report["disagreements"].append(
                    f"{label}: {CARGO_LOCK} pins {len(revisions)} revisions: "
                    + ", ".join(f"{revision} at {CARGO_LOCK}:{line}" for revision, line in pins)
                )
            reference = {"revision": pins[0][0], "where": f"{CARGO_LOCK}:{pins[0][1]}"}
        sources[CARGO_LOCK] = reference
        sources[TREE] = {"revision": tree[label], "where": TREE} if label in tree else None
        disagreeing = []
        if reference is not None:
            for name, value in sources.items():
                if name != CARGO_LOCK and value is not None and value["revision"] != reference["revision"]:
                    disagreeing.append(name)
                    report["disagreements"].append(
                        f"{label}: {value['where']} names {value['revision']}, "
                        f"but {reference['where']} pins {reference['revision']}"
                    )
        report["companions"][label] = {
            "repository": REPOSITORIES[label], "sources": sources,
            "not_applicable": [],
            "disagreeing_sources": disagreeing,
        }
    report["status"] = "coherent" if not report["disagreements"] and not report["errors"] else "incoherent"
    return report


def text_lines(report: dict) -> list[str]:
    lines = []
    for label, companion in report["companions"].items():
        lines.append(f"{label} ({companion['repository']}):")
        for name, value in companion["sources"].items():
            if value is None:
                continue
            verdict = "DISAGREES" if name in companion["disagreeing_sources"] else "reference" if name == CARGO_LOCK else "agrees"
            lines.append(f"  {value['where']}: {value['revision']} {verdict}")
        lines.extend(f"  {name}: not applicable" for name in companion["not_applicable"])
    lines.extend(f"DISAGREEMENT: {item}" for item in report["disagreements"])
    lines.extend(f"ERROR: {item}" for item in report["errors"])
    lines.append(f"companion identities: {report['status'].upper()}")
    return lines


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0], allow_abbrev=False)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root (default: this checkout)")
    parser.add_argument("--json", action="store_true", help="print the comparison as JSON")
    args = parser.parse_args(argv)
    try:
        report = coherence(args.root)
    except (OSError, UnicodeError) as error:
        print(f"companion coherence check failed: {error}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2) if args.json else "\n".join(text_lines(report)))
    return 0 if report["status"] == "coherent" else 1


if __name__ == "__main__":
    raise SystemExit(main())
