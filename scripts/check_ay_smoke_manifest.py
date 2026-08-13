#!/usr/bin/env python3
"""Validate the exact ay smoke obligation manifest against ProofDatabase."""

from __future__ import annotations

import argparse
import csv
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


REPO = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO / "ratchet/ay_smoke_obligation_manifest.json"
INVENTORY_EXAMPLE = "proof_database_inventory"
REQUIRED_F16_OBLIGATION = "Fdemote_F16_F32 -> FCVT Hd,Sn"
REQUIRED_F16_HOOK = "ay_prove_fp_convert_fcvt_f16_f32"
REQUIRED_F16_LABEL = "fp_convert_fcvt_f16_f32"
VALID_VERIFICATIONS = {"strict_verified", "verified_or_timeout"}


@dataclass(frozen=True)
class InventoryEntry:
    categories: frozenset[str]


class ManifestError(Exception):
    pass


def run_inventory() -> str:
    env = os.environ.copy()
    env.setdefault("CARGO_INCREMENTAL", "0")
    proc = subprocess.run(
        [
            "cargo",
            "run",
            "-p",
            "trust-cg-verify",
            "--example",
            INVENTORY_EXAMPLE,
            "--quiet",
            "--",
            "--format",
            "tsv",
        ],
        cwd=REPO,
        env=env,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.stderr:
        print(proc.stderr, file=sys.stderr, end="")
    if proc.returncode != 0:
        raise ManifestError(f"ProofDatabase inventory command failed with exit {proc.returncode}")
    return proc.stdout


def load_inventory(inventory_tsv: Path | None) -> dict[str, InventoryEntry]:
    text = inventory_tsv.read_text() if inventory_tsv is not None else run_inventory()
    reader = csv.DictReader(text.splitlines(), delimiter="\t")
    required_columns = {"category", "name"}
    if reader.fieldnames is None or not required_columns.issubset(reader.fieldnames):
        raise ManifestError("inventory TSV must include category and name columns")

    categories_by_name: dict[str, set[str]] = {}
    for row in reader:
        name = row["name"]
        categories_by_name.setdefault(name, set()).add(row["category"])
    return {
        name: InventoryEntry(categories=frozenset(categories))
        for name, categories in categories_by_name.items()
    }


def require_string(entry: dict[str, Any], field: str, index: int) -> str:
    value = entry.get(field)
    if not isinstance(value, str) or not value:
        raise ManifestError(f"entries[{index}].{field} must be a nonempty string")
    return value


def load_manifest(path: Path) -> list[dict[str, Any]]:
    try:
        manifest = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise ManifestError(f"{path}: invalid JSON: {exc}") from exc

    if not isinstance(manifest, dict):
        raise ManifestError("manifest root must be an object")
    if manifest.get("schema") != "trust-cg.ay_smoke_obligation_manifest.v1":
        raise ManifestError("manifest schema must be trust-cg.ay_smoke_obligation_manifest.v1")
    entries = manifest.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ManifestError("manifest entries must be a nonempty list")
    if not all(isinstance(entry, dict) for entry in entries):
        raise ManifestError("manifest entries must be objects")
    return entries


def validate_manifest(manifest_path: Path, inventory_tsv: Path | None) -> tuple[int, int]:
    inventory = load_inventory(inventory_tsv)
    entries = load_manifest(manifest_path)

    seen: set[str] = set()
    strict = 0
    tolerant = 0
    required_f16_entry: dict[str, Any] | None = None

    for index, entry in enumerate(entries):
        name = require_string(entry, "obligation_name", index)
        category = require_string(entry, "category", index)
        verification = require_string(entry, "verification", index)
        require_string(entry, "source", index)
        require_string(entry, "smoke_hook", index)
        require_string(entry, "smoke_label", index)

        if verification not in VALID_VERIFICATIONS:
            raise ManifestError(
                f"entries[{index}].verification must be one of {sorted(VALID_VERIFICATIONS)}"
            )
        if verification == "strict_verified":
            strict += 1
        else:
            tolerant += 1

        if name in seen:
            raise ManifestError(f"duplicate manifest obligation: {name}")
        seen.add(name)

        inventory_entry = inventory.get(name)
        if inventory_entry is None:
            raise ManifestError(f"manifest obligation is not in ProofDatabase::new(): {name}")
        if category not in inventory_entry.categories:
            raise ManifestError(
                f"manifest category mismatch for {name}: "
                f"manifest={category!r} inventory={sorted(inventory_entry.categories)!r}"
            )

        if name == REQUIRED_F16_OBLIGATION:
            required_f16_entry = entry

    if required_f16_entry is None:
        raise ManifestError(
            f"missing required typed F16 smoke obligation: {REQUIRED_F16_OBLIGATION}"
        )
    if required_f16_entry.get("smoke_hook") != REQUIRED_F16_HOOK:
        raise ManifestError(
            f"{REQUIRED_F16_OBLIGATION}: smoke_hook must be {REQUIRED_F16_HOOK}"
        )
    if required_f16_entry.get("smoke_label") != REQUIRED_F16_LABEL:
        raise ManifestError(
            f"{REQUIRED_F16_OBLIGATION}: smoke_label must be {REQUIRED_F16_LABEL}"
        )
    if required_f16_entry.get("verification") != "strict_verified":
        raise ManifestError(f"{REQUIRED_F16_OBLIGATION}: verification must be strict_verified")

    return strict, tolerant


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate the exact ay smoke obligation manifest."
    )
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--inventory-tsv", type=Path, help="use a precomputed inventory TSV")
    args = parser.parse_args()

    try:
        strict, tolerant = validate_manifest(args.manifest, args.inventory_tsv)
    except ManifestError as exc:
        print(f"ay smoke manifest: ERROR: {exc}", file=sys.stderr)
        return 1

    print(
        "ay smoke manifest: ok "
        f"manifest={args.manifest} strict_verified={strict} "
        f"verified_or_timeout={tolerant}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
