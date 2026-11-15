#!/usr/bin/env python3
"""Export the real-builder x86 qualification diagnostic into a new private directory.

Capture the existing print_slice_ten_fixtures test with --ignored --exact
--nocapture and TCG_X86_BODY_QUALIFICATION_MATRIX=1. This utility requires its
complete JSON-line stream, checks canonical bytes against all declared source snapshots,
and preserves alternative spellings verbatim. It runs no solver or checker and
grants no proof credit. The caller must separately authenticate the capture's
producer; supplying --verifier records bytes, not an attestation of execution.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

from export_x86_body_queries import FAMILIES, FIXTURES, ROOT, snapshot_queries


PREFIX = "X86_BODY_MATRIX\t"
FORMAT = "trust-cg-x86-body-qualification-matrix-v1"
CLASSES = {"canonical", "machine-variant", "encoding", "wrong-lowering"}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_capture(data: bytes) -> tuple[dict, list[dict]]:
    payloads = [line[len(PREFIX):] for line in data.decode("utf-8").splitlines()
                if line.startswith(PREFIX)]
    if len(payloads) < 3:
        raise ValueError("missing complete matrix stream")
    header, *records, footer = [json.loads(text) for text in payloads]
    if (header.get("kind") != "header" or header.get("format") != FORMAT
            or header.get("proof_credit") is not False):
        raise ValueError("invalid diagnostic header")
    source_hash = header.get("verifier_source_sha256", "")
    if len(source_hash) != 64 or any(c not in "0123456789abcdef" for c in source_hash):
        raise ValueError("invalid verifier source digest")
    if footer.get("kind") != "footer" or footer.get("records") != len(records):
        raise ValueError("missing or inconsistent completion footer")
    if footer.get("records_sha256") != digest(("\n".join(payloads[1:-1]) + "\n").encode()):
        raise ValueError("matrix record digest mismatch")
    keys = set()
    for index, record in enumerate(records):
        family, label, cls = record.get("family"), record.get("label"), record.get("class")
        kind = record.get("kind")
        if (record.get("sequence") != index or family not in FAMILIES
                or not isinstance(label, str) or not label or cls not in CLASSES
                or kind not in {"query", "refusal"}):
            raise ValueError(f"invalid matrix record {index}")
        key = (family, cls, label)
        if key in keys:
            raise ValueError(f"duplicate matrix record {key}")
        keys.add(key)
        if record.get("source_bound") is not (cls in {"canonical", "machine-variant"}):
            raise ValueError(f"incorrect source-bound diagnostic tag: {key}")
        if kind == "query":
            query = record.get("smt2")
            expected = "sat" if cls == "wrong-lowering" else "unsat"
            if (record.get("expected") != expected or not isinstance(query, str)
                    or not query.startswith("(set-option :timeout ")
                    or not query.rstrip("\n").endswith("(check-sat)\n(exit)")):
                raise ValueError(f"incomplete or mistagged query: {key}")
        elif cls != "encoding" or not isinstance(record.get("reason"), str) or not record["reason"]:
            raise ValueError(f"invalid encoding refusal: {key}")
    for kind, count_key in (("query", "queries"), ("refusal", "refusals")):
        if footer.get(count_key) != sum(record["kind"] == kind for record in records):
            raise ValueError(f"inconsistent {count_key} count")
    return header, records


def bind_snapshots(records: list[dict]) -> list[dict]:
    snapshots = []
    for family, filename in FAMILIES.items():
        source = FIXTURES / filename
        data = source.read_bytes()
        expected = dict(snapshot_queries(data, filename))
        actual = {record["label"]: record["smt2"].encode()
                  for record in records if record["family"] == family
                  and record["class"] == "canonical" and record["kind"] == "query"}
        if actual != expected:
            raise ValueError(f"{family}: canonical matrix differs from source snapshots")
        if not any(record["family"] == family and record["class"] == "wrong-lowering"
                   and record["kind"] == "query" for record in records):
            raise ValueError(f"{family}: missing actual wrong-lowering controls")
        snapshots.append({"family": family, "source": str(source.relative_to(ROOT)),
                          "source_sha256": digest(data), "queries": len(expected)})
    return snapshots


def export(out: Path, capture: Path, verifier: Path) -> dict:
    data = capture.read_bytes()
    header, records = read_capture(data)
    snapshots = bind_snapshots(records)
    verifier_hash = digest(verifier.read_bytes())
    queries, refusals, rendered = [], [], []
    for record in records:
        record = record.copy()
        if record["kind"] == "refusal":
            refusals.append(record)
            continue
        query = record.pop("smt2").encode()
        filename = f"{record['family']}--{record['class']}--{record['sequence']:04}.smt2"
        rendered.append((filename, query))
        record.update(file=filename, query_sha256=digest(query))
        queries.append(record)
    manifest = {
        "format": FORMAT, "proof_credit": False,
        "authority": "unverified diagnostic capture; producer execution must be authenticated separately",
        "capture_sha256": digest(data), "verifier_sha256": verifier_hash,
        "verifier_source_sha256": header["verifier_source_sha256"],
        "snapshots": snapshots, "queries": queries, "refusals": refusals,
    }
    out.mkdir(mode=0o700)
    try:
        for filename, query in rendered:
            (out / filename).write_bytes(query)
        (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    except BaseException:
        shutil.rmtree(out)
        raise
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="complete captured diagnostic stdout")
    parser.add_argument("--verifier", type=Path, required=True, help="test executable recorded by the caller")
    parser.add_argument("--out", type=Path, required=True, help="new output directory outside the repository")
    args = parser.parse_args()
    out = args.out.absolute()
    if out.resolve().is_relative_to(ROOT.resolve()):
        parser.error("--out must be outside the repository")
    try:
        manifest = export(out, args.input, args.verifier)
    except (OSError, UnicodeError, ValueError, TypeError, AttributeError) as error:
        print(f"export_x86_qualification_matrix: refused: {error}", file=sys.stderr)
        return 2
    print(f"exported {len(manifest['queries'])} queries and {len(manifest['refusals'])} encoding refusals to {out}; no proof credit")
    return 0


if __name__ == "__main__":
    sys.exit(main())
