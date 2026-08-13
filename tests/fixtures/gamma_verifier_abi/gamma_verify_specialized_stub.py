#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Standalone fixture wrapper for the gamma verifier ABI."""

import argparse
import json
import sys
from pathlib import Path


def read_json(path: str) -> dict:
    return json.loads(Path(path).read_text())


def check_compatibility(manifest: dict, query: dict) -> tuple[str, list[str]]:
    identity = manifest["identity_inputs"]
    contract = identity["contract"]
    mismatches = []

    comparisons = [
        ("artifact_id", manifest["artifact_id"], query["artifact_id"]),
        (
            "identity_inputs.model.model_sha256",
            identity["model"]["model_sha256"],
            query["model_sha256"],
        ),
        (
            "identity_inputs.gamma_crown.crown_relaxation_spec_sha256",
            identity["gamma_crown"]["crown_relaxation_spec_sha256"],
            query["spec_sha256"],
        ),
        (
            "identity_inputs.contract.accepted_vnnlib_query_family",
            contract["accepted_vnnlib_query_family"],
            query["vnnlib_query_family"],
        ),
        (
            "identity_inputs.contract.query_adapter_abi",
            contract["query_adapter_abi"],
            query["query_adapter_abi"],
        ),
        (
            "identity_inputs.contract.output_abi",
            contract["output_abi"],
            query["output_abi"],
        ),
        (
            "identity_inputs.contract.certificate_format",
            contract["certificate_format"],
            query["certificate_format"],
        ),
        (
            "identity_inputs.contract.runtime_abi",
            contract["runtime_abi"],
            query["runtime_abi"],
        ),
    ]

    for field, expected, actual in comparisons:
        if expected != actual:
            mismatches.append(field)

    if not mismatches:
        return "unknown", []
    if "identity_inputs.model.model_sha256" in mismatches:
        return "artifact_mismatch", mismatches
    if "identity_inputs.gamma_crown.crown_relaxation_spec_sha256" in mismatches:
        return "spec_mismatch", mismatches
    if "identity_inputs.contract.runtime_abi" in mismatches:
        return "unsupported_abi", mismatches
    return "query_mismatch", mismatches


def result_for(manifest: dict, query: dict) -> dict:
    status, mismatches = check_compatibility(manifest, query)
    result = {
        "status": status,
        "artifact_id": manifest["artifact_id"],
        "timing_ns": {
            "parse": 1000,
            "compatibility": 2000,
            "verify": 0 if mismatches else 3000,
            "total": 3000 if mismatches else 6000,
        },
        "certificate": None,
        "checker": {
            "checker_id": "gamma-crown-checker-v1",
            "checker_abi": "gamma-checker-abi-v1",
        },
    }
    if mismatches:
        result["mismatch"] = {"field_paths": mismatches}
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--query-blob", required=True)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    result = result_for(read_json(args.manifest), read_json(args.query_blob))
    print(json.dumps(result, sort_keys=True))
    if result["status"] == "unknown":
        return 2
    if result["status"].endswith("mismatch") or result["status"] == "unsupported_abi":
        return 4
    return 5


if __name__ == "__main__":
    sys.exit(main())
