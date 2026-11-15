#!/usr/bin/env python3
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
"""Recognize a normal, explicit ABI refusal; never turn tool failures into one.

This classifies diagnostic records only, not backend correctness or proof
authority. The runner requests trustc JSON diagnostics and retains the bytes.
"""

import json
from pathlib import Path
import re
import sys

MAX_BYTES = 1024 * 1024
ABI_TAG = re.compile(r"\[TCG-(?:ARG|RET)-ABI\]")
ANY_TAG = re.compile(r"\[TCG-[A-Z0-9-]+\]")
FOOTER = re.compile(r"aborting due to (\d+) previous errors?(?:; \d+ warnings? emitted)?")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate diagnostic field")
        result[key] = value
    return result


def is_abi_refusal(status, data):
    if status != 1 or not data or len(data) > MAX_BYTES:
        return False
    try:
        records = [json.loads(line, object_pairs_hook=unique_object)
                   for line in data.decode("utf-8").splitlines()]
        errors = 0
        footer = None
        for record in records:
            if not isinstance(record, dict) or record.get("$message_type") != "diagnostic":
                return False
            message = record.get("message")
            level = record.get("level")
            if not isinstance(message, str) or level not in {"error", "warning", "note", "help"}:
                return False
            # An error hidden in a child must not be dismissed as context.
            pending = list(record.get("children", []))
            while pending:
                child = pending.pop()
                if not isinstance(child, dict) or child.get("level") not in {"warning", "note", "help"}:
                    return False
                pending.extend(child.get("children", []))
            if level != "error":
                continue
            if footer is not None:
                return False
            summary = FOOTER.fullmatch(message)
            if summary is not None:
                footer = int(summary[1])
                continue
            tags = ANY_TAG.findall(message)
            if not tags or any(ABI_TAG.fullmatch(tag) is None for tag in tags):
                return False
            if record.get("code") is not None:
                return False
            errors += 1
        return errors > 0 and (footer is None or footer == errors)
    except (ValueError, TypeError, RecursionError):
        return False


def main():
    if len(sys.argv) != 3:
        return 2
    try:
        status = int(sys.argv[1])
        with Path(sys.argv[2]).open("rb") as stream:
            data = stream.read(MAX_BYTES + 1)
    except (ValueError, OSError):
        return 2
    return 0 if is_abi_refusal(status, data) else 1


if __name__ == "__main__":
    raise SystemExit(main())
