"""Shared corpus admission for benchmark and compile-completeness runs.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.
"""

import json


class CorpusError(ValueError):
    """The corpus cannot supply a nonempty, complete program denominator."""


def _unique_object(pairs):
    """Refuse ambiguous JSON instead of silently retaining the final value."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise CorpusError(f"corpus manifest has duplicate object key: {key!r}")
        result[key] = value
    return result


def load_programs(directory):
    """Read a nonempty program map whose names match every Rust source file.

    A subset run still validates the full corpus before choosing its subset.
    """
    manifest_path = directory / "manifest.json"
    try:
        with manifest_path.open() as manifest_file:
            document = json.load(manifest_file, object_pairs_hook=_unique_object)
    except (OSError, UnicodeError, json.JSONDecodeError, RecursionError) as error:
        raise CorpusError(f"corpus manifest unreadable: {manifest_path}: {error}") from error
    programs = document.get("programs") if isinstance(document, dict) else None
    if not isinstance(programs, dict) or not programs:
        raise CorpusError(f"corpus manifest requires a nonempty programs object: {manifest_path}")
    invalid_rows = sorted(name for name, row in programs.items() if not isinstance(row, dict))
    if invalid_rows:
        raise CorpusError(f"corpus program metadata must be an object: {invalid_rows}")
    on_disk = {path.stem for path in directory.glob("*.rs") if path.is_file()}
    missing_rows = on_disk - set(programs)
    missing_files = set(programs) - on_disk
    if missing_rows or missing_files:
        raise CorpusError(
            f"corpus/manifest drift: .rs without manifest row: {sorted(missing_rows)}; "
            f"manifest row without .rs: {sorted(missing_files)} (update {manifest_path})")
    return programs
