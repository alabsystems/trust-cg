#!/usr/bin/env python3
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
"""Replay dumped x86 body-lane queries offline, one at a time, and record why
each one does or does not certify.

    python3 -I offline_replay.py --ay <ay> --clean <clean> [--clean-alt <clean>] \
        --budget-ms 300000 --out <tsv> <query.smt2>...

For each query (a `TCG_X86_BODY_QUALIFY_DUMP` file): its `(set-option :timeout
N)` is replaced by the budget, AY runs it as the lane's one-shot route does
(`ay -smt2 Q --strict-proofs --proof P --proof-format alethe`) under a wall
limit of the budget plus 30 s (SIGKILL past it), and an `unsat` with a proof is
wrapped as an `alethe_certificate` and checked by `clean cert verify-external
--verbose`, then by `--clean-alt` when given (a diagnostic second checker; it
never changes the recorded pair). Writes one TSV row per query.

The columns are `label ay_answer ay_wall_ms clean clean_alt ay_tail`. The
`ay_tail` column starts with the certificate fields AY printed anywhere in its
output (`unproved_steps=N trust_free=yes|no`, from its `c ay.proof.certificate`
line; `-` when it printed none), then ` | ` and AY's last two output lines.
Rows written before 2026-10-17 hold the last two lines alone, so they show
the fields only when the certificate line was one of them: AY's
`carcara_surface=clean-dialect` warning comes after it for a proof that uses
the `zero_extend` spelling, and then it was not.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
import time
from pathlib import Path

TIMEOUT_OPTION = re.compile(r"\(set-option :timeout \d+\)")
CERTIFICATE_FIELDS = ("unproved_steps", "trust_free")
CERTIFICATE_FIELD = re.compile(r"(?<![\w.])(" + "|".join(CERTIFICATE_FIELDS) + r")=(\S+)")


def last_lines(text: str, count: int = 3) -> str:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    return " | ".join(lines[-count:])


def certificate_fields(text: str) -> str:
    """Every `unproved_steps=` and `trust_free=` AY printed, in order, wherever
    it printed them: its certificate line need not be among the last lines."""
    found = [f"{key}={value}" for key, value in CERTIFICATE_FIELD.findall(text)]
    return " ".join(found) if found else "-"


def ay_answer(stdout: str) -> str:
    for line in stdout.splitlines():
        line = line.strip()
        if line in ("sat", "unsat", "unknown"):
            return line
    return "none"


def check(clean: str, cert: Path) -> str:
    result = subprocess.run(
        [clean, "cert", "verify-external", str(cert), "--verbose"],
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
    )
    text = result.stdout + "\n" + result.stderr
    lowered = [line.strip().lower() for line in text.splitlines()]
    if "proof status: fully verified" in lowered and "external certificate verification: passed" in lowered:
        return "fully verified"
    errors = [line.strip() for line in text.splitlines() if line.strip().startswith("Error:")]
    return errors[0] if errors else last_lines(text)


def replay(args: argparse.Namespace, query: Path, work: Path) -> list[str]:
    text = TIMEOUT_OPTION.sub(f"(set-option :timeout {args.budget_ms})", query.read_text())
    local = work / query.name
    local.write_text(text)
    proof = work / (query.stem + ".alethe")
    started = time.monotonic()
    try:
        result = subprocess.run(
            [args.ay, "-smt2", str(local), "--strict-proofs", "--proof", str(proof), "--proof-format", "alethe"],
            capture_output=True,
            text=True,
            timeout=args.budget_ms / 1000 + 30,
            check=False,
        )
        stdout, stderr, killed = result.stdout, result.stderr, False
    except subprocess.TimeoutExpired as expired:
        stdout = (expired.stdout or b"").decode(errors="replace") if isinstance(expired.stdout, bytes) else (expired.stdout or "")
        stderr = (expired.stderr or b"").decode(errors="replace") if isinstance(expired.stderr, bytes) else (expired.stderr or "")
        killed = True
    wall_ms = round((time.monotonic() - started) * 1000)
    answer = "killed-at-wall-limit" if killed else ay_answer(stdout)
    output = stdout + "\n" + stderr
    reason = f"{certificate_fields(output)} | {last_lines(output, 2)}"
    clean_verdict = alt_verdict = "-"
    if answer == "unsat" and proof.is_file() and proof.stat().st_size > 0:
        cert = work / (query.stem + ".cert.json")
        cert.write_text(
            json.dumps(
                {"type": "alethe_certificate", "version": "1.0", "problem": text, "proof": proof.read_text()}
            )
        )
        clean_verdict = check(args.clean, cert)
        if args.clean_alt:
            alt_verdict = check(args.clean_alt, cert)
    return [query.stem, answer, str(wall_ms), clean_verdict, alt_verdict, reason.replace("\t", " ")]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ay", required=True)
    parser.add_argument("--clean", required=True)
    parser.add_argument("--clean-alt")
    parser.add_argument("--budget-ms", type=int, default=300000)
    parser.add_argument("--out", required=True)
    parser.add_argument("queries", nargs="+", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="tcg-offline-replay-") as scratch, open(args.out, "w") as out:
        out.write("label\tay_answer\tay_wall_ms\tclean\tclean_alt\tay_tail\n")
        for query in args.queries:
            row = replay(args, query, Path(scratch))
            out.write("\t".join(row) + "\n")
            out.flush()
            print("\t".join(row[:5]), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
