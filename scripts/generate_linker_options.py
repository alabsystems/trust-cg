#!/usr/bin/env python3
"""Generate, from native measurement, the link driver's table of how the
Linux AArch64 host's three linkers read an option spelled in a `-Wl`
piece: whether the piece after it is the option's value or a linker input.

The link driver skips the piece after an option (reads it as that option's
value, not as a possible linker-script input) only when every linker that
accepts the spelling was measured to take it as the value
(`link_driver::option_operand`). The table is measured, not parsed:

1. Candidates. Each linker's `--help` (GNU ld 2.42's `ld.bfd`, gold 2.42's
   `ld.gold`, LLD 22's `ld.lld`) is read, column-aware, for option names
   only. Every name any of the three lists is a candidate with one dash and
   with two; so is every prefix of a GNU ld long name (getopt_long_only
   abbreviations). The same candidates are measured against all three
   linkers, so a spelling one linker's help does not list is measured too.
2. Sweep. Each linker links a small object with `OPTION marker.ld`, where
   `marker.ld` is `INPUT(tcg-marker-input-7f3a.o)`: a linker that reads it
   as an input fails to find that file and says so. The spelling is
   - `NotNext` when it did (the piece after it is read as an input, or
     as a script, which is as conservative);
   - `Next` when the link succeeded without reading it;
   - rejected (left out) when the linker reports the spelling itself as
     unrecognized, unknown or ambiguous;
   - otherwise (the link failed without reading it) `Next` when the
     spelling alone, as the last argument, fails and the linker reports
     that the option wants a value (`<spelling>: missing argument`, or GNU
     ld's report of a trailing short option as unrecognized), and
     `Unsettled` when it fails for another reason (GNU ld's `-)` without a
     `-(`) or links. `Next` is thus always positive evidence: the linker
     took the piece and linked, or said the option wants one.
3. Controls (`--gc-sections`, `-e`, `-T`, `--version-script`, `-l` and an
   unknown option) must read as expected on each linker, or nothing is
   written.

The table records each linker's version (the first line of `--version`)
and the SHA-256 of each `--help`. The driver asks the link's linker for its
version (`<driver> -Wl,--version`) where the table decides a link, which is
only where it reads a script-like piece as an option's value: any other
reading refuses the piece or reads it as an input whatever the linker. A
linker that is not one of these three versions is refused there
(`link_driver::option_table_applies`). The gate
`scripts/tests/test_generate_linker_options.py` runs `--check` and
`--check --sweep` wherever the three linkers are installed.

Usage: generate_linker_options.py --write | --check [--sweep]. `--check`
compares the recorded versions and help hashes with the installed linkers
(fast); `--check --sweep` measures again and compares the whole table.
LLD is found as the native tests find it: `TCG_LLD_DIR`, `~/.local/bin`,
or `PATH`.
"""
import argparse
import concurrent.futures
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "crates/trust-cg-codegen/src/link_driver/linker_options.rs"
MARKER_INPUT = "tcg-marker-input-7f3a.o"
MARKER_READ = re.compile(r"(cannot|unable to) (find|open) " + re.escape(MARKER_INPUT))
# An option name as a help line spells it.
NAME = re.compile(r"^-{1,2}(?:\[no-\])?([A-Za-z0-9_()][^\s=\[<,]*)")


def find_lld():
    candidates = []
    if os.environ.get("TCG_LLD_DIR"):
        candidates.append(Path(os.environ["TCG_LLD_DIR"]) / "ld.lld")
    candidates.append(Path.home() / ".local/bin/ld.lld")
    found = shutil.which("ld.lld")
    if found:
        candidates.append(Path(found))
    for candidate in candidates:
        if candidate.is_file():
            return str(candidate)
    return None


def linkers():
    """The three linkers, `(table name, executable)`, or None when one is
    missing."""
    bfd = shutil.which("ld.bfd")
    gold = shutil.which("ld.gold")
    lld = find_lld()
    if not (bfd and gold and lld):
        return None
    return [("GNU_LD", bfd), ("GOLD", gold), ("LLD", lld)]


def output(command):
    return subprocess.run(command, capture_output=True, text=True, errors="replace").stdout


def description_column(lines):
    """The column most help lines start their description at."""
    columns = {}
    for line in lines:
        match = re.match(r"^(  -\S.*?)(\s{2,})\S", line)
        if match:
            column = len(match.group(1)) + len(match.group(2))
            columns[column] = columns.get(column, 0) + 1
    return max(columns, key=columns.get) if columns else 30


def help_names(text):
    """Every option name a `--help` lists: the spellings before the
    description, which starts after two spaces or at the description
    column (one space when a spelling fills the column)."""
    lines = text.splitlines()
    column = description_column(lines)
    names = set()
    for line in lines:
        if not line.startswith("  -"):
            continue
        spec = re.split(r"\s{2,}", line.strip())[0]
        if len(line) > column and line[column - 1] == " " and line[column] != " ":
            spec = min(spec, line[:column].strip(), key=len)
        for spelling in (part.strip() for part in spec.split(",")):
            match = NAME.match(spelling)
            if not match:
                continue
            name = match.group(1)
            names.add(name)
            if spelling.startswith(("--[no-]", "-[no-]")):
                names.add("no-" + name)
    return names


def candidates(helps):
    names = set()
    for text in helps.values():
        names |= help_names(text)
    spellings = set()
    for name in names:
        spellings.add("-" + name)
        spellings.add("--" + name)
    for name in help_names(helps["GNU_LD"]):
        if len(name) < 2:
            continue
        for length in range(1, len(name)):
            spellings.add("-" + name[:length])
            spellings.add("--" + name[:length])
    return sorted(spellings), sorted(names)


def rejected(stderr, spelling):
    short = spelling[1:2] if not spelling.startswith("--") else None
    patterns = [
        f"unrecognized option '{spelling}'",
        f"option '{spelling}' is ambiguous",
        f"{spelling}: unknown option",
        f"unknown argument '{spelling}'",
    ]
    if short:
        patterns.append(f"invalid option -- '{short}'")
    return any(pattern in stderr for pattern in patterns)


def run(linker, arguments, workdir):
    (workdir / "marker.ld").write_text(f"INPUT({MARKER_INPUT})\n")
    out = workdir / "out"
    if out.exists() or out.is_symlink():
        out.unlink()
    try:
        result = subprocess.run(
            [linker, "-o", "out", "base.o", *arguments],
            cwd=workdir,
            capture_output=True,
            text=True,
            errors="replace",
            timeout=30,
            stdin=subprocess.DEVNULL,
        )
    except subprocess.TimeoutExpired:
        return None, ""
    return result.returncode, result.stderr


def wants_value(table, stderr, spelling):
    """Whether `stderr`, of a link whose last argument is `spelling` (a
    spelling the linker accepts with a piece after it), reports that the
    option wants a value. GNU ld's getopt_long_only reports a trailing short
    option that wants one as unrecognized."""
    patterns = [f"{spelling}: missing argument", "option requires an argument"]
    if table == "GNU_LD":
        patterns.append(f"unrecognized option '{spelling}'")
    return any(pattern in stderr for pattern in patterns)


def measure(table, linker, spelling, workdir):
    """How `linker` reads `spelling` followed by a piece: `Next`,
    `NotNext`, `Unsettled`, or None when it rejects the spelling."""
    code, stderr = run(linker, [spelling, "marker.ld"], workdir)
    if code is None:
        return "Unsettled"
    if MARKER_READ.search(stderr):
        return "NotNext"
    if code == 0:
        return "Next"
    if rejected(stderr, spelling):
        return None
    alone, alone_stderr = run(linker, [spelling], workdir)
    if alone is not None and alone != 0 and wants_value(table, alone_stderr, spelling):
        return "Next"
    return "Unsettled"


def base_object(workdir):
    (workdir / "base.s").write_text("\t.globl _start\n_start:\n\tret\n")
    subprocess.run(["as", "-o", str(workdir / "base.o"), str(workdir / "base.s")], check=True)


def sweep(tools, spellings, jobs):
    """`{table: {spelling: read}}` for the accepted spellings."""
    with tempfile.TemporaryDirectory(prefix="tcg-linker-options-") as scratch:
        scratch = Path(scratch)
        workdirs = []
        for index in range(jobs):
            workdir = scratch / f"w{index}"
            workdir.mkdir()
            base_object(workdir)
            workdirs.append(workdir)
        tasks = [(table, linker, spelling) for table, linker in tools for spelling in spellings]
        chunks = [tasks[index::jobs] for index in range(jobs)]

        def work(chunk, workdir):
            return [
                (table, spelling, measure(table, linker, spelling, workdir))
                for table, linker, spelling in chunk
            ]

        results = {table: {} for table, _ in tools}
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
            for done in pool.map(work, chunks, workdirs):
                for table, spelling, read in done:
                    if read is not None:
                        results[table][spelling] = read
        return results


# `(spelling, {table: read})`: what each linker must be measured to do.
# gold takes `-T`'s value and fails in its own script reader on an
# `INPUT`-only script; GNU ld and LLD read the script's `INPUT`.
CONTROLS = [
    ("--gc-sections", {"GNU_LD": "NotNext", "GOLD": "NotNext", "LLD": "NotNext"}),
    ("-s", {"GNU_LD": "NotNext", "GOLD": "NotNext", "LLD": "NotNext"}),
    ("-e", {"GNU_LD": "Next", "GOLD": "Next", "LLD": "Next"}),
    ("-T", {"GNU_LD": "NotNext", "GOLD": "Next", "LLD": "NotNext"}),
    ("--version-script", {"GNU_LD": "Next", "GOLD": "Next", "LLD": "Next"}),
    ("-l", {"GNU_LD": "Next", "GOLD": "Next", "LLD": "Next"}),
    ("--tcg-no-such-option", {"GNU_LD": None, "GOLD": None, "LLD": None}),
]


def check_controls(results):
    problems = []
    for spelling, expected in CONTROLS:
        for table, reads in results.items():
            if reads.get(spelling) != expected[table]:
                problems.append(
                    f"{table} {spelling}: measured {reads.get(spelling)}, expected {expected[table]}"
                )
    return problems


def split(spelling):
    dashes = 2 if spelling.startswith("--") else 1
    return dashes, spelling[dashes:]


def ranges(reads, names):
    """Encode one linker's measured reads as `(dashes, name, shortest,
    read)`: every spelling `dashes + name[:k]` with `shortest <= k <=
    len(name)` reads `read`. Each accepted spelling is covered, and no
    rejected one."""
    entries = []
    covered = set()
    for name in names:
        for dashes in (1, 2):
            full = "-" * dashes + name
            read = reads.get(full)
            if read is None:
                continue
            shortest = len(name)
            for length in range(len(name) - 1, 0, -1):
                if reads.get("-" * dashes + name[:length]) == read:
                    shortest = length
                else:
                    break
            entries.append((dashes, name, shortest, read))
            for length in range(shortest, len(name) + 1):
                covered.add("-" * dashes + name[:length])
    for spelling, read in reads.items():
        if spelling not in covered:
            dashes, body = split(spelling)
            entries.append((dashes, body, len(body), read))
    return sorted(set(entries))


def decode(entries, spelling):
    dashes, body = split(spelling)
    for entry_dashes, name, shortest, read in entries:
        if entry_dashes == dashes and name.startswith(body) and len(body) >= shortest:
            return read
    return None


def version_line(linker):
    return output([linker, "--version"]).splitlines()[0]


def sha256(text):
    return hashlib.sha256(text.encode()).hexdigest()


def render(tools, helps, results, names, spellings):
    count = len(spellings)
    versions = {table: version_line(linker) for table, linker in tools}
    lines = [
        "//! How the Linux AArch64 host's three linkers read an option spelled in a",
        "//! `-Wl` piece: whether the piece after it is the option's value",
        "//! ([`super::option_operand`]). Measured by",
        "//! `scripts/generate_linker_options.py`, which links with each candidate",
        "//! spelling followed by a script input and records whether the linker read",
        f"//! it; {count} candidate spellings (every name the three `--help` outputs",
        "//! list, with one dash and two, and every prefix of a GNU ld long name)",
        "//! against each linker. `Next` is positive evidence: the linker took the",
        "//! piece and linked, or said the spelling alone wants a value. A spelling",
        "//! a linker rejects is not listed for it. The driver uses the table only",
        "//! for a linker whose `--version` is recorded here",
        "//! ([`super::option_table_applies`]). Checked by",
        "//! `scripts/tests/test_generate_linker_options.py`; do not edit by hand.",
        "//!",
    ]
    for table, _ in tools:
        lines.append(f"//! {table} help sha256: {sha256(helps[table])}")
    lines += [
        "",
        "/// How a linker read an option spelling followed by a piece.",
        "#[derive(Debug, Clone, Copy, PartialEq, Eq)]",
        "pub(super) enum Read {",
        "    /// It took the piece as the option's value.",
        "    Next,",
        "    /// It read the piece as an input (or the option read it as a script).",
        "    NotNext,",
        "    /// The link failed without reading the piece, and the spelling alone",
        "    /// is not reported to want a value: whether it takes the piece is not",
        "    /// settled.",
        "    Unsettled,",
        "}",
        "",
        "/// `(table, version)`: the first line of each linker's `--version` the",
        "/// table was measured with.",
        "pub(super) const VERSIONS: [(&str, &str); 3] = [",
    ]
    for table, _ in tools:
        line = f'    ("{table}", "{versions[table]}"),'
        # trustfmt's default `max_width` (100).
        if len(line) <= 100 and len(line) - 7 <= 60:
            lines.append(line)
        else:
            lines += ["    (", f'        "{table}",', f'        "{versions[table]}",', "    ),"]
    lines.append("];")
    for table, _ in tools:
        entries = ranges(results[table], names)
        # Every measured spelling decodes to what was measured, a rejected
        # one to nothing.
        for spelling in spellings:
            assert decode(entries, spelling) == results[table].get(spelling), (table, spelling)
        lines += [
            "",
            f"/// {table}'s accepted spellings, `(dashes, name, shortest, read)`: every",
            "/// spelling of `dashes` dashes and a prefix of `name` at least `shortest`",
            "/// long reads `read`.",
            f"pub(super) const {table}: &[(u8, &str, u8, Read)] = &[",
        ]
        for dashes, name, shortest, read in entries:
            tuple_text = f'({dashes}, "{name}", {shortest}, Read::{read})'
            # trustfmt's default `fn_call_width` (60) bounds a tuple's
            # elements on one line.
            if len(tuple_text) - 2 > 60:
                lines += [
                    "    (",
                    f"        {dashes},",
                    f'        "{name}",',
                    f"        {shortest},",
                    f"        Read::{read},",
                    "    ),",
                ]
            else:
                lines.append(f"    {tuple_text},")
        lines.append("];")
    return "\n".join(lines) + "\n", entries


def recorded(text):
    """The recorded `(table, version)` pairs, on one line each or as
    trustfmt breaks a long one, and the `--help` hashes."""
    versions = {}
    if "pub(super) const VERSIONS" in text:
        block = text.split("pub(super) const VERSIONS")[1].split("];")[0]
        versions = dict(re.findall(r'\(\s*"(\w+)",\s*"([^"]*)",?\s*\)', block))
    helps = dict(re.findall(r"^//! (\w+) help sha256: ([0-9a-f]+)$", text, re.M))
    return versions, helps


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--sweep", action="store_true", help="with --check, measure again")
    parser.add_argument("--jobs", type=int, default=min(12, os.cpu_count() or 1))
    args = parser.parse_args()
    tools = linkers()
    if tools is None:
        print("ld.bfd, ld.gold and ld.lld are not all installed; nothing to measure")
        return 2
    helps = {table: output([linker, "--help"]) for table, linker in tools}
    if args.check and not args.sweep:
        if not OUT.is_file():
            print(f"{OUT.relative_to(ROOT)} is missing; run scripts/generate_linker_options.py --write")
            return 1
        versions, hashes = recorded(OUT.read_text())
        problems = []
        for table, linker in tools:
            if versions.get(table) != version_line(linker):
                problems.append(f"{table}: recorded version {versions.get(table)!r}, installed {version_line(linker)!r}")
            if hashes.get(table) != sha256(helps[table]):
                problems.append(f"{table}: its --help changed")
        if problems:
            for problem in problems:
                print(problem)
            print(f"{OUT.relative_to(ROOT)} was measured with other linkers; regenerate it: "
                  "scripts/generate_linker_options.py --write")
            return 1
        print(f"{OUT.relative_to(ROOT)} matches the installed linkers' versions and --help")
        return 0
    spellings, names = candidates(helps)
    spellings = sorted(set(spellings) | {spelling for spelling, _ in CONTROLS})
    results = sweep(tools, spellings, args.jobs)
    problems = check_controls(results)
    if problems:
        for problem in problems:
            print("control failed:", problem)
        return 1
    text, _ = render(tools, helps, results, names, spellings)
    summary = ", ".join(
        f"{table} {sum(1 for read in results[table].values() if read == 'Next')} next / "
        f"{sum(1 for read in results[table].values() if read == 'NotNext')} not / "
        f"{sum(1 for read in results[table].values() if read == 'Unsettled')} unsettled"
        for table, _ in tools
    )
    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(text)
        print(f"wrote {OUT.relative_to(ROOT)}: {len(spellings)} spellings x {len(tools)} linkers; {summary}")
        return 0
    if not OUT.is_file() or OUT.read_text() != text:
        print(f"{OUT.relative_to(ROOT)} differs from a new measurement; regenerate it: "
              "scripts/generate_linker_options.py --write")
        return 1
    print(f"{OUT.relative_to(ROOT)} matches a new measurement ({len(spellings)} spellings; {summary})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
