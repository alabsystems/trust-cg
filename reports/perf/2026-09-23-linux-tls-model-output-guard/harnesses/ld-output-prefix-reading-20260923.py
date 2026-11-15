#!/usr/bin/env python3
"""Which files GNU ld writes for the prefixes of `output` that do not redirect it.

Supplements ld-option-reading-20260923.py, whose output setup only asks whether
redir.elf replaced default.elf. For each spelling, `ld -o default.elf obj.o
SPELLING` runs in a fresh directory and every file it leaves is listed with its
ELF type: `-ou`/`-out`/`--ou`/`--out` write an ET_REL import library
(`--out-implib`) beside the executable, and one-dash `-outp=`/`-outpu=`/`-output=`
are `-o <rest>` (the executable is written as `utp=redir.elf` and so on).

Usage: ld-output-prefix-reading-20260923.py OUTDIR
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

OUT = Path(sys.argv[1]).resolve()
SPELLINGS = [
    ["-ou", "redir.elf"], ["-ou=redir.elf"], ["--ou", "redir.elf"], ["--ou=redir.elf"],
    ["-out", "redir.elf"], ["-out=redir.elf"], ["--out", "redir.elf"], ["--out=redir.elf"],
    ["--out-implib=redir.elf"],
    ["-outp=redir.elf"], ["-outpu=redir.elf"], ["-output=redir.elf"],
    ["--outp=redir.elf"], ["--output=redir.elf"],
]


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    root = Path(tempfile.mkdtemp(prefix="tcg-ld-output-"))
    (root / "obj.c").write_text("int main(void) { return 42; }\n")
    subprocess.run(["cc", "-O1", "-fPIC", "-c", "obj.c", "-o", "obj.o"], cwd=root, check=True)
    rows, lines = [], [subprocess.run(["ld", "--version"], capture_output=True, text=True).stdout.splitlines()[0], ""]
    for index, spelling in enumerate(SPELLINGS):
        work = root / f"run{index}"
        work.mkdir()
        shutil.copy(root / "obj.o", work / "obj.o")
        argv = ["ld", "-o", "default.elf", "obj.o", *spelling]
        done = subprocess.run(argv, cwd=work, capture_output=True, text=True)
        written = {}
        for path in sorted(work.iterdir()):
            if path.name == "obj.o":
                continue
            header = subprocess.run(["readelf", "-h", path.name], cwd=work, capture_output=True, text=True).stdout
            written[path.name] = next((l.split(":", 1)[1].strip().split()[0] for l in header.splitlines() if "Type:" in l), "?")
        rows.append({"argv": argv, "exit": done.returncode, "written": written})
        lines.append(f"{' '.join(spelling):26} exit={done.returncode} written={written}")
    (OUT / "ld-output-prefix-reading.json").write_text(json.dumps(rows, indent=2) + "\n")
    (OUT / "ld-output-prefix-reading.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    shutil.rmtree(root)
    return 0


if __name__ == "__main__":
    sys.exit(main())
