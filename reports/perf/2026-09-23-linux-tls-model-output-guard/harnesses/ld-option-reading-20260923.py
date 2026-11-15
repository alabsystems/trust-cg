#!/usr/bin/env python3
"""How the host GNU ld reads each spelling of a driver-owned link option.

For every driver-owned GNU ld long option name L (output, shared, Bshareable,
pie, pic-executable, no-pie, static, nostdlib, soname, rpath, just-symbols) and
every non-empty prefix P of L, the spellings -P and --P (and, for an option
that takes a value, -P VALUE and -P=VALUE) are passed straight to `ld` in a
setup that makes that option's effect observable:

- output:        ld -o default.elf obj.o SPELLING [redir.elf] -> redir.elf is written
- shared/Bshareable: ld -o out.elf obj.o SPELLING   -> ET_DYN without DF_1_PIE
- pie/pic-executable: ld -o out.elf obj.o SPELLING  -> ET_DYN with DF_1_PIE
- no-pie:        ld -pie -o out.elf obj.o SPELLING  -> ET_EXEC
- static:        ld -o out.elf obj.o SPELLING -L. -lprobe (only libprobe.so) -> cannot find -lprobe
- nostdlib:      ld -o out.elf obj.o SPELLING -lc   -> cannot find -lc
- soname:        ld -shared -o out.so obj.o SPELLING [libtcgprobe.so.7] -> DT_SONAME
- rpath:         ld -shared -o out.so obj.o SPELLING [/tcg/rpath-probe] -> DT_RUNPATH
- just-symbols:  ld -shared -o out.so obj.o SPELLING [<dir>] -> DT_RUNPATH <dir>

A spelling is reported as the owned option when its effect appears, as an ld
error (with ld's first message) when ld exits non-zero without the effect, and
as "other" when ld exits 0 without it. Controls without the spelling show that
no effect appears by itself. Additional rows read the joined short forms
(-o<value>, -h<value>, -R<value>), -G, and the accepted neighbours
(-s, -n, -r, -S, -O1, -z now, -L, -l, -rpath-link, --hash-style, --omagic,
--oformat, -Bstatic, --gpsize) through the C driver; GNU ld's refusal of
grouped short options that take a value; lld's reading of the joined short
forms; and which option `--n`, `--no` and `--no-` select (they undo -N).

Usage: ld-option-reading-20260923.py OUTDIR   (writes OUTDIR/ld-option-reading.json and .txt)
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

OUT = Path(sys.argv[1]).resolve()
OWNED = {
    "output": "value",
    "shared": "flag",
    "Bshareable": "flag",
    "pie": "flag",
    "pic-executable": "flag",
    "no-pie": "flag",
    "static": "flag",
    "nostdlib": "flag",
    "soname": "value",
    "rpath": "value",
    "just-symbols": "value",
}


def sh(argv, cwd):
    done = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=60)
    return done.returncode, done.stdout, done.stderr


def elf_facts(path: Path) -> dict:
    if not path.exists():
        return {"exists": False}
    code, header, _ = sh(["readelf", "-hW", str(path)], path.parent)
    kind = next((line.split(":", 1)[1].strip() for line in header.splitlines() if line.strip().startswith("Type:")), "?")
    code, dynamic, _ = sh(["readelf", "-dW", str(path)], path.parent)
    facts = {"exists": True, "type": kind.split()[0] if kind else "?", "pie": "PIE" in dynamic}
    for tag in ("SONAME", "RUNPATH", "RPATH"):
        for line in dynamic.splitlines():
            if f"({tag})" in line and "[" in line:
                facts[tag.lower()] = line[line.index("[") + 1 : line.rindex("]")]
    return facts


def setup(root: Path) -> None:
    (root / "obj.c").write_text("int main(void) { return 42; }\n")
    (root / "probe.c").write_text("int probe(void) { return 1; }\n")
    for argv in (
        ["cc", "-O1", "-fPIC", "-c", "obj.c", "-o", "obj.o"],
        ["cc", "-O1", "-fPIC", "-shared", "probe.c", "-o", "libprobe.so"],
    ):
        code, _, err = sh(argv, root)
        assert code == 0, err
    (root / "jsdir").mkdir()


def fresh(root: Path, name: str) -> Path:
    work = root / "runs" / name
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    for f in ("obj.o", "libprobe.so"):
        shutil.copy(root / f, work / f)
    (work / "jsdir").mkdir()
    return work


def run_owned(root: Path, owned: str, spelling: list[str], tag: str) -> dict:
    """Run SPELLING in OWNED's setup; return exit, first stderr lines and whether the effect appeared."""
    work = fresh(root, tag)
    value = {
        "output": "redir.elf",
        "soname": "libtcgprobe.so.7",
        "rpath": "/tcg/rpath-probe",
        "just-symbols": str(work / "jsdir"),
    }.get(owned)
    spelled = [s.replace("{VALUE}", value or "") for s in spelling]
    if owned == "output":
        argv = ["ld", "-o", "default.elf", "obj.o", *spelled]
    elif owned in ("shared", "Bshareable", "pie", "pic-executable"):
        argv = ["ld", "-o", "out.elf", "obj.o", *spelled]
    elif owned == "no-pie":
        argv = ["ld", "-pie", "-o", "out.elf", "obj.o", *spelled]
    elif owned == "static":
        argv = ["ld", "-o", "out.elf", "obj.o", *spelled, "-L.", "-lprobe"]
    elif owned == "nostdlib":
        argv = ["ld", "-o", "out.elf", "obj.o", *spelled, "-lc"]
    else:  # soname, rpath, just-symbols
        argv = ["ld", "-shared", "-o", "out.so", "obj.o", *spelled]
    code, _, err = sh(argv, work)
    err_lines = [line for line in err.splitlines() if line.strip()]
    if owned == "output":
        effect = (work / "redir.elf").exists() and not (work / "default.elf").exists()
    elif owned in ("shared", "Bshareable"):
        facts = elf_facts(work / "out.elf")
        effect = facts.get("type") == "DYN" and not facts.get("pie")
    elif owned in ("pie", "pic-executable"):
        facts = elf_facts(work / "out.elf")
        effect = facts.get("type") == "DYN" and bool(facts.get("pie"))
    elif owned == "no-pie":
        effect = elf_facts(work / "out.elf").get("type") == "EXEC"
    elif owned == "static":
        effect = "cannot find -lprobe" in err
    elif owned == "nostdlib":
        effect = "cannot find -lc" in err
    elif owned == "soname":
        effect = elf_facts(work / "out.so").get("soname") == value
    else:
        effect = elf_facts(work / "out.so").get("runpath") == value
    shown = [a.replace(str(work), "$RUN") for a in argv]
    return {"argv": shown, "exit": code, "stderr": [l.replace(str(work), "$RUN") for l in err_lines[:2]], "effect": effect}


def spellings_for(name: str, kind: str) -> list[tuple[str, list[str]]]:
    rows = []
    for dashes in ("-", "--"):
        if kind == "flag":
            rows.append((f"{dashes}{name}", [f"{dashes}{name}"]))
        else:
            rows.append((f"{dashes}{name} VALUE", [f"{dashes}{name}", "{VALUE}"]))
            rows.append((f"{dashes}{name}=VALUE", [f"{dashes}{name}={{VALUE}}"]))
    return rows


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    root = Path(tempfile.mkdtemp(prefix="tcg-ld-reading-"))
    setup(root)
    ld_version = sh(["ld", "--version"], root)[1].splitlines()[0]
    rows = []
    controls = {}
    for owned in OWNED:
        controls[owned] = run_owned(root, owned, [], f"control-{owned}")
    serial = 0
    for owned, kind in OWNED.items():
        for length in range(1, len(owned) + 1):
            prefix = owned[:length]
            for label, spelling in spellings_for(prefix, kind):
                serial += 1
                result = run_owned(root, owned, spelling, f"p{serial}")
                if result["effect"]:
                    reading = f"reads as {owned}"
                elif result["exit"] != 0:
                    reading = "ld error: " + (result["stderr"][0] if result["stderr"] else "")
                else:
                    reading = "other (exit 0, no effect)"
                rows.append({"owned": owned, "prefix": prefix, "spelling": label, "reading": reading, **result})
    # Joined short forms, -G, and accepted neighbours, through the C driver as
    # trust-cg runs it: cc -o OUT -Wl,-z,noexecstack obj.o -Wl,GROUP.
    driver_rows = []
    for label, group, extra in [
        ("-Wl,-G", "-G", []),
        ("-Wl,-G,8", "-G,8", []),
        ("-Wl,--gpsize=8", "--gpsize=8", []),
        ("-Wl,-oredir.elf", "-oredir.elf", []),
        ("-Wl,--outp=redir.elf", "--outp=redir.elf", []),
        ("-Wl,-outp=redir.elf", "-outp=redir.elf", []),
        ("-Wl,-omagic", "-omagic", []),
        ("-Wl,--omagic", "--omagic", []),
        ("-Wl,-oformat=elf64-littleaarch64", "-oformat=elf64-littleaarch64", []),
        ("-Wl,--oformat=elf64-littleaarch64", "--oformat=elf64-littleaarch64", []),
        ("-Wl,-orphan-handling=place", "-orphan-handling=place", []),
        ("-Wl,--orphan-handling=place", "--orphan-handling=place", []),
        ("-Wl,-hlibtcgprobe.so.7 (with -shared)", "-hlibtcgprobe.so.7", ["-shared"]),
        ("-Wl,-hash-style=gnu", "-hash-style=gnu", []),
        ("-Wl,--hash-style=gnu", "--hash-style=gnu", []),
        ("-Wl,-R/tcg/joined-rpath (with -shared)", "-R/tcg/joined-rpath", ["-shared"]),
        ("-Wl,-sh", "-sh", []),
        ("-Wl,--pic-exec (with -no-pie)", "--pic-exec", ["-no-pie"]),
        ("-Wl,-s", "-s", []),
        ("-Wl,-S", "-S", []),
        ("-Wl,-n", "-n", []),
        ("-Wl,-r", "-r", ["-nostdlib"]),
        ("-Wl,-O1", "-O1", []),
        ("-Wl,-z,now", "-z,now", []),
        ("-Wl,-L.,-lprobe", "-L.,-lprobe", []),
        ("-Wl,-rpath-link,.", "-rpath-link,.", []),
        ("-Wl,--rpath-link=.", "--rpath-link=.", []),
        ("-Wl,-Bstatic,-lprobe", "-Bstatic,-L.,-lprobe", []),
        ("-Wl,--gc-sections", "--gc-sections", []),
        ("-Wl,--as-needed", "--as-needed", []),
        ("-Wl,--version", "--version", []),
    ]:
        work = fresh(root, f"cc-{len(driver_rows)}")
        argv = ["cc", *extra, "-o", "out.elf", "-Wl,-z,noexecstack", "obj.o", f"-Wl,{group}"]
        code, out, err = sh(argv, work)
        created = sorted(p.name for p in work.iterdir() if p.name not in ("obj.o", "libprobe.so", "jsdir"))
        facts = {name: elf_facts(work / name) for name in created}
        driver_rows.append(
            {
                "spelling": label,
                "argv": argv,
                "exit": code,
                "stdout_first": out.splitlines()[:1],
                "stderr": [l.replace(str(work), "$RUN") for l in err.splitlines() if l.strip()][:3],
                "created": created,
                "facts": facts,
            }
        )
    # Grouped short options, which 2.42 refuses when a later letter takes a
    # value, and the joined short forms under lld (LLD_PATH first on PATH).
    lld_env = dict(os.environ, PATH=os.pathsep.join([str(Path.home() / ".local/bin"), os.environ["PATH"]]))
    extra_rows = []
    for label, argv, env in [
        ("GNU ld: -Wl,-sofoo (grouped -s -o foo)", ["cc", "-o", "out.elf", "obj.o", "-Wl,-sofoo"], None),
        ("GNU ld: -Wl,-nhfoo (grouped -n -h foo, -shared)", ["cc", "-shared", "-o", "out.elf", "obj.o", "-Wl,-nhfoo"], None),
        ("lld: -Wl,-oredir.elf", ["cc", "-fuse-ld=lld", "-o", "out.elf", "obj.o", "-Wl,-oredir.elf"], lld_env),
        ("lld: -Wl,-hlibtcgprobe.so.9,-R/tcg/lld-rpath (with -shared)", ["cc", "-fuse-ld=lld", "-shared", "-o", "out.elf", "obj.o", "-Wl,-hlibtcgprobe.so.9,-R/tcg/lld-rpath"], lld_env),
        ("lld: -Wl,--outp=redir.elf", ["cc", "-fuse-ld=lld", "-o", "out.elf", "obj.o", "-Wl,--outp=redir.elf"], lld_env),
        ("lld: -Wl,-sh", ["cc", "-fuse-ld=lld", "-o", "out.elf", "obj.o", "-Wl,-sh"], lld_env),
        ("lld: version", ["ld.lld", "--version"], lld_env),
    ]:
        work = fresh(root, f"extra-{len(extra_rows)}")
        done = subprocess.run(argv, cwd=work, capture_output=True, text=True, timeout=60, env=env)
        created = sorted(p.name for p in work.iterdir() if p.name not in ("obj.o", "libprobe.so", "jsdir"))
        extra_rows.append(
            {
                "spelling": label,
                "argv": argv,
                "exit": done.returncode,
                "stdout_first": done.stdout.splitlines()[:1],
                "stderr": [l.replace(str(work), "$RUN") for l in done.stderr.splitlines() if l.strip()][:3],
                "created": created,
                "facts": {name: elf_facts(work / name) for name in created},
            }
        )
    # --n, --no and --no- after -N: which option undoes --omagic's RWX segment.
    omagic_rows = []
    for spelling in ([], ["--n"], ["--no"], ["--no-"], ["--no-omagic"]):
        work = fresh(root, f"omagic-{len(omagic_rows)}")
        code, _, err = sh(["ld", "-N", "-o", "x.elf", "obj.o", *spelling], work)
        _, segments, _ = sh(["readelf", "-lW", "x.elf"], work)
        flags = [" ".join(line.split()[6:-1]) for line in segments.splitlines() if line.strip().startswith("LOAD")]
        omagic_rows.append({"argv": ["ld", "-N", "-o", "x.elf", "obj.o", *spelling], "exit": code, "load_flags": flags})
    result = {
        "ld": ld_version,
        "controls": controls,
        "prefix_rows": rows,
        "driver_rows": driver_rows,
        "extra_rows": extra_rows,
        "omagic_rows": omagic_rows,
    }
    (OUT / "ld-option-reading.json").write_text(json.dumps(result, indent=2) + "\n")
    lines = [f"# {ld_version}", "", "## controls (no spelling): effect must be false"]
    for owned, control in controls.items():
        lines.append(f"{owned:16} exit={control['exit']} effect={control['effect']} {control['stderr'][:1]}")
    lines += ["", "## prefixes of driver-owned GNU ld long options"]
    for row in rows:
        lines.append(f"{row['owned']:15} {row['spelling']:28} -> {row['reading']}")
    lines += ["", "## through the C driver: cc [extra] -o out.elf -Wl,-z,noexecstack obj.o -Wl,GROUP"]
    for row in driver_rows:
        summary = ", ".join(
            f"{name}: {facts.get('type', '-')}{' PIE' if facts.get('pie') else ''}"
            + (f" SONAME={facts['soname']}" if "soname" in facts else "")
            + (f" RUNPATH={facts['runpath']}" if "runpath" in facts else "")
            for name, facts in row["facts"].items()
        )
        lines.append(f"{row['spelling']:44} exit={row['exit']} created=[{summary}] {row['stderr'][:1]} {row['stdout_first']}")
    lines += ["", "## grouped short options (GNU ld) and joined short forms (lld)"]
    for row in extra_rows:
        summary = ", ".join(
            f"{name}: {facts.get('type', '-')}{' PIE' if facts.get('pie') else ''}"
            + (f" SONAME={facts['soname']}" if "soname" in facts else "")
            + (f" RUNPATH={facts['runpath']}" if "runpath" in facts else "")
            for name, facts in row["facts"].items()
        )
        lines.append(f"{row['spelling']:60} exit={row['exit']} created=[{summary}] {row['stderr'][:1]} {row['stdout_first']}")
    lines += ["", "## ld -N -o x.elf obj.o SPELLING: LOAD segment flags (RWE = --omagic in effect)"]
    for row in omagic_rows:
        lines.append(f"{' '.join(row['argv'][5:]) or '(none)':14} exit={row['exit']} LOAD={row['load_flags']}")
    (OUT / "ld-option-reading.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    shutil.rmtree(root)
    return 0


if __name__ == "__main__":
    sys.exit(main())
