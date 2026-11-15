#!/usr/bin/env python3
"""Where GNU ld 2.42 and LLD 22.1.6 put an explicit data section (2026-09-23).

For every probed input-section NAME and shape, an assembly object defines one
8-byte global `tcg_probe` with exactly the section type and flags trust-cg's
pre-repair `classify_elf_section` would emit for that shape. GNU as gives
some names a type or flags of its own (`.stab*` even crashes it, `.rel*`
becomes SHT_REL, `.tdata*` gains SHF_TLS), so the section is assembled under
a same-length placeholder (`QQ..Q`) and renamed in place in `.shstrtab`,
which leaves every other byte of the object as assembled:

* `rw0`: a MUTABLE all-zero u64 -- `"aw",@nobits` for a zero-fill family name
  (`.bss*`, `.tbss*`, `.sbss*`, `.lbss*`), else `"aw",@progbits` (the
  catch-all arm keeps zero bytes in PROGBITS);
* `rw`: a MUTABLE u64 holding 7, `"aw",@progbits` (skipped for zero-fill
  names, which trust-cg refuses as [TCG-SECTION-NOBITS]);
* `ro`: an IMMUTABLE u64 holding 7, `"a",@progbits` (loaded, never stored);
* `table`: a MUTABLE 8-byte constructor-table slot holding `&tcg_probe_noop`
  (`@init_array`/`@fini_array`/`@preinit_array`, `"aw"`), for the table names;
* `table-ro`: the same slot, IMMUTABLE (trust-cg's table flags are `"aw"`
  either way), loaded only;
* `fn`: a FUNCTION `tcg_probe_fn` returning 42 in `"ax",@progbits`, called by
  the driver (the explicit function-section rule, for the undotted names).

Accessors (`tcg_probe_load`, `tcg_probe_store`) reach it with ADRP/ADD, as
trust-cg's O2 code does. A C driver loads it (and, except for `ro`, stores
`load + 3`, or the same pointer for `table`, and re-loads). Each object is
linked with the host `cc` (gcc 13.3 driving GNU ld 2.42) and with `cc
-fuse-ld=lld -B<dir>` (LLD 22.1.6) in four modes: the gcc default (`-pie -z
now -z relro`), `-no-pie`, `-Wl,-z,norelro` (PIE) and a `-shared` library the
driver links against. For every link the harness records the link status,
the output section holding `tcg_probe` (name, type, flags), the program
headers covering its address (PT_LOAD flags, PT_GNU_RELRO, PT_TLS), whether it
lies between crtbegin/crtend's `__TMC_LIST__`/`__TMC_END__`, and the run's exit
status (-11 is SIGSEGV).

Also records `ld --verbose` for exe/pie/shared with `-z relro`, `-z norelro`
and `-z now -z relro`, which ldscripts variant each selects, and the output
section statements of the gcc-default variant with their region (read-only
before DATA_SEGMENT_ALIGN, PT_GNU_RELRO before DATA_SEGMENT_RELRO_END,
writable after it, non-alloc at address 0 or INFO, /DISCARD/).

This is evidence about the linkers' placement of input-section names, not a
linker proof, and it does not run trust-cg output. Writes results.json,
scripts/ and a summary under --out.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import zlib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ZERO_FILL = (".bss", ".tbss", ".sbss", ".lbss")
TABLES = {".init_array": "init_array", ".fini_array": "fini_array", ".preinit_array": "preinit_array"}

# (name, why it is probed)
NAMES = [
    # The independent verifier's list (pre-existing catch-all admissions).
    (".tcommon", "verifier"),
    (".gnu_extab", "verifier"),
    (".gcc_except_table.x", "verifier"),
    (".exception_ranges", "verifier"),
    (".sframe", "verifier"),
    (".eh_frame.x", "verifier"),
    (".jcr", "verifier"),
    # GNU ld script read-only outputs and executable outputs.
    (".rodata1", "gnu-ro"),
    (".rodata1.x", "gnu-ro-boundary"),
    (".eh_frame_entry", "gnu-ro"),
    (".eh_frame_entry.x", "gnu-ro"),
    (".stub", "gnu-exec"),
    (".iplt", "gnu-exec"),
    # ONLY_IF_RO / ONLY_IF_RW unwind statements.
    (".gnu_extab.x", "gnu-unwind"),
    (".exception_ranges.x", "gnu-unwind"),
    (".sframe.x", "gnu-unwind"),
    (".gcc_except_table", "gnu-unwind"),
    (".eh_frame", "gnu-unwind"),
    # RELRO statements.
    (".data.rel.ro", "relro"),
    (".data.rel.ro.local", "relro"),
    (".data.rel.ro.tcg", "relro"),
    (".bss.rel.ro", "lld-relro"),
    (".bss.rel.ro.tcg", "lld-relro"),
    (".igot", "gnu-relro"),
    (".igot.plt", "gnu-relro"),
    (".init_array", "relro-table"),
    (".fini_array", "relro-table"),
    (".preinit_array", "relro-table"),
    (".ctors", "relro-legacy"),
    (".dtors", "relro-legacy"),
    # TLS statements (a non-TLS global).
    (".tdata.tcg", "tls"),
    (".tbss.tcg", "tls"),
    (".tcommon.x", "tls-boundary"),
    # Non-alloc, debug and discarded statements.
    (".stab", "gnu-unloaded"),
    (".stabstr", "gnu-unloaded"),
    (".stab.excl", "gnu-unloaded"),
    (".stab.index", "gnu-unloaded"),
    (".line", "gnu-unloaded"),
    (".gnu_debuglink", "gnu-discard"),
    (".gnu_debugaltlink", "discard-neighbour"),
    # Runtime-read tables without a linker statement.
    (".tm_clone_table", "crt-table"),
    ("COMMON", "common-pseudo"),
    # lld built-in names.
    (".relro_padding", "lld-synthetic"),
    (".relr.dyn", "lld-synthetic"),
    (".toc", "lld-relro-name"),
    (".openbsd.randomdata", "lld-relro-name"),
    (".gdb_index", "lld-synthetic"),
    (".ldata", "lld-prefix"),
    (".ldata.x", "lld-prefix"),
    (".lrodata", "lld-prefix"),
    (".lrodata.x", "lld-prefix"),
    (".sdata", "lld-prefix"),
    (".sdata.x", "lld-prefix"),
    (".srodata", "lld-prefix"),
    (".srodata.x", "lld-prefix"),
    # Honoured names that must stay writable (positive controls).
    (".data", "writable"),
    (".data.tcg", "writable"),
    (".data1", "writable"),
    (".data.rel.rox", "writable-boundary"),
    (".bss", "writable"),
    (".bss.tcg", "writable"),
    (".bss.rel.rox", "writable-boundary"),
    (".sbss", "writable"),
    (".sbss.x", "writable"),
    (".lbss", "writable"),
    (".lbss.tcg", "writable"),
    (".bssx", "orphan"),
    (".tbss_x", "orphan"),
    (".lbssy", "orphan"),
    ("tcg_custom_rw", "orphan"),
    (".textual", "orphan"),
    (".jcrx", "orphan"),
    (".eh_framex", "orphan"),
    (".sframex", "orphan"),
    (".linex", "orphan"),
    (".stabx", "orphan"),
    (".custom", "orphan"),
    (".rel.rox", "bfd-rel-prefix"),
    (".relx", "bfd-rel-prefix"),
    (".rela_x", "bfd-rel-prefix"),
    (".relative", "bfd-rel-prefix"),
    (".relro", "bfd-rel-prefix"),
    (".rex", "orphan"),
    (".stab.exclstr", "gnu-unloaded"),
    (".stab.indexstr", "gnu-unloaded"),
    (".lineage", "orphan"),
    (".comment.x", "orphan"),
    (".tdata1", "orphan"),
    (".data.rel", "writable"),
    (".data.rel.local", "writable"),
    (".rodata.tcg", "gnu-ro"),
    # BFD's special-section table types an OUTPUT section by name.
    (".noinit", "bfd-special"),
    (".noinit.x", "bfd-special"),
    (".persistent", "bfd-special"),
    (".persistent.x", "bfd-special"),
    (".persistent.bss", "bfd-special"),
    (".ctf", "bfd-special"),
    (".gnu_object_only", "bfd-special"),
    (".rela", "bfd-rel-prefix"),
    (".rel", "bfd-rel-prefix"),
    (".relr", "bfd-rel-prefix"),
    (".relr.auth.dyn", "lld-synthetic"),
    (".dynamicx", "orphan"),
    (".interpx", "orphan"),
    (".plt2", "orphan"),
    (".gotx", "orphan"),
    (".hashx", "orphan"),
    (".initx", "orphan"),
    (".finix", "orphan"),
    (".init_arrayx", "orphan"),
    (".ctorsx", "orphan"),
    (".sdata2", "orphan"),
    (".sbss2", "orphan"),
    (".ARM.extabx", "orphan"),
    (".debugx", "orphan"),
    (".note_x", "orphan"),
    (".stabq", "gas-stab-prefix"),
    (".stabqstr", "bfd-stabstr-suffix"),
    (".stab.qstr", "bfd-stabstr-suffix"),
    (".eh_frameq", "orphan"),
]

# Function-section probes (the explicit function rule admits undotted names).
FUNCTION_NAMES = [("COMMON", "common-pseudo"), ("tcg_code", "orphan"), (".text.tcg", "text")]

LINKERS = {"gnu": [], "lld": None}  # lld flags filled from --lld-dir
MODES = {
    "pie": [],
    "nopie": ["-no-pie"],
    "norelro": ["-Wl,-z,norelro"],
    "shared": None,
}


def sh(command, cwd=None, **kwargs):
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True, check=False, **kwargs)


def is_zero_fill(name: str) -> bool:
    return any(name == b or name.startswith(b + ".") for b in ZERO_FILL)


def section_type(name: str, shape: str) -> tuple[str, str]:
    if shape in ("table", "table-ro"):
        return "aw", "@" + TABLES[name]
    if shape == "fn":
        return "ax", "@progbits"
    if is_zero_fill(name):
        # trust-cg's zero-fill arm: all-zero, SHF_ALLOC|SHF_WRITE, NOBITS.
        return "aw", "@nobits"
    if shape == "ro":
        return "a", "@progbits"
    return "aw", "@progbits"


def placeholder(name: str) -> str:
    return "Q" * len(name)


def assembly(name: str, shape: str) -> str:
    flags, kind = section_type(name, shape)
    section = placeholder(name)
    if shape in ("table", "table-ro"):
        body = "\t.xword\ttcg_probe_noop\n"
    elif kind == "@nobits" or shape == "rw0":
        body = "\t.zero\t8\n"
    else:
        body = "\t.xword\t7\n"
    if shape == "fn":
        return f"""\t.section\t{section},"{flags}",{kind}
\t.p2align 2
\t.globl tcg_probe_fn
\t.type tcg_probe_fn,%function
tcg_probe_fn:
\tmov\tx0, #42
\tret
\t.size tcg_probe_fn, .-tcg_probe_fn
\t.section\t.note.GNU-stack,"",@progbits
"""
    return f"""\t.text
\t.p2align 2
\t.globl tcg_probe_noop
\t.hidden tcg_probe_noop
\t.type tcg_probe_noop,%function
tcg_probe_noop:
\tret
\t.size tcg_probe_noop, .-tcg_probe_noop
\t.globl tcg_probe_load
\t.type tcg_probe_load,%function
tcg_probe_load:
\tadrp\tx1, tcg_probe
\tadd\tx1, x1, :lo12:tcg_probe
\tldr\tx0, [x1]
\tret
\t.size tcg_probe_load, .-tcg_probe_load
\t.globl tcg_probe_store
\t.type tcg_probe_store,%function
tcg_probe_store:
\tadrp\tx1, tcg_probe
\tadd\tx1, x1, :lo12:tcg_probe
\tstr\tx0, [x1]
\tret
\t.size tcg_probe_store, .-tcg_probe_store
\t.globl tcg_probe_addr
\t.type tcg_probe_addr,%function
tcg_probe_addr:
\tadrp\tx0, tcg_probe
\tadd\tx0, x0, :lo12:tcg_probe
\tret
\t.size tcg_probe_addr, .-tcg_probe_addr
\t.globl tcg_probe_noop_addr
\t.type tcg_probe_noop_addr,%function
tcg_probe_noop_addr:
\tadrp\tx0, tcg_probe_noop
\tadd\tx0, x0, :lo12:tcg_probe_noop
\tret
\t.size tcg_probe_noop_addr, .-tcg_probe_noop_addr
\t.section\t{section},"{flags}",{kind}
\t.p2align 3
\t.globl tcg_probe
\t.hidden tcg_probe
\t.type tcg_probe,%object
\t.size tcg_probe, 8
tcg_probe:
{body}\t.section\t.note.GNU-stack,"",@progbits
"""


def rename_section(path: Path, old: str, new: str) -> int:
    """Rewrite every occurrence of `old` inside `.shstrtab` to `new` (same
    length), including the tail of a merged `.rela<old>`. Returns the count."""
    data = bytearray(path.read_bytes())
    shoff = int.from_bytes(data[0x28:0x30], "little")
    shentsize = int.from_bytes(data[0x3A:0x3C], "little")
    shstrndx = int.from_bytes(data[0x3E:0x40], "little")
    header = shoff + shstrndx * shentsize
    offset = int.from_bytes(data[header + 0x18:header + 0x20], "little")
    size = int.from_bytes(data[header + 0x20:header + 0x28], "little")
    table = bytes(data[offset:offset + size])
    count = table.count(old.encode())
    data[offset:offset + size] = table.replace(old.encode(), new.encode())
    path.write_bytes(bytes(data))
    return count


def driver(shape: str, zero_fill: bool = False) -> str:
    if shape == "fn":
        return """extern long tcg_probe_fn(void);
int main(void) { return tcg_probe_fn() == 42 ? 0 : 4; }
"""
    noop = "(unsigned long)tcg_probe_noop_addr()"
    expect = {"rw0": "0", "rw": "7", "ro": "0" if zero_fill else "7", "table": noop,
              "table-ro": noop}[shape]
    store = {
        "rw0": "tcg_probe_store(v + 3); if (tcg_probe_load() != v + 3) return 3;",
        "rw": "tcg_probe_store(v + 3); if (tcg_probe_load() != v + 3) return 3;",
        "table": "tcg_probe_store(v); if (tcg_probe_load() != v) return 3;",
        "ro": "",
        "table-ro": "",
    }[shape]
    return f"""#include <stdio.h>
extern unsigned long tcg_probe_load(void);
extern void tcg_probe_store(unsigned long);
extern void *tcg_probe_noop_addr(void);
int main(void) {{
    unsigned long v = tcg_probe_load();
    if (v != {expect}) return 2;
    {store}
    puts("probe-ok");
    return 0;
}}
"""


def program_headers(listing: str) -> list[dict]:
    headers = []
    for line in listing.splitlines():
        fields = line.split()
        if len(fields) >= 8 and fields[0].isupper() and fields[1].startswith("0x"):
            try:
                vaddr, memsz = int(fields[2], 16), int(fields[5], 16)
            except ValueError:
                continue
            flags = " ".join(fields[6:-1])
            headers.append({"type": fields[0], "vaddr": vaddr, "memsz": memsz, "flags": flags})
    return headers


def sections(listing: str) -> dict[int, dict]:
    table = {}
    for line in listing.splitlines():
        match = re.match(
            r"\s*\[\s*(\d+)\]\s+(\S*)\s+(\S+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([A-Za-z]*)\s+\d+",
            line,
        )
        if match:
            table[int(match[1])] = {
                "name": match[2],
                "type": match[3],
                "addr": int(match[4], 16),
                "size": int(match[6], 16),
                "flags": match[8],
            }
    return table


def symbol(listing: str, name: str):
    for line in listing.splitlines():
        fields = line.split()
        if len(fields) >= 8 and fields[-1] == name and fields[6] != "UND":
            return int(fields[1], 16), fields[6]
    return None


def inspect(image: Path, target: str) -> dict:
    env = dict(os.environ, LC_ALL="C")
    s = sh(["readelf", "-SW", str(image)], env=env).stdout
    l = sh(["readelf", "-lW", str(image)], env=env).stdout
    y = sh(["readelf", "-sW", str(image)], env=env).stdout
    found = symbol(y, target)
    if found is None:
        return {"symbol": None}
    addr, ndx = found
    info = {"addr": addr}
    if ndx.isdigit():
        sec = sections(s).get(int(ndx), {})
        info["output"] = {k: sec.get(k) for k in ("name", "type", "flags")}
    else:
        info["output"] = {"name": ndx}
    info["segments"] = sorted(
        f"{h['type']}({h['flags']})"
        for h in program_headers(l)
        if h["vaddr"] <= addr < h["vaddr"] + max(h["memsz"], 1)
    )
    tmc = [symbol(y, "__TMC_LIST__"), symbol(y, "__TMC_END__")]
    if all(tmc):
        info["in_tm_clone_list"] = tmc[0][0] <= addr < tmc[1][0]
    return info


def probe_one(args, work: Path, name: str, shape: str) -> dict:
    tag = re.sub(r"[^A-Za-z0-9]", "_", name).strip("_") + "-" + shape + f"-{zlib.crc32(name.encode()) % 10**6}"
    case_dir = work / tag
    case_dir.mkdir()
    (case_dir / "probe.s").write_text(assembly(name, shape))
    (case_dir / "driver.c").write_text(driver(shape, is_zero_fill(name)))
    record = {"name": name, "shape": shape, "asm_flags": " ".join(section_type(name, shape))}
    assembled = sh(["cc", "-c", "-o", "probe.o", "probe.s"], cwd=case_dir)
    if assembled.returncode:
        record["assemble_error"] = assembled.stderr.strip()
        return record
    record["renamed"] = rename_section(case_dir / "probe.o", placeholder(name), name)
    listing = sh(["readelf", "-SW", "probe.o"], cwd=case_dir, env=dict(os.environ, LC_ALL="C")).stdout
    record["object_section"] = next(
        ({k: v for k, v in sec.items() if k in ("name", "type", "flags")}
         for sec in sections(listing).values() if sec["name"] == name),
        None,
    )
    target = "tcg_probe_fn" if shape == "fn" else "tcg_probe"
    lld_flags = ["-fuse-ld=lld", f"-B{args.lld_dir}"]
    for linker, lflags in [("gnu", []), ("lld", lld_flags)]:
        for mode in MODES:
            key = f"{linker}-{mode}"
            exe = case_dir / f"{key}.exe"
            if mode == "shared":
                lib = case_dir / f"lib{key}.so"
                link = sh(["cc", *lflags, "-shared", "-o", str(lib), "probe.o"], cwd=case_dir)
                if link.returncode == 0:
                    link = sh(
                        ["cc", *lflags, "-o", str(exe), "driver.c", str(lib),
                         f"-Wl,-rpath,{case_dir}"],
                        cwd=case_dir,
                    )
                image = lib
            else:
                link = sh(["cc", *lflags, *MODES[mode], "-o", str(exe), "driver.c", "probe.o"],
                          cwd=case_dir)
                image = exe
            entry = {"link_exit": link.returncode}
            diagnostics = (link.stderr or "").strip().splitlines()
            if diagnostics:
                entry["link_stderr"] = [line[:240] for line in diagnostics[:4]]
            if link.returncode == 0:
                entry |= inspect(image, target)
                ran = subprocess.run([str(exe)], cwd=case_dir, capture_output=True, text=True,
                                     timeout=20, check=False)
                entry["exit"] = ran.returncode
            record[key] = entry
    if not args.keep:
        shutil.rmtree(case_dir)
    return record


def tcommon_beside_tls(args, work: Path) -> dict:
    """`.tcommon` next to a real thread-local: GNU ld folds both into one
    `.tbss` output, which becomes SHF_TLS (PT_TLS) with the non-TLS global
    inside the template. Records each linker's output and run status."""
    case_dir = work / "tcommon-beside-tls"
    case_dir.mkdir()
    (case_dir / "probe.s").write_text(assembly(".tcommon", "rw0"))
    (case_dir / "tls.c").write_text("__thread unsigned long real_tls;\n")
    (case_dir / "driver.c").write_text(
        "extern unsigned long tcg_probe_load(void);\n"
        "extern void tcg_probe_store(unsigned long);\n"
        "extern __thread unsigned long real_tls;\n"
        "int main(void) { real_tls = 1; tcg_probe_store(tcg_probe_load() + 3); return 0; }\n"
    )
    sh(["cc", "-c", "-o", "probe.o", "probe.s"], cwd=case_dir)
    rename_section(case_dir / "probe.o", placeholder(".tcommon"), ".tcommon")
    record = {}
    for linker, flags in [("gnu", []), ("lld", ["-fuse-ld=lld", f"-B{args.lld_dir}"])]:
        exe = case_dir / f"{linker}.exe"
        link = sh(["cc", *flags, "-o", str(exe), "driver.c", "tls.c", "probe.o"], cwd=case_dir)
        entry = {"link_exit": link.returncode,
                 "link_stderr": (link.stderr or "").strip().splitlines()[:3]}
        if link.returncode == 0:
            entry |= inspect(exe, "tcg_probe")
            entry["exit"] = subprocess.run([str(exe)], cwd=case_dir, check=False).returncode
        record[linker] = entry
    if not args.keep:
        shutil.rmtree(case_dir)
    return record


def ld_scripts(out: Path) -> dict:
    scripts = out / "scripts"
    scripts.mkdir()
    variants = {}
    ldscripts = Path("/usr/lib/aarch64-linux-gnu/ldscripts")
    for mode, flags in [("exe", []), ("pie", ["-pie"]), ("shared", ["-shared"])]:
        for z, zflags in [("relro", ["-z", "relro"]), ("norelro", ["-z", "norelro"]),
                          ("now-relro", ["-z", "now", "-z", "relro"])]:
            text = sh(["ld", "--verbose", *flags, *zflags]).stdout
            body = text.split("=" * 50)[1].strip("\n") if "=" * 50 in text else text
            match = None
            for candidate in sorted(ldscripts.glob("aarch64linux.*")):
                if [l for l in candidate.read_text().splitlines() if l.strip()] == [
                    l for l in body.splitlines() if l.strip()
                ]:
                    match = candidate.name
            variants[f"{mode}/{z}"] = match
            path = scripts / f"ld-verbose-{mode}-{z}.x"
            if not path.exists():
                path.write_text(body + "\n")
    return variants


REGION_MARKERS = [
    ("DATA_SEGMENT_ALIGN", "relro"),
    ("DATA_SEGMENT_RELRO_END", "writable"),
    ("DATA_SEGMENT_END", "unloaded"),
]


def script_statements(script: str) -> list[dict]:
    """Output statements of a GNU ld default script with their input patterns."""
    region = "read-only"
    statements = []
    lines = script.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        for marker, next_region in REGION_MARKERS:
            if marker + " (" in line and "=" in line:
                region = next_region
        head = re.match(r"\s*(/DISCARD/|\.[\w.$-]+)\s*(0\s*)?(\(INFO\)\s*)?:\s*(ONLY_IF_R[OW])?", line)
        if head and "{" in "".join(lines[i:i + 2]):
            depth, body, j = 0, [], i
            while True:
                text = lines[j]
                body.append(text)
                depth += text.count("{") - text.count("}")
                if depth <= 0 and "{" in "".join(body):
                    break
                j += 1
            joined = " ".join(body)
            inner = joined[joined.index("{") + 1: joined.rindex("}")]
            patterns = []
            for group in re.findall(r"\*\(([^()]*(?:\([^()]*\)[^()]*)*)\)", inner):
                for token in re.sub(r"(SORT\w*|EXCLUDE_FILE)\s*\(", " ", group).replace(")", " ").split():
                    if token.startswith(".") or token in ("COMMON",):
                        patterns.append(token)
            output = head[1]
            kind = region
            if output == "/DISCARD/":
                kind = "discard"
            elif head[2] or head[3]:
                kind = "unloaded"
            statements.append({
                "output": output,
                "constraint": head[4],
                "region": kind,
                "patterns": patterns,
            })
            i = j + 1
            continue
        i += 1
    return statements


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--lld-dir", type=Path, default=Path.home() / ".local/bin")
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--keep", action="store_true")
    parser.add_argument("--only", action="append", default=[],
                        help="probe only these names (development runs)")
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    work = out / "work"
    work.mkdir()
    lld = args.lld_dir / "ld.lld"
    results = {
        "tools": {
            "cc": sh(["cc", "--version"]).stdout.splitlines()[0],
            "ld": sh(["ld", "--version"]).stdout.splitlines()[0],
            "lld": sh([str(lld), "--version"]).stdout.strip(),
            "readelf": sh(["readelf", "--version"]).stdout.splitlines()[0],
            "glibc": sh(["ldd", "--version"]).stdout.splitlines()[0],
            "uname": sh(["uname", "-srm"]).stdout.strip(),
        },
        "gcc_default_link": " ".join(
            flag for flag in sh(["cc", "-v", "-x", "c", "/dev/null", "-o", "/dev/null"]).stderr.split()
            if flag in ("-pie", "-no-pie", "now", "relro", "-z", "--hash-style=gnu")
        ),
    }
    results["ld_script_variants"] = ld_scripts(out)
    default = (out / "scripts" / "ld-verbose-pie-now-relro.x").read_text()
    results["gnu_default_statements"] = script_statements(default)
    jobs = []
    for name, why in NAMES:
        if args.only and name not in args.only:
            continue
        shapes = ["rw0", "ro"]
        if name in TABLES:
            shapes = ["table", "table-ro"]
        elif not is_zero_fill(name):
            shapes.insert(1, "rw")
        for shape in shapes:
            jobs.append((name, why, shape))
    for name, why in FUNCTION_NAMES:
        if args.only and name not in args.only:
            continue
        jobs.append((name, why, "fn"))
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        records = list(pool.map(lambda job: probe_one(args, work, job[0], job[2]) | {"why": job[1]},
                                jobs))
    results["cases"] = records
    if not args.only:
        results["tcommon_beside_tls"] = tcommon_beside_tls(args, work)
    if not args.keep:
        shutil.rmtree(work)
    (out / "results.json").write_text(json.dumps(results, indent=1) + "\n")
    # Compact summary: one line per (name, shape).
    lines = []
    for record in records:
        cells = []
        for linker in ("gnu", "lld"):
            for mode in MODES:
                entry = record.get(f"{linker}-{mode}", {})
                if "link_exit" not in entry:
                    cells.append("-")
                elif entry["link_exit"]:
                    cells.append("LINKFAIL")
                else:
                    out_name = (entry.get("output") or {}).get("name")
                    segs = ",".join(
                        s.split("(")[0].replace("GNU_RELRO", "RELRO") + (
                            "" if not s.startswith("LOAD") else s[4:].replace(" ", ""))
                        for s in entry.get("segments", [])
                    )
                    cells.append(f"{out_name}[{segs}]={entry.get('exit')}")
        obj = record.get("object_section") or {}
        lines.append(f"{record['name']:22} {record['shape']:8} {obj.get('type', '?'):10} {obj.get('flags', '?'):4} "
                     + " | ".join(cells))
    (out / "summary.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())
