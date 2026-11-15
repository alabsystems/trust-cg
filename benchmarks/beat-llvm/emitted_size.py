#!/usr/bin/env python3
"""benchmarks/beat-llvm/emitted_size.py — emitted-code size from the linker's map.

The linked executable's file size (`st_size`) includes the Rust standard
library, which both lanes link from the same sysroot rlibs, compiled by LLVM.
It therefore reads about 1.000x whatever the backend emits (ledger L14-P10),
and it cannot show an emitted-code difference.

Definition (gates.json version 3, metrics-contract.md "Size and memory"):

    emitted-code size = the bytes of the LINKED executable that the linker
    places from object files this compile produced, counted in code sections
    and read-only data sections, after dead stripping.

* "Object files this compile produced": the non-archive input objects whose
  path lies inside the compile's own fresh, private output directory. These are
  rustc's codegen-unit objects and the allocator shim, emitted by the backend
  under test (LLVM or trust-cg), including the monomorphized standard-library
  generics the crate instantiates. Archive members (the sysroot `.rlib`s:
  `std`, `core`, `alloc`, `compiler_builtins`, ...), system startup objects,
  dylibs, text stubs and linker-synthesized atoms (stubs, GOT, compact unwind)
  are not the program's.
* "Code": `__TEXT,__text` (Mach-O) or output sections named `.text*` (ELF).
* "Read-only data": `__TEXT` constant and literal sections and
  `__DATA_CONST,__const` / `__DATA,__const` (Mach-O), or `.rodata*` and
  `.data.rel.ro*` (ELF).
* Writable data, zero-fill and unwind/exception tables attributed to the
  program are recorded per class but are not part of the measure: Darwin's
  compact unwind table is synthesized by the linker and cannot be attributed
  per object, so an unwind class would compare unlike quantities across
  platforms.

The linker states the attribution itself, so nothing here guesses from symbol
names. The map is requested with one link argument (`link_map_args`), which
changes no code; the harness links the lane's measured binary with it.

Supported map formats: Apple ld (`-map`, ld64 and ld-prime share the format)
and GNU ld (`-Map`). Any other format, an unreadable map, or a map that
attributes no byte to the program is UNMEASURED (`bytes` None with an
`error`), never zero: the harness's fail-closed aggregation names the reading.
"""

import bisect
import hashlib
import os
import re
import struct
import sys
from pathlib import Path

DEFINITION = (
    "emitted-code size: bytes of the linked executable placed from object files the "
    "compile wrote into its own private output directory (codegen units and the "
    "allocator shim, not sysroot rlib members, system objects or linker-synthesized "
    "atoms), in code sections (__TEXT,__text / .text*) plus read-only data sections "
    "(__TEXT constants and literals, __DATA_CONST,__const / .rodata*, .data.rel.ro*), "
    "after dead stripping, as the linker's own map attributes them"
)
MEASURED_CLASSES = ("text", "rodata")
CLASSES = ("text", "rodata", "data", "zerofill", "unwind", "other")

_MACHO_RODATA = {
    ("__TEXT", "__const"), ("__TEXT", "__cstring"), ("__TEXT", "__literal4"),
    ("__TEXT", "__literal8"), ("__TEXT", "__literal16"), ("__TEXT", "__ustring"),
    ("__DATA_CONST", "__const"), ("__DATA", "__const"),
}
_MACHO_UNWIND = {"__eh_frame", "__gcc_except_tab", "__unwind_info", "__compact_unwind"}
_MACHO_ZEROFILL = {"__bss", "__common", "__thread_bss"}


def map_format_for(platform=None):
    """The map format this platform's default linker writes."""
    return "ld64" if (platform or sys.platform) == "darwin" else "gnu-ld"


def link_map_args(map_path, platform=None):
    """trustc arguments that make the system linker write its map to MAP_PATH."""
    if map_format_for(platform) == "ld64":
        return ["-C", f"link-arg=-Wl,-map,{map_path}"]
    return ["-C", f"link-arg=-Wl,-Map={map_path}"]


def classify_macho(segment, section):
    """The measure class of a Mach-O (segment, section)."""
    if section == "__text":
        return "text"
    if (segment, section) in _MACHO_RODATA:
        return "rodata"
    if section in _MACHO_UNWIND:
        return "unwind"
    if section in _MACHO_ZEROFILL:
        return "zerofill"
    if segment.startswith("__DATA"):
        return "data"
    return "other"


def classify_elf(section):
    """The measure class of an ELF OUTPUT section name."""
    if section == ".text" or section.startswith(".text."):
        return "text"
    if section.startswith(".rodata") or section.startswith(".data.rel.ro") or section == ".srodata":
        return "rodata"
    if section.startswith(".eh_frame") or section.startswith(".gcc_except_table") \
            or section in (".ARM.exidx", ".ARM.extab"):
        return "unwind"
    if section.startswith((".bss", ".tbss", ".sbss")):
        return "zerofill"
    if section.startswith((".data", ".tdata", ".sdata", ".got")) \
            or section in (".init_array", ".fini_array"):
        return "data"
    return "other"


def _is_archive_member(path):
    return path.endswith(")") and "(" in path


def program_object(path, program_dir, cwd=None):
    """Whether an input object named PATH in a map is one the compile produced:
    not an archive member, and inside PROGRAM_DIR (relative paths resolve
    against CWD, the linker's working directory, default PROGRAM_DIR). Only
    relocatable object files (`.o`) qualify: a map also names its own
    synthesized atoms ("linker synthesized"), dylibs and text stubs."""
    if not path or _is_archive_member(path) or Path(path).suffix != ".o":
        return False
    candidate = Path(path)
    if not candidate.is_absolute():
        candidate = Path(cwd or program_dir) / candidate
    try:
        resolved = Path(os.path.realpath(candidate))
        root = Path(os.path.realpath(program_dir))
    except (OSError, ValueError):
        return False
    return resolved == root or root in resolved.parents


class MapError(ValueError):
    """The map cannot be read as a supported linker map."""


def _empty_record(fmt):
    return {"format": fmt, "classes": dict.fromkeys(CLASSES, 0), "sections": {},
            "program_objects": [], "atoms": 0}


def _finish(record, error=None):
    measured = sum(record["classes"][c] for c in MEASURED_CLASSES)
    if error is None and measured <= 0:
        error = "the map attributes no code or read-only byte to the program's objects"
    record["bytes"] = None if error else measured
    record["error"] = error
    record["program_objects"] = sorted(record["program_objects"])
    return record


_LD64_OBJECT = re.compile(r"^\[\s*(\d+)\]\s+(.*)$")
_LD64_SECTION = re.compile(r"^0x([0-9A-Fa-f]+)\s+0x([0-9A-Fa-f]+)\s+(\S+)\s+(\S+)\s*$")
_LD64_SYMBOL = re.compile(r"^0x([0-9A-Fa-f]+)\s+0x([0-9A-Fa-f]+)\s+\[\s*(\d+)\]\s")


def parse_ld64(text, program_dir, cwd=None):
    """Attribute an Apple ld `-map` (ld64 / ld-prime) to the program's objects.

    The map lists input files (`[ n] path`), output sections (address, size,
    segment, section) and every live atom (address, size, file index, name);
    dead-stripped atoms follow `# Dead Stripped Symbols:` and are not in the
    image. An atom is placed in the section whose address range holds it."""
    record = _empty_record("ld64")
    part, files, sections = None, {}, []
    atoms = []
    for line in text.splitlines():
        if line.startswith("#"):
            header = line.lower()
            if header.startswith("# object files:"):
                part = "objects"
            elif header.startswith("# sections:"):
                part = "sections"
            elif header.startswith("# symbols:"):
                part = "symbols"
            elif header.startswith("# dead stripped symbols:"):
                part = "dead"
            continue
        if part == "objects":
            m = _LD64_OBJECT.match(line)
            if m:
                files[int(m.group(1))] = m.group(2).strip()
        elif part == "sections":
            m = _LD64_SECTION.match(line)
            if m:
                sections.append((int(m.group(1), 16), int(m.group(2), 16), m.group(3), m.group(4)))
        elif part == "symbols":
            m = _LD64_SYMBOL.match(line)
            if m:
                atoms.append((int(m.group(1), 16), int(m.group(2), 16), int(m.group(3))))
    if not files or not sections:
        raise MapError("not an Apple ld map (no object-file or section table)")
    sections.sort()
    starts = [s[0] for s in sections]
    mine = {index for index, path in files.items() if program_object(path, program_dir, cwd)}
    record["program_objects"] = [os.path.basename(files[i]) for i in mine]
    for address, size, index in atoms:
        if index not in mine or size == 0:
            continue
        slot = bisect.bisect_right(starts, address) - 1
        if slot < 0 or address >= sections[slot][0] + max(sections[slot][1], 1):
            return _finish(record, f"a program atom at 0x{address:x} lies in no mapped section")
        _, _, segment, section = sections[slot]
        key = f"{segment},{section}"
        record["sections"][key] = record["sections"].get(key, 0) + size
        record["classes"][classify_macho(segment, section)] += size
        record["atoms"] += 1
    return _finish(record)


_GNU_OUTPUT = re.compile(r"^(\S+)\s+0x([0-9a-fA-F]+)\s+0x([0-9a-fA-F]+)(?:\s.*)?$")
_GNU_NAME_ONLY = re.compile(r"^(\S+)\s*$")
_GNU_ADDR_SIZE = re.compile(r"^\s+0x([0-9a-fA-F]+)\s+0x([0-9a-fA-F]+)(?:\s+(.*))?$")
_GNU_INPUT = re.compile(r"^ (\S+)\s+0x([0-9a-fA-F]+)\s+0x([0-9a-fA-F]+)\s+(\S.*)$")
_GNU_INPUT_NAME = re.compile(r"^ ([^\s*]\S*)\s*$")
_GNU_KEYWORDS = ("LOAD", "OUTPUT", "START", "END", "INPUT", "GROUP", "TARGET", "SEARCH_DIR")


def parse_gnu_ld(text, program_dir, cwd=None):
    """Attribute a GNU ld `-Map` to the program's objects.

    Only the "Linker script and memory map" part describes the image (the
    "Discarded input sections" part before it lists what was removed). There,
    an OUTPUT section starts in column 0 (its address and size on the same line
    or, for a long name, the next); an INPUT section is indented one space and
    names its file after its address and size (again on the next line for a
    long name). Fill, patterns (` *(...)`) and symbol lines carry no file."""
    record = _empty_record("gnu-ld")
    marker = "Linker script and memory map"
    at = text.find(marker)
    if at < 0:
        raise MapError("not a GNU ld map (no 'Linker script and memory map' part)")
    output, pending_output, pending_input = None, None, None
    seen_objects = set()

    def place(section, size, path):
        path = path.strip()
        if size == 0 or output in (None, "/DISCARD/") or not program_object(path, program_dir, cwd):
            return
        seen_objects.add(os.path.basename(path))
        key = f"{output}"
        record["sections"][key] = record["sections"].get(key, 0) + size
        record["classes"][classify_elf(output)] += size
        record["atoms"] += 1

    for line in text[at + len(marker):].splitlines():
        if not line.strip():
            pending_input = None
            continue
        if pending_output is not None:
            m = _GNU_ADDR_SIZE.match(line)
            output, pending_output = (pending_output if m else None), None
            if m:
                continue
        if pending_input is not None:
            m = _GNU_ADDR_SIZE.match(line)
            name, pending_input = pending_input, None
            if m and m.group(3):
                place(name, int(m.group(2), 16), m.group(3))
                continue
        if not line.startswith(" "):
            if line.split()[0] in _GNU_KEYWORDS:
                continue
            m = _GNU_OUTPUT.match(line)
            if m:
                output = m.group(1)
                continue
            m = _GNU_NAME_ONLY.match(line)
            if m:
                pending_output = m.group(1)
            continue
        if line.startswith(" *"):
            continue  # an input pattern or *fill*
        m = _GNU_INPUT.match(line)
        if m:
            place(m.group(1), int(m.group(3), 16), m.group(4))
            continue
        m = _GNU_INPUT_NAME.match(line)
        if m:
            pending_input = m.group(1)
    record["program_objects"] = sorted(seen_objects)
    return _finish(record)


def parse_map(text, program_dir, cwd=None):
    """Attribute a linker map in any supported format (see the module docstring)."""
    head = text.lstrip()[:200]
    if head.startswith("# Path:") or "\n# Object files:" in text[:4096]:
        return parse_ld64(text, program_dir, cwd)
    if "Linker script and memory map" in text:
        return parse_gnu_ld(text, program_dir, cwd)
    raise MapError("unsupported linker map format (neither Apple ld nor GNU ld)")


def measure_map(map_path, program_dir, cwd=None):
    """The emitted-size record for one linked binary: `bytes` (None when
    unmeasured), per-class and per-section bytes, the program objects, the
    map's format and SHA-256, and `error` naming why a reading is missing."""
    try:
        data = Path(map_path).read_bytes()
    except OSError as error:
        record = _finish(_empty_record(None), f"linker map unreadable: {error}")
        record["map_sha256"] = None
        return record
    text = data.decode("utf-8", errors="replace")
    try:
        record = parse_map(text, program_dir, cwd)
    except MapError as error:
        record = _finish(_empty_record(None), str(error))
    record["map_sha256"] = hashlib.sha256(data).hexdigest()
    return record


_MH_MAGIC_64 = 0xFEEDFACF
_LC_SEGMENT_64 = 0x19
_ZEROFILL_TYPES = {0x1, 0xC, 0x12}  # S_ZEROFILL, S_GB_ZEROFILL, S_THREAD_LOCAL_ZEROFILL
_SHT_NOBITS = 8
_SHF_ALLOC = 0x2


def _macho_sections(data):
    """(segment, section, bytes) of every file-backed section of a 64-bit
    little-endian Mach-O image, in load-command order."""
    magic, _, _, _, ncmds, _, _, _ = struct.unpack_from("<IiiIIIII", data, 0)
    if magic != _MH_MAGIC_64:
        raise MapError("not a 64-bit little-endian Mach-O image")
    offset, out = 32, []
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from("<II", data, offset)
        if cmd == _LC_SEGMENT_64:
            segname = data[offset + 8:offset + 24].rstrip(b"\0").decode()
            nsects = struct.unpack_from("<I", data, offset + 64)[0]
            at = offset + 72
            for _ in range(nsects):
                sectname = data[at:at + 16].rstrip(b"\0").decode()
                size, fileoff = struct.unpack_from("<QI", data, at + 40)
                flags = struct.unpack_from("<I", data, at + 64)[0]
                if (flags & 0xFF) not in _ZEROFILL_TYPES and size:
                    out.append((segname, sectname, data[fileoff:fileoff + size]))
                at += 80
        offset += cmdsize
    return out


def _elf_sections(data):
    """("", name, bytes) of every file-backed ALLOCATED section of a 64-bit
    little-endian ELF image (what is loaded; symbol tables are not)."""
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise MapError("not a 64-bit little-endian ELF image")
    shoff = struct.unpack_from("<Q", data, 0x28)[0]
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 0x3A)
    headers = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize) for i in range(shnum)]
    names = headers[shstrndx]
    strtab = data[names[4]:names[4] + names[5]]
    out = []
    for name_off, kind, flags, _, offset, size, *_ in headers:
        if kind != _SHT_NOBITS and size and flags & _SHF_ALLOC:
            name = strtab[name_off:strtab.index(b"\0", name_off)].decode()
            out.append(("", name, data[offset:offset + size]))
    return out


# Sections the linker fills with per-link identity, not with the program: the
# ELF build-id note. (Mach-O keeps its per-link UUID and code signature in load
# commands and __LINKEDIT, which are not sections.)
_IDENTITY_SECTIONS = {".note.gnu.build-id"}


def image_digest(path):
    """SHA-256 over every file-backed section's name and bytes of a linked
    image, ignoring load commands, __LINKEDIT (symbol tables, code signature)
    and the per-link identity note. Two links of the same code and data agree
    on it even though their LC_UUID and signature differ."""
    data = Path(path).read_bytes()
    sections = _macho_sections(data) if data[:4] == struct.pack("<I", _MH_MAGIC_64) \
        else _elf_sections(data)
    digest = hashlib.sha256()
    for segment, section, content in sections:
        if section in _IDENTITY_SECTIONS:
            continue
        digest.update(f"{segment},{section},{len(content)}\0".encode())
        digest.update(content)
    return digest.hexdigest()


if __name__ == "__main__":
    import json

    if len(sys.argv) != 3:
        print("usage: emitted_size.py <linker map> <program output directory>", file=sys.stderr)
        sys.exit(2)
    print(json.dumps(measure_map(sys.argv[1], sys.argv[2]), indent=1, sort_keys=True))
