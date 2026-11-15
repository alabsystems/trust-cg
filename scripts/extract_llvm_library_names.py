#!/usr/bin/env python3
"""Extract, from an LLVM source tree, the library-name and intrinsic tables the
LLVM importer's name refusals are derived from.

The importer refuses a module that defines a function or global under a name
llc's code generator calls or replaces on its own
(`crates/trust-cg-llvm-import/src/parser.rs`, `LLC_LIBRARY_NAMES` and
`src/llvm_runtime_libcalls.rs`), and reads an overloaded intrinsic only under
the name LLVM gives its types (`OVERLOADED_INTRINSICS`). The unit tests
`parser::tests::runtime_libcall_table_is_llvms_aarch64_system_library`,
`parser::tests::library_name_table_is_complete` and
`parser::tests::overloaded_intrinsic_table_is_complete` re-derive those
tables from the extract this script writes; this script reproduces the
extract from LLVM's TableGen sources.

`llvm-tblgen --dump-json` is run on three files, and the extract records:

- `runtime_libcalls` (`llvm/IR/RuntimeLibcalls.td`): the member list of the
  `AArch64SystemLibrary` record, the runtime library calls llc's AArch64
  code generator may call, as `sets` (every `LibcallImpls` or
  `LibcallsWithCC` record the list reaches, with its availability predicate
  and members; a nested `(add ...)` or list is flattened into its set) and
  `impls` (every `RuntimeLibcallImpl` reached, with its `LibCallFuncName`);
- `target_library_calls` (`llvm/Analysis/TargetLibraryInfo.td`): every
  `TargetLibCall` record with the function name it stands for;
- `intrinsics` (`llvm/IR/Intrinsics.td`): every target-independent
  overloaded intrinsic, by its name, with its number of results and the
  positions (in its result types, then its parameter types) of its
  overloaded types in the order LLVM writes them into the name.

A set operator other than `add` is refused, as is a record in a member list
that is neither a set nor an impl.

Usage:
  extract_llvm_library_names.py --llvm-project DIR --tblgen PATH (--write | --check)

`--write` writes the extract; `--check` compares it with the committed one
and exits 1 when they differ. The committed extract was written from LLVM
22.1.2 as Trust ae9c2c1da builds it (`src/llvm-project` tree 11b2938808).
"""
import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "crates/trust-cg-llvm-import/tests/fixtures/llvm22_library_names.json"
SYSTEM_LIBRARY = "AArch64SystemLibrary"


def dump(tblgen: str, llvm: Path, td: str) -> dict:
    with tempfile.TemporaryDirectory() as scratch:
        out = Path(scratch) / "dump.json"
        subprocess.run(
            [tblgen, "--dump-json", "-I", str(llvm / "include"), str(llvm / "include" / td),
             "-o", str(out)],
            check=True,
        )
        with open(out, encoding="utf-8") as handle:
            return json.load(handle)


def superclasses(records: dict, name: str) -> list:
    return records[name].get("!superclasses", [])


def runtime_libcalls(records: dict) -> dict:
    sets, impls = {}, {}

    def members_of(node, out):
        if isinstance(node, list):
            for item in node:
                members_of(item, out)
            return
        if not isinstance(node, dict):
            raise SystemExit(f"unexpected member {node!r}")
        if node.get("kind") == "dag":
            operator = node["operator"]["def"]
            if operator != "add":
                raise SystemExit(f"set operator {operator!r} is not read")
            for arg in node["args"]:
                members_of(arg[0], out)
            return
        if node.get("kind") != "def":
            raise SystemExit(f"unexpected member {node!r}")
        record = node["def"]
        classes = superclasses(records, record)
        if "RuntimeLibcallImpl" in classes:
            impls[record] = records[record]["LibCallFuncName"]
        elif "LibcallImpls" in classes or "LibcallsWithCC" in classes:
            visit_set(record)
        else:
            raise SystemExit(f"member {record} is neither a set nor an impl: {classes}")
        out.append(record)

    def visit_set(record):
        if record in sets:
            return
        sets[record] = None
        predicate = records[record].get("AvailabilityPredicate")
        members = []
        members_of(records[record]["MemberList"], members)
        sets[record] = {
            "predicate": predicate["def"] if predicate else "AlwaysAvailable",
            "members": members,
        }

    root = records[SYSTEM_LIBRARY]["MemberList"]["def"]
    visit_set(root)
    return {"system_library": SYSTEM_LIBRARY, "root": root, "sets": sets, "impls": impls}


def target_library_calls(records: dict) -> dict:
    return {name: value["String"] for name, value in records.items()
            if not name.startswith("!") and "TargetLibCall" in value.get("!superclasses", [])}


def intrinsics(records: dict) -> dict:
    out = {}
    for record, value in records.items():
        if record.startswith("!") or "Intrinsic" not in value.get("!superclasses", []):
            continue
        if value["TargetPrefix"] != "":
            continue
        info = records[value["TypeInfo"]["def"]]
        if not info["isOverloaded"]:
            continue
        name = value["LLVMName"] or "llvm." + record.removeprefix("int_").replace("_", ".")
        positions = sorted((index, position)
                           for position, index in enumerate(info["ACIdxs"]) if index is not None)
        if [index for index, _ in positions] != list(range(len(positions))):
            raise SystemExit(f"{name}: overload indices {info['ACIdxs']} are not 0..n")
        if name in out:
            raise SystemExit(f"two intrinsics named {name!r}")
        out[name] = {"results": len(value["RetTypes"]),
                     "overloads": [position for _, position in positions]}
    return out


def render(tables: dict) -> str:
    """One entry per line, keys sorted."""
    lines = ["{"]
    sections = list(tables)
    for s_index, section in enumerate(sections):
        value = tables[section]
        lines.append(f"  {json.dumps(section)}: {{")
        if section == "runtime_libcalls":
            for key in ("system_library", "root"):
                lines.append(f"    {json.dumps(key)}: {json.dumps(value[key])},")
            for k_index, key in enumerate(("impls", "sets")):
                entries = value[key]
                lines.append(f"    {json.dumps(key)}: {{")
                for e_index, name in enumerate(sorted(entries)):
                    comma = "," if e_index + 1 < len(entries) else ""
                    lines.append(f"      {json.dumps(name)}: {json.dumps(entries[name])}{comma}")
                lines.append("    }" + ("," if k_index == 0 else ""))
        else:
            for e_index, name in enumerate(sorted(value)):
                comma = "," if e_index + 1 < len(value) else ""
                lines.append(f"    {json.dumps(name)}: {json.dumps(value[name])}{comma}")
        lines.append("  }" + ("," if s_index + 1 < len(sections) else ""))
    lines.append("}")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--llvm-project", required=True, type=Path)
    parser.add_argument("--tblgen", required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    llvm = args.llvm_project / "llvm"
    text = render({
        "intrinsics": intrinsics(dump(args.tblgen, llvm, "llvm/IR/Intrinsics.td")),
        "runtime_libcalls": runtime_libcalls(
            dump(args.tblgen, llvm, "llvm/IR/RuntimeLibcalls.td")),
        "target_library_calls": target_library_calls(
            dump(args.tblgen, llvm, "llvm/Analysis/TargetLibraryInfo.td")),
    })
    if args.write:
        OUT.write_text(text, encoding="utf-8")
        print(f"wrote {OUT.relative_to(ROOT)}")
        return 0
    if OUT.read_text(encoding="utf-8") != text:
        print(f"{OUT.relative_to(ROOT)} differs from this LLVM's tables; review and rerun "
              "with --write", file=sys.stderr)
        return 1
    print(f"{OUT.relative_to(ROOT)} matches this LLVM's tables")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
