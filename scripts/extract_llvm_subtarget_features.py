#!/usr/bin/env python3
"""Extract, from an LLVM source tree, the subtarget feature and processor
tables the LLVM importer's mode-feature refusal is derived from.

The importer refuses a `+feature` among `MODE_FEATURE_PREFIXES`
(`crates/trust-cg-llvm-import/src/attributes.rs`), and a `+feature`,
`"target-cpu"` or `"tune-cpu"` whose features imply one: llc sets every
feature a `+feature` implies (`SubtargetFeatures::ApplyFeatureFlag`, closed
under `Implies`) and every feature and tuning feature a processor lists. The
unit test `attributes::tests::mode_implying_tables_are_the_closure_of_llvms_tables`
re-derives `MODE_IMPLYING_FEATURES` and `MODE_IMPLYING_PROCESSORS` from the
extract this script writes; this script reproduces the extract from LLVM's
TableGen sources.

For each of the AArch64, X86 and RISCV targets, `llvm-tblgen --dump-json` of
the target's `.td` file is read, and the extract records:

- `features`: every `SubtargetFeature` record, by its `Name` (the spelling
  of `+name`), with the names its `Implies` list holds;
- `processors`: every `Processor` record (`ProcessorModel` and the targets'
  subclasses are `Processor`s), by its `Name`, with the names of its
  `Features` and `TuneFeatures` lists (a name with several records keeps
  each one);
- `aliases`: every `ProcessorAlias`, by its `Name`, with the processor name
  it stands for.

Usage:
  extract_llvm_subtarget_features.py --llvm-project DIR --tblgen PATH (--write | --check)

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
OUT = ROOT / "crates/trust-cg-llvm-import/tests/fixtures/llvm22_subtarget_features.json"
TARGETS = ("AArch64", "RISCV", "X86")


def dump(tblgen: str, llvm: Path, target: str) -> dict:
    target_dir = llvm / "lib" / "Target" / target
    with tempfile.TemporaryDirectory() as scratch:
        out = Path(scratch) / f"{target}.json"
        subprocess.run(
            [tblgen, "--dump-json", "-I", str(llvm / "include"), "-I", str(target_dir),
             str(target_dir / f"{target}.td"), "-o", str(out)],
            check=True,
        )
        with open(out, encoding="utf-8") as handle:
            return json.load(handle)


def extract(records: dict) -> dict:
    def is_a(value, superclass):
        return isinstance(value, dict) and superclass in value.get("!superclasses", [])

    names = {record: value["Name"] for record, value in records.items()
             if not record.startswith("!") and is_a(value, "SubtargetFeature")}

    def feature_names(value, field):
        return sorted(names[entry["def"]] for entry in value.get(field, []))

    features, processors, aliases = {}, {}, {}
    for record, value in records.items():
        if record.startswith("!"):
            continue
        if is_a(value, "SubtargetFeature"):
            name = value["Name"]
            if name in features:
                raise SystemExit(f"two SubtargetFeature records named {name!r}")
            features[name] = feature_names(value, "Implies")
        elif is_a(value, "Processor"):
            processors.setdefault(value["Name"], []).append({
                "features": feature_names(value, "Features"),
                "tune": feature_names(value, "TuneFeatures"),
            })
        elif is_a(value, "ProcessorAlias"):
            aliases[value["Name"]] = value["Alias"]
    return {"features": features, "processors": processors, "aliases": aliases}


def render(tables: dict) -> str:
    """One feature, processor or alias per line, keys sorted."""
    lines = ["{", '  "targets": {']
    for t_index, target in enumerate(sorted(tables)):
        lines.append(f"    {json.dumps(target)}: {{")
        sections = tables[target]
        for s_index, section in enumerate(("aliases", "features", "processors")):
            entries = sections[section]
            lines.append(f"      {json.dumps(section)}: {{")
            for e_index, name in enumerate(sorted(entries)):
                comma = "," if e_index + 1 < len(entries) else ""
                lines.append(f"        {json.dumps(name)}: {json.dumps(entries[name])}{comma}")
            lines.append("      }" + ("," if s_index < 2 else ""))
        lines.append("    }" + ("," if t_index + 1 < len(tables) else ""))
    lines.append("  }")
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
    text = render({target: extract(dump(args.tblgen, llvm, target)) for target in TARGETS})
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
