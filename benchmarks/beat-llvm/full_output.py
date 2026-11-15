#!/usr/bin/env python3
"""Bounded complete-state controls for actual c84 benchmark kernels.

Original fixtures and measured binaries are unchanged. Generated validation
clones have separate identities and grant no performance or formal authority.
"""

import hashlib
import json
import re
from pathlib import Path

MANIFEST_SHA256 = "25c1bd79b6efb728e0d307e60b22f283d636e1decc6f2bf86d9dd6232e368a40"
BASE_REVISION = "c84d39e930b1030794a61a6e37abefc95fcf1532"
LANES = ("llvm", "bridge", "clang")
U64_MAX = (1 << 64) - 1
TRANSPORT = (0, 1, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF,
             0x8000000000000000, U64_MAX)
SUPPORTED = {
    "p1_xorshift": {
        "fields": ("x", "acc"), "values": ("x", "acc"), "checksum": "acc",
        "rust_sha256": "d078806cd0d7854031c737fb012066a11ca3125d2afcee2e1501c1b06be871aa",
        "c_sha256": "a5ff6afaa42d74186f602929659f1123a45d25b835e0730316a02ca22485f761",
        "rust_stop": "    done(acc);", "c_stop": "    exit((int)(acc % 126));",
        "iterations": 400_000_000,
    },
    "p3_gcd": {
        "fields": ("s", "acc"), "values": ("s", "acc"), "checksum": "acc",
        "rust_sha256": "e285fc82a61edd8d6b3164d2e9770cf2867dcc562111aeb069118adf6186b87c",
        "c_sha256": "b137d5da263cbd74e4c8e8f3028ce433bee5867ace55f9640e5b148d9b705cbd",
        "rust_stop": "    done(acc);", "c_stop": "    exit((int)(acc % 126));",
        "iterations": 4_000_000,
    },
    "p5_struct_acc": {
        "fields": ("a", "b", "c"), "values": ("st.a", "st.b", "st.c"),
        "checksum": "(st.a ^ st.b ^ st.c)",
        "rust_sha256": "e5221d2560df371b49f7d34a4b6d4ccb5c638483a41b38475f2073922fa9d086",
        "c_sha256": "ae68caec8b9f9c878c9b5c3fef1908e076665c167f3b940ed9e9f3fce085d658",
        "rust_stop": "    done((st.a ^ st.b ^ st.c));",
        "c_stop": "    exit((int)((st.a ^ st.b ^ st.c) % 126));",
        "iterations": 300_000_000,
    },
}
RUST_DONE = "fn done(code: u64) -> ! {\n    std::process::exit((code % 126) as i32)\n}"
UNSUPPORTED_REASONS = {
    "p2_collatz": "per-input step counts and termination/overflow controls have not been exposed",
    "p4_matmul": "complete final matrix/storage state and signed wrapping carrier controls are pending",
    "p6_branch_match": "seven-way enum dispatch, every rotation arm and full final state controls are pending",
    "p7_sieve": "complete 1024-byte sieve image and count/start-position controls are pending",
    "p8_closure_nest": "captured-closure/nested-loop state and source/C carrier equivalence controls are pending",
    "v1_saxpy": "complete i32 array images and signed-to-u32 output transport controls are pending",
    "v2_memfill": "complete 8192-byte output image and fill/probe range controls are pending",
    "v3_popcount": "complete byte image and popcount/mutation state controls are pending",
    "h1_vec_push_sum": "no existing C port; complete Vec allocation/growth/storage state controls are pending",
    "h2_vec_grow": "no existing C port; complete Vec reallocation/read/storage state controls are pending",
    "h3_box_leak": "no existing C port; complete Box/Vec pointer, allocation and storage controls are pending",
    "h4_vec_dropper": "no existing C port; complete drop/deallocation/lifetime controls are pending",
    "m1_call_chain": "complete call-chain state and source/C scalar call transport controls are pending",
    "m2_call_heavy": "complete non-inlined call state and source/C scalar ABI transport controls are pending",
    "b1_mispredict": "complete 16-word scratch image and per-arm store/rotation controls are pending",
}


class OutputError(ValueError):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load_manifest(here):
    here = Path(here)
    data = (here / "progs" / "manifest.json").read_bytes()
    if digest(data) != MANIFEST_SHA256:
        raise OutputError("original manifest differs from the sealed 18-program corpus")
    programs = json.loads(data)["programs"]
    if len(programs) != 18 or set(programs) != {p.stem for p in (here / "progs").glob("*.rs")}:
        raise OutputError("original corpus/manifest membership differs")
    if not set(SUPPORTED).issubset(programs):
        raise OutputError("supported kernel is absent from the original corpus")
    return programs


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise OutputError("exact source boundary is missing or ambiguous")
    return text.replace(old, new, 1)


def rust_emitter(stem, fields):
    names = [f"u{index}" for index in range(len(TRANSPORT))] + list(fields)
    pattern = "TCG-BENCH-OUTPUT-V1 " + stem + " " + " ".join(name + "={:016x}" for name in names)
    values = [f"0x{value:016x}u64" for value in TRANSPORT]
    values.extend(f"values[{index}]" for index in range(len(fields)))
    return ("#[cfg(not(target_endian = \"little\"))]\n"
            "compile_error!(\"full-output scope requires little endian\");\n"
            "const _: [(); 8] = [(); std::mem::size_of::<u64>()];\n"
            "const _: [(); 8] = [(); std::mem::size_of::<usize>()];\n"
            f"fn oracle_output(code: u64, values: [u64; {len(fields)}]) -> ! {{\n"
            f"    println!(\"{pattern}\", {', '.join(values)});\n"
            "    std::process::exit((code % 126) as i32)\n}")


def c_emitter(stem, fields):
    names = [f"u{index}" for index in range(len(TRANSPORT))] + list(fields)
    pattern = '"TCG-BENCH-OUTPUT-V1 ' + stem
    pattern += "".join(' ' + name + '=%016" PRIx64 "' for name in names)
    pattern += '\\n"'
    values = [f"UINT64_C(0x{value:016x})" for value in TRANSPORT]
    values.extend(f"values[{index}]" for index in range(len(fields)))
    return ("\n#include <inttypes.h>\n#include <stdio.h>\n#include <limits.h>\n"
            "#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__\n"
            "#error full-output scope requires little endian\n#endif\n"
            "_Static_assert(CHAR_BIT == 8 && sizeof(uint64_t) == 8 && sizeof(uintptr_t) == 8,\n"
            "               \"full-output scope requires 64-bit carriers\");\n"
            "static void oracle_output(uint64_t code, const uint64_t *values) {\n"
            f"    if (printf({pattern}, {', '.join(values)}) < 0 || fflush(stdout) != 0) exit(127);\n"
            "    exit((int)(code % 126));\n}\n")


def render_validation(stem, language, data):
    if stem not in SUPPORTED or language not in ("rust", "c"):
        raise OutputError("kernel/language is outside the three-kernel scope")
    spec = SUPPORTED[stem]
    if digest(data) != spec[language + "_sha256"]:
        raise OutputError(f"{stem}: original {language} source differs from the sealed kernel")
    text = data.decode("utf-8")
    fields, values = spec["fields"], spec["values"]
    if language == "rust":
        text = replace_once(text, RUST_DONE, rust_emitter(stem, fields))
        call = f"    oracle_output({spec['checksum']}, [{', '.join(values)}]);"
    else:
        text = replace_once(text, "#include <stdlib.h>", "#include <stdlib.h>" + c_emitter(stem, fields))
        call = f"    oracle_output({spec['checksum']}, (uint64_t[]){{{', '.join(values)}}});"
    return replace_once(text, spec[language + "_stop"], call).encode("utf-8")


def output_bytes(stem, state):
    """Control serializer; compiler outputs are checked by the strict reader."""
    fields = SUPPORTED[stem]["fields"]
    if len(state) != len(fields) or any(type(value) is not int or not 0 <= value <= U64_MAX for value in state):
        raise OutputError("state has a wrong arity or a non-u64 field")
    names = [f"u{index}" for index in range(len(TRANSPORT))] + list(fields)
    values = TRANSPORT + tuple(state)
    return ("TCG-BENCH-OUTPUT-V1 " + stem + " " + " ".join(
        f"{name}={value:016x}" for name, value in zip(names, values)) + "\n").encode("ascii")


def checksum(stem, state):
    return state[0] ^ state[1] ^ state[2] if stem == "p5_struct_acc" else state[1]


def decode_output(stem, stdout, stderr, returncode, expected_exit):
    if stem not in SUPPORTED:
        raise OutputError("unsupported kernel")
    if stderr:
        raise OutputError("program stderr is nonempty")
    names = [f"u{index}" for index in range(len(TRANSPORT))] + list(SUPPORTED[stem]["fields"])
    prefix = b"TCG-BENCH-OUTPUT-V1 " + stem.encode("ascii")
    pattern = re.escape(prefix) + b"".join(
        b" " + name.encode("ascii") + b"=([0-9a-f]{16})" for name in names) + b"\n"
    found = re.fullmatch(pattern, stdout)
    if found is None:
        raise OutputError("stdout is not exactly one complete canonical fixed-width state record")
    values = tuple(int(value, 16) for value in found.groups())
    if values[:len(TRANSPORT)] != TRANSPORT:
        raise OutputError("known full-width unsigned output transport control differs")
    state = values[len(TRANSPORT):]
    if type(returncode) is not int or not 0 <= returncode < 126:
        raise OutputError("program did not complete with a normal benchmark exit residue")
    if returncode != expected_exit or returncode != checksum(stem, state) % 126:
        raise OutputError("exit residue differs from the original manifest or the full returned state")
    return state


def compare_lanes(states):
    """Three complete lanes and every repeat must agree on each state field."""
    if set(states) != {"llvm", "bridge", "clang"}:
        return False
    records = [state for lane in ("llvm", "bridge", "clang") for state in states[lane]]
    return (all(len(states[lane]) >= 3 for lane in states)
            and bool(records) and all(state == records[0] for state in records))


def empty_accounting(manifest):
    """Every original row remains; unsupported output scope is visible."""
    return {stem: {"category": row["category"], "expected_exit": row["expected_exit"],
                   "scope_supported": stem in SUPPORTED,
                   "verdict": "INCOMPLETE" if stem in SUPPORTED else "UNSUPPORTED",
                   "reason": "qualification has not run" if stem in SUPPORTED else UNSUPPORTED_REASONS[stem],
                   "lanes": {lane: {"status": "NOT_RUN" if stem in SUPPORTED else "UNSUPPORTED"}
                             for lane in LANES}}
            for stem, row in manifest.items()}


def counts(programs):
    return {"original_denominator": len(programs),
            "supported_count": sum(row["scope_supported"] for row in programs.values()),
            "unsupported_count": sum(row["verdict"] == "UNSUPPORTED" for row in programs.values()),
            "full_output_agreement_count": sum(row["verdict"] == "FULL_OUTPUT_AGREEMENT" for row in programs.values()),
            "incomplete_count": sum(row["verdict"] == "INCOMPLETE" for row in programs.values()),
            "mismatch_count": sum(row["verdict"] == "MISMATCH" for row in programs.values())}
