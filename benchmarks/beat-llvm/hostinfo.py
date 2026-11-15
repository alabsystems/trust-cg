#!/usr/bin/env python3
"""benchmarks/beat-llvm/hostinfo.py — CPU identity, feature summary and core
affinity for performance provenance.

metrics-contract.md requires the host model and stated CPU policies, and the
perf ratchet keys same-host comparisons on `host_model`. A hostname is not a
CPU model: it says nothing about the silicon a ratio was measured on, and it
changes with the box's name, not its processor. These probes return the
processor as the kernel/firmware names it, with the source of each value, so a
reader can tell a detected value from a fallback. A board or machine name
(device-tree `model`, DMI product, `hw.model`) is recorded separately as
`machine_model` and never stands in for the CPU model.

Every probe returns ("", "unavailable") or ([], "unavailable") rather than a
guess when nothing can be read; the harness treats that as incomplete
provenance (not evidence), never as an eligible default.

Core pinning mirrors reports/perf/run_scaling.sh: on a big.LITTLE host the
scheduler alone gives a ~1.4x spread, so every lane is pinned to the SAME core,
chosen by that script's `pick_core` rule (the first `cpu_capacity` maximum in
sysfs glob order; core 0 when sysfs exposes no capacities). Pinning is opt-in
and the affinity policy is recorded in provenance either way.
"""

import hashlib
import os
import platform
import subprocess
from pathlib import Path

CPUINFO = Path("/proc/cpuinfo")
DEVICE_TREE_MODEL = Path("/proc/device-tree/model")
DMI_PRODUCT = Path("/sys/devices/virtual/dmi/id/product_name")
SYSFS_CPU = Path("/sys/devices/system/cpu")

# MIDR implementer and Arm Ltd part numbers, for kernels whose /proc/cpuinfo
# names no model (arm64 prints only these ids). Deliberately small: an id
# missing here is reported as its raw hex pair, never guessed, and every decoded
# name keeps its raw ids beside it so the decode stays auditable.
ARM_IMPLEMENTERS = {
    "0x41": "ARM", "0x42": "Broadcom", "0x43": "Cavium", "0x48": "HiSilicon",
    "0x4e": "NVIDIA", "0x51": "Qualcomm", "0x61": "Apple", "0xc0": "Ampere",
}
ARM_LTD_PARTS = {
    "0xd03": "Cortex-A53", "0xd04": "Cortex-A35", "0xd05": "Cortex-A55",
    "0xd07": "Cortex-A57", "0xd08": "Cortex-A72", "0xd09": "Cortex-A73",
    "0xd0a": "Cortex-A75", "0xd0b": "Cortex-A76", "0xd0c": "Neoverse-N1",
    "0xd0d": "Cortex-A77", "0xd40": "Neoverse-V1", "0xd41": "Cortex-A78",
    "0xd44": "Cortex-X1", "0xd46": "Cortex-A510", "0xd47": "Cortex-A710",
    "0xd48": "Cortex-X2", "0xd49": "Neoverse-N2", "0xd4d": "Cortex-A715",
    "0xd4e": "Cortex-X3", "0xd4f": "Neoverse-V2", "0xd80": "Cortex-A520",
    "0xd81": "Cortex-A720", "0xd82": "Cortex-X4", "0xd84": "Neoverse-V3",
    "0xd85": "Cortex-X925", "0xd87": "Cortex-A725", "0xd8e": "Neoverse-N3",
}


def _run(cmd, timeout=10, env=None):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
    except (OSError, subprocess.TimeoutExpired):
        return ""
    return r.stdout if r.returncode == 0 else ""


def _sysctl(name):
    return _run(["sysctl", "-n", name]).strip()


def _read(path):
    try:
        return Path(path).read_text(errors="replace")
    except OSError:
        return ""


def _cpuinfo_blocks(text):
    """/proc/cpuinfo as a list of {key: value} dicts, one per blank-line block."""
    blocks, cur = [], {}
    for line in text.splitlines():
        if not line.strip():
            if cur:
                blocks.append(cur)
                cur = {}
            continue
        key, sep, value = line.partition(":")
        if sep:
            cur.setdefault(key.strip(), value.strip())
    if cur:
        blocks.append(cur)
    return blocks


def _hex(value):
    try:
        return hex(int(value, 0))
    except (TypeError, ValueError):
        return None


# ---------- CPU model ----------
def cpu_model_from_cpuinfo(text):
    """(model, source) from /proc/cpuinfo text, or None when it names no CPU.

    x86 kernels print `model name`. arm64 kernels print only the MIDR
    implementer/part ids per core; every distinct core type is listed (in order
    of first appearance), so a heterogeneous host reads as e.g.
    "ARM Cortex-X925 [0x41:0xd85] + ARM Cortex-A725 [0x41:0xd87]". The `Model`
    line some boards add names the BOARD and is left to `machine_model`.
    """
    blocks = _cpuinfo_blocks(text)
    for block in blocks:
        name = block.get("model name", "")
        if name:
            return name, "/proc/cpuinfo model name"
    kinds = []
    for block in blocks:
        implementer, part = _hex(block.get("CPU implementer")), _hex(block.get("CPU part"))
        if implementer and part and (implementer, part) not in kinds:
            kinds.append((implementer, part))
    if not kinds:
        return None
    names = []
    for implementer, part in kinds:
        vendor = ARM_IMPLEMENTERS.get(implementer, f"implementer {implementer}")
        core = ARM_LTD_PARTS.get(part) if implementer == "0x41" else None
        names.append(f"{vendor} {core or 'part ' + part} [{implementer}:{part}]")
    return " + ".join(names), "/proc/cpuinfo CPU implementer/part"


def cpu_model_from_lscpu(text):
    """(model, source) from `lscpu` output; every distinct `Model name` (one per
    core cluster on a heterogeneous host), joined with " + "."""
    names = []
    for line in text.splitlines():
        key, _, value = line.partition(":")
        value = value.strip()
        if key.strip() == "Model name" and value and value != "-" and value not in names:
            names.append(value)
    return (" + ".join(names), "lscpu Model name") if names else None


def cpu_model(system=None, cpuinfo=None, lscpu=None, sysctl=None):
    """(cpu_model, source). The model is the processor's name, never a hostname
    and never a board/machine name."""
    system = system or platform.system()
    if system == "Darwin":
        brand = (sysctl or _sysctl)("machdep.cpu.brand_string")
        return (brand, "sysctl machdep.cpu.brand_string") if brand else ("", "unavailable")
    if system == "Linux":
        info = _read(CPUINFO) if cpuinfo is None else cpuinfo
        found = cpu_model_from_cpuinfo(info)
        if found and found[1] == "/proc/cpuinfo model name":
            return found
        # lscpu decodes more MIDR part numbers than the table above; prefer it
        # over the raw-id rendering when it is installed.
        # LC_ALL=C: lscpu localises its field names ("Modellname" under de_DE).
        if lscpu is None:
            lscpu = _run(["lscpu"], env={**os.environ, "LC_ALL": "C"})
        by_lscpu = cpu_model_from_lscpu(lscpu)
        return by_lscpu or found or ("", "unavailable")
    return "", "unavailable"


# ---------- CPU features ----------
def cpu_features_from_cpuinfo(text):
    """Sorted feature tokens common to EVERY core (`flags` on x86, `Features` on
    arm64), so a heterogeneous host lists only what all its cores support."""
    common = None
    for block in _cpuinfo_blocks(text):
        line = block.get("flags") or block.get("Features")
        if not line:
            continue
        tokens = set(line.split())
        common = tokens if common is None else common & tokens
    return sorted(common) if common else []


def cpu_features_from_sysctl(text):
    """Feature names from `sysctl hw.optional machdep.cpu` output: every
    `hw.optional.<name>: 1` (Apple silicon reports `hw.optional.arm.FEAT_*`
    and `hw.optional.<ext>`), plus the space-separated x86
    `machdep.cpu.features` / `leaf7_features` / `extfeatures` lists."""
    found = set()
    for line in text.splitlines():
        key, _, value = line.partition(":")
        key, value = key.strip(), value.strip()
        if key.startswith("hw.optional.") and value == "1":
            found.add(key[len("hw.optional."):])
        elif key in ("machdep.cpu.features", "machdep.cpu.leaf7_features",
                     "machdep.cpu.extfeatures"):
            found.update(value.split())
    return sorted(found)


def cpu_features(system=None, cpuinfo=None, sysctl_text=None):
    """(sorted feature list, source)."""
    system = system or platform.system()
    if system == "Darwin":
        text = _run(["sysctl", "hw.optional", "machdep.cpu"]) if sysctl_text is None else sysctl_text
        feats = cpu_features_from_sysctl(text)
        return feats, ("sysctl hw.optional / machdep.cpu" if feats else "unavailable")
    if system == "Linux":
        feats = cpu_features_from_cpuinfo(_read(CPUINFO) if cpuinfo is None else cpuinfo)
        return feats, ("/proc/cpuinfo flags/Features (common to all cores)" if feats
                       else "unavailable")
    return [], "unavailable"


def features_digest(features):
    """SHA-256 of the sorted feature list, one per line — a compact identity for
    ledger rows (the full list stays in the results JSON)."""
    return hashlib.sha256("\n".join(sorted(features)).encode()).hexdigest() if features else ""


def machine_model(system=None):
    """The box's product identity (e.g. Mac16,5, a device-tree or DMI product
    name), or "". Recorded beside the CPU model, never instead of it."""
    system = system or platform.system()
    if system == "Darwin":
        return _sysctl("hw.model")
    if system == "Linux":
        dt = _read(DEVICE_TREE_MODEL).replace("\x00", "").strip()
        if dt:
            return dt
        dmi = _read(DMI_PRODUCT).strip()
        if dmi:
            return dmi
        for block in _cpuinfo_blocks(_read(CPUINFO)):
            if block.get("Model"):
                return block["Model"]
    return ""


# ---------- core topology and affinity ----------
def read_cpu_capacities(sysfs=SYSFS_CPU):
    """{cpu_index: cpu_capacity} for every cpuN exposing the sysfs attribute."""
    caps = {}
    try:
        entries = list(Path(sysfs).glob("cpu[0-9]*"))
    except OSError:
        return caps
    for d in entries:
        try:
            caps[int(d.name[3:])] = int((d / "cpu_capacity").read_text().strip())
        except (OSError, ValueError):
            continue
    return caps


def pick_core(capacities):
    """(core, selection note) by reports/perf/run_scaling.sh's `pick_core` rule.

    That function walks `/sys/devices/system/cpu/cpu[0-9]*` in glob order
    (lexicographic: cpu0, cpu1, cpu10, ..., cpu2) and keeps a core only when its
    capacity is STRICTLY greater than the best so far, starting from core 0 /
    capacity 0. The same walk is reproduced here so both harnesses land on the
    same core on the same host.
    """
    if not capacities:
        return 0, "no cpu_capacity in sysfs; core 0 (reports/perf/run_scaling.sh default)"
    best_cpu, best_cap = 0, 0
    for cpu in sorted(capacities, key=lambda c: f"cpu{c}"):
        if capacities[cpu] > best_cap:
            best_cpu, best_cap = cpu, capacities[cpu]
    distinct = sorted(set(capacities.values()))
    kind = "heterogeneous (big.LITTLE)" if len(distinct) > 1 else "homogeneous"
    return best_cpu, (f"cpu_capacity {best_cap}, the first maximum of {distinct} in sysfs "
                      f"glob order ({kind}); reports/perf/run_scaling.sh pick_core")


def core_topology(system=None, capacities=None, sysctl=None):
    """Whether the host mixes core types, and the evidence for that answer."""
    system = system or platform.system()
    if system == "Linux":
        caps = read_cpu_capacities() if capacities is None else capacities
        if not caps:
            return {"heterogeneous": None, "source": "no cpu_capacity in sysfs"}
        distinct = sorted(set(caps.values()))
        return {"heterogeneous": len(distinct) > 1,
                "source": f"sysfs cpu_capacity values {distinct}"}
    if system == "Darwin":
        levels = (sysctl or _sysctl)("hw.nperflevels")
        try:
            count = int(levels)
        except ValueError:
            return {"heterogeneous": None, "source": "sysctl hw.nperflevels unavailable"}
        return {"heterogeneous": count > 1, "source": f"sysctl hw.nperflevels {count}"}
    return {"heterogeneous": None, "source": "unavailable"}


def unpinned_record(topology=None):
    """The affinity record when no pin was requested: the scheduler chooses."""
    topology = topology or {"heterogeneous": None, "source": "not probed"}
    return {"policy": "none", "core": None, "method": None, "selection": None,
            "cpu_capacity": None, "heterogeneous": topology["heterogeneous"],
            "topology_source": topology["source"]}


def pin_core(requested="auto", capacities=None, setaffinity=None, getaffinity=None):
    """Pin this process (and every subprocess it later spawns) to one core and
    return the affinity record for provenance.

    Raises RuntimeError when the platform cannot pin or the kernel does not
    report the requested mask afterwards: the caller must fail closed rather
    than record a pin that did not happen.
    """
    setaffinity = setaffinity if setaffinity is not None else getattr(os, "sched_setaffinity", None)
    getaffinity = getaffinity if getaffinity is not None else getattr(os, "sched_getaffinity", None)
    if setaffinity is None or getaffinity is None:
        raise RuntimeError("core pinning is unsupported here: os.sched_setaffinity is unavailable "
                           "(Linux only; macOS exposes no core-affinity API). Drop --pin-core or "
                           "measure on the Linux target host")
    caps = read_cpu_capacities() if capacities is None else capacities
    if requested == "auto":
        core, selection = pick_core(caps)
    else:
        try:
            core = int(requested)
        except (TypeError, ValueError):
            raise RuntimeError(f"--pin-core expects a core number or no value, got {requested!r}") from None
        if core < 0:
            raise RuntimeError(f"--pin-core expects a non-negative core number, got {core}")
        selection = "explicit --pin-core"
    try:
        setaffinity(0, {core})
        actual = set(getaffinity(0))
    except (OSError, ValueError) as error:
        raise RuntimeError(f"cannot pin to core {core}: {error}") from None
    if actual != {core}:
        raise RuntimeError(f"pinned to core {core} but the kernel reports affinity {sorted(actual)}")
    distinct = set(caps.values())
    return {
        "policy": "pinned",
        "core": core,
        "method": f"os.sched_setaffinity(0, {{{core}}}) in the harness process before any lane "
                  "runs; every lane subprocess (both compilers, both binaries, the RSS wrapper) "
                  "inherits the mask",
        "selection": selection,
        "cpu_capacity": caps.get(core),
        "heterogeneous": (len(distinct) > 1) if caps else None,
        "topology_source": (f"sysfs cpu_capacity values {sorted(distinct)}" if caps
                            else "no cpu_capacity in sysfs"),
    }


def legacy_host_identity():
    """The value the harness stamped as `host_model` before it named the CPU:
    `sysctl -n hw.model` (a Mac's product id), else the hostname (every Linux
    row, e.g. the DGX Spark rows' "spark-d5a4"). Recorded only so the perf
    ratchet can keep comparing a new row with the committed baselines keyed on
    that identity; it is never the CPU model and never required provenance."""
    return _sysctl("hw.model") or platform.node()


def host_provenance():
    """CPU identity fields shared by the beat-llvm harnesses."""
    model, model_source = cpu_model()
    features, features_source = cpu_features()
    return {
        "host_model": model,
        "host_model_source": model_source,
        "host_name": platform.node(),
        "machine_model": machine_model(),
        "legacy_host_model": legacy_host_identity(),
        "cpu_features": features,
        "cpu_features_source": features_source,
        "cpu_features_sha256": features_digest(features),
    }


# ---------- CPU policy of the compared trustc lanes ----------
def _codegen_option(cmd, name):
    """Every value of `-C<name>=` / `-C <name>=` in a trustc command, in order."""
    values = []
    for i, tok in enumerate(cmd):
        if tok.startswith(f"-C{name}="):
            values.append(tok.split("=", 1)[1])
        elif tok == "-C" and i + 1 < len(cmd) and cmd[i + 1].startswith(f"{name}="):
            values.append(cmd[i + 1].split("=", 1)[1])
    return values


def parse_default_target_cpu(text):
    """The CPU `trustc --print target-cpus` marks as the target's default, or None."""
    for line in text.splitlines():
        if "default target CPU" in line and line.split():
            return line.split()[0]
    return None


def parse_cfg_target_features(text):
    """Sorted `target_feature="…"` values from `trustc --print cfg`, or None."""
    feats = sorted({line.split("=", 1)[1].strip().strip('"') for line in text.splitlines()
                    if line.startswith("target_feature=")})
    return feats or None


def cpu_policy_from_cmds(llvm_cmd, bridge_cmd):
    """The CPU policy both lanes were ACTUALLY given, read off their commands.

    "default" means no `-C target-cpu` / `-C target-feature` was passed, i.e.
    the target triple's baseline CPU for both backends. Lane parity holds when
    the bridge command is the LLVM command plus only its `-Zcodegen-backend`
    flag — the contract's "same target and stated CPU policies" as a checked
    fact rather than a sentence.
    """
    cpus = _codegen_option(llvm_cmd, "target-cpu")
    feats = _codegen_option(llvm_cmd, "target-feature")
    extra = [t for t in bridge_cmd if t not in llvm_cmd]
    missing = [t for t in llvm_cmd if t not in bridge_cmd]
    parity = not missing and all(t.startswith("-Zcodegen-backend=") for t in extra)
    return {
        "target_cpu": ",".join(cpus) if cpus else "default",
        "target_feature": ",".join(feats) if feats else "default",
        "lane_parity": parity,
        "bridge_extra_flags": extra,
        "llvm_only_flags": missing,
        "source": "derived from each lane's compile command",
        "statement": (
            ("Both lanes receive the identical trustc command except -Zcodegen-backend. "
             if parity else "LANE COMMANDS DIFFER beyond -Zcodegen-backend (see the flag lists). ")
            + ("No -C target-cpu / -C target-feature is passed: the LLVM lane compiles for the "
               "target's default CPU (llvm_default_target_cpu); the trust-cg lane selects "
               "instructions by its own per-target ISA profile (AArch64: "
               "AArch64IsaProfile::for_aot_target in crates/trust-cg-codegen/src/target.rs)."
               if not cpus and not feats else
               "Explicit -C target-cpu / -C target-feature values are passed (target_cpu, "
               "target_feature); whether the trust-cg lane honours them is not established "
               "by this record.")),
    }
