#!/usr/bin/env python3
"""Execute TrustCG x86-64 multi-result objects under the Unicorn x86-64 emulator.

Input: the directory written by
  TRUST_CG_X86_MULTI_RESULT_ARTIFACTS=<dir> cargo test -p trust-cg-codegen \
      --test e2e_x86_64_internal_multi_result internal_multi_results_execute_exactly_at_every_level
(one Mach-O x86-64 object per shape and optimization level, layout.txt and
expected.txt, the expected bytes computed in Rust by the test, never by TrustCG).

For each optimization level the objects are linked by the host C driver
(`cc -arch x86_64`, link only; nothing is run natively), the linked image's
segments are mapped into Unicorn, and:

  * every C wrapper call the Rosetta lane makes (direct and indirect, four
    seeds, two chained multi-result calls each, twelve live values) is executed
    and its output buffer and counter compared byte-for-byte; and
  * every multi-result CALLEE is entered directly and its result REGISTERS are
    read in the documented internal order (RAX,RDX,RCX,RSI,RDI,R8,R9 /
    XMM0-XMM7) and compared with the expected result bytes -- the callee half
    observed with no TrustCG caller in between;
  * NEGATIVE CONTROL: the same callee registers read in the System V ARGUMENT
    order past RAX,RDX (RDI,RSI,RCX,R8,R9, i.e. a plausible wrong convention)
    must MISMATCH for every shape that reaches RSI/RDI, or the register check
    proves nothing.

Requires: pip install unicorn (2.x); an Apple `cc` able to link x86_64.
"""
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

from unicorn import Uc, UC_ARCH_X86, UC_MODE_64, UcError, UC_PROT_ALL
from unicorn import x86_const as X

OPTS = ["O0", "O1", "O2", "O3"]
PAGE = 0x1000
STACK_TOP = 0x7FFF_0000
STACK_SIZE = 0x10_0000
DATA_BASE = 0x6000_0000
SENTINEL = 0x5000_0000

GPR = {
    "rax": X.UC_X86_REG_RAX, "rdx": X.UC_X86_REG_RDX, "rcx": X.UC_X86_REG_RCX,
    "rsi": X.UC_X86_REG_RSI, "rdi": X.UC_X86_REG_RDI, "r8": X.UC_X86_REG_R8,
    "r9": X.UC_X86_REG_R9, "r10": X.UC_X86_REG_R10, "r11": X.UC_X86_REG_R11,
}
XMM = [getattr(X, f"UC_X86_REG_XMM{i}") for i in range(16)]
ARG_REGS = [X.UC_X86_REG_RDI, X.UC_X86_REG_RSI, X.UC_X86_REG_RDX,
            X.UC_X86_REG_RCX, X.UC_X86_REG_R8, X.UC_X86_REG_R9]

TYPE_BYTES = {"I64": 8, "U64": 8, "I32": 4, "U32": 4, "I16": 2, "I8": 1,
              "Bool": 1, "F64": 8, "F32": 4, "I128": 16}


def align_down(x):
    return x & ~(PAGE - 1)


def align_up(x):
    return (x + PAGE - 1) & ~(PAGE - 1)


def macho_segments(path):
    data = Path(path).read_bytes()
    magic, _cpu, _sub, _ftype, ncmds, _size, _flags, _res = struct.unpack_from("<IiiIIIII", data, 0)
    assert magic == 0xFEEDFACF, "not a 64-bit Mach-O"
    off = 32
    segs = []
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from("<II", data, off)
        if cmd == 0x19:  # LC_SEGMENT_64
            segname = data[off + 8:off + 24].rstrip(b"\0").decode()
            vmaddr, vmsize, fileoff, filesize = struct.unpack_from("<QQQQ", data, off + 24)
            if segname != "__PAGEZERO" and vmsize:
                segs.append((segname, vmaddr, vmsize, data[fileoff:fileoff + filesize]))
        off += cmdsize
    return segs


def symbols(path):
    out = subprocess.run(["nm", "--defined-only", str(path)], check=True,
                         capture_output=True, text=True).stdout
    table = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3:
            table[parts[2].lstrip("_")] = int(parts[0], 16)
    return table


class Machine:
    def __init__(self, image):
        self.uc = Uc(UC_ARCH_X86, UC_MODE_64)
        for _name, vmaddr, vmsize, content in macho_segments(image):
            base = align_down(vmaddr)
            self.uc.mem_map(base, align_up(vmaddr + vmsize) - base, UC_PROT_ALL)
            self.uc.mem_write(vmaddr, content)
        self.uc.mem_map(STACK_TOP - STACK_SIZE, STACK_SIZE, UC_PROT_ALL)
        self.uc.mem_map(DATA_BASE, 0x10_0000, UC_PROT_ALL)
        self.uc.mem_map(SENTINEL, PAGE, UC_PROT_ALL)
        self.uc.mem_write(SENTINEL, b"\xcc" * PAGE)
        self.sym = symbols(image)

    def call(self, name_or_addr, args):
        uc = self.uc
        addr = self.sym[name_or_addr] if isinstance(name_or_addr, str) else name_or_addr
        # Poison every caller-saved register a result could be read from, so a
        # stale value can never pass for a result.
        for reg in list(GPR.values()):
            uc.reg_write(reg, 0x5A5A_5A5A_5A5A_5A5A)
        for reg in XMM:
            uc.reg_write(reg, 0x5A5A5A5A5A5A5A5A5A5A5A5A5A5A5A5A)
        for reg, value in zip(ARG_REGS, args):
            uc.reg_write(reg, value)
        rsp = STACK_TOP - 0x1000 - 8  # 16-byte aligned before the call's push
        uc.mem_write(rsp, struct.pack("<Q", SENTINEL))
        uc.reg_write(X.UC_X86_REG_RSP, rsp)
        uc.emu_start(addr, SENTINEL, count=5_000_000)
        assert uc.reg_read(X.UC_X86_REG_RIP) == SENTINEL, "did not return"

    def gpr(self, name):
        return self.uc.reg_read(GPR[name])

    def xmm(self, index):
        return self.uc.reg_read(XMM[index])


def parse_artifacts(root):
    layout = {}
    live = None
    for line in (root / "layout.txt").read_text().splitlines():
        parts = line.split()
        if parts[0] == "live":
            live = [int(x, 16) for x in parts[1].split(",")]
        elif parts[0] == "lane_bytes":
            continue
        else:
            layout[parts[0]] = (parts[1].split(","), parts[2].split(","))
    wrappers, callees = [], []
    for line in (root / "expected.txt").read_text().splitlines():
        parts = line.split()
        if parts[0] == "callee":
            callees.append((parts[1], int(parts[2], 16), int(parts[3], 16),
                            [bytes.fromhex(b) for b in parts[4].split(",")]))
        else:
            wrappers.append((parts[0], int(parts[1]), int(parts[2], 16), int(parts[3], 16),
                             bytes.fromhex(parts[4])))
    return layout, live, wrappers, callees


def register_bytes(machine, regspec, nbytes):
    """Low `nbytes` of the register(s) named by `regspec` (`rax`, `xmm3`,
    or an i128 pair `rsi:rdi`)."""
    if ":" in regspec:
        lo, hi = regspec.split(":")
        value = machine.gpr(lo) | (machine.gpr(hi) << 64)
        return value.to_bytes(16, "little")[:nbytes]
    if regspec.startswith("xmm"):
        return machine.xmm(int(regspec[3:])).to_bytes(16, "little")[:nbytes]
    return machine.gpr(regspec).to_bytes(8, "little")[:nbytes]


def wrong_order(regs):
    """The control: past RAX,RDX, read the SysV ARGUMENT order instead."""
    remap = {"rcx": "rdi", "rsi": "rsi", "rdi": "rcx", "r8": "r8", "r9": "r9"}
    out = []
    for spec in regs:
        if ":" in spec:
            out.append(":".join(remap.get(r, r) for r in spec.split(":")))
        else:
            out.append(remap.get(spec, spec))
    return out


def main(root):
    root = Path(root)
    layout, live, wrappers, callees = parse_artifacts(root)
    totals = {"wrapper_calls": 0, "callee_register_checks": 0, "controls_refuted": 0}
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        stub = tmp / "stub.c"
        stub.write_text("int main(void) { return 0; }\n")
        for opt in OPTS:
            objects = sorted(root.glob(f"*_{opt}.o"))
            image = tmp / f"image_{opt}"
            subprocess.run(["cc", "-arch", "x86_64", "-o", str(image), str(stub)]
                           + [str(o) for o in objects], check=True)
            m = Machine(image)
            state_ptr, live_ptr, out_ptr = DATA_BASE, DATA_BASE + 0x100, DATA_BASE + 0x1000
            m.uc.mem_write(live_ptr, b"".join(struct.pack("<Q", v) for v in live))
            for tag, indirect, seed, final_state, expected in wrappers:
                # The driver line's state is the FINAL counter; the initial one
                # is two less (each wrapper makes two counting calls).
                state0 = (final_state - 2) % (1 << 64)
                m.uc.mem_write(state_ptr, struct.pack("<Q", state0))
                m.uc.mem_write(out_ptr, b"\xa5" * len(expected))
                if indirect:
                    m.call(f"produce_addr_{tag}", [])
                    callee = m.gpr("rax")
                    m.call(f"indirect_{tag}", [callee, state_ptr, live_ptr, seed, out_ptr])
                else:
                    m.call(f"direct_{tag}", [state_ptr, live_ptr, seed, out_ptr])
                out = bytes(m.uc.mem_read(out_ptr, len(expected)))
                state = struct.unpack("<Q", bytes(m.uc.mem_read(state_ptr, 8)))[0]
                if out != expected or state != final_state:
                    print(f"MISMATCH {opt} {tag} indirect={indirect} seed={seed:#x}")
                    print(f"  got      {out.hex()} state={state:#x}")
                    print(f"  expected {expected.hex()} state={final_state:#x}")
                    return 1
                totals["wrapper_calls"] += 1
            for tag, seed, state0, result_bytes in callees:
                types, regs = layout[tag]
                m.uc.mem_write(state_ptr, struct.pack("<Q", state0))
                m.call(f"produce_{tag}", [state_ptr, seed])
                got = [register_bytes(m, r, len(b)) for r, b in zip(regs, result_bytes)]
                if got != result_bytes:
                    print(f"CALLEE MISMATCH {opt} {tag} seed={seed:#x}: regs {regs}")
                    print(f"  got      {[g.hex() for g in got]}")
                    print(f"  expected {[b.hex() for b in result_bytes]}")
                    return 1
                totals["callee_register_checks"] += 1
                control = wrong_order(regs)
                if control != regs:
                    wrong = [register_bytes(m, r, len(b)) for r, b in zip(control, result_bytes)]
                    if wrong == result_bytes:
                        print(f"CONTROL FAILED {opt} {tag}: the wrong order matched too")
                        return 1
                    totals["controls_refuted"] += 1
            print(f"{opt}: wrappers {sum(1 for _ in wrappers)} exact, callees {len(callees)} exact")
    print("TOTAL", totals)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
