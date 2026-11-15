#!/usr/bin/env python3
# formal/lean/scripts/gen_a64_silicon_checks.py
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Record A64 instruction results on the host CPU and render them as Lean checks.

Each case is one A64 instruction (assembled by the host C compiler's integrated
assembler) run natively on chosen register, NZCV and memory inputs. The script
records the instruction word and address, X0, X1 and X4, NZCV, the next PC and
a 64-byte memory window after it, and renders `Trust/A64/SiliconChecks.lean`,
whose kernel-checked theorem requires `Trust.A64.decodeNat` +
`Trust.A64.exec` to reproduce every recorded result.

Three kinds of case: `alu` (data processing; the next PC is the fall-through),
`branch` (a conditional or compare/test branch whose target is three
instructions ahead; the harness records whether it was taken, and only the
next PC and NZCV are compared) and `mem` (a load or store whose base X0 points
32 bytes into the 64-byte window, filled with the pattern
`(37 * i + 11) mod 256` before the instruction).

This is a native differential of the Lean semantics on enumerated inputs
(testing evidence about the model's faithfulness), not a proof. It needs an
AArch64 host (Apple silicon or Linux AArch64) with `clang` or `cc`:

    python3 formal/lean/scripts/gen_a64_silicon_checks.py \\
        --out formal/lean/Trust/A64/SiliconChecks.lean

Register convention of every case: Rn = X0/W0, Rm = X1/W1 (also Rt2),
Ra = X2/W2 (also the register offset), Rd = Rt = X4/W4 (initially `d0`); NZCV
is set with MSR from X3 before the instruction and read with MRS after it.
"""

from __future__ import annotations

import argparse
import itertools
import os
import platform
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

M64 = (1 << 64) - 1
VALUES64 = [
    0,
    1,
    0x7FFF_FFFF_FFFF_FFFF,
    0x8000_0000_0000_0000,
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_8000_0000,
    0x0000_0000_7FFF_FFFF,
    0x1234_5678_9ABC_DEF0,
    0xFFFF_FFFF_0000_0003,
]
# Flag inputs (N Z C V as a 4-bit value).
FLAGS = [0b0000, 0b0100, 0b1000, 0b0010, 0b0001, 0b1001, 0b0110, 0b1111]


def pairs(values: list[int], limit: int) -> list[tuple[int, int]]:
    out = list(itertools.product(values, values))
    step = max(1, len(out) // limit)
    return out[::step][:limit]


Case = tuple[str, str, int, int, int, int, int]


def cases() -> list[Case]:
    """(kind, asm, n, m, a, nzcv_in, d0) for every recorded case."""
    out: list[Case] = []

    def binop(asm: str, limit: int = 12, flags: list[int] | None = None) -> None:
        for (n, m), f in itertools.product(pairs(VALUES64, limit), flags or [0]):
            out.append(("alu", asm, n, m, 0x0123_4567_89AB_CDEF, f, 0xDEAD_BEEF_DEAD_BEEF))

    # Add/subtract and flags (shifted register, immediate, extended, carry).
    for asm in [
        "adds x4, x0, x1",
        "subs x4, x0, x1",
        "adds w4, w0, w1",
        "subs w4, w0, w1",
        "add x4, x0, x1, asr #7",
        "sub w4, w0, w1, lsr #31",
        "subs x4, x0, x1, lsl #63",
        "cmn w0, w1",
        "cmp x0, x1",
        "adds x4, x0, #4095, lsl #12",
        "subs w4, w0, #1",
        "add x4, x0, w1, sxtb #2",
        "add x4, x0, w1, uxth #4",
        "subs x4, x0, w1, sxtw",
        "add w4, w0, w1, uxtb #1",
        "adds x4, x0, x1, sxtx #3",
        "neg w4, w1",
    ]:
        binop(asm)
    for asm in ["adcs x4, x0, x1", "sbcs x4, x0, x1", "adcs w4, w0, w1", "sbcs w4, w0, w1"]:
        binop(asm, limit=6, flags=[0b0000, 0b0010])
    # Logical (shifted register and immediate).
    for asm in [
        "ands x4, x0, x1",
        "bics w4, w0, w1, ror #3",
        "orn x4, x0, x1, lsl #63",
        "eon w4, w0, w1, asr #5",
        "and x4, x0, #0xff00ff00ff00ff00",
        "orr w4, w0, #0x80000001",
        "eor x4, x0, #0x5555555555555555",
        "ands w4, w0, #0xfffffffe",
        "tst x0, #0x1",
        "tst w0, w1",
        "mvn x4, x1",
    ]:
        binop(asm, limit=8)
    # Move wide (MOVK keeps the other halfwords of d0).
    for asm in [
        "movz x4, #0x1234, lsl #48",
        "movn w4, #0x5678, lsl #16",
        "movk x4, #0xbeef, lsl #32",
        "movk w4, #0xcafe, lsl #16",
        "movn x4, #0",
    ]:
        out.append(("alu", asm, 0, 0, 0, 0, 0x0123_4567_89AB_CDEF))
    # Bitfield and extract (BFM-family reads d0).
    for asm in [
        "ubfm x4, x0, #3, #7",
        "sbfm x4, x0, #60, #3",
        "bfm x4, x0, #8, #15",
        "ubfm w4, w0, #31, #30",
        "sbfm w4, w0, #0, #7",
        "bfm w4, w0, #28, #3",
        "lsl x4, x0, #13",
        "asr w4, w0, #31",
        "lsr x4, x0, #1",
        "ubfx x4, x0, #17, #40",
        "sbfx w4, w0, #4, #9",
        "bfi x4, x0, #60, #4",
        "bfxil w4, w0, #3, #10",
        "sxtw x4, w0",
        "uxth w4, w0",
        "extr x4, x0, x1, #17",
        "extr w4, w0, w1, #31",
        "ror x4, x0, #63",
    ]:
        binop(asm, limit=6)
    # Data processing (2 source): division edge cases and variable shifts.
    for asm in [
        "udiv x4, x0, x1",
        "sdiv x4, x0, x1",
        "udiv w4, w0, w1",
        "sdiv w4, w0, w1",
        "lslv x4, x0, x1",
        "lsrv w4, w0, w1",
        "asrv x4, x0, x1",
        "rorv w4, w0, w1",
    ]:
        binop(asm, limit=16)
    for n, m in [(7, 0), (0x8000_0000_0000_0000, M64), (0x8000_0000, 0xFFFF_FFFF), (M64 - 6, 2),
                 (7, M64 - 1), (100, 67), (100, 64), (100, 32)]:
        for asm in ["sdiv x4, x0, x1", "sdiv w4, w0, w1", "lslv x4, x0, x1", "rorv w4, w0, w1"]:
            out.append(("alu", asm, n, m, 0, 0, 0))
    # Data processing (1 source).
    for asm in ["rbit x4, x0", "rbit w4, w0", "rev16 x4, x0", "rev32 x4, x0", "rev x4, x0",
                "rev w4, w0", "rev16 w4, w0", "clz x4, x0", "clz w4, w0", "cls x4, x0",
                "cls w4, w0"]:
        for n in VALUES64 + [0x0000_0000_0001_0000, 0xFFFF_FFFF_FFFF_FFFE]:
            out.append(("alu", asm, n, 0, 0, 0, 0))
    # Data processing (3 source).
    for asm in [
        "madd x4, x0, x1, x2",
        "msub w4, w0, w1, w2",
        "smaddl x4, w0, w1, x2",
        "umsubl x4, w0, w1, x2",
        "smulh x4, x0, x1",
        "umulh x4, x0, x1",
        "mul w4, w0, w1",
    ]:
        binop(asm, limit=10)
    # CRC32 / CRC32C (FEAT_CRC32).
    for asm in ["crc32b w4, w0, w1", "crc32h w4, w0, w1", "crc32w w4, w0, w1", "crc32x w4, w0, x1",
                "crc32cb w4, w0, w1", "crc32ch w4, w0, w1", "crc32cw w4, w0, w1",
                "crc32cx w4, w0, x1"]:
        binop(asm, limit=6)
    # Conditional select over every flag input.
    for asm in [
        "csel x4, x0, x1, eq",
        "csinc w4, w0, w1, lt",
        "csinv x4, x0, x1, hi",
        "csneg w4, w0, w1, ge",
        "cset x4, ls",
        "csetm w4, ne",
        "cneg x4, x0, mi",
        "csel x4, x0, x1, vs",
        "csel w4, w0, w1, gt",
        "csinc x4, x0, x1, le",
        "csel x4, x0, x1, cc",
        "csel x4, x0, x1, al",
    ]:
        for f in FLAGS:
            out.append(("alu", asm, 0x1111_2222_3333_4444, 0x8000_0000_0000_0005, 0, f, 0))
    # PC-relative addresses (results depend on the recorded instruction address).
    # The Mach-O assembler refuses a non-symbolic ADRP, so these are spelled as `.inst`.
    for op, imm in [(0, 0x1234), (0, -4), (1, 5), (1, -3), (1, 0)]:
        out.append(("alu", pc_rel_inst(op, imm), 0, 0, 0, 0, 0))
    # Branches: every condition but NV over every flag input; compare and test
    # branches over zero, W-zero-but-X-nonzero and sign-bit values.
    conds = ["eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt",
             "le", "al"]
    for cond in conds:
        for f in FLAGS:
            out.append(("branch", f"b.{cond} 1f", 0, 0, 0, f, 0))
    for asm in ["cbz x0, 1f", "cbnz x0, 1f", "cbz w0, 1f", "cbnz w0, 1f", "b 1f"]:
        for n in [0, 1, 0x1_0000_0000, 0x8000_0000_0000_0000]:
            out.append(("branch", asm, n, 0, 0, 0, 0))
    for asm in ["tbz x0, #0, 1f", "tbnz x0, #0, 1f", "tbz x0, #63, 1f", "tbnz x0, #32, 1f",
                "tbz w0, #31, 1f", "tbnz w0, #5, 1f"]:
        for n in [0, 1, 0x8000_0000_0000_0000, 0x1_0000_0020, 0x8000_0000]:
            out.append(("branch", asm, n, 0, 0, 0, 0))
    # Loads and stores (base X0 = window + 32; X2 is the register offset).
    for asm in [
        "ldr x4, [x0, #8]", "ldr w4, [x0, #4]", "ldrb w4, [x0, #3]", "ldrh w4, [x0, #6]",
        "ldrsb x4, [x0, #7]", "ldrsb w4, [x0, #9]", "ldrsh x4, [x0, #10]",
        "ldrsh w4, [x0, #12]", "ldrsw x4, [x0, #16]", "ldur x4, [x0, #-13]",
        "ldursh w4, [x0, #-3]", "str x4, [x0, #8]", "str w4, [x0, #24]",
        "strb w4, [x0, #31]", "strh w4, [x0, #2]", "stur w4, [x0, #-5]",
        "stur x4, [x0, #-32]", "ldr x4, [x0, #16]!", "ldr w4, [x0], #-8",
        "str x4, [x0, #-16]!", "strb w4, [x0], #3", "ldrsb x4, [x0, #-1]!",
        "ldr x4, [x0, x2, lsl #3]", "ldrb w4, [x0, w2, sxtw]", "str w4, [x0, x2]",
        "ldrsw x4, [x0, x2, lsl #2]", "ldrh w4, [x0, w2, uxtw #1]", "strh w4, [x0, x2, lsl #1]",
        "ldp x4, x1, [x0, #-16]", "ldp w4, w1, [x0, #8]!", "stp x4, x1, [x0], #16",
        "ldpsw x4, x1, [x0, #-8]", "stp w4, w1, [x0, #-32]", "ldnp x4, x1, [x0, #16]",
        "stnp w4, w1, [x0, #-4]", "ldp x4, x1, [x0], #-24",
    ]:
        # A UXTW index is zero-extended, so it stays small and positive.
        for index in [1, 5] if "uxtw" in asm else [1, 0xFFFF_FFFF_FFFF_FFFD]:
            if "x2" not in asm and "w2" not in asm and index != 1:
                continue
            out.append(("mem", asm, 0, 0x5A5A_A5A5_0F0F_F0F0, index, 0, 0x8899_AABB_CCDD_EEFF))
    return out


def pc_rel_inst(op: int, imm: int) -> str:
    """`.inst` for ADR (op 0, byte offset) / ADRP (op 1, page offset) X4."""
    raw = imm & ((1 << 21) - 1)
    word = (op << 31) | ((raw & 3) << 29) | (0b10000 << 24) | ((raw >> 2) << 5) | 4
    name = "adrp" if op else "adr"
    return f".inst {word:#010x} // {name} x4, {'page ' if op else ''}{imm:+#x}"


C_HEADER = r"""
#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef void (*op_fn)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t *);
static unsigned char window[64] __attribute__((aligned(16)));
"""

# Byte i of the memory window before every case.
def pattern(i: int) -> int:
    return (37 * i + 11) % 256


def render_c(all_cases: list[Case], symbol_prefix: str) -> str:
    lines = [C_HEADER]
    epilogue = (
        "  mrs x5, nzcv\\n  str x4, [x6]\\n  str x5, [x6, #8]\\n  str x0, [x6, #16]\\n"
        "  str x1, [x6, #24]\\n  ret\\n"
    )
    for k, (kind, asm, *_rest) in enumerate(all_cases):
        name = f"{symbol_prefix}op_{k}"
        if kind == "branch":
            body = (f"  msr nzcv, x3\\n  {asm}\\n  mov x4, #0\\n  b 2f\\n1:\\n"
                    f"  mov x4, #1\\n2:\\n")
        else:
            body = f"  msr nzcv, x3\\n  {asm}\\n"
        lines.append(
            f'__asm__(".text\\n.p2align 2\\n.globl {name}\\n{name}:\\n{body}{epilogue}");'
        )
        lines.append(
            f"void op_{k}(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t *)"
            f' __asm__("{name}");'
        )
    lines.append("static const op_fn ops[] = {")
    lines.extend(f"  op_{k}," for k in range(len(all_cases)))
    lines.append("};")
    lines.append("static const uint64_t inputs[][6] = {")
    for kind, _asm, n, m, a, f, d0 in all_cases:
        lines.append(f"  {{{n}ULL, {m}ULL, {a}ULL, {f << 28}ULL, {d0}ULL, {int(kind == 'mem')}ULL}},")
    lines.append("};")
    lines.append(
        r"""
int main(void) {
  for (unsigned k = 0; k < sizeof(ops) / sizeof(ops[0]); k++) {
    uint64_t out[4] = {0, 0, 0, 0};
    const uint64_t *in = inputs[k];
    for (unsigned i = 0; i < 64; i++) window[i] = (unsigned char)((37 * i + 11) % 256);
    uint64_t base = (uint64_t)(uintptr_t)window;
    uint64_t x0 = in[5] ? base + 32 : in[0];
    ops[k](x0, in[1], in[2], in[3], in[4], 0, out);
    uint32_t word;
    const unsigned char *code = (const unsigned char *)(uintptr_t)ops[k];
    memcpy(&word, code + 4, 4);
    printf("%u %u %llu %llu %llu %llu %llu %llu %llu ", k, word,
           (unsigned long long)(uintptr_t)(code + 4), (unsigned long long)x0,
           (unsigned long long)base, (unsigned long long)out[0],
           (unsigned long long)((out[1] >> 28) & 15), (unsigned long long)out[2],
           (unsigned long long)out[3]);
    for (unsigned i = 0; i < 64; i++) printf("%02x", window[63 - i]);
    printf("\n");
  }
  return 0;
}
"""
    )
    return "\n".join(lines)


LEAN_HEADER = """/-
  A64.SiliconChecks — GENERATED native differential of the Lean A64 semantics.
  DO NOT EDIT: regenerate on an AArch64 host with

      python3 formal/lean/scripts/gen_a64_silicon_checks.py \\
          --out formal/lean/Trust/A64/SiliconChecks.lean

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  Each row is one A64 instruction word the host assembler produced, run once on the host CPU
  ({host}): its kind (0 data processing, 1 branch, 2 load/store), word and address, the inputs
  (X0, X1, X2, NZCV, initial X4, and the address of a 64-byte memory window holding
  `windowByte`), and what the CPU left: X4, X0, X1, NZCV, the next PC and the window.
  `siliconCases_hold` (kernel evaluation) requires the instruction-word decoder and `exec` to
  reproduce every recorded result; for a branch (whose harness overwrites X4 with a taken
  marker) it compares the next PC and NZCV.  Testing evidence on enumerated inputs; not a proof
  that the model agrees with the hardware elsewhere.
-/
import Trust.A64.Machine

namespace Trust
namespace A64

/-- One recorded native execution. -/
structure SiliconCase where
  kind : Nat
  word : Nat
  pc : Nat
  n : Nat
  m : Nat
  a : Nat
  nzcvIn : Nat
  d0 : Nat
  base : Nat
  x4 : Nat
  x0 : Nat
  x1 : Nat
  nzcvOut : Nat
  nextPc : Nat
  window : Nat

/-- NZCV from its 4-bit value. -/
def nzcvOfBits (b : Nat) : NZCV := ⟨b / 8 % 2 == 1, b / 4 % 2 == 1, b / 2 % 2 == 1, b % 2 == 1⟩

/-- The 4-bit value of NZCV. -/
def nzcvBits (f : NZCV) : Nat := 8 * f.n.toNat + 4 * f.z.toNat + 2 * f.c.toNat + f.v.toNat

/-- Byte `i` of the memory window before every case. -/
def windowByte (i : Nat) : Nat := (37 * i + 11) % 256

/-- The state a case starts from (registers the harness does not set are zero; memory outside
    the window is zero). -/
def SiliconCase.state (c : SiliconCase) : MachState where
  x := fun i =>
    match i.val with
    | 0 => BitVec.ofNat 64 c.n
    | 1 => BitVec.ofNat 64 c.m
    | 2 => BitVec.ofNat 64 c.a
    | 3 => BitVec.ofNat 64 (c.nzcvIn * 2 ^ 28)
    | 4 => BitVec.ofNat 64 c.d0
    | _ => 0
  sp := 0
  pc := BitVec.ofNat 64 c.pc
  nzcv := nzcvOfBits c.nzcvIn
  mem := fun addr =>
    if c.base ≤ addr.toNat ∧ addr.toNat < c.base + 64 then
      BitVec.ofNat 8 (windowByte (addr.toNat - c.base))
    else 0

/-- The model decodes the recorded word and reproduces the recorded results. -/
def SiliconCase.holds (c : SiliconCase) : Bool :=
  match decodeNat c.word with
  | none => false
  | some i =>
    match exec i c.state with
    | none => false
    | some s =>
      s.pc.toNat == c.nextPc && nzcvBits s.nzcv == c.nzcvOut &&
      (c.kind == 1 ||
        ((s.readX 4).toNat == c.x4 && (s.readX 0).toNat == c.x0 && (s.readX 1).toNat == c.x1 &&
          s.readMem (BitVec.ofNat 64 c.base) 64 == c.window))

set_option maxRecDepth 16384 in
/-- The recorded cases (`-- asm` comments name each instruction). -/
def siliconCases : List SiliconCase := ["""

LEAN_FOOTER = """]

theorem siliconCases_hold : siliconCases.all SiliconCase.holds = true := by decide +kernel

/-- Control: the check is not vacuous — flipping bit 0 of any recorded X4 of a non-branch case,
    or bit 0 of any recorded next PC, makes that case fail. -/
theorem siliconCases_refuse_corruption :
    ((siliconCases.filter (·.kind != 1)).map fun c => { c with x4 := c.x4 ^^^ 1 }).any
        SiliconCase.holds = false ∧
      (siliconCases.map fun c => { c with nextPc := c.nextPc ^^^ 4 }).any
        SiliconCase.holds = false := by decide +kernel

theorem siliconCases_length : siliconCases.length = {count} := by decide +kernel

end A64
end Trust
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--cc", default=os.environ.get("CC") or shutil.which("clang") or "cc")
    args = parser.parse_args()
    if platform.machine().lower() not in ("arm64", "aarch64"):
        print("error: an AArch64 host is required to record native results", file=sys.stderr)
        return 2
    all_cases = cases()
    prefix = "_" if platform.system() == "Darwin" else ""
    with tempfile.TemporaryDirectory(prefix="a64-silicon-") as work:
        source = Path(work) / "cases.c"
        binary = Path(work) / "cases"
        source.write_text(render_c(all_cases, prefix))
        subprocess.run([args.cc, "-O0", "-o", str(binary), str(source)], check=True)
        run = subprocess.run([str(binary)], check=True, capture_output=True, text=True)
    rows = []
    kinds = {"alu": 0, "branch": 1, "mem": 2}
    for line, case in zip(run.stdout.splitlines(), all_cases, strict=True):
        fields = line.split()
        k, word, pc, x0_in, base, x4, nzcv, x0, x1 = (int(field) for field in fields[:9])
        window = int(fields[9], 16)
        kind, asm, _n, m, a, f, d0 = case
        taken = kind == "branch" and x4 == 1
        next_pc = pc + 12 if taken else pc + 4
        rows.append(
            f"  ⟨{kinds[kind]}, {word:#010x}, {pc:#x}, {x0_in:#x}, {m:#x}, {a:#x}, {f}, {d0:#x}, "
            f"{base:#x}, {x4:#x}, {x0:#x}, {x1:#x}, {nzcv}, {next_pc:#x}, {window:#x}⟩ -- {asm}"
        )
    if len(rows) != len(all_cases):
        print("error: the harness did not report every case", file=sys.stderr)
        return 1
    host = f"{platform.system()} {platform.machine()}"
    try:
        brand = subprocess.run(
            ["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True, text=True,
            check=False,
        ).stdout.strip()
        if brand:
            host = f"{brand}, {host}"
    except OSError:
        pass
    text = LEAN_HEADER.replace("{host}", host) + "\n" + "\n".join(
        _place_comma(row, i == len(rows) - 1) for i, row in enumerate(rows)
    ) + "\n" + LEAN_FOOTER.replace("{count}", str(len(rows)))
    args.out.write_text(text)
    print(f"recorded {len(rows)} cases on {host} -> {args.out}")
    return 0


def _place_comma(row: str, last: bool) -> str:
    code, comment = row.split(" -- ", 1)
    return f"{code}{'' if last else ','} -- {comment}"


if __name__ == "__main__":
    sys.exit(main())
