#!/usr/bin/env python3
"""The selector's half of the slice-14 mutants: `TCG_S14_MUTANT=selector-64-bit-copy`
makes `emit_x86_jump_table` copy a 32-bit selector with the former 64-bit `mov`.
Restore the file with `git checkout` afterwards; never commit it.

usage: mutate_selector.py <crates/trust-cg-lower/src/x86_64_isel.rs>
"""
import sys

path = sys.argv[1]
text = open(path).read()
old = "            X86ISelOperand::VReg(vreg) if vreg.class == RegClass::Gpr32 => X86Opcode::MovRR32,\n"
new = ("            X86ISelOperand::VReg(vreg)\n"
       "                if vreg.class == RegClass::Gpr32\n"
       "                    && !std::env::var(\"TCG_S14_MUTANT\")\n"
       "                        .is_ok_and(|mutant| mutant == \"selector-64-bit-copy\") =>\n"
       "            {\n"
       "                X86Opcode::MovRR32\n"
       "            }\n")
if text.count(old) != 1:
    sys.exit(f"anchor found {text.count(old)} times")
open(path, "w").write(text.replace(old, new))
print("applied the selector mutant guard")
