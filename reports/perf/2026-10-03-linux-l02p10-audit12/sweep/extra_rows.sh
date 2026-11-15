#!/bin/sh
# The 65 rows appended to gen.sh's matrix for this round (LLVM bitcode modes
# through LLD, the C-runtime replacement probes, and the DSO-dependency
# modes of case2.sh).
for M in bc_so bc_ar bc_ar_st bc_thin_st bc_thin bc_st_cxx evil_bc_ar_st evil_bc_st evil2_bc_ar_st evil2_bc_ar_cxx_st; do
  for O in none -z,relro,-z,now --gc-sections -s; do echo "lld $M $O none"; done
done
for L in bfd lld gold; do
  for M in dso dso_np dso_so evil_elf_ar_st evil_elf_st evil2_elf_ar_st evil2_elf_ar_cxx_st; do echo "$L $M none none"; done
done
for L in bfd gold; do
  for M in evil2_lto_ar_st evil2_lto_st; do echo "$L $M none none"; done
done
