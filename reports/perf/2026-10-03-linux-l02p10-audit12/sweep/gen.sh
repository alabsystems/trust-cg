#!/bin/bash
# Emit the sweep matrix: "LINKER MODE OPTS EXTRA" per line.
W=${W:-$(cd "$(dirname "$0")" && pwd)}
modes="pie np st cxx_pie cxx_np cxx_st so so_full ar ar_st thin fpic dbg lto_pie lto_st lto_np"
lto_modes_bfd_gold="cxx_lto ar_lto so_lto"
# Options every linker reads.
common=(
none
-z,relro,-z,now
-z,now
-z,lazy
-z,norelro
--gc-sections
--gc-sections,--print-gc-sections
--build-id=sha1
--build-id=md5
--build-id=uuid
--build-id=0x1234abcd
--build-id=none
--hash-style=both
--hash-style=sysv
--hash-style=gnu
-O1,--as-needed
--as-needed
--no-as-needed
-s
--strip-all
-S
--strip-debug
-x
-X
--export-dynamic
-E
-z,max-page-size=65536
-z,max-page-size=65536,-z,common-page-size=65536
-z,max-page-size=4096,-z,common-page-size=4096
-z,max-page-size=16384
--fatal-warnings
--enable-new-dtags
--disable-new-dtags
--sort-common
-z,text
--start-group,-lm,--end-group
-u,c_cb
--undefined=tcg_get
--warn-common
-z,noexecstack
--compress-debug-sections=zlib
--no-undefined
-z,defs
--dynamic-list=$W/dyn.list
--version-script=$W/lib.map
-Bsymbolic
-Bsymbolic-functions
--exclude-libs,ALL
-z,origin
-z,nodelete
--eh-frame-hdr
--emit-relocs
-q
--sort-section=name
--sort-section=alignment
-rpath-link,$W
-L$W
--no-gc-sections
-z,relro
--hash-style=gnu,-z,relro,-z,now,--as-needed,-O1,--sort-common,--build-id=sha1
--hash-style=gnu,--as-needed,-z,relro,-z,now,--gc-sections,-s
-Map=$W/out/MAPNAME.map
-Map,$W/out/MAPNAME.map,--cref
--dependency-file=$W/out/MAPNAME.d
--fix-cortex-a53-843419
--defsym=tcg_alias=tcg_get
--wrap=puts
-z,global
--no-warn-mismatch
--warn-shared-textrel
--threads
)
bfd_only=(
--no-relax
--relax
--fix-cortex-a53-835769
-z,separate-code
-z,noseparate-code
-z,pack-relative-relocs
-z,pack-relative-relocs,-z,now
-z,keep-text-section-prefix
--no-warn-rwx-segments
--no-warn-execstack
--orphan-handling=warn
--require-defined=main
--push-state,--as-needed,-lm,--pop-state
--no-ld-generated-unwind-info
-z,start-stop-visibility=hidden
--gc-keep-exported
-z,unique-symbol
-z,mark-plt
--error-execstack
)
lld_only=(
--icf=all
--icf=safe
--gdb-index
--threads=2
-z,separate-code
-z,pack-relative-relocs
--pack-dyn-relocs=relr
-z,keep-text-section-prefix
--no-rosegment
--rosegment
--orphan-handling=warn
--require-defined=main
--push-state,--as-needed,-lm,--pop-state
-z,rodynamic
--image-base=0x2000000
-z,start-stop-visibility=hidden
--lto-O2
--Bsymbolic-non-weak-functions
--build-id=fast
-z,nognustack
--no-allow-shlib-undefined
)
gold_only=(
--icf=all
--icf=safe
--gdb-index
--fix-cortex-a53-835769
--no-relax
-z,relro,-z,now,--threads,--thread-count,2
--detect-odr-violations
--rosegment
--ld-generated-unwind-info
)
for L in bfd lld gold; do
  case $L in bfd) extra=("${bfd_only[@]}");; lld) extra=("${lld_only[@]}");; gold) extra=("${gold_only[@]}");; esac
  ms="$modes"
  if [ $L != lld ]; then ms="$ms $lto_modes_bfd_gold"; fi
  for M in $ms; do
    for O in "${common[@]}" "${extra[@]}"; do
      echo "$L $M $O none"
    done
    echo "$L $M none --function-sections"
    echo "$L $M --gc-sections --function-sections"
    echo "$L $M --gc-sections,-z,relro,-z,now,--build-id --function-sections"
  done
  for M in pie lto_pie cxx_pie fpic dbg; do
    echo "$L $M none --relocation-model_pie"
    echo "$L $M -z,relro,-z,now --relocation-model_pie"
  done
done
