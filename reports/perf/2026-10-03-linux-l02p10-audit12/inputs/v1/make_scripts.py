#!/usr/bin/env python3
"""Write the linker scripts of repro_v1.sh into this directory.

Four are small literal scripts. Two derive from GNU ld 2.42's default PIE
script (`ld -pie --verbose`) through the patches beside this file:
`tbssfirst_pie.ld` (PHDRS, `.tbss` moved before `.tdata`, both in PT_TLS) and
`datatls_pie_al.ld` (PHDRS, `.data` moved before `.tdata` and put in PT_TLS).
Linker scripts are not committed under reports/ (.gitignore), so they are
made here.
"""
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))


def eh_frame_script(flags):
    """A dynamic no-PIE PHDRS script giving `.eh_frame` a PT_LOAD of its own
    with the permissions `flags` (the first verifier's dyneh0.ld/dyneh4.ld)."""
    return f"""ENTRY(_start)
PHDRS
{{
  phdr PT_PHDR PHDRS;
  interp PT_INTERP;
  text PT_LOAD FILEHDR PHDRS FLAGS(5);
  eh PT_LOAD FLAGS({flags});
  data PT_LOAD FLAGS(6);
  dynamic PT_DYNAMIC;
  ehhdr PT_GNU_EH_FRAME;
  stack PT_GNU_STACK FLAGS(6);
}}
SECTIONS
{{
  . = 0x400000 + SIZEOF_HEADERS;
  .interp : {{ *(.interp) }} :text :interp
  .note.gnu.build-id : {{ *(.note.gnu.build-id) }} :text
  .note.ABI-tag : {{ *(.note.ABI-tag) }} :text
  .hash : {{ *(.hash) }} :text
  .gnu.hash : {{ *(.gnu.hash) }} :text
  .dynsym : {{ *(.dynsym) }} :text
  .dynstr : {{ *(.dynstr) }} :text
  .gnu.version : {{ *(.gnu.version) }} :text
  .gnu.version_r : {{ *(.gnu.version_r) }} :text
  .rela.dyn : {{ *(.rela.dyn) *(.rela.got) }} :text
  .rela.plt : {{ *(.rela.plt) }} :text
  .init : {{ KEEP(*(.init)) }} :text
  .plt : {{ *(.plt) }} :text
  .text : {{ *(.text .text.*) }} :text
  .fini : {{ KEEP(*(.fini)) }} :text
  .rodata : {{ *(.rodata .rodata.*) }} :text
  .eh_frame_hdr : {{ *(.eh_frame_hdr) }} :text :ehhdr
  . = 0x500000;
  .eh_frame : {{ KEEP(*(.eh_frame)) }} :eh
  . = 0x600000;
  .init_array : {{ KEEP(*(.init_array .init_array.*)) }} :data
  .fini_array : {{ KEEP(*(.fini_array .fini_array.*)) }} :data
  .dynamic : {{ *(.dynamic) }} :data :dynamic
  .got : {{ *(.got) }} :data
  .got.plt : {{ *(.got.plt) }} :data
  .data : {{ *(.data .data.*) }} :data
  .bss : {{ *(.bss .bss.*) *(COMMON) }} :data
}}
"""


# trust-cg's `.data` in no segment (`:NONE`), after `.bss` in the page of
# the data segment, in a static layout with `.eh_frame_hdr`.
DATA_NONE = """ENTRY(_start)
PHDRS { text PT_LOAD FILEHDR PHDRS; data PT_LOAD; hdr PT_GNU_EH_FRAME; }
SECTIONS {
  . = 0x400000 + SIZEOF_HEADERS;
  .text : { *(.text*) } :text
  .rodata : { *(.rodata*) } :text
  .eh_frame_hdr : { *(.eh_frame_hdr) } :text :hdr
  .eh_frame : { KEEP(*(.eh_frame)) } :text
  . = 0x500000;
  .bss : { *(.bss*) *(COMMON) } :data
  .data : { *(.data*) } :NONE
}
"""

# trust-cg's `.rodata` marked `(NOLOAD)` in a read-only segment of its own.
RODATA_NOLOAD = """ENTRY(_start)
PHDRS { text PT_LOAD FILEHDR PHDRS FLAGS(5); ro PT_LOAD FLAGS(4); data PT_LOAD FLAGS(6); }
SECTIONS {
  . = 0x400000 + SIZEOF_HEADERS;
  .note.gnu.build-id : { *(.note.gnu.build-id) } :text
  .text : { *(.text*) } :text
  .eh_frame : { KEEP(*(.eh_frame)) } :text
  .eh_frame_hdr : { *(.eh_frame_hdr) } :text
  . = 0x500000;
  .rodata (NOLOAD) : { *(.rodata*) } :ro
  . = 0x600000;
  .data : { *(.data*) } :data
  .bss : { *(.bss*) *(COMMON) } :data
}
"""


def default_pie_script():
    """GNU ld's default PIE script: the text between its `ld --verbose` rules."""
    text = subprocess.run(
        ["ld", "-pie", "--verbose"], check=True, capture_output=True, text=True
    ).stdout
    rule = "=" * 50
    # The script's lines, from the one after the first rule to the second.
    return text.split(rule)[1][1:]


def main():
    for name, text in [
        ("dyneh0.ld", eh_frame_script(0)),
        ("dyneh4.ld", eh_frame_script(4)),
        ("datanone.ld", DATA_NONE),
        ("ronl.ld", RODATA_NOLOAD),
        ("pie.ld", default_pie_script()),
    ]:
        with open(os.path.join(HERE, name), "w") as out:
            out.write(text)
    for name in ["tbssfirst_pie", "datatls_pie_al"]:
        subprocess.run(
            ["patch", "-s", "-o", f"{name}.ld", "pie.ld", f"{name}.patch"],
            cwd=HERE,
            check=True,
        )


if __name__ == "__main__":
    main()
