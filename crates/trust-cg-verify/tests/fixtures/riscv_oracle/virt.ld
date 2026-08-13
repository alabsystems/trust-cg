/* virt.ld — linker script for the bare-metal RV64 oracle on QEMU `virt`.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Copyright 2026 Andrew Yates | License: Apache-2.0
 *
 * QEMU's `virt` machine loads a `-kernel` ELF and (with `-bios none`) begins
 * execution at the firmware/kernel load address 0x80000000. We place .text.start
 * (the `_start` trampoline) first so the entry instruction is at 0x80000000, then
 * the rest of the program, and reserve a small stack at the end.
 */
ENTRY(_start)

SECTIONS {
  . = 0x80000000;

  .text : {
    *(.text.start)
    *(.text .text.*)
  }

  .rodata : { *(.rodata .rodata.*) }
  .data   : { *(.data .data.*) }
  .sdata  : { *(.sdata .sdata.*) }
  .bss    : { *(.bss .bss.*) *(.sbss .sbss.*) *(COMMON) }

  . = ALIGN(16);
  . += 0x10000;          /* 64 KiB stack */
  _stack_top = .;
}
