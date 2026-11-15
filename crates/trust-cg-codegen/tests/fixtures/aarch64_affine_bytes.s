// Independent assembler controls for tests/aarch64_affine_bytes.rs.
// Reproduce with GNU as/objdump; these tools are not test dependencies:
// aarch64-linux-gnu-as -o /tmp/affine-controls.o aarch64_affine_bytes.s
// aarch64-linux-gnu-objdump -d /tmp/affine-controls.o
.text
.global affine64
affine64:
  mov x9, x0
  add x9, x9, #4095, lsl #12
  sub x9, x9, #4095
  add x0, x9, x0, lsl #2
  ret
.global affine32
affine32:
  mov w9, w0
  add w9, w9, #4095, lsl #12
  sub w9, w9, #4095
  add w0, w9, w0, lsl #2
  ret
.global constant64
constant64:
  movn x0, #0xffff
  movk x0, #0x1234, lsl #16
  ret
