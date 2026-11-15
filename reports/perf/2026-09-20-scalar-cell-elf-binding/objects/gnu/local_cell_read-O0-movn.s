.text
.balign 4
.global local_cell_read
.type local_cell_read, %function
local_cell_read:
stp x20, x19, [sp, #-32]!
stp x29, x30, [sp, #16]
add x29, sp, #16
sub sp, sp, #16
movn x0, #65535
movk x0, #0, lsl #16
movk x0, #32768, lsl #32
movk x0, #49205, lsl #48
fmov d1, x0
sub x19, x29, #24
str d1, [x19]
mov x0, x19
bl c_change
ldr d0, [x19]
add sp, sp, #16
ldp x29, x30, [sp, #16]
ldp x20, x19, [sp], #32
ret
.size local_cell_read, .-local_cell_read
