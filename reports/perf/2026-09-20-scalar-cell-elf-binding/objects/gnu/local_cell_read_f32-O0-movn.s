.text
.balign 4
.global local_cell_read_f32
.type local_cell_read_f32, %function
local_cell_read_f32:
stp x20, x19, [sp, #-32]!
stp x29, x30, [sp, #16]
add x29, sp, #16
sub sp, sp, #16
movn w0, #65535
movk w0, #49580, lsl #16
fmov s1, w0
sub x19, x29, #20
str s1, [x19]
mov x0, x19
bl c_change
ldr s0, [x19]
add sp, sp, #16
ldp x29, x30, [sp, #16]
ldp x20, x19, [sp], #32
ret
.size local_cell_read_f32, .-local_cell_read_f32
