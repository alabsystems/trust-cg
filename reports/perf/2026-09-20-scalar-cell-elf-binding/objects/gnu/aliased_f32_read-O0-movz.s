.text
.balign 4
.global aliased_f32_read
.type aliased_f32_read, %function
aliased_f32_read:
stp x20, x19, [sp, #-32]!
stp x29, x30, [sp, #16]
add x29, sp, #16
sub sp, sp, #16
sub x19, x29, #20
str s0, [x19]
mov x0, x19
mov v0.16b, v1.16b
bl c_change
ldr s0, [x19]
add sp, sp, #16
ldp x29, x30, [sp, #16]
ldp x20, x19, [sp], #32
ret
.size aliased_f32_read, .-aliased_f32_read
