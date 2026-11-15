.text
.balign 4
.global aliased_f64_read
.type aliased_f64_read, %function
aliased_f64_read:
stp x20, x19, [sp, #-32]!
stp x29, x30, [sp, #16]
add x29, sp, #16
sub sp, sp, #16
sub x19, x29, #24
str d0, [x19]
mov x0, x19
mov v0.16b, v1.16b
bl c_change
ldr d0, [x19]
add sp, sp, #16
ldp x29, x30, [sp, #16]
ldp x20, x19, [sp], #32
ret
.size aliased_f64_read, .-aliased_f64_read
