// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
.text
.global checked_bounds_unwind
.type checked_bounds_unwind, %function
checked_bounds_unwind:
    sub sp, sp, #160
    stp x19, x20, [sp, #0]
    stp x21, x22, [sp, #16]
    stp x23, x24, [sp, #32]
    stp x25, x26, [sp, #48]
    stp x27, x28, [sp, #64]
    stp x29, x30, [sp, #80]
    stp d8, d9, [sp, #96]
    stp d10, d11, [sp, #112]
    stp d12, d13, [sp, #128]
    stp d14, d15, [sp, #144]
    mov x29, sp
    mov x19, #19
    mov x20, #20
    mov x21, #21
    mov x22, #22
    mov x23, #23
    mov x24, #24
    mov x25, #25
    mov x26, #26
    mov x27, #27
    mov x28, #28
    mov x9, #8
    fmov d8, x9
    mov x9, #9
    fmov d9, x9
    mov x9, #10
    fmov d10, x9
    mov x9, #11
    fmov d11, x9
    mov x9, #12
    fmov d12, x9
    mov x9, #13
    fmov d13, x9
    mov x9, #14
    fmov d14, x9
    mov x9, #15
    fmov d15, x9
    bl bounds_unwind
    mov x9, sp
    cmp x9, x29
    b.ne .Labi_fail
    .irp reg,19,20,21,22,23,24,25,26,27,28
    cmp x\reg, #\reg
    b.ne .Labi_fail
    .endr
    .irp reg,8,9,10,11,12,13,14,15
    fmov x9, d\reg
    cmp x9, #\reg
    b.ne .Labi_fail
    .endr
    ldp x19, x20, [sp, #0]
    ldp x21, x22, [sp, #16]
    ldp x23, x24, [sp, #32]
    ldp x25, x26, [sp, #48]
    ldp x27, x28, [sp, #64]
    ldp x29, x30, [sp, #80]
    ldp d8, d9, [sp, #96]
    ldp d10, d11, [sp, #112]
    ldp d12, d13, [sp, #128]
    ldp d14, d15, [sp, #144]
    add sp, sp, #160
    ret
.Labi_fail:
    mov x0, #77
    mov x8, #93
    svc #0
.size checked_bounds_unwind, .-checked_bounds_unwind
.section .note.GNU-stack,"",%progbits
