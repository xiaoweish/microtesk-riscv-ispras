addi sp, sp, -16
sd s0, 0(sp)
sd ra, 8(sp)
addi s0, a0, 0
beq a2, zero, 6
andi a1, a1, 255
jal ra, 0xffff4
ld ra, 8(sp)
addi a0, s0, 0
ld s0, 0(sp)
addi sp, sp, 16
jalr zero, ra, 0
