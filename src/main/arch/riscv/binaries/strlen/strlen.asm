lbu a5, 0(a0)
beq a5, zero, 14
addi a5, a0, 0
lbu a4, 1(a5)
addi a5, a5, 1
bne a4, zero, -4
sub a0, a5, a0
jalr zero, ra, 0
addi a0, zero, 0
jalr zero, ra, 0
