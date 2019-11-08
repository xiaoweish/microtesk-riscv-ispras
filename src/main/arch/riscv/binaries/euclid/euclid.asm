beq a0, a1, 10
bge a1, a0, 10
subw a0, a0, a1
bne a1, a0, -4
jalr zero, ra, 0
jalr zero, ra, 0
subw a1, a1, a0
bne a0, a1, -12
jal zero, 0xffffa
