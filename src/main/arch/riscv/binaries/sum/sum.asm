bge zero, a1, 26
addiw a4, a1, -1
slli a4, a4, 0x20
addi a3, a0, 4
srli a4, a4, 0x1e
addi a5, a0, 0
add a4, a4, a3
addi a0, zero, 0
lw a3, 0(a5)
addi a5, a5, 4
addw a0, a3, a0
bne a4, a5, -6
jalr zero, ra, 0
addi a0, zero, 0
jalr zero, ra, 0
