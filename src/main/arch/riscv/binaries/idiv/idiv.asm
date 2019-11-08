addi a5, a0, 0
addi a0, zero, 0
blt a5, a1, 8
subw a5, a5, a1
addiw a0, a0, 1
bge a5, a1, -4
sw a5, 0(a2)
jalr zero, ra, 0
