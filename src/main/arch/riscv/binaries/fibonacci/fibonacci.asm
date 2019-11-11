addi a5, zero, 1
sd a5, 0(a0)
sd a5, 8(a0)
addi a5, zero, 2
bgeu a5, a1, 52
addi a5, zero, 4
bgeu a5, a1, 50
addi a3, a1, -5
andi a3, a3, -2
addi a2, a0, 16
addi a3, a3, 4
addi a4, zero, 1
addi a5, zero, 1
addi a6, zero, 2
add a5, a5, a4
add a4, a4, a5
sd a5, 0(a2)
sd a4, 8(a2)
addi a6, a6, 2
addi a2, a2, 16
bne a6, a3, -12
slli a5, a3, 0x3
add a5, a0, a5
ld a4, -16(a5)
ld a2, -8(a5)
addi a5, a5, 8
addi a3, a3, 1
add a4, a4, a2
sd a4, -8(a5)
bltu a3, a1, -12
jalr zero, ra, 0
addi a3, zero, 2
jal zero, 0xfffea
