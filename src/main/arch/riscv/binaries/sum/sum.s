	.file	"sum.c"
	.option nopic
	.text
	.align	1
	.globl	sum
	.type	sum, @function
sum:
	ble	a1,zero,.L4
	addiw	a4,a1,-1
	slli	a4,a4,32
	addi	a3,a0,4
	srli	a4,a4,30
	mv	a5,a0
	add	a4,a4,a3
	li	a0,0
.L3:
	lw	a3,0(a5)
	addi	a5,a5,4
	addw	a0,a3,a0
	bne	a4,a5,.L3
	ret
.L4:
	li	a0,0
	ret
	.size	sum, .-sum
	.ident	"GCC: (GNU) 9.2.0"
	.section	.note.GNU-stack,"",@progbits
