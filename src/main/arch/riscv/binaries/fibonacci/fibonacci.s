	.file	"fibonacci.c"
	.option nopic
	.text
	.align	1
	.globl	fibonacci
	.type	fibonacci, @function
fibonacci:
	li	a5,1
	sd	a5,0(a0)
	sd	a5,8(a0)
	li	a5,2
	bleu	a1,a5,.L1
	li	a5,4
	bleu	a1,a5,.L6
	addi	a3,a1,-5
	andi	a3,a3,-2
	addi	a2,a0,16
	addi	a3,a3,4
	li	a4,1
	li	a5,1
	li	a6,2
.L4:
	add	a5,a5,a4
	add	a4,a4,a5
	sd	a5,0(a2)
	sd	a4,8(a2)
	addi	a6,a6,2
	addi	a2,a2,16
	bne	a6,a3,.L4
.L3:
	slli	a5,a3,3
	add	a5,a0,a5
.L5:
	ld	a4,-16(a5)
	ld	a2,-8(a5)
	addi	a5,a5,8
	addi	a3,a3,1
	add	a4,a4,a2
	sd	a4,-8(a5)
	bgtu	a1,a3,.L5
.L1:
	ret
.L6:
	li	a3,2
	j	.L3
	.size	fibonacci, .-fibonacci
	.ident	"GCC: (GNU) 9.2.0"
	.section	.note.GNU-stack,"",@progbits
