	.file	"strlen.c"
	.option nopic
	.text
	.align	1
	.globl	strlen
	.type	strlen, @function
strlen:
	lbu	a5,0(a0)
	beq	a5,zero,.L4
	mv	a5,a0
.L3:
	lbu	a4,1(a5)
	addi	a5,a5,1
	bne	a4,zero,.L3
	sub	a0,a5,a0
	ret
.L4:
	li	a0,0
	ret
	.size	strlen, .-strlen
	.ident	"GCC: (GNU) 9.2.0"
	.section	.note.GNU-stack,"",@progbits
