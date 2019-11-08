	.file	"euclid.c"
	.option nopic
	.text
	.align	1
	.globl	euclid
	.type	euclid, @function
euclid:
	beq	a0,a1,.L11
.L2:
	ble	a0,a1,.L4
	subw	a0,a0,a1
	bne	a1,a0,.L2
	ret
.L11:
	ret
.L4:
	subw	a1,a1,a0
	bne	a0,a1,.L2
	j	.L11
	.size	euclid, .-euclid
	.ident	"GCC: (GNU) 9.2.0"
	.section	.note.GNU-stack,"",@progbits
