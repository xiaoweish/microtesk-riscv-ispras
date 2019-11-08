	.file	"memset.c"
	.option nopic
	.text
	.align	1
	.globl	memset
	.type	memset, @function
memset:
	addi	sp,sp,-16
	sd	s0,0(sp)
	sd	ra,8(sp)
	mv	s0,a0
	beq	a2,zero,.L4
	andi	a1,a1,0xff
	call	memset
.L4:
	ld	ra,8(sp)
	mv	a0,s0
	ld	s0,0(sp)
	addi	sp,sp,16
	jr	ra
	.size	memset, .-memset
	.ident	"GCC: (GNU) 9.2.0"
	.section	.note.GNU-stack,"",@progbits
