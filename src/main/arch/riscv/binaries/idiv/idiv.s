	.file	"idiv.c"
	.option nopic
	.text
	.align	1
	.globl	idiv
	.type	idiv, @function
idiv:
	mv	a5,a0
	li	a0,0
	blt	a5,a1,.L2
.L3:
	subw	a5,a5,a1
	addiw	a0,a0,1
	ble	a1,a5,.L3
.L2:
	sw	a5,0(a2)
	ret
	.size	idiv, .-idiv
	.ident	"GCC: (GNU) 9.2.0"
	.section	.note.GNU-stack,"",@progbits
