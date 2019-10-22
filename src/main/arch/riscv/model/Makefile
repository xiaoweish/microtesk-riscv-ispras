ARCH=riscv

all:
	sh $(MICROTESK_HOME)/bin/compile.sh $(ARCH).nml --extension-dir ../extensions --rev-id RV32FULL
	sh $(MICROTESK_HOME)/bin/autogen.sh riscv \
	--output-dir $(MICROTESK_HOME)/arch/riscv/templates/autogen/ \
	--base-template-name RiscVBaseTemplate --base-template-path '../riscv_base' \
	--ignored-instructions 'ecall:ebreak:fence:fencei:mret:sret:uret:wfi:c_addi4spn:'\
	'c_lq:c_flw:c_fld:c_sw:c_sd:c_sq:c_fsw:c_fsd:c_nop:c_addi:c_addiw:c_addi16sp:'\
	'c_li:c_lui:c_srli:c_srli64:c_srai:c_srai64:c_lwsp:c_ldsp:c_swsp:c_sdsp:c_lw:c_ld:'\
	'c_andi:c_add:c_or:c_xor:c_sub:c_and:c_addw:c_subw:c_j:c_jal:c_beqz:c_bnez:'\
	'c_slli:c_slli64:c_lqsp:c_flwsp:c_fldsp:c_jr:c_jalr:c_mv:c_ebreak:c_sqsp:c_fswsp:c_fsdsp:jalr'
