TESTS = instruction_la\
        instruction_ld_sd\
        instruction_li\
        instruction_lw_sw\
        instruction_lw_sw_sv32\
        instruction_rv32a\
        instruction_rv32d\
        instruction_rv32f\
        instruction_rv32i\
        instruction_rv32m\
        instruction_rv32v_gen1\
        instruction_rv64a\
        instruction_rv64d\
        instruction_rv64f\
        instruction_rv64i\
        instruction_rv64m\
        instruction_rvc

all: $(TESTS)

$(TESTS):
	sh ../run.sh $@
	sh ../run-toolchain.sh $@
