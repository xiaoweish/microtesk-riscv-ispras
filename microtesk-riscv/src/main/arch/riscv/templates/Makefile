TESTS = arithmetic\
        block\
        instruction_rv32i\
        instruction_rv64i\
        instruction_rv32m\
        instruction_rv64m\
        instruction_rv32a\
        instruction_rv64a\
        instruction_rv32f\
        instruction_rv64f\
        instruction_rv32d\
        instruction_rv64d\
        bubble_sort_byte\
        bubble_sort_hword\
        bubble_sort_word\
        coverage\
        euclid\
        groups\
        int_divide

all: $(TESTS)

$(TESTS):
	sh run.sh $@

clean:
	rm *.s *.o *.bin *.elf *.stdout *.stderr -f
