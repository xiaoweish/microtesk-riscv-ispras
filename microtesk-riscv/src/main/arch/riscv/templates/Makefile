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
        instruction_rv64c\
        bubble_sort_byte\
        bubble_sort_hword\
        bubble_sort_word\
        coverage\
        euclid\
        groups\
        int_divide\
        int_sqrt\
        min_max\
        preparators_test\
        random\
        register_allocation

SELFCHECK_TESTS = selfcheck_example

all: $(TESTS) $(SELFCHECK_TESTS)

$(TESTS):
	sh run.sh $@

$(SELFCHECK_TESTS):
	sh run-sc.sh $@

clean:
	rm *.s *.o *.bin *.elf *.stdout *.stderr -f