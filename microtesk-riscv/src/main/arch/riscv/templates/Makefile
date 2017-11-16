TESTS = instruction_rv32i\
        instruction_rv64i\
        instruction_rv32m\
        instruction_rv64m\
        instruction_rv32a\
        instruction_rv64a\
        bubble_sort_byte\
        bubble_sort_byte\
	euclid

all: $(TESTS)

$(TESTS):
	sh run.sh $@

clean:
	rm *.s *.o *.bin *.elf *.stdout *.stderr -f
