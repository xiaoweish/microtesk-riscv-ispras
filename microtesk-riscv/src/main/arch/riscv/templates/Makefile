TESTS = instruction_alu\
        instruction_bpu\
        instruction_mmu\
        instruction_rv32i\
        instruction_rv64i\
        bubble_sort_byte

all: $(TESTS)

$(TESTS):
	sh run.sh $@

clean:
	rm *.s *.o *.bin *.elf *.stdout *.stderr -f
