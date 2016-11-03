TESTS = instruction_alu\
        instruction_bpu\
        instruction_mmu

all: $(TESTS)

$(TESTS):
	sh run.sh $@

clean:
	rm *.s *.o *.bin *.elf *.stdout *.stderr -f
