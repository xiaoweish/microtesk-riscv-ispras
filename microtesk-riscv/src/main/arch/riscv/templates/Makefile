TESTS = coverage\
        groups\
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