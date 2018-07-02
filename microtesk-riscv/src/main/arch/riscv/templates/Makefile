TESTS = coverage\
        groups\
        preparators_test\
        random

SELFCHECK_TESTS = selfchecks

all: $(TESTS) $(SELFCHECK_TESTS)

$(TESTS):
	sh run.sh $@
	sh run-toolchain.sh $@

$(SELFCHECK_TESTS):
	sh run-selfchecks.sh $@
	sh run-toolchain.sh $@

clean:
	rm $(MICROTESK_HOME)/*.s $(MICROTESK_HOME)/*.ld \
	$(MICROTESK_HOME)/*.o $(MICROTESK_HOME)/*.bin $(MICROTESK_HOME)/*.elf \
	$(MICROTESK_HOME)/*.stdout $(MICROTESK_HOME)/*.stderr -f
