TESTS = coverage\
        groups\
        preparators_test\
        random

SELFCHECK_TESTS = selfchecks

all:\
	$(TESTS) \
	$(SELFCHECK_TESTS)
	make -C algorithm
	make -C autogen
	make -C branch
	make -C instruction
	make -C registers
	make -C sequence

$(TESTS):
	sh run.sh $@
	sh run-toolchain.sh $@

$(SELFCHECK_TESTS):
	sh run-selfchecks.sh $@
	sh run-toolchain.sh $@

clean:
	rm $(MICROTESK_HOME)/*.s \
	   $(MICROTESK_HOME)/*.ld \
	   $(MICROTESK_HOME)/*.dump \
	   $(MICROTESK_HOME)/*.o \
	   $(MICROTESK_HOME)/*.bin \
	   $(MICROTESK_HOME)/*.elf \
	   $(MICROTESK_HOME)/*.stdout \
	   $(MICROTESK_HOME)/*.stderr -f
