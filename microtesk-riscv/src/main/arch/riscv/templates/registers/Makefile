TESTS = registers\
        register_allocation\
        register_reservation

all: $(TESTS)

$(TESTS):
	sh ../run.sh $@
	sh ../run-toolchain.sh $@
