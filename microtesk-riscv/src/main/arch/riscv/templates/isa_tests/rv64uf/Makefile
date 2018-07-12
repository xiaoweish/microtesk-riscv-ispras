TESTS = fadd\
        fclass\
        fcmp\
        fcvt\
        fdiv\
        fmadd

all: $(TESTS)

$(TESTS):
	sh ../../run.sh $@
	sh ../../run-toolchain.sh $@
