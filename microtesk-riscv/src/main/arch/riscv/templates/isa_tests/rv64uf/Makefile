TESTS = fadd\
        fclass\
        fcmp\
        fcvt\
        fcvt_w\
        fdiv\
        fmadd

all: $(TESTS)

$(TESTS):
	sh ../../run.sh $@
	sh ../../run-toolchain.sh $@
