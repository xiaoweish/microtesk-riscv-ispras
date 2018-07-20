TESTS = fadd\
        fclass\
        fcmp\
        fcvt\
        fcvt_w\
        fdiv\
        fmadd\
        fmin\
        ldst\
        move\
        structural

all: $(TESTS)

$(TESTS):
	sh ../../run.sh $@
	sh ../../run-toolchain.sh $@
