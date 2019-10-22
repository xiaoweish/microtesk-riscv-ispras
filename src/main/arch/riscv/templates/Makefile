all:
	make -C debug
	make -C examples
	make -C algorithms
	make -C compliance
	make -C synthetics
	make -C autogen

clean:
	if [ -d $(MICROTESK_HOME)/output ]; then \
		rm -r -f $(MICROTESK_HOME)/output/*; \
	fi
