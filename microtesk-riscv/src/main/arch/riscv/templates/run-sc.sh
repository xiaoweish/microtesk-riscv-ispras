#!/bin/bash
sh $MICROTESK_HOME/bin/generate.sh --rev-id RV64FULL riscv $1.rb --self-checks --code-file-prefix $1 --code-file-extension s -v -sd 1>$1.stdout 2>$1.stderr
