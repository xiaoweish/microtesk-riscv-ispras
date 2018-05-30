#!/bin/bash
sh $MICROTESK_HOME/bin/generate.sh --rev-id RV64FULL riscv $1.rb --code-file-prefix $1 --code-file-extension s -v -sd 1>$MICROTESK_HOME/$1.stdout 2>$MICROTESK_HOME/$1.stderr
