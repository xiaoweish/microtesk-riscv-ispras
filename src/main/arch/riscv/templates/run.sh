#!/bin/bash

cur_dir=$(pwd)
out_dir="$MICROTESK_HOME/output/${cur_dir##*arch/riscv/templates}/$1"
mkdir $out_dir -p

sh $MICROTESK_HOME/bin/generate.sh riscv $1.rb \
   --code-file-prefix $1 \
   --code-file-extension s \
   --output-dir $out_dir \
   --verbose -debug-print \
   --asserts-enabled \
   1>$out_dir/$1.stdout \
   2>$out_dir/$1.stderr
