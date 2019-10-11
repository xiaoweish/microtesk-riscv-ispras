#!/bin/bash

cur_dir=$(pwd)
out_dir="$MICROTESK_HOME/output/${cur_dir##*arch/riscv/templates}/$1"

rm -r $out_dir
