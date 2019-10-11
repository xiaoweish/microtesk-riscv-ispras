#!/bin/bash

cur_dir=$(pwd)
out_dir="$MICROTESK_HOME/output/${cur_dir##*arch/riscv/templates}/$1"

if [ -x "$(command -v riscv64-unknown-elf-gcc)" ] &&
   [ -x "$(command -v riscv64-unknown-elf-objdump)" ] ; then
  for file in $out_dir/$1*.s; do
    riscv64-unknown-elf-gcc -nostdlib -nostartfiles -Wa,-march=rv64imafdc \
      -T$out_dir/$1.ld $file -o ${file%%.*}.elf
    riscv64-unknown-elf-objdump ${file%%.*}.elf --disassemble-all --disassemble-zeroes \
      --section=.text --section=.text.startup --section=.text.init --section=.data\
      >${file%%.*}.dump
  done
else
  echo "Warning: RISC-V toolchain is not installed."
fi
