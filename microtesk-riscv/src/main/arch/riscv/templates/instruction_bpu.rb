#
# MicroTESK RISC-V Edition
#
# Copyright (c) 2016 Institute for System Programming of the Russian Academy of Sciences
# All Rights Reserved
#
# Institute for System Programming of the Russian Academy of Sciences (ISP RAS)
# 25 Alexander Solzhenitsyn st., Moscow, 109004, Russia
# http://www.ispras.ru
#

require_relative 'riscv_base'

#
# Description:
#
# This small tests for BPU instructions.
#

class InstructionBPU < RISCVBaseTemplate

  def run
    trace "Run BPU instruction:"

    trace "\n\n"

    nop
    trace "0"
    b :branch1
    label :branch2
    trace "2"
    nop
    b :branch3
    label :branch1
    trace "1"
    b :branch2
    nop
    label :branch3
    trace "3"
    nop

  end

end