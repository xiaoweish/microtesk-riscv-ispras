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
# This small tests for ALU instructions.
#

class InstructionALU < RISCVBaseTemplate

  def run
    trace "Run ALU instruction:"

    trace "\nRISC-V Arithmetic:\n"

    add r1, r2, r3
    trace "(add): r1 = %x", gpr_observer(1)

    nop
    nop
  end

end
