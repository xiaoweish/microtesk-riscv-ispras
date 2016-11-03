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

    addi r1, r0, 0x11
    trace "(add): r1 = %x", gpr_observer(1)
    add r2, r1, r1
    trace "(add): r2 = %x", gpr_observer(2)
    addi r3, r0, 0x1
    trace "(add): r3 = %x", gpr_observer(3)

    ori r4, r2, 0x11
    trace "(add): r4 = %x", gpr_observer(4)
    add_d r5, r4, r4
    trace "(add): r5 = %x", gpr_observer(5)
    nop
    nop
  end

end
