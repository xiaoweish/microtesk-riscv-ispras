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
# This small tests for MMU instructions.
#

class InstructionMMU < RISCVBaseTemplate

  def run
    trace "Run MMU instruction:"

    #addi r1, r0, 0x0fff
    #addi r2, r0, 0x0123
    #addi r5, r0, 0x0f00
    trace "\nRISCV Load/Store:\n"

    #sw r2, 0x0, r1
    trace "r2 = %x", gpr_observer(2)
    #sw r5, 0x4, r1
    trace "r5 = %x", gpr_observer(5)

    #lw r3, 0x0, r1
    trace "r3 = %x", gpr_observer(3)
    #lw r4, 0x1, r1
    trace "r4 = %x", gpr_observer(4)
  end

end