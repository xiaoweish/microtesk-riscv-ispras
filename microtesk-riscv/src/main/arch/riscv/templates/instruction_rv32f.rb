#
# MicroTESK for RISC-V
#
# Copyright (c) 2017 Institute for System Programming of the Russian Academy of Sciences
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
# This small tests for RV32F instructions.
#

class InstructionRV32F < RISCVBaseTemplate

  def run
    trace "Run RV32F instruction:"
    nop

    if rv32f == true then
      auipc s0, 0x80
      srli s0, s0, 12
      slli s0, s0, 12

      fsw ft0, s0, 0x0
      flw ft0, s0, 0x0

    else
      trace "Error: RV32F"
    end

    nop
    nop
  end

end
