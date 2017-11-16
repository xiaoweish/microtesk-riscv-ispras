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
# This small tests for RV32M instructions.
#

class InstructionRV32M < RISCVBaseTemplate

  def run
    trace "Run RV32M instruction:"
    nop

    if rv32m == true then
      mul t0, t1, t2
      mulh t0, t1, t2
      mulhsu t0, t1, t2
      mulhu t0, t1, t2
      div t0, t1, t2
      divu t0, t1, t2
      rem t0, t1, t2
      remu t0, t1, t2
    else
      trace "Error: RV32M"
    end

    nop
    nop
  end

end
