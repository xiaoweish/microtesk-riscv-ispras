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
# This small tests for RV64M instructions.
#

class InstructionRV64M < RISCVBaseTemplate

  def run
    trace "Run 64M instruction:"
    nop

    if rv64m == true then
      mulw t0, t1, t2
      divw t0, t1, t2
      divuw t0, t1, t2
      remw t0, t1, t2
      remuw t0, t1, t2
    else
      trace "Error: RV64M"
    end

    nop
    nop
  end

end
