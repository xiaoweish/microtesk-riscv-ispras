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
# This small tests for RV64F instructions.
#

class InstructionRV64F < RISCVBaseTemplate

  def run
    trace "Run RV64F instruction:"
    nop

    if rv64f == true then
      fcvt_l_s t0, ft0
      fcvt_lu_s t0, ft0
      fcvt_s_l ft0, t0
      fcvt_s_lu ft0, t0
    else
      trace "Error: RV64F"
    end

    nop
  end

end
