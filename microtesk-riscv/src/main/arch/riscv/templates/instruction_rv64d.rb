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
# This small tests for RV64D instructions.
#

class InstructionRV64D < RISCVBaseTemplate

  def run
    trace "Run RV64D instruction:"
    nop

    if rv64d == true then
      fcvt_l_d t0, ft0
      fcvt_lu_d t0, ft0
      fcvt_d_l ft0, t0
      fcvt_d_lu ft0, t0

      fmv_x_d t0, ft0
      fmv_d_x ft0, t0
    else
      trace "Error: RV64D"
    end

    nop
  end

end
