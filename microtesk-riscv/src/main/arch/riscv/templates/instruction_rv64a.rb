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
# This small tests for RV64A instructions.
#

class InstructionRV64A < RISCVBaseTemplate

  def run
    trace "Run RV64A instruction:"
    nop

    if rv64a == true then
      auipc s0, 0x80
      srli s0, s0, 12
      slli s0, s0, 12

      lr_d t0, s0
      sc_d t0, t1, s0

      amoswap_d t0, t1, s0
      amoadd_d t0, t1, s0
      amoand_d t0, t1, s0
      amoor_d t0, t1, s0
      amoxor_d t0, t1, s0
      amomin_d t0, t1, s0
      amomax_d t0, t1, s0
      amominu_d t0, t1, s0
      amomaxu_d t0, t1, s0
    else
      trace "Error: RV64A"
    end

    nop
  end

end
