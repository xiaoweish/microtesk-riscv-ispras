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
# This small tests for RV32A instructions.
#

class InstructionRV32A < RISCVBaseTemplate

  def run
    trace "Run RV32A instruction:"
    nop

    if rv32a == true then
      auipc s0, 0x80
      srli s0, s0, 12
      slli s0, s0, 12

      lr_w t0, s0
      sc_w t0, t1, s0

      amoswap_w t0, t1, s0
      amoadd_w t0, t1, s0
      amoand_w t0, t1, s0
      amoor_w t0, t1, s0
      amoxor_w t0, t1, s0
      amomin_w t0, t1, s0
      amomax_w t0, t1, s0
      amominu_w t0, t1, s0
      amomaxu_w t0, t1, s0
    else
      trace "Error: RV32A"
    end

    nop
    nop
  end

end
