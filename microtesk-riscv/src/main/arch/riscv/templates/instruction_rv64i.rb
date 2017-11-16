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
# This small tests for RV64I instructions.
#

class InstructionRV64I < RISCVBaseTemplate

  def run
    trace "Run RV64I instruction:"
    nop

    if rv64i == true then
      lwu t0, t1, 0x0
      trace "t0 = %x", gpr_observer(5)

      auipc s0, 0x80
      trace "s0 = %x", gpr_observer(8)
      srli s0, s0, 12
      slli s0, s0, 12
      srai t0, s0, 12

      ld t2, s0, 0x0
      sd t4, s0, 0x0

      addiw a0, a1, 0x11
      slliw t0, a1, 0x11
      srliw t1, a1, 0x11
      sraiw t2, a1, 0x11

      addw t1, t2, t3
      subw t2, t3, t4

      sllw t0, t1, t2
      srlw t0, t1, t2
      sraw t0, t1, t2
    else
      trace "Error: RV64I"
    end

    nop
  end

end
