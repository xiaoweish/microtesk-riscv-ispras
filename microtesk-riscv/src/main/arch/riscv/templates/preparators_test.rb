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
#
class PreparatorsTest < RISCVBaseTemplate

  def run
    trace "Run preparators:"
    nop

    prepare t1, -1
    trace "prepare -1 in t1 = %x", gpr(6)
    nop

    prepare t1, -2
    trace "prepare -2 in t1 = %x", gpr(6)

    prepare t2, 0xFF120000
    trace "prepare in t2 = %x", gpr(7)

    add t1, t0, t0
    trace "(add): t1 = %x", gpr(6)
  end

end
