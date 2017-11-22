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
# This test template demonstrates how to generate test cases based on
# constraints extracted from instruction specifications.
#
class CoverageTemplate < RISCVBaseTemplate

  def run
    # ADD instruction with biased operand values.
    #TODO: add t0, t1, t2 do situation('IntegerOverflow') end
    add t3, t4, t5 do situation('normal') end
  end

end
