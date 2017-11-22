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
# This test template demonstrates how to generate test cases by using combinators and compositors.
#
class ArithmeticTemplate < RISCVBaseTemplate

  def run
    # :combinator => 'product': all possible combinations of the inner blocks' instructions.
    # :compositor => 'random' : random composition (merging) of the combined instructions.
    block(:combinator => 'product', :compositor => 'random') {
      iterate {
        xor x(_), x(_), x(_)
        lui x(_), _
      }

      iterate {
        AND   x(_), x(_), x(_)
        OR    x(_), x(_), x(_)
      }

      iterate {
        auipc   x(_), _
      }
    }.run
  end
end
