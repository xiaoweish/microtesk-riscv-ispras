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
# This test template demonstrates how to use instruction blocks.
#
class BlockTemplate < RISCVBaseTemplate

  def run
    # Adds nop to all test cases as a placeholder to return from an exception
    epilogue { nop }

    # Produces a single test case that consists of three instructions
    sequence {
      Add t0, t1, t2
      Sub t3, t4, t5
      And x(_), x(_), x(_)
    }.run

    # Atomic sequence. Works as sequence in this context.
    atomic {
      Add t0, t1, t2
      Sub t3, t4, t5
      And x(_), x(_), x(_)
    }.run

    # Produces three test cases each consisting of one instruction
    iterate {
      Add t0, t1, t2
      Sub t3, t4, t5
      And x(_), x(_), x(_)
    }.run

    # Produces four test cases consisting of two instructions
    # (Cartesian product composed in a random order)
    block(:combinator => 'product', :compositor => 'random') {
      iterate {
        Add t0, t1, t2
        Sub t3, t4, t5
      }

      iterate {
        And x(_), x(_), x(_)
        nop
      }
    }.run

    # Merges two sequnces in random fashion. Atomic sequences are unmodifiable.
    block(:combinator => 'diagonal', :compositor => 'random', :obfuscator => 'random') {
      sequence {
        Add t0, t1, t2
        Sub t3, t4, t5
        Or  s3, s4, s5
      }

      atomic {
        prologue { comment 'Atomic starts' }
        epilogue { comment 'Atomic ends' }

        And x(_), x(_), x(_)
        nop
      }
    }.run
  end

end
