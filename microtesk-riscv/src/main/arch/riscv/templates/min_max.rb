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
# This test template demonstrates how to work with data declaration constucts.
# The generated program finds minimum and maximum in a 5-element array
# storing random numbers from 0 to 31. 
#
class MinMaxTemplate < RISCVBaseTemplate

  def pre
    super

    data {
      org 0x0
      align 8
      label :data
      word rand(0, 127), rand(0, 127), rand(0, 127), rand(0, 127), rand(0, 127), rand(0, 127)
      word rand(0, 127), rand(0, 127), rand(0, 127), rand(0, 127), rand(0, 127), rand(0, 127)
      word rand(0, 127), rand(0, 127), rand(0, 127), rand(0, 127)
      label :end
      space 1
    }
  end

  def run
    # trace_data :data, :end

    load_address_to_reg t0, :data
    load_address_to_reg t1, :end
    #la t0, :data
    #la t1, :end

    lw t2, t0, 0
    Or s0, zero, t2 
    Or s1, zero, t2

    label :cycle
    addi t0, t0, 4

    beq t0, t1, :done
    lw t2, t0, 0

    slt t3, t2, s0
    beq t3, zero, :test_max
    nop
    Or s0, zero, t2 

    label :test_max
    slt t4, s1, t2
    beq t4, zero, :cycle
    nop
    Or s1, zero, t2

    j :cycle
    nop

    label :done
    trace "\nmin(r16)=%d, max(r17)=0x%x", gpr_observer(8), gpr_observer(9)
  end

end
