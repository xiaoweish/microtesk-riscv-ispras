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
# This test template demonstrates how MicroTESK can simulate the execution
# of a test program to predict the resulting state of a microprocessor
# design under test. The described program calculates the greatest common
# divisor of two 5-bit random numbers ([1..63]) by using the Euclidean 
# algorithm.
#
class EuclidTemplate < RISCVBaseTemplate

  def run
    trace "Euclidean Algorithm (RISCV): Debug Output"

    # Values from [1..63], zero is excluded because there is no solution
    val1 = rand(1, 63)
    val2 = rand(1, 63)

    trace "\nInput parameter values: %d, %d\n", val1, val2

    #prepare t1, val1
    #prepare t2, val2
    addi t1, zero, val1
    addi t2, zero, val2

    label :cycle
    trace "\nCurrent values: $t1($6)=%d, $t2($7)=%d\n", gpr_observer(6), gpr_observer(7)
    beq t1, t2, :done

    slt t0, t1, t2
    bne t0, zero, :if_less
    nop

    sub t1, t1, t2
    j :cycle
    nop

    label :if_less
    sub t2, t2, t1
    j :cycle

    label :done
    add t3, t1, zero

    trace "\nResult stored in $t3($28): %d", gpr_observer(28)
  end

end
