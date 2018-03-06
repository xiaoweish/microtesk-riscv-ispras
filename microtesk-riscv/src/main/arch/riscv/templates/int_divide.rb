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
# design under test. The described program calculates the quotient and
# the remainder of division of two random numbers by using
# the simple algorithm of repeated subtraction.
#
class IntDivideTemplate < RISCVBaseTemplate

  def run
    trace "Division: Debug Output"

    dividend = rand(0, 1023)
    divisor  = rand(1, 63) #zero is excluded

    addi s0, zero, dividend
    addi s1, zero, divisor

    trace "\nInput parameter values: dividend x8(s0) = %d, divisor x9(s1) = %d\n",
      gpr_observer(8), gpr_observer(9)

    add t0, zero, zero
    add t1, zero, s0

    label :cycle
    trace "\nCurrent register values: x5(t0) = %d, x6(t1) = %d, x7(t2) = %d\n",
      gpr_observer(5), gpr_observer(6), gpr_observer(7)

    sub t2, t1, s1
    slt t3, t2, zero

    bne t3, zero, :done
    nop

    add t1, zero, t2
    addi t0, t0, 1

    j :cycle
    nop

    label :done
    trace "\nCurrent register values: x5(t0) = %d, x6(t1) = %d\n",
      gpr_observer(5), gpr_observer(6)
  end

end
