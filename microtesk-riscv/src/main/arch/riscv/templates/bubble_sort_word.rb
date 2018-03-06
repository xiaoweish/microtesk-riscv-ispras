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
# design under test. The described test program is a simple implemention of
# the bubble sort algorithm. The algorithm in pseudocode (from Wikipedia):
#
# procedure bubbleSort( A : list of sortable items )
#   n = length(A)
#   repeat
#     swapped = false
#     for i = 1 to n-1 inclusive do
#       /* if this pair is out of order */
#       if A[i-1] > A[i] then
#         /* swap them and remember something changed */
#         swap( A[i-1], A[i] )
#         swapped = true
#       end if
#     end for
#   until not swapped
# end procedure
#
class BubbleSortWordTemplate < RISCVBaseTemplate
  def pre
    super

    data {
      label :data
      word rand(1, 9), rand(1, 9), rand(1, 9), rand(1, 9)
      word rand(1, 9), rand(1, 9), rand(1, 9), rand(1, 9)
      word rand(1, 9), rand(1, 9), rand(1, 9), rand(1, 9)
      label :end
      space 1
    }
  end

  def run
    trace_data :data, :end

    add s0, zero, zero
    add s1, zero, zero
    load_address_to_reg s0, :data
    load_address_to_reg s1, :end
    nop
#    la s0, :data
#    la s1, :end

    addi a0, zero, 4
    nop
    ########################### Outer loop starts ##############################
    label :repeat
    Or t0, zero, zero

    addi t1, s0, 4
    ########################### Inner loop starts ##############################
    label :for
    beq t1, s1, :exit_for
    sub t2, t1, a0 # a0 = 4;

    lw t4, t1, 0
    lw t5, t2, 0

    slt t6, t4, t5
    beq t6, zero, :next
    nop

    addi t0, zero, 0xf # t0 != 0

    sw t4, t2, 0
    sw t5, t1, 0

    label :next
    addi t1, t1, 4
    j :for
    nop
    ############################ Inner loop ends ###############################
    label :exit_for

    bne t0, zero, :repeat
    nop
    ############################ Outer loop ends ###############################

    trace_data :data, :end
  end

end
