#
# MicroTESK MIPS64 Edition
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
class BubbleSortByteTemplate < RISCVBaseTemplate
  def pre
    super

    data {
      label :data
      byte rand(1, 9), rand(1, 9), rand(1, 9), rand(1, 9)
      byte rand(1, 9), rand(1, 9), rand(1, 9), rand(1, 9)
      byte rand(1, 9), rand(1, 9), rand(1, 9), rand(1, 9)
      label :end
      space 1
    }
  end

  def run
    trace_data :data, :end

    addi a0, zero, 1
    nop
    add s0, zero, zero
    add s1, zero, zero
    #la s0, :data # TODO
    auipc s0, 0x80
    srli s0, s0, 12
    slli s0, s0, 12
    nop
    nop
#    la s1, :end
    auipc s1, 0x80
    srli s1, s1, 12
    slli s1, s1, 12
    addi s1, s1, 0xc

    #Or t0, zero, zero
    ########################### Outer loop starts ##############################
    label :repeat
    Or t0, zero, zero

    addi t1, s0, 1
    ########################### Inner loop starts ##############################
    label :for
    beq t1, s1, :exit_for
    sub t2, t1, a0 # a0 = 1;

    lb t4, t1, 0
    lb t5, t2, 0

    slt t6, t4, t5
    beq t6, zero, :next
    nop

    addi t0, zero, 0xf # t0 != 0

    sb t4, t2, 0
    sb t5, t1, 0
    nop

    label :next
    addi t1, t1, 1
    j :for
    nop # TODO
    ############################ Inner loop ends ###############################
    label :exit_for

    bne t0, zero, :repeat
    ############################ Outer loop ends ###############################

    lb a1, s0, 0
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 1
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 2
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 3
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 4
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 5
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 6
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 7
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 8
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 9
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 10
    trace "a1 = %x", gpr_observer(11)
    lb a1, s0, 11
    trace "a1 = %x", gpr_observer(11)

    trace " 0x6, 0x6, 0x8, 0x1"
    trace " 0x9, 0x6, 0x3, 0x3"
    trace " 0x9, 0x5, 0x9, 0x2"

    trace_data :data, :end
  end

end
