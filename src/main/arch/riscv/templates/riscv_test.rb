#
# Copyright 2018 ISP RAS (http://www.ispras.ru)
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# THIS FILE IS BASED ON THE FOLLOWING RISC-V TEST SUITE HEADER:
# https://github.com/riscv/riscv-test-env/blob/master/p/riscv_test.h
# WHICH IS DISTRIBUTED UNDER THE FOLLOWING LICENSE:
#
# Copyright (c) 2012-2015, The Regents of the University of California (Regents).
# All Rights Reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
# 3. Neither the name of the Regents nor the
#    names of its contributors may be used to endorse or promote products
#    derived from this software without specific prior written permission.
#
# IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
# SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING
# OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS
# BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
# THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
# PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED
# HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE
# MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
#

require_relative 'riscv_encoding'

module RiscvTest
  include RiscvEncoding

  ##################################################################################################
  # Begin Macro
  ##################################################################################################

  # Assembler macro 'init' is replaced with dynamic method
  # 'RVTEST_INIT' that performs code inlining.
  #
  # def RVTEST_INIT
  #  text "init"
  # end

  def RVTEST_RV64U
    # text '.macro init'
    # text '.endm'

    proc = Proc.new {}
    RiscvTest.send(:define_method, :"RVTEST_INIT", proc)
  end

  def RVTEST_RV64UF
    # text '.macro init'
    # RVTEST_FP_ENABLE()
    # text '.endm'

    proc = Proc.new { RVTEST_FP_ENABLE() }
    RiscvTest.send(:define_method, :"RVTEST_INIT", proc)
  end

  def RVTEST_RV32U
    # text '.macro init'
    # text '.endm'

    proc = Proc.new {}
    RiscvTest.send(:define_method, :"RVTEST_INIT", proc)
  end

  def RVTEST_RV32UF
    # text '.macro init'
    # RVTEST_FP_ENABLE()
    # text '.endm'

    proc = Proc.new { RVTEST_FP_ENABLE() }
    RiscvTest.send(:define_method, :"RVTEST_INIT", proc)
   end

  def RVTEST_RV64M
    # text '.macro init'
    # RVTEST_ENABLE_MACHINE()
    # text '.endm'

    proc = Proc.new { RVTEST_ENABLE_MACHINE() }
    RiscvTest.send(:define_method, :"RVTEST_INIT", proc)
  end

  def RVTEST_RV64S
    # text '.macro init'
    # RVTEST_ENABLE_SUPERVISOR()
    # text '.endm'

    proc = Proc.new { RVTEST_ENABLE_SUPERVISOR() }
    RiscvTest.send(:define_method, :"RVTEST_INIT", proc)
  end

  def RVTEST_RV32M
    # text '.macro init'
    # RVTEST_ENABLE_MACHINE()
    # text '.endm'

    proc = Proc.new { RVTEST_ENABLE_MACHINE() }
    RiscvTest.send(:define_method, :"RVTEST_INIT", proc)
  end

  def RVTEST_RV32S
    # text '.macro init'
    # RVTEST_ENABLE_SUPERVISOR()
    # text '.endm'

    proc = Proc.new { RVTEST_ENABLE_SUPERVISOR() }
    RiscvTest.send(:define_method, :"RVTEST_INIT", proc)
  end

  def CHECK_XLEN
    li a0, 1
    slli a0, a0, 31
    if is_rev('RV64I') then bgez a0, label_f(1)
                       else bltz a0, label_f(1) end
    RVTEST_PASS()
label 1
  end

  def INIT_PMP
    la t0, label_f(1)
    csrw mtvec, t0
    # Set up a PMP to permit all accesses
    li t0, -1
    csrw pmpaddr0, t0
    li t0, PMP_NAPOT | PMP_R | PMP_W | PMP_X
    csrw pmpcfg0, t0
    align 2
label 1
  end

  def INIT_SATP
    la t0, label_f(1)
    csrw mtvec, t0
    csrwi satp, 0
    align 2
label 1
  end

  def DELEGATE_NO_TRAPS
  end

  def RVTEST_ENABLE_SUPERVISOR
    newline
    comment 'RVTEST_ENABLE_SUPERVISOR'

    li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1)
    csrs mstatus, a0
    li a0, SIP_SSIP | SIP_STIP
    csrs mideleg, a0

    newline
  end

  def RVTEST_ENABLE_MACHINE
    newline
    comment 'RVTEST_ENABLE_MACHINE'

    li a0, MSTATUS_MPP
    csrs mstatus, a0

    newline
  end

  def RVTEST_FP_ENABLE
    newline
    comment 'RVTEST_FP_ENABLE'

    li a0, MSTATUS_FS & (MSTATUS_FS >> 1)
    csrs mstatus, a0
    csrwi fcsr, 0

    newline
  end

  def RISCV_MULTICORE_DISABLE
    csrr a0, mhartid
label 1
    bnez a0, label_b(1)
  end

  #define EXTRA_TVEC_USER
  #define EXTRA_TVEC_MACHINE

  def EXTRA_INIT
  end

  def EXTRA_INIT_TIMER
  end

  def INTERRUPT_HANDLER
    # No interrupts should occur
    j :other_exception
  end

  def RVTEST_CODE_BEGIN
    text ".text"
    text ".globl TEST_FUNC_RET"

    global_label :TEST_FUNC_NAME
    la a0, :test_name
    lui a2, 0x10000000 >> 12

    label :prname_next
    lb a1, a0, 0
    beq a1, zero, :prname_done
    sw a1, a2, 0
    addi a0, a0, 1
    jal zero, :prname_next

    label :test_name
    ascii "TEST_FUNC_TXT"
    byte 0x0
    balign 4

    label :prname_done
    addi a1, zero, ".".ord
    sw a1, a2, 0

    #org 0xc0
    #align 6
    #weak :stvec_handler
    #weak :mtvec_handler

#label :trap_vector
    # test whether the test came from pass/fail
    #csrr a4, mcause

    #li a5, CAUSE_USER_ECALL
    #beq a4, a5, :_report

    #li a5, CAUSE_SUPERVISOR_ECALL
    #beq a4, a5, :_report

    #li a5, CAUSE_MACHINE_ECALL
    #beq a4, a5, :_report

    # if an mtvec_handler is defined, jump to it
    #la a4, :mtvec_handler
    #beqz a4, label_f(1)
    #jr a4

    # was it an interrupt or an exception?
#label 1
#    csrr a4, mcause
#    bgez a4, :handle_exception

#    INTERRUPT_HANDLER()
#label :handle_exception
    # we don't know how to handle whatever the exception was
#label :other_exception
    # some unhandlable exception occurred
#    li a0, 1
#label 1

#label :_report
#    j :sc_exit
#    nop
#    align 6
#global_label :_start
#    RISCV_MULTICORE_DISABLE()
#    DELEGATE_NO_TRAPS()
#    li TESTNUM(), 0
#    la t0, :trap_vector
#    csrw mtvec, t0
#    CHECK_XLEN()

    # if an stvec_handler is defined, delegate exceptions to it
 #   la t0, :stvec_handler
#    beqz t0, label_f(1)
#    csrw stvec, t0

#    li t0, (1 << CAUSE_LOAD_PAGE_FAULT)  |
#           (1 << CAUSE_STORE_PAGE_FAULT) |
#           (1 << CAUSE_FETCH_PAGE_FAULT) |
#           (1 << CAUSE_MISALIGNED_FETCH) |
#           (1 << CAUSE_USER_ECALL)       |
#           (1 << CAUSE_BREAKPOINT)
#    csrw medeleg, t0
#    csrr t1, medeleg
#    bne t0, t1, :other_exception

#label 1
#    csrwi mstatus, 0
#    RVTEST_INIT()

#    EXTRA_INIT()
#    EXTRA_INIT_TIMER()

#    la t0, :_run_test
#    csrw mepc, t0
#    csrr a0, mhartid
#    mret
#label :_run_test
  end

  ##################################################################################################
  # End Macro
  ##################################################################################################

  def RVTEST_CODE_END
    #label :sc_exit
    #nop
    #text "j SIM_EXIT"
    #pseudo 'unimp'
  end

  ##################################################################################################
  # Pass/Fail Macro
  ##################################################################################################

  def RVTEST_PASS
    lui a0, 0x10000000 >> 12
    addi a1, zero, "O".ord
    addi a2, zero, "K".ord
    addi a3, zero, "\n".ord
    sw a1, a0, 0x0
    sw a2, a0, 0x0
    sw a3, a0, 0x0
    text "jal zero, TEST_FUNC_RET"
  end

  def TESTNUM
    t3
  end

  def RVTEST_FAIL
    lui a0, 0x10000000 >> 12
    addi a1, zero, "E".ord
    addi a2, zero, "R".ord
    addi a3, zero, "O".ord
    addi a4, zero, "\n".ord
    sw a1, a0, 0x0
    sw a2, a0, 0x0
    sw a3, a0, 0x0
    sw a4, a0, 0x0
    trace 'Error: Test failed (self check did not pass)!'
    ecall
  end

  ##################################################################################################
  # Data Section Macro
  ##################################################################################################

  #def EXTRA_DATA
  #end

  def RVTEST_DATA_BEGIN
    #EXTRA_DATA()

# TODO: Temporary commented out because it causes the "HTIF tohost must be 8 bytes" error in QEMU.
#     # .pushsection .tohost,"aw",@progbits
#     section(:name => '.tohost') {
#       data {
#         align 6
# global_label :tohost
#         dword 0
#
#         align 6
# global_label :fromhost
#         dword 0
#       }
#     }
#     # .popsection


    text ".balign 4"
    #data {
    #  text '.align 4'
      # TODO: Fix me!
    #  text '.pushsection .tohost,"aw",@progbits'
    #  text '.align 8; .global tohost; tohost: .dword 0;'
    #  text '.align 8; .global fromhost; fromhost: .dword 0;'
    #  text '.popsection;'
      # TODO: end Fix me!

    #  align 4
    #  global_label :begin_signature
    #}
  end

  def RVTEST_DATA_END
    #data {
    #  align 4
    #  global_label :end_signature

      # TODO: Fix me!
    #  text '.align 8; .global begin_regstate; begin_regstate:'
    #  text '.word 128;'
    #  text '.align 8; .global end_regstate; end_regstate:'
    #  text '.word 4;'
    #  # TODO: end Fix me!
    #}
  end

end
