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
# https://github.com/riscv/riscv-tests/blob/master/isa/macros/scalar/test_macros.h
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

module RiscvTestMacros

  ##################################################################################################
  # Helper macros
  ##################################################################################################

  def __riscv_xlen
    if rv64i then 64 else 32 end
  end

  def MASK_XLEN(x)
     ((x) & ((1 << (__riscv_xlen - 1) << 1) - 1))
  end

  def TEST_CASE( testnum, testreg, correctval, &code)
label :"test_#{testnum}"
    self.instance_eval &code
    li x29, MASK_XLEN(correctval)
    li TESTNUM(), testnum
    bne testreg, x29, :fail
  end

  # We use a macro hack to simplify code generation for various numbers
  # of bubble cycles.

  def TEST_INSERT_NOPS(n)
    n.times do
      nop
    end
  end

  ##################################################################################################
  # RV64UI MACROS
  ##################################################################################################

  ##################################################################################################
  # Tests for instructions with immediate operand
  ##################################################################################################

  def SEXT_IMM(x)
    ((x) | (-(((x) >> 11) & 1) << 11))
  end

  def TEST_IMM_OP(testnum, inst, result, val1, imm)
    TEST_CASE(testnum, x30, result) do
      li x1, MASK_XLEN(val1)
      self.send :"#{inst}", x30, x1, SEXT_IMM(imm)
    end
  end

  def TEST_IMM_SRC1_EQ_DEST(testnum, inst, result, val1, imm)
    TEST_CASE(testnum, x1, result) do
      li x1, MASK_XLEN(val1)
      self.send :"#{inst}", x1, x1, SEXT_IMM(imm)
    end
  end

  def TEST_IMM_DEST_BYPASS(testnum, nop_cycles, inst, result, val1, imm)
    TEST_CASE(testnum, x6, result) do
      li x4, 0
label 1
      li x1, MASK_XLEN(val1)
      self.send :"#{inst}", x30, x1, SEXT_IMM(imm)
      TEST_INSERT_NOPS(nop_cycles)
      addi x6, x30, 0
      addi x4, x4, 1
      li x5, 2
      bne x4, x5, label_b(1)
    end
  end

  def TEST_IMM_SRC1_BYPASS(testnum, nop_cycles, inst, result, val1, imm)
    TEST_CASE(testnum, x30, result) do
      li x4, 0
label 1
      li x1, MASK_XLEN(val1)
      TEST_INSERT_NOPS(nop_cycles)
      self.send :"#{inst}", x30, x1, SEXT_IMM(imm)
      addi x4, x4, 1
      li x5, 2
      bne x4, x5, label_b(1)
    end
  end

  def TEST_IMM_ZEROSRC1(testnum, inst, result, imm)
    TEST_CASE(testnum, x1, result) do
      self.send :"#{inst}", x1, x0, SEXT_IMM(imm)
    end
  end

  def TEST_IMM_ZERODEST(testnum, inst, val1, imm)
    TEST_CASE(testnum, x0, 0) do
      li x1, MASK_XLEN(val1)
      self.send :"#{inst}", x0, x1, SEXT_IMM(imm)
    end
  end

  ##################################################################################################
  # Tests for an instruction with register operands
  ##################################################################################################

  def TEST_R_OP(testnum, inst, result, val1)
    TEST_CASE(testnum, x30, result) do
      li x1, val1
      self.send :"#{inst}", x30, x1
     end
  end

  def TEST_R_SRC1_EQ_DEST(testnum, inst, result, val1)
    TEST_CASE(testnum, x1, result) do
      li x1, val1
      self.send :"#{inst}", x1, x1
    end
  end

  def TEST_R_DEST_BYPASS(testnum, nop_cycles, inst, result, val1)
    TEST_CASE(testnum, x6, result) do
      li x4, 0
label 1
      li x1, val1
      self.send :"#{inst}", x30, x1
      TEST_INSERT_NOPS(nop_cycles)
      addi x6, x30, 0
      addi x4, x4, 1
      li x5, 2
      bne x4, x5, label_b(1)
    end
  end

  # TODO: Implement the macros here

  ##################################################################################################
  # Pass and fail code (assumes test num is in TESTNUM)
  ##################################################################################################

  def TEST_PASSFAIL
    bne x0, TESTNUM(), :pass
label :fail
    RVTEST_FAIL()
label :pass
    RVTEST_PASS()
  end

  ##################################################################################################
  # Test data section
  ##################################################################################################

  def TEST_DATA
  end

end
