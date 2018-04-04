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

module RiscvTestMacros

  ##################################################################################################
  # Helper macros
  ##################################################################################################

  #define MASK_XLEN(x) ((x) & ((1 << (__riscv_xlen - 1) << 1) - 1))

  #define TEST_CASE( testnum, testreg, correctval, code... ) \
  #test_ ## testnum: \
  #    code; \
  #    li  x29, MASK_XLEN(correctval); \
  #    li  TESTNUM, testnum; \
  #    bne testreg, x29, fail;

  # We use a macro hack to simplify code generation for various numbers
  # of bubble cycles.

  def TEST_INSERT_NOPS(n)
    n.times do
      nop
    end
  end

  def TEST_INSERT_NOPS_0
    TEST_INSERT_NOPS(0)
  end

  def TEST_INSERT_NOPS_1
    TEST_INSERT_NOPS(1)
  end

  def TEST_INSERT_NOPS_2
    TEST_INSERT_NOPS(2)
  end

  def TEST_INSERT_NOPS_3
    TEST_INSERT_NOPS(3)
  end

  def TEST_INSERT_NOPS_4
    TEST_INSERT_NOPS(4)
  end

  def TEST_INSERT_NOPS_5
    TEST_INSERT_NOPS(5)
  end

  def TEST_INSERT_NOPS_6
    TEST_INSERT_NOPS(6)
  end

  def TEST_INSERT_NOPS_7
    TEST_INSERT_NOPS(7)
  end

  def TEST_INSERT_NOPS_8
    TEST_INSERT_NOPS(8)
  end

  def TEST_INSERT_NOPS_9
    TEST_INSERT_NOPS(9)
  end

  def TEST_INSERT_NOPS_10
    TEST_INSERT_NOPS(10)
  end

  # TODO: Implement the macros here

end
