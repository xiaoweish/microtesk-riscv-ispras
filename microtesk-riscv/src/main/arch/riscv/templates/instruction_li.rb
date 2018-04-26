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

require_relative 'riscv_base'

#
# Description:
#
# This test checks LI (load immediate) pseudo instruction.
#
class InstructionLiTemplate < RISCVBaseTemplate

  def initialize
    super
    @testnum = 1
  end

  def LI_TEST_CASE( value, &code )
    newline
label :"test_#{@testnum}"
    li TESTNUM(), @testnum
    li t0, value
    self.instance_eval &code
    bne t0, t1, :fail
    @testnum = @testnum + 1
  end

  def run
    ################################################################################################
    # 12-bit values
    ################################################################################################

    LI_TEST_CASE( 0 ) do
      mv t1, zero
    end

    LI_TEST_CASE( 1 ) do
      ori t1, zero, 1
    end

    LI_TEST_CASE( -1 ) do
      Not t1, zero
    end

    LI_TEST_CASE( 0x700 ) do
      ori t1, zero, 7
      slli t1, t1, 8
    end


    LI_TEST_CASE( 0x800 ) do
      ori t1, zero, 1
      slli t1, t1, 11
    end

    ################################################################################################
    # 32-bit values
    ################################################################################################

    LI_TEST_CASE( 0x0000_0000_FFFF_FFFF ) do
      ori  t1, zero, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xFF
    end

    LI_TEST_CASE( 0x0000_0000_7FFF_FFFF ) do
      ori  t1, zero, 0x7F
      slli t1, t1, 8
      ori  t1, t1, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xFF
    end

    LI_TEST_CASE( 0x0000_0000_8FFF_FFFF ) do
      ori  t1, zero, 0x8F
      slli t1, t1, 8
      ori  t1, t1, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xFF
    end

    LI_TEST_CASE( 0x0000_0000_7FFF_F7FF ) do
      ori  t1, zero, 0x7F
      slli t1, t1, 8
      ori  t1, t1, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xF7
      slli t1, t1, 8
      ori  t1, t1, 0xFF
    end

    LI_TEST_CASE( 0x0000_0000_8FFF_F8FF ) do
      ori  t1, zero, 0x8F
      slli t1, t1, 8
      ori  t1, t1, 0xFF
      slli t1, t1, 8
      ori  t1, t1, 0xF8
      slli t1, t1, 8
      ori  t1, t1, 0xFF
    end

    ################################################################################################
    # 64-bit values
    ################################################################################################

    LI_TEST_CASE( 0xFFFF_FFFF_FFFF_FFFF ) do
      Not t1, zero
    end

    ################################################################################################

    TEST_PASSFAIL()

    RVTEST_CODE_END()

    RVTEST_DATA_BEGIN()
    TEST_DATA()
    RVTEST_DATA_END()
  end

end
