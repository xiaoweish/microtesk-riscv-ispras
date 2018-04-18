#
# Copyright 2018 ISP RAS (http://www.ispras.ru)
#
# Licensed under the Apache License, Version 2.0 (the "License")
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
# THIS FILE IS BASED ON THE FOLLOWING RISC-V TEST SUITE SOURCE FILE:
# https://github.com/riscv/riscv-tests/blob/master/isa/rv64ui/blt.S
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

require_relative '../../riscv_base'

class BltTemplate < RISCVBaseTemplate

  def prologue
    RVTEST_RV64U()
    RVTEST_CODE_BEGIN()
  end

  def run
    #-------------------------------------------------------------
    # Branch tests
    #-------------------------------------------------------------

    # Each test checks both forward and backward branches

    TEST_BR2_OP_TAKEN( 2, 'blt',  0,  1 )
    TEST_BR2_OP_TAKEN( 3, 'blt', -1,  1 )
    TEST_BR2_OP_TAKEN( 4, 'blt', -2, -1 )

    TEST_BR2_OP_NOTTAKEN( 5, 'blt',  1,  0 )
    TEST_BR2_OP_NOTTAKEN( 6, 'blt',  1, -1 )
    TEST_BR2_OP_NOTTAKEN( 7, 'blt', -1, -2 )
    TEST_BR2_OP_NOTTAKEN( 8, 'blt',  1, -2 )

    #-------------------------------------------------------------
    # Bypassing tests
    #-------------------------------------------------------------

    TEST_BR2_SRC12_BYPASS( 9,  0, 0, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 10, 0, 1, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 11, 0, 2, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 12, 1, 0, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 13, 1, 1, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 14, 2, 0, 'blt', 0, -1 )

    TEST_BR2_SRC12_BYPASS( 15, 0, 0, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 16, 0, 1, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 17, 0, 2, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 18, 1, 0, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 19, 1, 1, 'blt', 0, -1 )
    TEST_BR2_SRC12_BYPASS( 20, 2, 0, 'blt', 0, -1 )

    #-------------------------------------------------------------
    # Test delay slot instructions not executed nor bypassed
    #-------------------------------------------------------------

    TEST_CASE( 21, x1, 3 ) do
      li  x1, 1
      blt x0, x1, label_f(1)
      addi x1, x1, 1
      addi x1, x1, 1
      addi x1, x1, 1
      addi x1, x1, 1
label 1
      addi x1, x1, 1
      addi x1, x1, 1
    end

    TEST_PASSFAIL()

    RVTEST_CODE_END()

    RVTEST_DATA_BEGIN()
    TEST_DATA()
    RVTEST_DATA_END()
  end

end
