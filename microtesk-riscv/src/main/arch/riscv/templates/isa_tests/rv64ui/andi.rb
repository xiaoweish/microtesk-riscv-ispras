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
# https://github.com/riscv/riscv-tests/blob/master/isa/rv64ui/andi.S
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

class AndiTemplate < RISCVBaseTemplate

  def run
    RVTEST_RV64U()
    # RVTEST_CODE_BEGIN()

    #-------------------------------------------------------------
    # Logical tests
    #-------------------------------------------------------------

    TEST_IMM_OP( 2, 'andi', 0xff00ff00, 0xff00ff00, 0xf0f )
    TEST_IMM_OP( 3, 'andi', 0x000000f0, 0x0ff00ff0, 0x0f0 )
    TEST_IMM_OP( 4, 'andi', 0x0000000f, 0x00ff00ff, 0x70f )
    TEST_IMM_OP( 5, 'andi', 0x00000000, 0xf00ff00f, 0x0f0 )

    #-------------------------------------------------------------
    # Source/Destination tests
    #-------------------------------------------------------------

    TEST_IMM_SRC1_EQ_DEST( 6, 'andi', 0x00000000, 0xff00ff00, 0x0f0 )

    #-------------------------------------------------------------
    # Bypassing tests
    #-------------------------------------------------------------

    TEST_IMM_DEST_BYPASS( 7,  0, 'andi', 0x00000700, 0x0ff00ff0, 0x70f )
    TEST_IMM_DEST_BYPASS( 8,  1, 'andi', 0x000000f0, 0x00ff00ff, 0x0f0 )
    TEST_IMM_DEST_BYPASS( 9,  2, 'andi', 0xf00ff00f, 0xf00ff00f, 0xf0f )

    TEST_IMM_SRC1_BYPASS( 10, 0, 'andi', 0x00000700, 0x0ff00ff0, 0x70f )
    TEST_IMM_SRC1_BYPASS( 11, 1, 'andi', 0x000000f0, 0x00ff00ff, 0x0f0 )
    TEST_IMM_SRC1_BYPASS( 12, 2, 'andi', 0x0000000f, 0xf00ff00f, 0x70f )

    TEST_IMM_ZEROSRC1( 13, 'andi', 0, 0x0f0 )
    TEST_IMM_ZERODEST( 14, 'andi', 0x00ff00ff, 0x70f )

    TEST_PASSFAIL()

    RVTEST_CODE_END()

    RVTEST_DATA_BEGIN()
    TEST_DATA()
    RVTEST_DATA_END()
  end

end
