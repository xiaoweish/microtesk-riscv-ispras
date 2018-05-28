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
# https://github.com/riscv/riscv-tests/blob/master/isa/rv32um/mulhu.S
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

class MulhuTemplate < RISCVBaseTemplate

  def pre_rvtest
    RVTEST_RV32U()
    RVTEST_CODE_BEGIN()
  end

  def run
    #-------------------------------------------------------------
    # Arithmetic tests
    #-------------------------------------------------------------

  if __riscv_xlen == 32
    TEST_RR_OP( 2,  'mulhu', 0x00000000, 0x00000000, 0x00000000 )
    TEST_RR_OP( 3,  'mulhu', 0x00000000, 0x00000001, 0x00000001 )
    TEST_RR_OP( 4,  'mulhu', 0x00000000, 0x00000003, 0x00000007 )

    TEST_RR_OP( 5,  'mulhu', 0x00000000, 0x00000000, 0xffff8000 )
    TEST_RR_OP( 6,  'mulhu', 0x00000000, 0x80000000, 0x00000000 )
    TEST_RR_OP( 7,  'mulhu', 0x7fffc000, 0x80000000, 0xffff8000 )

    TEST_RR_OP(30,  'mulhu', 0x0001fefe, 0xaaaaaaab, 0x0002fe7d )
    TEST_RR_OP(31,  'mulhu', 0x0001fefe, 0x0002fe7d, 0xaaaaaaab )

    TEST_RR_OP(32,  'mulhu', 0xfe010000, 0xff000000, 0xff000000 )

    TEST_RR_OP(33,  'mulhu', 0xfffffffe, 0xffffffff, 0xffffffff )
    TEST_RR_OP(34,  'mulhu', 0x00000000, 0xffffffff, 0x00000001 )
    TEST_RR_OP(35,  'mulhu', 0x00000000, 0x00000001, 0xffffffff )

    #-------------------------------------------------------------
    # Source/Destination tests
    #-------------------------------------------------------------

    TEST_RR_SRC1_EQ_DEST( 8, 'mulhu', 36608, 13<<20, 11<<20 )
    TEST_RR_SRC2_EQ_DEST( 9, 'mulhu', 39424, 14<<20, 11<<20 )
    TEST_RR_SRC12_EQ_DEST( 10, 'mulhu', 43264, 13<<20 )

    #-------------------------------------------------------------
    # Bypassing tests
    #-------------------------------------------------------------

    TEST_RR_DEST_BYPASS( 11, 0, 'mulhu', 36608, 13<<20, 11<<20 )
    TEST_RR_DEST_BYPASS( 12, 1, 'mulhu', 39424, 14<<20, 11<<20 )
    TEST_RR_DEST_BYPASS( 13, 2, 'mulhu', 42240, 15<<20, 11<<20 )

    TEST_RR_SRC12_BYPASS( 14, 0, 0, 'mulhu', 36608, 13<<20, 11<<20 )
    TEST_RR_SRC12_BYPASS( 15, 0, 1, 'mulhu', 39424, 14<<20, 11<<20 )
    TEST_RR_SRC12_BYPASS( 16, 0, 2, 'mulhu', 42240, 15<<20, 11<<20 )
    TEST_RR_SRC12_BYPASS( 17, 1, 0, 'mulhu', 36608, 13<<20, 11<<20 )
    TEST_RR_SRC12_BYPASS( 18, 1, 1, 'mulhu', 39424, 14<<20, 11<<20 )
    TEST_RR_SRC12_BYPASS( 19, 2, 0, 'mulhu', 42240, 15<<20, 11<<20 )

    TEST_RR_SRC21_BYPASS( 20, 0, 0, 'mulhu', 36608, 13<<20, 11<<20 )
    TEST_RR_SRC21_BYPASS( 21, 0, 1, 'mulhu', 39424, 14<<20, 11<<20 )
    TEST_RR_SRC21_BYPASS( 22, 0, 2, 'mulhu', 42240, 15<<20, 11<<20 )
    TEST_RR_SRC21_BYPASS( 23, 1, 0, 'mulhu', 36608, 13<<20, 11<<20 )
    TEST_RR_SRC21_BYPASS( 24, 1, 1, 'mulhu', 39424, 14<<20, 11<<20 )
    TEST_RR_SRC21_BYPASS( 25, 2, 0, 'mulhu', 42240, 15<<20, 11<<20 )

    TEST_RR_ZEROSRC1( 26, 'mulhu', 0, 31<<26 )
    TEST_RR_ZEROSRC2( 27, 'mulhu', 0, 32<<26 )
    TEST_RR_ZEROSRC12( 28, 'mulhu', 0 )
    TEST_RR_ZERODEST( 29, 'mulhu', 33<<20, 34<<20 )
  end

    RVTEST_DATA_BEGIN()
    TEST_DATA()
    RVTEST_DATA_END()
  end

  def post
    TEST_PASSFAIL()
    RVTEST_CODE_END()
  end

end

