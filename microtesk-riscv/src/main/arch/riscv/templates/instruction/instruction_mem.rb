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

require_relative '../riscv_base'

#
# Description:
#

class InstructionMemTemplate < RiscVBaseTemplate

  def TEST_DATA
    data {
      org 0x00010000
      label :data
      word 0x0, 0x0, 0x0, 0x0,
           0x0, 0x0, 0x0, 0x0
      label :end
      space 1
    }
  end

  def run
    la s0, :data # Address
    prepare t0, 0xFFFFFFFFDEADBEEF # Value being loaded/stored

    trace "s0 = 0x%x", XREG(8)
    #sw t0, s0, 0x0
    trace "t0 = 0x%x", XREG(5)
    lw t1, s0, 0x0
    trace "t1 = 0x%x", XREG(6)
    nop
  end

end
