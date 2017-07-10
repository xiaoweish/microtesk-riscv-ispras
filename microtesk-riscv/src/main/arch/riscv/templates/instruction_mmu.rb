#
# Copyright 2017 ISP RAS (http://www.ispras.ru)
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
# This small tests for MMU instructions.
#
class InstructionMMU < RISCVBaseTemplate

  def run
    trace "Run MMU instruction:"

    #addi r1, r0, 0x0fff
    #addi r2, r0, 0x0123
    #addi r5, r0, 0x0f00
    trace "\nRISCV Load/Store:\n"

    #sw r2, 0x0, r1
    trace "r2 = %x", gpr_observer(2)
    #sw r5, 0x4, r1
    trace "r5 = %x", gpr_observer(5)

    #lw r3, 0x0, r1
    trace "r3 = %x", gpr_observer(3)
    #lw r4, 0x1, r1
    trace "r4 = %x", gpr_observer(4)
  end

end