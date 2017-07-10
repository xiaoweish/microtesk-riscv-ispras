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
# This small tests for ALU instructions.
#
class InstructionALU < RISCVBaseTemplate

  def run
    trace "Run ALU instruction:"

    trace "\nRISC-V Arithmetic:\n"

    addi x3, x2, 15
    trace "(addi): r3 = %x", gpr_observer(3)

    add x1, x2, x3
    trace "(add): r1 = %x", gpr_observer(1)

    sub x1, x2, x3
    trace "(sub): r1 = %x", gpr_observer(1)

    nop
    nop
  end

end
