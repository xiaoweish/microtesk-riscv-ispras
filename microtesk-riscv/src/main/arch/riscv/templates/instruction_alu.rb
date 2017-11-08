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

    addi x5, x6, 15
    trace "(addi): x5 = %x", gpr_observer(5)

    addi x6, x7, 7
    trace "(addi): x6 = %x", gpr_observer(6)

    add x7, x6, x5
    trace "(add): x7 = %x", gpr_observer(7)

    sub x7, x6, x5
    trace "(sub): x7 = %x", gpr_observer(7)

    nop
    nop
  end

end
