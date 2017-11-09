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
# This small tests for RV32I instructions.
#

class InstructionRV32I < RISCVBaseTemplate

  def run
    trace "Run RV32I instruction:"

    lui t3, 8
    auipc t4, 0
    jal t5, :jal_label
    nop
    label :jal_label
    nop
    addi t6, zero, :jalr_label
    #jalr t0, t6, 0
    nop
    label :jalr_label
    nop

    addi t0, t1, 15
    trace "(addi): x5 = %x", gpr_observer(5)

    addi t1, t2, 7
    trace "(addi): x6 = %x", gpr_observer(6)

    add t2, t1, t0
    trace "(add): x7 = %x", gpr_observer(7)

    sub t2, t1, t0
    trace "(sub): x7 = %x", gpr_observer(7)

    nop
    nop
  end

end
