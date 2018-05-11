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
# This small tests for Compressed Instructions.
#
class InstructionRVC < RISCVBaseTemplate

  def run
    trace "Compressed Instructions:"

    c_andi a0, 7
    c_andi a1, 5
    c_add s0, a1
    c_or s0, a0
    c_xor s0, a1
    c_sub s0, a0
    c_addw s0, a0
    c_subw s0, a0

    nop
    nop
  end

end
