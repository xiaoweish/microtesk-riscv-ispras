#
# Copyright 2024 ISP RAS (http://www.ispras.ru)
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

require_relative '../../riscv_base'

#
# Description:
#
# This test template demonstrates how to create randomized instruction
# sequences using block constructs.
#
class BlockRandomTemplate < RiscVBaseTemplate
  def run
    instructions = iterate {
      add  x(_), x(_), x(_)
      sub  x(_), x(_), x(_)
      neg  x(_), x(_)
      Xor  x(_), x(_), x(_)
      And  x(_), x(_), x(_)
      ori  x(_), x(_), _
      xori x(_), x(_), _
      andi x(_), x(_), _
      addi x(_), x(_), _
    }
    #
    # Constructs 10 instruction sequences which consist of 10 instructions
    # randomly selected from a collection described by the "iterate" construct.
    #
    block(:combinator => 'random') {
      instructions.add 10
    }.run 10
  end
end
