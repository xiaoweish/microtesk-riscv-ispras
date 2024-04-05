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
class BlockRandomArgsTemplate < RiscVBaseTemplate
  def run

    #
    # Constructs 10 instruction sequences which consist of 20 instructions
    #
    block(:combinator => 'random') {
      20.times {
        get_instruction(Random.rand(9))
      }
    }.run 10
  end

  def get_instruction(value)
    case value
    when 0
      add  x(_), x(_), x(_)
    when 1
      sub  x(_), x(_), x(_)
    when 2
      neg  x(_), x(_)
    when 3
      Xor  x(_), x(_), x(_)
    when 4
      And  x(_), x(_), x(_)
    when 5
      ori  x(_), x(_), _
    when 6
      xori x(_), x(_), _
    when 7
      andi x(_), x(_), _
    when 8
      addi x(_), x(_), _
    end
  end
end
