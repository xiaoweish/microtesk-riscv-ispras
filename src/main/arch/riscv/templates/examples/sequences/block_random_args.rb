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
    my_dist = dist(
      range(:value => lambda do add_sequence end, :bias => 10),
      range(:value => lambda do sub_sequence end, :bias => 10),
      range(:value => lambda do neg_sequence end, :bias => 10),
      range(:value => lambda do xor_sequence end, :bias => 10),
      range(:value => lambda do and_sequence end, :bias => 10),
      range(:value => lambda do logic_sequence end,  :bias => 10))

    block(:combinator => 'diagonal',
          :compositor => 'catenation',
          :permutator => 'random') {
      20.times {
        my_dist.next_value.call
      }

      epilogue {
        nop
      }
    }.run
  end

  def add_sequence
    iterate() {
      add  x(rand(3,7)), x(_ FREE), x(_)
    }
  end

  def sub_sequence
    iterate() {
      sub  x(_), x(_), x(_)
    }
  end

  def neg_sequence
    iterate() {
      neg  x(_), x(_)
    }
  end

  def xor_sequence
    iterate() {
      Xor  x(_), x(_), x(_)
    }
  end

  def and_sequence
    iterate() {
      And  x(_), x(_), x(_)
    }
  end

  def logic_sequence
    sequence(:obfuscator => 'random') {
      ori  x(_), x(_), _
      xori x(_), x(_), _
      andi x(_), x(_), _
      addi x(_), x(_), _
    }
  end
end
