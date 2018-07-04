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
require_relative '../riscv_rand'

require_relative 'seq_alu'
require_relative 'seq_fpu'
require_relative 'seq_fdiv'

#
# Description:
#
#
class TortureTemplate < RiscVBaseTemplate
  include RiscvRand

  include SeqAlu
  include SeqFpu
  include SeqFdiv

  def initialize
    super

    set_option_value 'reserve-dependencies', true
  end

  def pre_rvtest
    RVTEST_RV64U()
    RVTEST_CODE_BEGIN()
  end

  def run
    block(:combinator => 'diagonal',
          :compositor => 'catenation',
          :permutator => 'random') {
      seq_dist = dist(
        range(:value => lambda do seq_alu end,  :bias => 50),
        range(:value => lambda do seq_fpu end,  :bias => 35),
        range(:value => lambda do seq_fdiv end, :bias => 15))

      100.times { seq_dist.next_value.call }
    }.run
  end

end
