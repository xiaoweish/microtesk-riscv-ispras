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
require_relative 'seq_fax'
require_relative 'seq_fdiv'
require_relative 'seq_fpmem'
require_relative 'seq_fpu'
require_relative 'seq_mem'

require_relative 'torture_data'

#
# Description:
#
#
class TortureTemplate < RiscVBaseTemplate
  include RiscvRand

  include SeqAlu
  include SeqFax
  include SeqFdiv
  include SeqFpmem
  include SeqFpu
  include SeqMem

  include TortureData

  # Configuration settings
  NSEQS = 200
  MEMSIZE = 1024

  USE_AMO = true
  USE_MUL = true
  USE_DIV = true

  def initialize
    super

    set_option_value 'reserve-dependencies', true
    #set_option_value 'default-test-data', false
  end

  def pre_rvtest
    RVTEST_RV64U()
    RVTEST_CODE_BEGIN()
  end

  def pre_testdata
    TORTURE_DATA(MEMSIZE)
  end

  def run
    # Registers must be selected at random (taking into account existing reservations)
    set_default_allocator RANDOM

    block(:combinator => 'diagonal',
          :compositor => 'random',
          :permutator => 'random') {
      prologue {
        # This register must be excluded as it is used as temp by preparators and comparators.
        set_reserved ra, true

        j :test_start
label :crash_backward
        j :fail
label :test_start
      }

      seq_dist = dist(
        range(:bias => 30, :value => lambda do seq_alu(USE_MUL, USE_DIV) end),
        range(:bias => 20, :value => lambda do seq_fax end),
        range(:bias => 15, :value => lambda do seq_fdiv end),
        range(:bias =>  5, :value => lambda do seq_fpmem(MEMSIZE) end),
        range(:bias => 20, :value => lambda do seq_fpu end),
        range(:bias => 10, :value => lambda do seq_mem(MEMSIZE, USE_AMO) end)
        )

      NSEQS.times { seq_dist.next_value.call }

      epilogue {
        j :test_end
label :crash_forward
        j :fail
label :test_end
      }
    }.run
  end

end
