#
# Copyright 2018-2019 ISP RAS (http://www.ispras.ru)
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
require_relative '../../riscv_rand'

require_relative 'seq_alu'
require_relative 'seq_alu_rvc'
require_relative 'seq_branch'
require_relative 'seq_branch_rvc'
require_relative 'seq_fax'
require_relative 'seq_fdiv'
require_relative 'seq_fpmem'
require_relative 'seq_fpmem_rvc'
require_relative 'seq_fpu'
require_relative 'seq_mem'
require_relative 'seq_mem_rvc'

require_relative 'seq_xxx_data'
require_relative 'seq_xxx_regs'

#
# Description:
#
# This test template demonstrates how to generate random torture tests.
# It provides facilities that are similar to the ones of
# RISC-V Torture Test Generator (https://github.com/ucb-bar/riscv-torture).
#
class TortureTemplate < RiscVBaseTemplate
  include RiscvRand

  include SeqAlu
  include SeqAluRvc
  include SeqBranch
  include SeqBranchRvc
  include SeqFax
  include SeqFdiv
  include SeqFpmem
  include SeqFpmemRvc
  include SeqFpu
  include SeqMem
  include SeqMemRvc

  include TortureData
  include TortureRegs

  # Configuration settings
  SEQ_NUMBER = 256
  SEQ_LENGTH = 64

  MEMSIZE = 1024

  USE_AMO = true
  USE_MUL = true
  USE_DIV = true

  def initialize
    super

    set_option_value 'reserve-dependencies', true
    set_option_value 'reserve-explicit', false
    set_option_value 'default-test-data', false
    set_option_value 'self-checks', false
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

    block {
      prologue {
        # This register must be excluded as it is used as temp by initializers and finalizers.
        set_reserved sp, true

        j :test_start
label :crash_backward
        j :test_end # FIXME: :fail
label :test_start
      }

      SEQ_LENGTH.times do
        next_random_sequence
      end

      epilogue {
        SAVE_XREGS()
        SAVE_FREGS()

        newline
        j :test_end
label :crash_forward
        j :fail
label :test_end
      }
    }.run SEQ_NUMBER
  end

  # Selects a random instruction sequence using the specified distribution.
  def next_random_sequence
    if not (defined? @sequence_distribution) then
      @sequence_distribution = dist(
          range(:bias => 20, :value => lambda do seq_alu(USE_MUL, USE_DIV) end),
          range(:bias => 10, :value => lambda do seq_alu_rvc end),
          range(:bias => 15, :value => lambda do seq_branch end),
          range(:bias =>  5, :value => lambda do seq_branch_rvc end),
          range(:bias =>  5, :value => lambda do seq_fax end),
          range(:bias =>  5, :value => lambda do seq_fdiv end),
          range(:bias =>  5, :value => lambda do seq_fpmem(MEMSIZE) end),
          range(:bias =>  5, :value => lambda do seq_fpmem_rvc(MEMSIZE) end),
          range(:bias => 10, :value => lambda do seq_fpu end),
          range(:bias => 15, :value => lambda do seq_mem(MEMSIZE, USE_AMO) end),
          range(:bias =>  5, :value => lambda do seq_mem_rvc(MEMSIZE) end)
      )
    end
    @sequence_distribution.next_value.call
  end

end
