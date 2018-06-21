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

#
# Description:
#
# This test template demonstrates how to generate test cases with branch instructions.
#
class BranchGenerationTemplate < RISCVBaseTemplate

  def initialize
    super
    set_option_value 'default-test-data', false
  end

  def TEST_DATA
    data {
      align 8
      # Arrays to store test data for branch instructions.
      label :branch_data_0
      dword 0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0
      label :branch_data_1
      dword 0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0
      label :branch_data_2
      dword 0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0
      label :branch_data_3
      dword 0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,
            0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0,    0x0, 0x0, 0x0, 0x0
    }
  end

  def pre
    super

    stream_preparator(:data_source => 'X', :index_source => 'X') {
      init {
        la index_source, start_label
      }

      read {
        ld data_source, index_source, 0x0
        addi index_source, index_source, 8
      }

      write {
        sd data_source, index_source, 0x0
        addi index_source, index_source, 8
      }
    }
  end

  def run
    # Stream  Label            Data  Addr  Size
    stream   :branch_data_0,   s0,   s4,   256
    stream   :branch_data_1,   s1,   s5,   256
    stream   :branch_data_2,   s2,   s6,   256
    stream   :branch_data_3,   s3,   s7,   256

    # A branch structure is as follows:
    #
    #  0: NOP
    #  1: if (BGEZ) then goto 0
    #  2: NOP
    #  3: if (BGTZ) then goto 2
    #  4: NOP
    #  5: if (BLEZ) then goto 4
    #  6: NOP
    #  7: if (BLTZ) then goto 10
    #  8: NOP
    #  9: goto 0
    # 10: NOP

    # Parameter 'branch_exec_limit' bounds the number of executions of a single branch:
    #   the default value is 1.
    # Parameter 'trace_count_limit' bounds the number of execution traces to be created:
    #   the default value is -1 (no limitation).
    sequence(
        :engines => {
            :branch => {:branch_exec_limit => 3,
                        :block_exec_limit => 3,
                        :trace_count_limit => -1}}) {
      label :label0
        nop  # A basic block should contain at least one instruction
        bgez s0, :label0 do
          situation('bgez-if-then', :engine => :branch, :stream => 'branch_data_0')
        end
        addi reg1=get_register, reg1, 1 # reg1 is a random unreserved register

      label :label1
        nop  # A basic block should not modify the registers used in the branches
        bgtz s1, :label1 do
          situation('bgtz-if-then', :engine => :branch, :stream => 'branch_data_1')
        end
        ori reg2=get_register, reg2, 2 # reg2 is a random unreserved register

      label :label2
        nop
        blez s2, :label2 do
          situation('blez-if-then', :engine => :branch, :stream => 'branch_data_2')
        end
        addi reg3=get_register, reg3, 3 # reg3 is a random unreserved register

      label :label3
        nop
        bltz s3, :label5 do
          situation('bltz-if-then', :engine => :branch, :stream => 'branch_data_3')
        end
        ori reg4=get_register, reg4, 4 # reg4 is a random unreserved register

      label :label4
        nop
        j :label0 do
          situation('j-goto', :engine => :branch)
        end
        addi reg5=get_register, reg5, 5 # reg5 is a random unreserved register

      label :label5
        nop
    }.run
  end

end
