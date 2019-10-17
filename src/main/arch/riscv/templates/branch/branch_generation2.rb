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
class BranchGeneration2Template < RiscVBaseTemplate

  def initialize
    super
    set_option_value 'default-test-data', false
  end

  def TEST_DATA
    data {
      org 0x00010000
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
        if is_rev('RV64I') then
          ld data_source, index_source, 0x0
        else
          lw data_source, index_source, 0x0
        end
        addi index_source, index_source, 8
      }

      write {
        if is_rev('RV64I') then
          sd data_source, index_source, 0x0
        else
          sw data_source, index_source, 0x0
        end
        addi index_source, index_source, 8
      }
    }
  end

  def run
    # Stream  Label            Data  Addr  Size
    stream   :branch_data_0,   s0,   s4,   128
    stream   :branch_data_1,   s1,   s5,   128
    stream   :branch_data_2,   s2,   s6,   128
    stream   :branch_data_3,   s3,   s7,   128

    # Parameter 'branch_exec_limit' bounds the number of executions of a single branch:
    #   the default value is 1.
    # Parameter 'trace_count_limit' bounds the number of execution traces to be created:
    #   the default value is -1 (no limitation).
    block(
       :combinator => 'diagonal',
       :compositor => 'catenation',
       :engines => {
           :branch => {:branch_exec_limit => 3,
                       :block_exec_limit => 3,
                       :trace_count_limit => 10}
       }) {
      sequence {
        label :labelA
        pseudo '# Start Label'
      }

      block(:compositor => 'random', :permurator => 'random', :rearranger => 'expand') {
        # Labels
        iterate {
          sequence {
            label :label0
              pseudo '# Basic Block 0'
          }

          sequence {
            label :label1
              pseudo '# Basic Block 1'
          }

          sequence {
            label :label2
              pseudo '# Basic Block 2'
          }

          sequence {}
          sequence {}
        }

        block(:combinator => 'diagonal') {
          sequence {
            nop
          }

          block(:combinator => 'diagonal') {
            # Branches
            iterate {
              bgez s0, :label0 do
                situation('bgez-if-then', :engine => :branch, :stream => 'branch_data_0')
              end
              bgtz s1, :label1 do
                situation('bgtz-if-then', :engine => :branch, :stream => 'branch_data_1')
              end
              blez s2, :label2 do
                situation('blez-if-then', :engine => :branch, :stream => 'branch_data_2')
              end
              bltz s3, :labelZ do
                situation('bltz-if-then', :engine => :branch,:stream => 'branch_data_3')
              end
              j :labelA do
                situation('j-goto', :engine => :branch)
              end
            }

            # Injected Code placed in delay slot
            iterate {
              # The code must not modify registers s0-s7
              addi reg1=x(_ FREE), reg1, 1
              ori  reg2=x(_ FREE), reg2, 2
              addi reg3=x(_ FREE), reg3, 3
              ori  reg4=x(_ FREE), reg4, 4
              addi reg5=x(_ FREE), reg5, 5
            }
          }
        }
      }

      sequence {
        label :labelZ
        pseudo '# End Label'
      }
    }.run 10 # Try several random compositions
  end

end
