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

require_relative 'seq_branch'

module SeqBranchRvc
  include SeqBranch

  def seq_branch_rvc
    pick_random {
      seq_taken_j_rvc('C_J')
      # seq_taken_j_rvc('C_JAL')
      seq_taken_jr_rvc('C_JR')
      seq_taken_jr_rvc('C_JALR')
    }
  end

  private

  def seq_taken_j_rvc(op)
    atomic {
      instr op, label_f(1)
      ILLEGAL()
    }
  end

  def seq_taken_jr_rvc(op)
    reg_dst = reg_write_hidden(:xregs, :exclude => [zero])
    block(:combinator => 'diagonal', :compositor => 'catenation') {
      la reg_dst, :c_jr_label
      atomic {
        instr op, reg_dst
        ILLEGAL()
        label :c_jr_label
      }
    }
  end

end
