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

module SeqAluRvc

  def seq_alu_rvc

    pick_random {
#     TODO:
#     C.LI
#     C.LUI

#     C.ADDI
#     C.ADDIW
#     C.ADDI16SP
#     C.ADDI4SPN
#     C.SLLI

#     C.SRLI
#     C.SRAI

#     C.ANDI

#     C.MV
#     C.ADD

      ['C_AND', 'C_OR', 'C_XOR', 'C_SUB', 'C_ADDW', 'C_SUBW'].each { |op|
        seq_alu_rvc_src(op)
        seq_alu_rvc_src_zero(op)
      }
    }
  end

  private

  def instr(op, *args)
    self.send :"#{op}", args
  end

  def seq_alu_rvc_src(op)
    src = reg_read_any(:xregs_c)
    dest = reg_write(:xregs_c, src)

    instr op, dest, src
  end

  def seq_alu_rvc_src_zero(op)
    src = reg_read_any(:xregs_c)
    dest = reg_write(:xregs_c, src)
    tmp = reg_write_visible(:xregs_c)

    addi tmp, reg_read_zero(:xregs), rand_imm
    instr op, dest, tmp
  end

end
