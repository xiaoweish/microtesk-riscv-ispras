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
      seq_alu_rvc_li()
      seq_alu_rvc_lui()

      seq_alu_rvc_addi4spn()
      seq_alu_rvc_addi16sp()

      seq_alu_rvc_immfn('C_ADDI',  rand_range(0, 63))
      seq_alu_rvc_immfn('C_ADDIW', rand_range(0, 63))
      seq_alu_rvc_immfn('C_SLLI',  rand_shift_imm)

      seq_alu_rvc_immfn_c('C_SRLI', rand_shift_imm)
      seq_alu_rvc_immfn_c('C_SRAI', rand_shift_imm)
      seq_alu_rvc_immfn_c('C_ANDI', rand_range(0, 63))

      ['C_MV', 'C_ADD'].each { |op|
        seq_alu_rvc_src(op)
        seq_alu_rvc_src_zero(op)
      }

      ['C_AND', 'C_OR', 'C_XOR', 'C_SUB', 'C_ADDW', 'C_SUBW'].each { |op|
        seq_alu_rvc_src_c(op)
        seq_alu_rvc_src_zero_c(op)
      }
    }
  end

  private

  def rand_shift_imm
    is_rev('RV64C') ? rand_range(1, 63) : rand_range(1, 31)
  end

  def instr(op, *args)
    self.send :"#{op}", args
  end

  def seq_alu_rvc_li
    c_li reg_write_visible(:xregs, :exclude => [zero]), rand_range(0, 63)
  end

  def seq_alu_rvc_lui
    # Positive immediate
    c_lui reg_write_visible(:xregs, :exclude => [zero, sp]), rand_range(0, 31)

    # Negative immediate
    c_lui reg_write_visible(:xregs, :exclude => [zero, sp]), _OR(0xFFFE0, rand_range(0, 31))
  end

  def seq_alu_rvc_addi4spn
    c_addi16sp _SLL(rand_range(1, 63), 4)
  end

  def seq_alu_rvc_addi16sp()
    c_addi4spn reg_write_hidden(:xregs_c), _SLL(rand_range(1, 255), 2)
  end

  def seq_alu_rvc_immfn(op, imm)
    src = reg_read_any(:xregs)
    dest = reg_write(:xregs, {:exclude => [zero]}, src)

    instr op, dest, imm
  end

  def seq_alu_rvc_immfn_c(op, imm)
    src = reg_read_any(:xregs_c)
    dest = reg_write(:xregs_c, src)

    instr op, dest, imm
  end

  def seq_alu_rvc_src(op)
    src = reg_read_any(:xregs)
    dest = reg_write(:xregs, {:exclude => [zero]}, src)

    instr op, dest, src
  end

  def seq_alu_rvc_src_zero(op)
    src = reg_read_any(:xregs)
    dest = reg_write(:xregs, {:exclude => [zero]}, src)
    tmp = reg_write_visible(:xregs)

    atomic {
      addi tmp, reg_read_zero(:xregs), rand_imm
      instr op, dest, tmp
    }
  end

  def seq_alu_rvc_src_c(op)
    src = reg_read_any(:xregs_c)
    dest = reg_write(:xregs_c, src)

    instr op, dest, src
  end

  def seq_alu_rvc_src_zero_c(op)
    src = reg_read_any(:xregs_c)
    dest = reg_write(:xregs_c, src)
    tmp = reg_write_visible(:xregs_c)

    atomic {
      addi tmp, reg_read_zero(:xregs), rand_imm
      instr op, dest, tmp
    }
  end

end
