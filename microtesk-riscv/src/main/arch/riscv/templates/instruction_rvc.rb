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

require_relative 'riscv_base'

#
# Description:
#
# This small tests for Compressed Instructions.
#
class InstructionRVC < RISCVBaseTemplate
  def pre
    super
    data {
      label :data
      word rand(1, 9), rand(1, 9), rand(1, 9), rand(1, 9)
      label :end_data
      space 1
    }
  end

  def run
    trace "Compressed Instructions:"

    c_addi4spn s1, 4

    la a3, :data
    c_flw fa2, a3, :data
    c_fld fa2, a3, :data
    c_fsw fa2, a3, :data
    c_fsd fa2, a3, :data

    c_sw a3, a3, :data
    c_sd a3, a3, :data

    c_nop
    c_addi a0, 4
    c_addiw a0, 8
    c_addi16sp 4
    c_li a0, 8
    c_lui a0, 4
    c_srli a0, 8
    c_srai a0, 4

    la sp, :data
    c_lwsp a0, 0
    c_ldsp a0, 0
    c_swsp a3, 0
    c_sdsp a3, 0

    la a3, :data
    c_lw a0, a3, :data
    c_ld a0, a3, :data

    c_andi a0, _
    c_add a0, a0
    c_or a0, a0
    c_xor a0, a0
    c_sub a0, a0
    c_and a0, a0
    c_addw a0, a0
    c_subw a0, a0

    c_j :c_j_label
    nop
    label :c_j_label
    nop

    c_jal 8
    nop
    label :c_jal_label
    nop

    c_beqz a0, :c_beqz_label
    nop
    label :c_beqz_label
    nop

    c_bnez a0, :c_bnez_label
    nop
    label :c_bnez_label
    nop

    la a5, :c_jr_label
    c_jr a5
    nop
    label :c_jr_label
    nop

    la a5, :c_jalr_label
    c_jalr a5
    nop
    label :c_jalr_label
    nop

    c_slli a0, _

    la sp, :data
    c_flwsp fa0, 4
    c_fldsp fa0, 4

    c_mv a0, a0
    c_ebreak

    c_fswsp fa2, 4
    c_fsdsp fa2, 4

    nop
    nop
  end

end
