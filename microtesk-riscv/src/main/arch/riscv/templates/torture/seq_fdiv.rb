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

module SeqFdiv

  def seq_fdiv
    pick_random {
      seq_src1_s('FSQRT_S')
      seq_src1_d('FSQRT_D')
      seq_src2_s('FDIV_S')
      seq_src2_d('FDIV_D')
    }
  end

  private

  def instr(op, *args)
    self.send :"#{op}", args
  end

  def seq_src1_s(op)
    src1 = f(_) # reg_read_any(fregs_s)
    dest = f(_) # reg_write(fregs_s, src1)

    instr op, dest, src1
  end

  def seq_src2_s(op)
    src1 = f(_) # reg_read_any(fregs_s)
    src2 = f(_) # reg_read_any(fregs_s)
    dest = f(_) # reg_write(fregs_s, src1, src2)

    instr op, dest, src1, src2
  end

  def seq_src1_d(op)
    src1 = f(_) # reg_read_any(fregs_d)
    dest = f(_) # reg_write(fregs_d, src1)

    instr op, dest, src1
  end

  def seq_src2_d(op)
    src1 = f(_) # reg_read_any(fregs_d)
    src2 = f(_) # reg_read_any(fregs_d)
    dest = f(_) # reg_write(fregs_d, src1, src2)

    instr op, dest, src1, src2
  end

end
