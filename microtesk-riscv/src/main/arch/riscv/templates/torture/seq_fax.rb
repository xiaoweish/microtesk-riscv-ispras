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

module SeqFax

  def seq_fax
    def xregs;   method(:x) end
    def fregs_d; method(:f) end
    def fregs_s; method(:f) end

    pick_random {
      # Intra-FPU Instructions
      seq_fax_src1('FCVT_S_D', fregs_s, fregs_d)
      seq_fax_src1('FCVT_D_S', fregs_d, fregs_s)

      ['FSGNJ_S', 'FSGNJN_S', 'FSGNJX_S'].each { |op|
        seq_fax_src2(op, fregs_s, fregs_s)
      }

      ['FSGNJ_D', 'FSGNJN_D', 'FSGNJX_D'].each { |op|
        seq_fax_src2(op, fregs_d, fregs_d)
      }

      # X<->F Instructions
      ['FCVT_S_L', 'FCVT_S_LU', 'FCVT_S_W', 'FCVT_S_WU', 'FMV_W_X'].each { |op|
        seq_fax_src1(op, fregs_s, xregs)
      }

      ['FCVT_D_L', 'FCVT_D_LU', 'FCVT_D_W', 'FCVT_D_WU', 'FMV_D_X'].each { |op|
        seq_fax_src1(op, fregs_d, xregs)
      }

      ['FCVT_L_S', 'FCVT_LU_S', 'FCVT_W_S', 'FCVT_WU_S', 'FMV_X_W'].each { |op|
        seq_fax_src1(op, xregs, fregs_s)
      }

      ['FCVT_L_D', 'FCVT_LU_D', 'FCVT_W_D', 'FCVT_WU_D', 'FMV_X_D'].each { |op|
        seq_fax_src1(op, xregs, fregs_d)
      }

      ['FEQ_S', 'FLT_S', 'FLE_S'].each { |op|
        seq_fax_src2(op, xregs, fregs_s)
      }

      ['FEQ_D', 'FLT_D', 'FLE_D'].each { |op|
        seq_fax_src2(op, xregs, fregs_d)
      }
    }
  end

  private

  def instr(op, *args)
    self.send :"#{op}", args
  end

  def seq_fax_src1(op, dst_pool, src_pool)
    src1 = src_pool.call(_) # reg_read_any(src_pool)
    dest = dst_pool.call(_) # reg_write(dst_pool, src1)
    instr op, dest, src1
  end

  def seq_fax_src2(op, dst_pool, src_pool)
    src1 = src_pool.call(_) # reg_read_any(src_pool)
    src2 = src_pool.call(_) # reg_read_any(src_pool)
    dest = dst_pool.call(_) # reg_write(dst_pool, src1, src2)
    instr op, dest, src1, src2
  end

end
