#
# MicroTESK for RISC-V
#
# Copyright (c) 2017 Institute for System Programming of the Russian Academy of Sciences
# All Rights Reserved
#
# Institute for System Programming of the Russian Academy of Sciences (ISP RAS)
# 25 Alexander Solzhenitsyn st., Moscow, 109004, Russia
# http://www.ispras.ru
#

require_relative 'riscv_base'

#
# Description:
#
# This small tests for RV32D instructions.
#

class InstructionRV32D < RISCVBaseTemplate

  def run
    trace "Run RV32D instruction:"
    nop

    if rv32d == true then
      auipc s0, 0x80
      srli s0, s0, 12
      slli s0, s0, 12

      fsd ft0, s0, 0x0
      fld ft0, s0, 0x0

      fadd_d ft0, ft1, ft2
      fsub_d ft0, ft1, ft2
      fmul_d ft0, ft1, ft2
      fdiv_d ft0, ft1, ft2

      fmin_d ft0, ft1, ft2
      fmax_d ft0, ft1, ft2
      fsqrt_d ft0, ft1

      fsgnj_d ft0, ft1, ft2
      fsgnjn_d ft0, ft1, ft2
      fsgnjx_d ft0, ft1, ft2

      fmadd_d ft0, ft1, ft2, ft3
      fmsub_d ft0, ft1, ft2, ft3
      fnmadd_d ft0, ft1, ft2, ft3
      fnmsub_d ft0, ft1, ft2, ft3

      fcvt_w_d t0, ft0
      fcvt_wu_d t0, ft0
      fcvt_d_w ft0, t0
      fcvt_d_wu ft0, t0

      fcvt_s_d ft0, ft1
      fcvt_d_s ft0, ft1

      feq_d t0, ft0, ft1
      flt_d t0, ft0, ft1
      fle_d t0, ft0, ft1

      fclass_d t0, ft0

      fmv_d ft0, ft1
      fabs_d ft0, ft1
      fneg_d ft0, ft1

      trace "Special:"
      addi t0, zero, 5
      addi t1, zero, 4
      fcvt_d_w ft0, t0
      fcvt_d_w ft1, t1
      fadd_d ft2, ft1, ft0
      trace "t2: x7 = %x", gpr_observer(7)
      fcvt_w_d t2, ft2
      trace "ft2 = %x", fpr_observer(2)
      trace "t2: x7 = %x", gpr_observer(7)
    else
      trace "Error: RV32D"
    end

    nop
    nop
  end

end
