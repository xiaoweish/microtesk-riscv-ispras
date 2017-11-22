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
# This small tests for RV32F instructions.
#

class InstructionRV32F < RISCVBaseTemplate

  def run
    trace "Run RV32F instruction:"
    nop

    if rv32f == true then
      auipc s0, 0x80
      srli s0, s0, 12
      slli s0, s0, 12

      fsw ft0, s0, 0x0
      flw ft0, s0, 0x0

      fadd_s ft0, ft1, ft2
      fsub_s ft0, ft1, ft2
      fmul_s ft0, ft1, ft2
      fdiv_s ft0, ft1, ft2

      fmin_s ft0, ft1, ft2
      fmax_s ft0, ft1, ft2
      fsqrt_s ft0, ft1

      fsgnj_s ft0, ft1, ft2
      fsgnjn_s ft0, ft1, ft2
      fsgnjx_s ft0, ft1, ft2

      fmadd_s ft0, ft1, ft2, ft3
      fmsub_s ft0, ft1, ft2, ft3
      fnmadd_s ft0, ft1, ft2, ft3
      fnmsub_s ft0, ft1, ft2, ft3

      fcvt_w_s t0, ft0
      fcvt_wu_s t0, ft0
      fcvt_s_w ft0, t0
      fcvt_s_wu ft0, t0

      fxm_x_w t0, ft0
      fxm_w_x ft0, t0

      feq_s t0, ft0, ft1
      flt_s t0, ft0, ft1
      fle_s t0, ft0, ft1

      fclass_s t0, ft0

      trace "Special:"
      addi t0, zero, 5
      addi t1, zero, 4
      fcvt_s_w ft0, t0
      fcvt_s_w ft1, t1
      fadd_s ft2, ft1, ft0
      trace "t2: x7 = %x", gpr_observer(7)
      fcvt_w_s t2, ft2
      trace "ft2 = %x", fpr_observer(2)
      trace "t2: x7 = %x", gpr_observer(7)
    else
      trace "Error: RV32F"
    end

    nop
    nop
  end

end
