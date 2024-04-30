require_relative '../../riscv_base'


class ErrataMicrochipSwap < RiscVBaseTemplate

  def run
    epilogue { nop } 
    sequence {
      rv32i_load_upper_imm a1, 100
      amoswap_d a0, a1, a2 
    }.run
  end
end