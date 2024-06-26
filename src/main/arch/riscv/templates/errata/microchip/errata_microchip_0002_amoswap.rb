# Automatic write error may occur when using amoswap_d instruction
# https://www.cs.sfu.ca/~ashriram/Courses/CS295/assets/books/rvbook.pdf

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