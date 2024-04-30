#When using the Signed 32-by-16-bit Division
#instruction, div.sd, the Overflow bit may not
#always get set when an overflow occurs.
#This erratum only affects operations in which at
#least one of the following conditions is true:
#a) Dividend and divisor differ in sign,
#b) Dividend > 0x3FFFFFFF or
#c) Dividend < 0xC0000000. 
require_relative '../../riscv_base'


class ErrataMicrochipDiv < RiscVBaseTemplate

  def run
    # Adds nop to all test cases as a placeholder to return from an exception
    epilogue { nop }
    # Produces a single test case 
    sequence {
        # a) Dividend and divisor differ in sign
        rv32i_load_upper_imm t5, -5 
        rv32i_load_upper_imm t6, 2 
        div a0, t5, t6         
    }.run
    sequence {
        # Dividend > 0x3FFFFFFF
        rv32i_load_upper_imm t3, rand(0x3FFFFFF, 0x8FFFFFF)   
        rv32i_load_upper_imm t4, rand(0, 0xFFFFF)           
        div a1, t3, t4         
    }.run
    sequence {   
        # Dividend < 0xC0000000
        rv32i_load_upper_imm t1, rand(0, 0xC0000000)  
        rv32i_load_upper_imm t2, 0x00010000  
        div a2, t1, t2       
    }.run  
  end
end