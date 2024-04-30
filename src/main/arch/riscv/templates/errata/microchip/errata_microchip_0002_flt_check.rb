# The FLIM instruction may incorrectly limit the 
# data range when operating on signed 
# operands of different sign values. 
# If the operands are either all negative or all 
# positive, the limit is correct.
# https://ww1.microchip.com/downloads/aemDocuments/documents/MCU16/ProductDocuments/Errata/dsPIC33CK64MP105-Family-Silicon-Errata-and-Data-Sheet-Clarification-DS80000809.pdf

require_relative '../../riscv_base'


class ErrataMicrochipFlt < RiscVBaseTemplate

  def run
    
    epilogue { nop }  
    sequence {
      fadd_d ft1, 10.5, 1      
      fadd_d ft2, -20.25, 1    
      flt_d a3, ft1, ft2           
    }.run  
  end
end