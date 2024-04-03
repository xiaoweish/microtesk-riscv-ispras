# Odd-numbered FPU register dependency not properly checked in some
# double-precision FPU operations
#
# Description:
#Odd-numbered FPU register dependency not properly checked in some double-precision FPU operations
#Data dependency is not properly checked between a load singleword floating-point instruction (LDF) involving an oddnumbered floating-point register as a destination of the load and an immediately following double-precision floating-point
#instruction (FADDd, FSUBd, FMULd, FDIVd or FSQRTd) that satisfies all of the following conditions:
# - the odd-numbered floating-point register is used as (part of) a source operand
# - the destination floating-point register is also a source operand
# - in an FSUBd or FDIVd, the two source operands are different registers
#In this case, the final result of the double-precision floating-point instruction will be wrong.
#Other double-precision floating-point instructions (FCMPd, FCMPEd, FdTOi and FdTOs) are not affected by this issue and
#will operate as expected.
#The error case appears when any of the six following sequences of instructions is present (n in [0:31], x and y as
#different even numbers in [0:30]):

#Source: https://www.microchip.com/content/dam/mchp/documents/OTH/ProductDocuments/Errata/at697f_errata.pdf

require_relative '../../riscv_base'

class ErrataMicrochip00 < RiscVBaseTemplate

  def run
    epilogue { nop }

     
    #TODO:

    sequence {
      fadd_d ft1, 10.5, 1 
      fadd_d ft2, 20.25, 1

      fadd_d ft3, ft2, f1     
    
    }.run

    sequence {
      fadd_d ft1, 10.5, 1 
      fadd_d ft2, 20.25, 1
      fsub_d ft3, ft2, ft1     
    
    }.run

    sequence {
      fadd_d ft1, 10.5, 1 
      fadd_d ft2, 20.25, 1
      fmul_d ft3, ft2, ft1     
    
    }.run

    sequence {
      fadd_d ft1, 10.5, 1 
      fadd_d ft2, 20.25, 1
      fdiv_d ft3, ft2, ft1     
    
    }.run

    sequence {
      fadd_d ft1, 10.5, 1 
      fadd_d ft2, 20.25, 1
      fsqrt_d ft3, ft1    
    
    }.run
  end

end
