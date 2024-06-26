# The Decimal Adjust instruction, DAW.b, may
# improperly clear the Carry bit, C (SR<0>), when
# executed.
# https://www.mouser.com/PCN/Microchip-6-4-10-dsPIC30F5011-5013.pdf


require_relative '../../riscv_base'


class ErrataMicrochipShiftLogicalImmediate < RiscVBaseTemplate

  def run   
    epilogue {nop}
    # Shift Left Logical Immediate
    sequence {
      rv32i_load_upper_imm a1, 100
      sllw a2, a1, 2
    }.run
    # Shift Right Logical Immediate
    sequence {
      rv32i_load_upper_imm a1, 100
      srlw a2, a1, 2
    }.run    
  end
end