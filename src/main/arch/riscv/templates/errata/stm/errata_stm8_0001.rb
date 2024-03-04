# Source: TODO 

require_relative '../../riscv_base'

class ErrataStm8Template < RiscVBaseTemplate
        
    def TEST_DATA
        data {
          org 0x0
          align 4
          label :data
          space 32
          label :end
          space 8
        }
      end

    def run
        arg1 = rand(1, 16)
        arg2 = rand(1, 16) 
        addi t4, arg1, 0
        addi t5, arg2, 0   
        la t1, :end 
        jal  t0, :routine1
        j :done

        label :routine1
        add t1, t1, -8
        sw t0, t1, 0
        jal  t0, :routine2
        jr t0

        label :routine2
        if is_rev('RV64I')
          lwu t0, t1, 0 
        else
          lw t0, t1, 0
        end
        jr t0

        label :done
        nop
        
    end
end