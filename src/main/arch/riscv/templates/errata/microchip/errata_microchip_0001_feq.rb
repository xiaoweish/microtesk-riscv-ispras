#
# Floating-Point Compare Single or Double Instruction followed by specific 
# IU Instruction followed by Floating-Point Store Double Instruction
#
# Description:
# If a floating-point compare single or double instruction (FCMPS, FCMPES, FCMPD or FCMPED) is immediately followed by
# one of the OR, ORcc, ORN, ORNcc, SRL, TADDccTV, Ticc, RDWIM or WRWIM instruction, and the next instruction is a
# floating-point store double (STDF) of any floating-point register (involved or not in the floating-point compare single or
# double instruction), the stored floating-point double value is corrupted.
# Data corruption happens as follows: the program location of the floating-point compare single or double instruction is
# written into memory at the effective store address instead of the expected most significant word in the even-numbered
# floating-point source register.
# The floating-point registers involved in the floating-point store double operation are not corrupted, nor any other floating- point register.
#
# Source: https://ww1.microchip.com/downloads/en/DeviceDoc/doc4280.pdf, page 3
#

require_relative '../../riscv_base'

class ErrataMicrochipFeq < RiscVBaseTemplate
    @rand_int = nil
    @rand_float = nil

    def TEST_DATA
        data {
            org 0x0
            align 4
            label :junk_data
            word rand(0,127)
            word rand(0,5)
            float self.rand_float(0.0, 10.0)
            float self.rand_float(0.0, 10.0)
            label :data
            space 16      
            label :end
            space 4
        }
    end

    def rand_template
        # Registers (check riscv_base)
        regs_gp_t = [6, 7, 28, 30, 31]
        regs_f_t = [0, 2, 4, 6, 28, 30]

        def rand_regs(regs_f, regs_gp)
            return [regs_f.sample(3), regs_gp.sample(3)]
        end

        return rand_regs(regs_f_t, regs_gp_t)
    end

    # Custom float randomizer 
    def rand_float(f_min, f_max)
        Kernel.srand
        return f_min + Kernel.rand * (f_max - f_min)
    end

    protected :rand_template, :rand_float

    def run
        regs_f, regs_gp = self.rand_template

        gp_reg_src1, gp_reg_src2, gp_reg_dst = regs_gp
        f_reg_src1, f_reg_src2, f_reg_dst = regs_f
        
        la t0, :end
        la t4, :junk_data
        j :case1

        # Case 1 (OR)
        label :case1
        add t0, t0, -8

        lw gp_reg_src1, t4, 0
        lw gp_reg_src2, t4, 4

        flw f_reg_src1, t4, 8
        flw f_reg_src2, t4, 12

        feq_s a0, f_reg_src1, f_reg_src2
        Or gp_reg_dst, gp_reg_src1, gp_reg_src2  

        fsw f_reg_dst, t0, 0
        add t0, t0, 8

        j :case2

        # Case 2 (ORI)
        label :case2
        add t0, t0, -8

        lw gp_reg_src1, t4, 0
        lw gp_reg_src2, t4, 4

        flw f_reg_src1, t4, 8
        flw f_reg_src2, t4, 12

        feq_s a0, f_reg_src1, f_reg_src2
        ori gp_reg_dst, gp_reg_src1, self.rand_int(1,64)

        fsw f_reg_dst, t0, 0
        add t0, t0, 8

        j :case3

        # Case 3 (pseudoORN)
        label :case3
        add t0, t0, -8

        lw gp_reg_src1, t4, 0
        lw gp_reg_src2, t4, 4

        flw f_reg_src1, t4, 8
        flw f_reg_src2, t4, 12

        feq_s a0, f_reg_src1, f_reg_src2
        xor gp_reg_src2, gp_reg_src2, 1
        Or gp_reg_dst, gp_reg_src1, gp_reg_src2  

        fsw f_reg_dst, t0, 0
        add t0, t0, 8

        j :case4

        # Case 4 (pseudoORcc)
        label :case4
        add t0, t0, -8

        lw gp_reg_src1, t4, 0
        lw gp_reg_src2, t4, 4

        flw f_reg_src1, t4, 8
        flw f_reg_src2, t4, 12

        feq_s a0, f_reg_src1, f_reg_src2
        Or gp_reg_dst, gp_reg_src1, gp_reg_src2
        beq gp_reg_dst, gp_reg_src1, :next4
        beq gp_reg_dst, gp_reg_src2, :next4
        bne gp_reg_dst, gp_reg_src1, :next4
        bnez gp_reg_dst, :next4
        beqz gp_reg_dst, :next4

        label :next4  
        fsw f_reg_dst, t0, 0
        add t0, t0, 8

        j :case5

        # Case 5 (SLL)
        label :case5
        add t0, t0, -8

        lw gp_reg_src1, t4, 0
        lw gp_reg_src2, t4, 4

        flw f_reg_src1, t4, 8
        flw f_reg_src2, t4, 12

        feq_s a0, f_reg_src1, f_reg_src2
        sll gp_reg_dst, gp_reg_src1, gp_reg_src2  

        fsw f_reg_dst, t0, 0
        add t0, t0, 8

        j :case6

        # Case 6 (SRL)
        label :case6
        add t0, t0, -8

        lw gp_reg_src1, t4, 0
        lw gp_reg_src2, t4, 4

        flw f_reg_src1, t4, 8
        flw f_reg_src2, t4, 12

        feq_s a0, f_reg_src1, f_reg_src2
        srl gp_reg_dst, gp_reg_src1, gp_reg_src2  

        fsw f_reg_dst, t0, 0
        add t0, t0, 8

        j :case7

        # Case 7 (pseudoTADDcc/pseudoTicc)
        label :case7
        add t0, t0, -8
        lw gp_reg_src1, t4, 0
        lw gp_reg_src2, t4, 4

        flw f_reg_src1, t4, 8
        flw f_reg_src2, t4, 12

        feq_s a0, f_reg_src1, f_reg_src2
        add gp_reg_dst, gp_reg_src1, gp_reg_src2
        beq gp_reg_dst, gp_reg_src1, :next7
        beq gp_reg_dst, gp_reg_src2, :next7
        bne gp_reg_dst, gp_reg_src1, :next7
        bnez gp_reg_dst, :next7
        beqz gp_reg_dst, :next7

        label :next7  
        fsw f_reg_dst, t0, 0
        add t0, t0, 8

        j :done

        label :done
        nop

    end
end
