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

class ErrataMicrochip0001Rand < RiscVBaseTemplate
    @rand_int = nil
    @rand_float = nil
    
    # NOTE: t0 and t4 is reserved for data section pointers
    def TEST_DATA
        data {
            org 0x0
            align 4
            label :junk_data
            word rand(0,127)
            word rand(0,127)
            float self.rand_float(0.1, 10.0)
            float self.rand_float(0.1, 10.0)
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

        # Ops (fcmp*)
        fcmp_op = [
            "feq_s a0, f(f_reg_src1), f(f_reg_src2)",
            "flt_s a0, f(f_reg_src1), f(f_reg_src2)",
            "fle_s a0, f(f_reg_src1), f(f_reg_src2)",
            "fmin_s f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fmax_s f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)"
        ]

        # Ops (target)
        ui_op = ["Or x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "ori x(gp_reg_dst), x(gp_reg_src1), 0x0f",
            "xor x(gp_reg_src2), x(gp_reg_src2), x(gp_reg_src1)\nOr x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "Or x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)\nbeq x(gp_reg_dst), 
                    x(gp_reg_src1), :done\nbeq x(gp_reg_dst), x(gp_reg_src2), :done\nbne x(gp_reg_dst), x(gp_reg_src1), 
                    :done\nbnez x(gp_reg_dst), :done\nbeqz x(gp_reg_dst), :done",
            "sll x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "srl x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "add x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)\nbeq x(gp_reg_dst), 
                    x(gp_reg_src1), :done\nbeq x(gp_reg_dst), x(gp_reg_src2), :done\nbne x(gp_reg_dst), x(gp_reg_src1), 
                    :done\nbnez x(gp_reg_dst), :done\nbeqz x(gp_reg_dst), :done"
        ]

        def rand_ops(fcmp_ops, uiop_ops)
            return [fcmp_ops.sample, uiop_ops.sample]
        end

        def rand_regs(regs_f, regs_gp)
            return [regs_f.sample(3), regs_gp.sample(3)]
        end

        return [rand_ops(fcmp_op, ui_op), rand_regs(regs_f_t, regs_gp_t)]
    end

    # Custom float randomizer 
    def rand_float(f_min, f_max)
        Kernel.srand
        return f_min + Kernel.rand * (f_max - f_min)
    end

    protected :rand_template, :rand_float

    def run
        elements_rand = self.rand_template
        op_fcmp, op_uiop = elements_rand[0]
        regs_f, regs_gp = elements_rand[1]

        gp_reg_src1, gp_reg_src2, gp_reg_dst = regs_gp
        f_reg_src1, f_reg_src2, f_reg_dst = regs_f

        la t0, :end
        la t4, :junk_data
        j :case1

        label :case1
        add t0, t0, -8

        lw X(gp_reg_src1), t4, 0
        lw X(gp_reg_src2), t4, 4

        flw F(f_reg_src1), t4, 8
        flw F(f_reg_src2), t4, 12

        eval(op_fcmp)
        eval(op_uiop)

        fsw f(f_reg_dst), t0, 0
        add t0, t0, 8

        j :done

        label :done
        nop
    end

end
