# 
# Floating-point Compare - Floating-point instruction sequence fault (TSC692E) 
# 
# Description:
# It occurs in the following sequence of instructions with waitstates:
# FCMP
# FPop
# If a Floating-point compare instruction FCMP is immediately followed by any other Floating-point instruction
# FPop with hardware interlock between both, and if a waitstate holds the FCMP in its E stage, and if the FCMP
# generates an exception, then the IU will trap on the FPop and return from trap will be done at the wrong address.
# For instance, if the FPop should have been re-executed after return, it is the FCMP that will be! One of the risks
# is then an unwanted infinite loop if the condition triggering the exception is still true.
# 
# Source http://microelectronics.esa.int/erc32/chipset/ERC32-CCA-Chipset-ErrataSheet-RevA-1998-10-26.pdf
# 

require_relative '../../riscv_base'

class ErrataTemic0005 < RiscVBaseTemplate
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
            align 8
            label :junk_data_double
            double self.rand_float(0.1, 10.0).round(2)
            double self.rand_float(0.1, 10.0).round(2)
            double self.rand_float(0.1, 10.0).round(2)
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
            "feq_d a0, f(f_reg_src1), f(f_reg_src2)",
            "flt_d a0, f(f_reg_src1), f(f_reg_src2)",
            "fle_d a0, f(f_reg_src1), f(f_reg_src2)",
            "fmin_d f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fmax_d f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)"
        ]

        # Ops (Fpop)
        fpop_op = [
            "fadd_d f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fsub_d f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fmul_d f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fdiv_d f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fsqrt_d f(f_reg_dst), f(f_reg_src1)"
        ]

        def rand_ops(fpop_ops, fcmp_ops)
            return [fpop_ops.sample, fcmp_ops.sample]
        end

        def rand_regs(regs_f, regs_gp)
            return [regs_f.sample(3), regs_gp.sample(3)]
        end

        return [rand_ops(fpop_op, fcmp_op), rand_regs(regs_f_t, regs_gp_t)]
    end

    # Custom int randomizer 
    def rand_int(min, max)
        gen_int = Random.new
        return gen_int.rand(min..max)
    end

    # Custom float randomizer 
    def rand_float(f_min, f_max)
        Kernel.srand
        return f_min + Kernel.rand * (f_max - f_min)
    end

    protected :rand_template, :rand_float

    def run
        elements_rand = self.rand_template
        op_fpop, op_fcmp = elements_rand[0]
        regs_f, regs_gp = elements_rand[1]

        gp_reg_src1, gp_reg_src2, gp_reg_dst = regs_gp
        f_reg_src1, f_reg_src2, f_reg_dst = regs_f

        la t0, :junk_data_double
        la t4, :junk_data
        j :case1

        label :case1
        lw X(gp_reg_src1), t4, 0
        lw X(gp_reg_src2), t4, 4
        flw F(f_reg_src1), t0, 0
        flw F(f_reg_src2), t0, 8

        la t0, :end
        add t0, t0, -8

        eval(op_fcmp)
        eval(op_fpop)

        add t0, t0, 8

        j :done

        label :done
        nop
    end

end