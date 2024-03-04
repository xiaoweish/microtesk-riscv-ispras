# 
# FPU register addressing fault (TSC692E) 
# 
# Description:
# The problem occurs in the following sequence:
# Fpop1 %rs1, %rs2, %rd
# up to 80 IU instructions (depending on Fpop1 and data)
# lddf [], %rd
# Fpop2 %rs1, %rs2, %rd
# with the following conditions:
# condition 1: rs2 (Fpop2) = rd (Fpop1)
# condition 2: rd(Fpop1) and rd(lddf) with bit[2] = bit[4] (example f0 and f2, f8 and
# f10, ...)
# In this case, the Fpop1 instruction will store the wrong data in the register File
# due to the lddf Fp instruction.
# 
# Source http://microelectronics.esa.int/erc32/chipset/ERC32-CCA-Chipset-ErrataSheet-RevA-1998-10-26.pdf
# 

require_relative '../../riscv_base'

class ErrataTemic0001 < RiscVBaseTemplate
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
            double self.rand_float(0.1, 5.0)
            double self.rand_float(0.1, 5.0)
            double self.rand_float(0.1, 5.0)
            label :data
            space 16       
            label :end
            space 12 
        }
    end

    def rand_template
        # Registers (check riscv_base)
        regs_gp_t = [6, 7, 28, 30, 31]
        regs_f_t = [0, 2, 4, 6, 28, 30] 

        # Ops (Fpop)
        fpop_op = [
            "fadd_s f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fsub_s f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fmul_s f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fdiv_s f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fsqrt_s f(f_reg_dst), f(f_reg_src1)",
            "feq_s a0, f(f_reg_src1), f(f_reg_src2)",
            "flt_s a0, f(f_reg_src1), f(f_reg_src2)",
            "fle_s a0, f(f_reg_src1), f(f_reg_src2)",
            "fmin_s f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)",
            "fmax_s f(f_reg_dst), f(f_reg_src1), f(f_reg_src2)"
        ]

        # Ops (UI)             
        ui_op = [
            "Or x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "ori x(gp_reg_dst), x(gp_reg_src1), rand_float(0.0, 10.0)",
            "xor x(gp_reg_src2), x(gp_reg_src2), x(gp_reg_src1)",
            "xori x(gp_reg_src2), x(gp_reg_src2), rand(0, 31)",
            "sll x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "slli x(gp_reg_dst), x(gp_reg_src1), rand(0, 31)",
            "srl x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "srli x(gp_reg_dst), x(gp_reg_src1), rand(0, 31)",
            "add x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "addi x(gp_reg_dst), x(gp_reg_src1), rand(0, 63)",
            "sub x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "mul x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "And x(gp_reg_dst), x(gp_reg_src1), x(gp_reg_src2)",
            "andi x(gp_reg_dst), x(gp_reg_src1), rand(0, 10)"
        ]

        def rand_ops(fpop_ops, uiop_ops)
            return [fpop_ops.sample(2), uiop_ops.cycle.take(rand_int(1, 80)).shuffle]
        end

        def rand_regs(regs_f, regs_gp)
            return [regs_f.sample(3), regs_gp.sample(3)]
        end

        return [rand_ops(fpop_op, ui_op), rand_regs(regs_f_t, regs_gp_t)]
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
        op_fpop, op_uiop = elements_rand[0]
        regs_f, regs_gp = elements_rand[1]

        gp_reg_src1, gp_reg_src2, gp_reg_dst = regs_gp
        f_reg_src1, f_reg_src2, f_reg_dst = regs_f

        la t0, :junk_data_double
        la t4, :junk_data
        j :case1

        label :case1
        lw X(gp_reg_src1), t4, 0
        lw X(gp_reg_src2), t4, 4
        fld F(f_reg_src1), t4, 0
        fld F(f_reg_src2), t4, 8

        la t0, :end
        add t0, t0, -8

        eval(op_fpop[0])
        eval(op_uiop.join("\n"))

        fld F(f_reg_dst), t4, 16
        eval(op_fpop[1])

        add t0, t0, 8

        j :done

        label :done
        nop
    end

end
