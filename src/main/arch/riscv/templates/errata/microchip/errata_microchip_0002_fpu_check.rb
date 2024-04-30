require_relative '../../riscv_base'

class ErrataMicrochipFCartesianProduct < RiscVBaseTemplate
  def run
    
    # Cartesian product
    block(:combinator => 'product', :compositor => 'random') {
      iterate {
        fadd_s  f(_), f(_), f(_)
        fsub_s  f(_), f(_), f(_)
        fmul_s  f(_), f(_), f(_)
        fdiv_s  f(_), f(_), f(_)
        fsqrt_s f(_), f(_)
      }

      iterate {
        fadd_s  f(_), f(_), f(_)
        fsub_s  f(_), f(_), f(_)
        fmul_s  f(_), f(_), f(_)
        fdiv_s  f(_), f(_), f(_)
        fsqrt_s f(_), f(_)
      }
    }.run
  end
end