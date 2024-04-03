

require_relative '../../riscv_base'

class ErrataMicrochip00 < RiscVBaseTemplate
  def run
    
    # Декартово произведение
    block(:combinator => 'product', :compositor => 'random') {
      iterate {
        fadd.s  x(_), x(_), x(_)
        fsub.s  x(_), x(_), x(_)
        fmul.s  x(_), x(_), x(_)
        fdiv.s  x(_), x(_), x(_)
        fsqrt.s x(_), x(_), x(_)
      }

      iterate {
        fadd.s  x(_), x(_), x(_)
        fsub.s  x(_), x(_), x(_)
        fmul.s  x(_), x(_), x(_)
        fdiv.s  x(_), x(_), x(_)
        fsqrt.s x(_), x(_), x(_)
      }
    }.run

  end

end

