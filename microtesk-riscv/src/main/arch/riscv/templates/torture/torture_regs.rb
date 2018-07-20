#
# Copyright 2018 ISP RAS (http://www.ispras.ru)
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

require_relative '../riscv_rand'

module TortureRegs
  include RiscvRand

  # returns register x0
  def reg_read_zero(regtype)
    if :xregs == regtype
      zero
    else
      raise "Unsupported register type: #{regtype}"
    end
  end

  # returns any type of register (hidden or visible)
  def reg_read_any(regtype)
    if :xregs == regtype
      x(_) do
        situation('random_biased', :dist => rand_biased_dist)
      end
    elsif :xregs_c == regtype
      x(_ :retain => [x8, x9, x10, x11, x12, x13, x14, x15]) do
        situation('random_biased', :dist => rand_biased_dist)
      end
    elsif :fregs_d == regtype
      f(_) do
        situation('random_biased', :dist => rand_biased_dist)
      end
    elsif :fregs_s == regtype
      f(_) do
        situation('random_biased', :dist => rand_biased_dist, :size => 32)
      end
    else
      raise "Unsupported register type: #{regtype}"
    end
  end

  # returns a visible register
  def reg_read_visible(regtype)
    # Currently, visibility is not tracked. Therefore, 'reg_read_any' is called.
    reg_read_any(regtype)
  end

  # returns register ra for write
  def reg_write_ra(regtype)
    if :xregs == regtype
      ra
    else
      raise "Unsupported register type: #{regtype}"
    end
  end

  # returns a visible register for write
  def reg_write_visible(regtype)
    if :xregs == regtype
      x(_)
    elsif :xregs_c == regtype
      x(_ :retain => [x8, x9, x10, x11, x12, x13, x14, x15])
    elsif :fregs_d == regtype
      f(_)
    elsif :fregs_s == regtype
      f(_)
    else
      raise "Unsupported register type: #{regtype}"
    end
  end

  # returns a hidden register for write
  def reg_write_hidden(regtype)
    # Currently, visibility is not tracked. Therefore, 'reg_write_visible' is called.
    reg_write_visible(regtype)
  end

  # returns a register that matches the type of regs
  # (if any reg in regs are hidden, the output type is hidden)
  def reg_write(regtype, *regs)
    # Currently, visibility is not tracked.
    # Therefore, 'reg_write_visible' is called and 'regs' is ignored.
    reg_write_visible(regtype)
  end

end
