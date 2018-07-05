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

module SeqMem

  def seq_mem(memsize, use_amo)
    pick_random {
      seq_load_addrfn('LB',  rand_addr_b(memsize))
      seq_load_addrfn('LBU', rand_addr_b(memsize))
      seq_load_addrfn('LH',  rand_addr_h(memsize))
      seq_load_addrfn('LHU', rand_addr_h(memsize))
      seq_load_addrfn('LW',  rand_addr_w(memsize))
      seq_load_addrfn('LWU', rand_addr_w(memsize))
      seq_load_addrfn('LD',  rand_addr_d(memsize))

      seq_store_addrfn('SB', rand_addr_b(memsize))
      seq_store_addrfn('SH', rand_addr_h(memsize))
      seq_store_addrfn('SW', rand_addr_w(memsize))
      seq_store_addrfn('SD', rand_addr_d(memsize))

      if use_amo then
        seq_amo_addrfn('AMOADD_W',  rand_addr_w(memsize))
        seq_amo_addrfn('AMOSWAP_W', rand_addr_w(memsize))
        seq_amo_addrfn('AMOAND_W',  rand_addr_w(memsize))
        seq_amo_addrfn('AMOOR_W',   rand_addr_w(memsize))
        seq_amo_addrfn('AMOMIN_W',  rand_addr_w(memsize))
        seq_amo_addrfn('AMOMINU_W', rand_addr_w(memsize))
        seq_amo_addrfn('AMOMAX_W',  rand_addr_w(memsize))
        seq_amo_addrfn('AMOMAXU_W', rand_addr_w(memsize))
        seq_amo_addrfn('AMOADD_D',  rand_addr_d(memsize))
        seq_amo_addrfn('AMOSWAP_D', rand_addr_d(memsize))
        seq_amo_addrfn('AMOAND_D',  rand_addr_d(memsize))
        seq_amo_addrfn('AMOOR_D',   rand_addr_d(memsize))
        seq_amo_addrfn('AMOMIN_D',  rand_addr_d(memsize))
        seq_amo_addrfn('AMOMINU_D', rand_addr_d(memsize))
        seq_amo_addrfn('AMOMAX_D',  rand_addr_d(memsize))
        seq_amo_addrfn('AMOMAXU_D', rand_addr_d(memsize))
      end
    }
  end

  private

  def instr(op, *args)
    self.send :"#{op}", args
  end

  def seq_load_addrfn(op, addr)
    reg_addr = x(_) # reg_write_hidden(xregs)
    reg_dest = x(_) # reg_write_visible(xregs)
    imm = rand_imm()

    lla_minus reg_addr, :test_memory, addr, imm
    instr op, reg_dest, reg_addr, imm
  end

  def seq_store_addrfn(op, addr)
    reg_addr = x(_) # reg_write_hidden(xregs)
    reg_src = x(_) # reg_read_visible(xregs)
    imm = rand_imm()

    lla_minus reg_addr, :test_memory, addr, imm
    instr op, reg_src, reg_addr, imm
  end

  def seq_amo_addrfn(op, addr)
    reg_addr = x(_) # reg_write_hidden(xregs)
    reg_dest = x(_) # reg_write_visible(xregs)
    reg_src = x(_) # reg_read_visible(xregs)

    lla reg_addr, :test_memory, addr
    instr op, reg_dest, reg_src, reg_addr
  end

end
