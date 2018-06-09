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
# THIS FILE IS BASED ON THE RISC TORTURE MODULE:
# https://github.com/ucb-bar/riscv-torture/blob/master/generator/src/main/scala/Rand.scala
#

#
# Description:
#
# This module contains methods that are commonly used to generate random values.
#
module RiscvRand

  def rand_word  rand(0, 0xFFFF_FFFF) end
  def rand_dword rand(0, 0xFFFF_FFFF_FFFF_FFFF) end

  def rand_range(low, high)
    rand(low, high)
  end

  def rand_shamt   rand_range(0, 63) end
  def rand_shamtw  rand_range(0, 31) end
  def rand_seglen  rand_range(0, 7) end
  def rand_imm     rand_range(-2048, 2047) end
  def rand_bigimm  rand_range(0, 1048575) end

  def rand_addr_b(memsize) rand_range(0, memsize-1) end
  def rand_addr_h(memsize) rand_range(0, memsize-1) & ~1 end
  def rand_addr_w(memsize) rand_range(0, memsize-1) & ~3 end
  def rand_addr_d(memsize) rand_range(0, memsize-1) & ~7 end

#  def rand_biased
#    rand(dist(
#      range(:value => , :bias => ),
#      range(:value => , :bias => ),
#      range(:value => , :bias => ),
#      range(:value => , :bias => ),
#      range(:value => , :bias => ),
#      range(:value => , :bias => )
#    ))
#  end

#  def rand_biased: Long =
#  {
#    val value = rand_dword
#    val s = rand_range(0, 17)
#
#    if (s < 9)
#    {
#      val small = rand_range(0, 9).toLong
#
#      s match
#      {
#        // return a value with a single bit set
#        case 0 => (1 << value & 63)
#        case 1 => (1 << value & 63)
#
#        // return a valueue with a single bit clear
#        case 2 => ~(1 << value & 63)
#        case 3 => ~(1 << value & 63)
#
#        // return a small integer around zero
#        case 4 => small
#
#        // return a very large/very small 8b signed number
#        case 5 => ((0x80L + small) << 56) >> 56
#
#        // return a very large/very small 16b signed number
#        case 6 => ((0x8000L + small) << 48) >> 48
#
#        // return a very large/very small 32b signed number
#        case 7 => ((0x80000000L + small) << 32) >> 32
#
#        // return a very large/very small 64b signed number
#        case 8 => 0x800000000000000L + small
#      }
#    }
#    else
#    {
#      value
#    }
#  }

end
