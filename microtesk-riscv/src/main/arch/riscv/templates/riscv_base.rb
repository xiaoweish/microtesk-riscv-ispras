#
# Copyright 2017-2018 ISP RAS (http://www.ispras.ru)
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

require ENV['TEMPLATE']

# RISC-V macros used to organize tests
require_relative 'riscv_encoding'
require_relative 'riscv_test'
require_relative 'riscv_test_macros'

class RISCVBaseTemplate < Template
  include RiscvEncoding
  include RiscvTest
  include RiscvTestMacros

  ##################################################################################################
  # Settings
  ##################################################################################################

  def initialize
    super
    # Initialize settings here

    # Sets the indentation token used in test programs
    set_option_value 'indent-token', "\t"

    # Sets the single-line comment text used in test programs
    set_option_value 'comment-token', "#"

    # Sets the token used in separator lines printed into test programs
    set_option_value 'separator-token', "="

    # Defines alias methods for X registers
    (0..31).each do |i|
      define_method "x#{i}" do |&contents| X(i, &contents) end
    end
  end

  ##################################################################################################
  # Revisions
  ##################################################################################################

  def rev_id
    get_option_value('rev-id')
  end

  def rv64full
    rev_id == 'RV64FULL'
  end

  def rv64i
    rev_id == 'RV64I' or rv64full
  end

  def rv32m
    rev_id == 'RV32M' or rv64full
  end

  def rv64m
    rev_id == 'RV64M' or rv64full
  end

  def rv32a
    rev_id == 'RV32A' or rv64full
  end

  def rv64a
    rev_id == 'RV64A' or rv64full
  end

  def rv32f
    rev_id == 'RV32F' or rv64full
  end

  def rv64f
    rev_id == 'RV64F' or rv64full
  end

  def rv32d
    rev_id == 'RV32D' or rv64full
  end

  def rv64d
    rev_id == 'RV64D' or rv64full
  end

  ##################################################################################################
  # Prologue
  ##################################################################################################

  def pre
    ################################################################################################

    #
    # Information on data types to be used in data sections.
    #
    data_config(:text => '.data', :target => 'MEM') {
      define_type :id => :byte,  :text => '.byte',  :type => type('card', 8)
      define_type :id => :half,  :text => '.half',  :type => type('card', 16)
      define_type :id => :word,  :text => '.word',  :type => type('card', 32)
      define_type :id => :dword, :text => '.dword', :type => type('card', 64)

      define_space        :id => :space,  :text => '.space',  :fill_with => 0
      define_ascii_string :id => :ascii,  :text => '.ascii',  :zero_term => false
      define_ascii_string :id => :asciiz, :text => '.asciiz', :zero_term => true
    }

    #
    # Defines .text section.
    #
    # pa: base physical address (used for memory allocation).
    # va: base virtual address (used for encoding instructions that refer to labels).
    #
    section_text(:pa => 0x0, :va => 0x0) {}

    #
    # Defines .data section.
    #
    # pa: base physical address (used for memory allocation).
    # va: base virtual address (used for encoding instructions that refer to labels).
    #
    section_data(:pa => 0x0008_0000, :va => 0x0008_0000) {}

    #
    # Simple exception handler. Continues execution from the next instruction.
    #
    exception_handler {
      entry_point(:org => 0x380,
                  :exception => ['IntegerOverflow',
                                 'SystemCall',
                                 'Breakpoint',
                                 'Invalid Operation']) {
        trace 'Exception handler (UEPC = 0x%x)', location('CSR', 0x041)
        nop
        csrr ra, risc_uepc
        addi ra, ra, 4
        ret
      }
    }

    ################################################################################################

    #
    # The code below specifies an instruction sequence that writes a value
    # to the specified register (target) via the X addressing mode.
    #
    # Default preparator: It is used when no special case previded below
    # is applicable.
    #
    preparator(:target => 'X') {
      li target, value
    }

    preparator(:target => 'X', :arguments => {:i => 0}) {
      # Empty
    }

    preparator(:target => 'X', :mask => ["0000_0000", "0000_0000_0000_0000"]) {
      Or target, zero, zero
    }

    preparator(:target => 'X', :mask => ["FFFF_FFFF", "FFFF_FFFF_FFFF_FFFF"]) {
      Not target, zero
    }

    preparator(:target => 'X', :mask => [
      "'b00000000_00000000_00000XXX_XXXXXXXX",
      "'b00000000_00000000_00000000_00000000_00000000_00000000_00000XXX_XXXXXXXX"]) {
      ori target, zero, value(0, 10)
    }

    preparator(:target => 'FR') {
      #TODO: t5
      if rv64f == true then
        prepare(t5, value(0, 63))

        fcvt_s_l target, t5
      end
      if rv64f == false then
        prepare(t5, value(0, 31))

        fcvt_s_w target, t5
      end
    }

    preparator(:target => 'USTATUS') {}

    ################################################################################################

    # The code below specifies a comparator sequence to be used in self-checking tests
    # to test values in the specified register (target) accessed via the REG
    # addressing mode.
    #
    # Comparators are described using the same syntax as in preparators and can be
    # overridden in the same way.
    #
    # Default comparator: It is used when no special case is applicable.
    #
    comparator(:target => 'X') {
      prepare ra, value
      bne ra, target, :error
    }

    #
    # Special case: Target is $zero register. Since it is read only and
    # always equal zero, it makes no sense to test it.
    #
    comparator(:target => 'X', :arguments => {:i => 0}) {
      # Empty
    }

    #
    # Special case: Value equals 0x00000000. In this case, it is
    # more convenient to test the target against the zero register.
    #
    comparator(:target => 'X', :mask => ["0000_0000", "0000_0000_0000_0000"]) {
      bne zero, target, :error
    }

    ################################################################################################

    org 0x1000
    newline

global_label :__start
    nop
    #j :test
    nop
    newline

label :test
    #mfc0 t8, c0_config0
    #lui  t9, 0xffff
    #ori  t9, t9, 0xfff8
    #AND  t8, t8, t9

    #mtc0 t8, c0_config0
    nop
    nop
  end

  ##################################################################################################
  # Epilogue
  ##################################################################################################

  def post
label :success
    #TODO:
    newline

label :error
    #TODO:
    newline

    6.times {
      nop
    }
  end

  ##################################################################################################
  # Shortcuts for registers
  ##################################################################################################

  # General-purpose registers
  def zero(&contents) X(0,  &contents) end
  def   ra(&contents) X(1,  &contents) end
  def   sp(&contents) X(2,  &contents) end
  def   gp(&contents) X(3,  &contents) end
  def   tp(&contents) X(4,  &contents) end
  def   t0(&contents) X(5,  &contents) end
  def   t1(&contents) X(6,  &contents) end
  def   t2(&contents) X(7,  &contents) end
  def   s0(&contents) X(8,  &contents) end
  def   s1(&contents) X(9,  &contents) end
  def   a0(&contents) X(10, &contents) end
  def   a1(&contents) X(11, &contents) end
  def   a2(&contents) X(12, &contents) end
  def   a3(&contents) X(13, &contents) end
  def   a4(&contents) X(14, &contents) end
  def   a5(&contents) X(15, &contents) end
  def   a6(&contents) X(16, &contents) end
  def   a7(&contents) X(17, &contents) end
  def   s2(&contents) X(18, &contents) end
  def   s3(&contents) X(19, &contents) end
  def   s4(&contents) X(20, &contents) end
  def   s5(&contents) X(21, &contents) end
  def   s6(&contents) X(22, &contents) end
  def   s7(&contents) X(23, &contents) end
  def   s8(&contents) X(24, &contents) end
  def   s9(&contents) X(25, &contents) end
  def  s10(&contents) X(26, &contents) end
  def  s11(&contents) X(27, &contents) end
  def   t3(&contents) X(28, &contents) end
  def   t4(&contents) X(29, &contents) end
  def   t5(&contents) X(30, &contents) end
  def   t6(&contents) X(31, &contents) end

  # Floating-point registers
  def  ft0(&contents) FR(0,  &contents) end
  def  ft1(&contents) FR(1,  &contents) end
  def  ft2(&contents) FR(2,  &contents) end
  def  ft3(&contents) FR(3,  &contents) end
  def  ft4(&contents) FR(4,  &contents) end
  def  ft5(&contents) FR(5,  &contents) end
  def  ft6(&contents) FR(6,  &contents) end
  def  ft7(&contents) FR(7,  &contents) end
  def  ft8(&contents) FR(8,  &contents) end
  def  ft9(&contents) FR(9,  &contents) end
  def ft10(&contents) FR(10, &contents) end
  def ft11(&contents) FR(11, &contents) end
  def ft12(&contents) FR(12, &contents) end
  def ft13(&contents) FR(13, &contents) end
  def ft14(&contents) FR(14, &contents) end
  def ft15(&contents) FR(15, &contents) end
  def ft16(&contents) FR(16, &contents) end
  def ft17(&contents) FR(17, &contents) end
  def ft18(&contents) FR(18, &contents) end
  def ft19(&contents) FR(19, &contents) end
  def ft20(&contents) FR(20, &contents) end
  def ft21(&contents) FR(21, &contents) end
  def ft22(&contents) FR(22, &contents) end
  def ft23(&contents) FR(23, &contents) end
  def ft24(&contents) FR(24, &contents) end
  def ft25(&contents) FR(25, &contents) end
  def ft26(&contents) FR(26, &contents) end
  def ft27(&contents) FR(27, &contents) end
  def ft28(&contents) FR(28, &contents) end
  def ft29(&contents) FR(29, &contents) end
  def ft30(&contents) FR(30, &contents) end
  def ft31(&contents) FR(31, &contents) end

  ##################################################################################################
  # Shortcuts for system registers
  ##################################################################################################

  def risc_time
    TIME()
  end

  def risc_uepc
    UEPC()
  end

  ##################################################################################################
  # Shortcut methods to access memory resources in debug messages.
  ##################################################################################################

  def gpr_observer(index)
    location('XREG', index)
  end

  def mem_observer(index)
    location('MEM', index)
  end

  def fpr_observer(index)
    if rv32f == true then
      location('FPR', index)
    end
  end

  ##################################################################################################
  # Utility method for printing data stored in memory using labels.
  ##################################################################################################

  def trace_data_addr(begin_addr, end_addr)
    count = (end_addr - begin_addr) / 4
    additional_count = (end_addr - begin_addr) % 4
    if additional_count > 0
       count = count + 1
    end
    begin_index = begin_addr / 4

    trace "\nData starts: 0x%x", begin_addr
    trace "Data ends:   0x%x", end_addr
    trace "Data count:  %d", count

    index = begin_index
    addr = begin_addr

    trace "\nData values:"
    count.times {
      trace "%016x (MEM[0x%x]): 0x%08x", addr, index, mem_observer(index)
      index = index + 1
      addr = addr + 4
    }
    trace ""
  end

  def trace_data(begin_label, end_label)
    begin_addr = get_address_of(begin_label)
    end_addr = get_address_of(end_label)

    trace_data_addr(begin_addr, end_addr)
  end

  ##################################################################################################
  # Utility method to specify a random register that is not used in the current test case.
  ##################################################################################################

  def get_register(attrs = {})
    if nil == @free_register_allocator
      @free_register_allocator = mode_allocator('FREE')
    end

    x(_ @free_register_allocator, attrs)
  end

  ###################################################################################################
  # Utility method to remove the specified addressing mode from the list of used registers.
  ###################################################################################################

  def free_register(mode)
    free_allocated_mode mode
  end

end # RISCVBaseTemplate
