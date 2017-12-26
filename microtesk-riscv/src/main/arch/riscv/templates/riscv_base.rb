#
# Copyright 2017 ISP RAS (http://www.ispras.ru)
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

class RISCVBaseTemplate < Template
  ##################################################################################################
  # Settings
  ##################################################################################################

  def initialize
    super
    # Initialize settings here 
    @setup_memory       = false
    @setup_cache        = false
    @kseg0_cache_policy = 0

    # Sets the indentation token used in test programs
    set_option_value 'indent-token', "\t"

    # Sets the single-line comment text used in test programs
    set_option_value 'comment-token', "#"

    # Sets the token used in separator lines printed into test programs
    set_option_value 'separator-token', "="

    # Defines Alias Methods for X Registers
    (0..31).each do |i|
      define_method "x#{i}" do x(i) end
    end
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
    section_text(:pa => 0x01000, :va => 0x000001000) {}

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
      entry_point(:org => 0x100380, :exception => ['IntegerOverflow', 'SystemCall', 'Breakpoint']) {
        trace 'Exception handler (EPC = 0x%x)', location('CPR', 14 * 8)
    #TODO:
        #mfc0 ra, c0_epc
        #addiu ra, ra, 4
        #jr ra 
        nop
      }
    }
    ##################################################################################################
    # Revisions
    ##################################################################################################

    def rv64i
      if get_option_value('rev-id') == 'RV64I' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    def rv32m
      if get_option_value('rev-id') == 'RV32M' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    def rv64m
      if get_option_value('rev-id') == 'RV64M' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    def rv32a
      if get_option_value('rev-id') == 'RV32A' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    def rv64a
      if get_option_value('rev-id') == 'RV64A' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    def rv32f
      if get_option_value('rev-id') == 'RV32F' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    def rv64f
      if get_option_value('rev-id') == 'RV64F' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    def rv32d
      if get_option_value('rev-id') == 'RV32D' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    def rv64d
      if get_option_value('rev-id') == 'RV64D' or get_option_value('rev-id') == 'RV64FULL' then true
      else false end
    end

    ################################################################################################

    #
    # The code below specifies an instruction sequence that writes a value
    # to the specified register (target) via the R addressing mode.
    #
    # Default preparator: It is used when no special case previded below
    # is applicable.
    #
    preparator(:target => 'X') {
      if rv64i == true then
        ori  target, zero,   value(53, 63)
        slli target, target, 11
        ori  target, target, value(42, 52)
        slli target, target, 10
        ori  target, target, value(32, 41)
        slli target, target, 11
        ori  target, target, value(21, 31)
      end
      if rv64i == false then
        ori  target, zero, value(21, 31)
      end
      slli target, target, 11
      ori  target, target, value(10,  20)
      slli target, target, 10
      ori  target, target, value(0,  9)
    }

    preparator(:target => 'X', :arguments => {:i => 0}) {
      # Empty
    }

    preparator(:target => 'X', :mask => "0000000000000000") {
      Or target, zero, zero
    }

    preparator(:target => 'X', :mask => "FFFFFFFFFFFFFFFF") {
      Not target, zero
    }

    preparator(:target => 'X', :mask => "00000000XXXXXXXX") {
      ori  target, zero, value(21, 31)
      slli target, target, 11
      ori  target, target, value(10,  20)
      slli target, target, 10
      ori  target, target, value(0,  9)
    }

    ################################################################################################

    buffer_preparator(:target => 'DTLB') {
      newline
      comment('Prepare DTLB')

      # TODO:
    }

    buffer_preparator(:target => 'JTLB') {
      newline
      comment('Prepare JTLB')

      # TODO:
    }

    buffer_preparator(:target => 'L1') {
      newline
      comment('Prepare L1')

      # TODO:
    }

    buffer_preparator(:target => 'L2') {
      newline
      comment('Prepare L2')

      # TODO:
    }

    buffer_preparator(:target => 'MEM') {
      # Do nothing.
    }

    ################################################################################################

    # The code below specifies a comparator sequence to be used in self-checking tests
    # to test values in the specified register (target) accessed via the REG
    # addressing mode.
    #
    # Comparators are described using the same syntax as in preparators and can be
    # overridden in the same way..
    #
    # Default comparator: It is used when no special case is applicable.
    #
    comparator(:target => 'X') {
      ori  ra, zero, value(21, 31)
      slli ra, ra, 11
      ori  ra, ra, value(10,  20)
      slli ra, ra, 10
      ori  ra, ra, value(0,  9)

      bne ra, target, :check_failed
      nop
    }

    #
    # Special case: Target is $zero register. Since it is read only and
    # always equal zero, it makes no sence to test it.
    #
    comparator(:target => 'X', :arguments => {:i => 0}) {
      # Empty
    }

    #
    # Special case: Value equals 0x00000000. In this case, it is
    # more convenient to test the target against the $zero register.
    #
    comparator(:target => 'X', :mask => "00000000") {
      bne zero, target, :check_failed
      nop
    }

    ################################################################################################

    # The code below specifies default situations that generate random values
    # for instructions which require arguments to be 32-bit sign-extended values.

    # Generator of 32-bit random values which will be sign-extended to fit the target register.
    random_word = situation('random', :size => 32, :sign_extend => true)

    # Input arguments of all instructions listed below are random words.
    # set_default_situation 'add'   do random_word end
    # set_default_situation 'addi'  do random_word end

    ################################################################################################

    # TODO:
    #text ".nolist"
    #text ".set noreorder"
    #text ".set noat"
    #newline
    #text "#include \"regdef_k64.h\""
    #text "#include \"kernel_k64.h\""
    #newline
    #text ".list"
    #text ".text"
    #text ".globl __start"
    #newline
    #org 0x2000
    #newline

label :__start
    nop
    #j :test
    nop
    newline

label :test
    #mfc0 t8, c0_config0
    #lui  t9, 0xffff
    #ori  t9, t9, 0xfff8
    #AND  t8, t8, t9

    if @kseg0_cache_policy != 0
      #ori t8, t9, @kseg0_cache_policy
    end

    #mtc0 t8, c0_config0
    nop
    nop

    if @setup_memory
      newline
      #jal :memory_setup
      nop
    end

    if @setup_cache
      newline
      #jal :cache_setup
      nop
    end
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

    if @setup_memory
      text "TODO: setup memory"
    end
    if @setup_cache
      text "TODO: setup cache"
    end

    6.times {
      nop
    }
  end

  ##################################################################################################
  # Shortcuts for registers
  ##################################################################################################

  def zero
    X(0)
  end

  def ra
    X(1)
  end

  def sp
    X(2)
  end

  def gp
    X(3)
  end

  def tp
    X(4)
  end

  def t0
    X(5)
  end

  def t1
    X(6)
  end

  def t2
    X(7)
  end

  def s0
    X(8)
  end

  def s1
    X(9)
  end

  def a0
    X(10)
  end

  def a1
    X(11)
  end

  def a2
    X(12)
  end

  def a3
    X(13)
  end

  def a4
    X(14)
  end

  def a5
    X(15)
  end

  def a6
    X(16)
  end

  def a7
    X(17)
  end

  def s2
    X(18)
  end

  def s3
    X(19)
  end

  def s4
    X(20)
  end

  def s5
    X(21)
  end

  def s6
    X(22)
  end

  def s7
    X(23)
  end

  def s8
    X(24)
  end

  def s9
    X(25)
  end

  def s10
    X(26)
  end

  def s11
    X(27)
  end

  def t3
    X(28)
  end

  def t4
    X(29)
  end

  def t5
    X(30)
  end

  def t6
    X(31)
  end

  # Floating Point registers

  def ft0
    FR(0)
  end

  def ft1
    FR(1)
  end

  def ft2
    FR(2)
  end

  def ft3
    FR(3)
  end

  def ft4
    FR(4)
  end

  def ft5
    FR(5)
  end

  def ft6
    FR(6)
  end

  def ft7
    FR(7)
  end

  def ft8
    FR(8)
  end

  def ft9
    FR(9)
  end

  def ft10
    FR(10)
  end

  def ft11
    FR(11)
  end

  def ft12
    FR(12)
  end

  def ft13
    FR(13)
  end

  def ft14
    FR(14)
  end

  def ft15
    FR(15)
  end

  def ft16
    FR(16)
  end

  def ft17
    FR(17)
  end

  def ft18
    FR(18)
  end

  def ft19
    FR(19)
  end

  def ft20
    FR(20)
  end

  def ft21
    FR(21)
  end

  def ft22
    FR(22)
  end

  def ft23
    FR(23)
  end

  def ft24
    FR(24)
  end

  def ft25
    FR(25)
  end

  def ft26
    FR(26)
  end

  def ft27
    FR(27)
  end

  def ft28
    FR(28)
  end

  def ft29
    FR(29)
  end

  def ft30
    FR(30)
  end

  def ft31
    FR(31)
  end

  ##################################################################################################
  # Shortcuts for system registers
  ##################################################################################################

  def risc_time
    TIME()
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

  def load_address_to_reg(reg_addr, address_label)
    lui reg_addr, get_address_of(address_label)>>12
    temp = 4095
    addi reg_addr, reg_addr, get_address_of(address_label)&temp
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
