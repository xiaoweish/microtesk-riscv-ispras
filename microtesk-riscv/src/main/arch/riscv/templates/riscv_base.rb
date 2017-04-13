#
# MicroTESK RISC-V Edition
#
# Copyright (c) 2016 Institute for System Programming of the Russian Academy of Sciences
# All Rights Reserved
#
# Institute for System Programming of the Russian Academy of Sciences (ISP RAS)
# 25 Alexander Solzhenitsyn st., Moscow, 109004, Russia
# http://www.ispras.ru
# 

require ENV['TEMPLATE']

class RISCVBaseTemplate < Template
  def initialize
    super
    # Initialize settings here 
    @setup_memory       = false
    @setup_cache        = false
    @kseg0_cache_policy = 0

    # Sets the indentation token used in test programs
    set_option_value 'indent-token', "\t"

    # Sets the token used in separator lines printed into test programs
    set_option_value 'separator-token', "="

    set_option_value 'base-virtual-address', 0xffffffffa0002000
    set_option_value 'base-physical-address', 0x0000000000002000
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
    # Simple exception handler. Continues execution from the next instruction.
    #
    exception_handler {
      section(:org => 0x380, :exception => ['IntegerOverflow', 'SystemCall', 'Breakpoint']) {
        trace 'Exception handler (EPC = 0x%x)', location('CPR', 14 * 8)
    #TODO:
        #mfc0 ra, c0_epc
        #addiu ra, ra, 4
        #jr ra 
        nop
      }
    }

    ################################################################################################

    #
    # The code below specifies an instruction sequence that writes a value
    # to the specified register (target) via the R addressing mode.
    #
    # Default preparator: It is used when no special case previded below
    # is applicable.
    #
    preparator(:target => 'X') {
      # TODO:
    }

    preparator(:target => 'X', :arguments => {:i => 0}) {
      # Empty
    }

    preparator(:target => 'X', :mask => "0000000000000000") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "FFFFFFFFFFFFFFFF") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "000000000000XXXX") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "00000000XXXX0000") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "0000XXXX00000000") {
      # TODO:
      #ori    target, zero, value(32, 47)
      #dsll32 target, target, 0
    }

    preparator(:target => 'X', :mask => "XXXX000000000000") {
      # TODO:
      #ori    target, zero,   value(48, 63)
      #dsll32 target, target, 16
    }

    preparator(:target => 'X', :mask => "00000000XXXXXXXX") {
      # TODO:
      #ori  target, zero,   value(16, 31)
      #dsll target, target, 16
      #ori  target, target, value(0, 15)
    }

    preparator(:target => 'X', :mask => "0000XXXX0000XXXX") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "XXXX00000000XXXX") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "0000XXXXXXXX0000") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "XXXX0000XXXX0000") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "XXXXXXXX00000000") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "0000XXXXXXXXXXXX") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "XXXXXXXXXXXX0000") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "XXXXXXXX0000XXXX") {
      # TODO:
    }

    preparator(:target => 'X', :mask => "XXXX0000XXXXXXXX") {
      # TODO:
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
      # TODO:
      #lui at, value(16, 31)
      #ori at, target, value(0, 15)

      #bne at, target, :check_failed
      #nop
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
      #bne zero, target, :check_failed
      #nop
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
  # Aliases for X Registers
  ##################################################################################################

  def x0
    x(0)
  end

  def x1
    x(1)
  end

  def x2
    x(2)
  end

  def x3
    x(3)
  end

  def x4
    x(4)
  end

  def x5
    x(5)
  end

  def x6
    x(6)
  end

  def x7
    x(7)
  end

  def x8
    x(8)
  end

  def x9
    x(9)
  end

  def x10
    x(10)
  end

  def x11
    x(11)
  end

  def x12
    x(12)
  end

  def x13
    x(13)
  end

  def x14
    x(14)
  end

  def x15
    x(15)
  end

  def x16
    x(16)
  end

  def x17
    x(17)
  end

  def x18
    x(18)
  end

  def x19
    x(19)
  end

  def x20
    x(20)
  end

  def x21
    x(21)
  end

  def x22
    x(22)
  end

  def x23
    x(23)
  end

  def x24
    x(24)
  end

  def x25
    x(25)
  end

  def x26
    x(26)
  end

  def x27
    x(27)
  end

  def x28
    x(28)
  end

  def x29
    x(29)
  end

  def x30
    x(30)
  end

  def x31
    x(31)
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

  ##################################################################################################
  # Utility method for printing data stored in memory using labels.
  ##################################################################################################

  def trace_data(begin_label, end_label)
    begin_addr = get_address_of(begin_label)
    end_addr = get_address_of(end_label)

    count = (end_addr - begin_addr) / 8
    additional_count = (end_addr - begin_addr) % 8
    if additional_count > 0
       count = count + 1
    end
    begin_index = begin_addr / 8 

    trace "\nData starts: 0x%x", begin_addr
    trace "Data ends:   0x%x", end_addr
    trace "Data count:  %d", count

    index = begin_index
    addr = begin_addr

    trace "\nData values:"
    count.times {
      trace "%016x (MEM[0x%x]): 0x%016x", addr, index, mem_observer(index)
      index = index + 1
      addr = addr + 8
    }
    trace ""
  end

  ##################################################################################################
  # Utility method to specify a random register that is not used in the current test case.
  ##################################################################################################

  def get_register(attrs = {})
    if nil == @free_register_allocator
      @free_register_allocator = mode_allocator('FREE')
    end

    r(_ @free_register_allocator, attrs)
  end

  ###################################################################################################
  # Utility method to remove the specified addressing mode from the list of used registers.
  ###################################################################################################

  def free_register(mode)
    free_allocated_mode mode
  end

end # PowerPCBaseTemplate
