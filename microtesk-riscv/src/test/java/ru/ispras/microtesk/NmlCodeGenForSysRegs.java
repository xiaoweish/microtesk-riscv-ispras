/*
 * Copyright 2018 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.microtesk;

import java.util.ArrayList;
import java.util.List;

/**
 * The {@link NmlCodeGenForSysRegs} is a utility class to generate nML code
 * for addressing mode that provide access to system registers.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class NmlCodeGenForSysRegs {
  public static void main(final String[] args) {
    /*
    section("User Counter/Timers")
      .add(0xC00, "cycle", "Cycle counter for RDCYCLE instruction")
      .add(0xC01, "time", "Timer for RDTIME instruction")
      .add(0xC02, "instret", "Instructions-retired counter for RDINSTRET instruction")
      .add(0xC03, "hpmcounter%d","Performance-monitoring counter", 3, 31)

      .add(0xC80, "cycleh", "Upper 32 bits of cycle, RV32I only")
      .add(0xC81, "timeh", "Upper 32 bits of time, RV32I only")
      .add(0xC82, "instreth", "Upper 32 bits of instret, RV32I only")
      .add(0xC83, "hpmcounter%dh","Upper 32 bits of hpmcounter%d, RV32I only", 3, 31)

      .print();
    */

    /*
    section("Supervisor Trap Setup")
        .add(0x100, "sstatus", "Supervisor status register")
        .add(0x102, "sedeleg", "Supervisor exception delegation register")
        .add(0x103, "sideleg", "Supervisor interrupt delegation register")
        .add(0x104, "sie", "Supervisor interrupt-enable register")
        .add(0x105, "stvec", "Supervisor trap handler base address")
        .add(0x106, "scounteren", "Supervisor counter enable")
        .print();
    */

    /*
    section("Supervisor Trap Handling")
        .add(0x140, "sscratch", "Scratch register for supervisor trap handlers")
        .add(0x141, "sepc", "Supervisor exception program counter")
        .add(0x142, "scause", "Supervisor trap cause")
        .add(0x143, "stval", "Supervisor bad address or instruction")
        .add(0x144, "sip", "Supervisor interrupt pending")
        .print();
    */

    /*
    section("Supervisor Protection and Translation")
        .add(0x180, "satp", "Supervisor address translation and protection")
        .print();
    */

    /*
    section("Machine Information Registers")
        .add(0xF11, "mvendorid", "Vendor ID")
        .add(0xF12, "marchid", "Architecture ID")
        .add(0xF13, "mimpid", "Implementation ID")
        .add(0xF14, "mhartid", "Hardware thread ID")
        .print();
    */

    /*
    section("Machine Trap Setup")
        .add(0x300, "mstatus", "Machine status register")
        .add(0x301, "misa", "ISA and extensions")
        .add(0x302, "medeleg", "Machine exception delegation register")
        .add(0x303, "mideleg", "Machine interrupt delegation register")
        .add(0x304, "mie", "Machine interrupt-enable register")
        .add(0x305, "mtvec", "Machine trap-handler base address")
        .add(0x306, "mcounteren", "Machine counter enable")
        .print();
    */

    /*
    section("Machine Trap Handling")
        .add(0x340, "mscratch", "Scratch register for machine trap handlers")
        .add(0x341, "mepc", "Machine exception program counter")
        .add(0x342, "mcause", "Machine trap cause")
        .add(0x343, "mtval", "Machine bad address or instruction")
        .add(0x344, "mip", "Machine interrupt pending")
        .print();
    */

    /*
    section("Machine Protection and Translation")
        .add(0x3A0, "pmpcfg0", "Physical memory protection configuration")
        .add(0x3A1, "pmpcfg1", "Physical memory protection configuration, RV32 only")
        .add(0x3A2, "pmpcfg2", "Physical memory protection configuration")
        .add(0x3A3, "pmpcfg3", "Physical memory protection configuration, RV32 only")
        .add(0x3B0, "pmpaddr%d", "Physical memory protection address register", 0, 15)
        .print();
    */

    section("Machine Counter/Timers")
        .add(0xB00, "mcycle", "Machine cycle counter")
        .add(0xB02, "minstret", "Machine instructions-retired counter")
        .add(0xB03, "mhpmcounter%d","Machine performance-monitoring counter", 3, 31)

        .add(0xB80, "mcycleh", "Upper 32 bits of mcycle, RV32I only")
        .add(0xB82, "minstreth", "Upper 32 bits of minstret, RV32I only")
        .add(0xB83, "mhpmcounter%dh","Upper 32 bits of mhpmcounter%d, RV32I only", 3, 31)

        .print();

    /*
    section("Debug/Trace Registers (shared with Debug Mode)")
        .add(0x7A0, "tselect", "Debug/Trace trigger register select")
        .add(0x7A1, "tdata1", "First Debug/Trace trigger data register")
        .add(0x7A2, "tdata2", "Second Debug/Trace trigger data register")
        .add(0x7A3, "tdata3", "Third Debug/Trace trigger data register")
        .print();
    */

    /*
    section("Debug Mode Registers")
        .add(0x7B0, "dcsr", "Debug control and status register")
        .add(0x7B1, "dpc", "Debug PC")
        .add(0x7B2, "dscratch", "Debug scratch register")
        .print();
    */
  }

  private static Printer section(final String title) {
    return new Printer(title);
  }

  private static final class Printer {
    private final class Item {
      public final int index;
      public final String name;
      public final String comment;

      public Item(final int index, final String name, final String comment) {
        this.index = index;
        this.name = name;
        this.comment = comment;
      }
    }

    private final String title;
    private final List<Item> items;

    public Printer(final String title) {
      this.title = title;
      this.items = new ArrayList<>();
    }

    public Printer add(
        final int index,
        final String name,
        final String comment) {
      this.items.add(new Item(index, name, comment));
      return this;
    }

    public Printer add(
        final int index,
        final String name,
        final String comment,
        final int start, final int end) {
      int currentIndex = index;
      for (int number = start; number <= end; ++number) {
        add(currentIndex++, String.format(name, number), String.format(comment, number));
      }
      return this;
    }

    public void print() {
      printHeader(title);
      for (final Item item : items) {
        printItem(item);
      }

      System.out.println();
      System.out.println("// " + title);
      for (final Item item : items) {
        System.out.print("              ");
        System.out.print("| ");
        System.out.print(item.name.toUpperCase());
        System.out.println();
      }
    }

    private static void printHeader(final String title) {
      System.out.print("//");
      for (int i = 0; i < 98; i++) {
        System.out.print("=");
      }
      System.out.println();

      System.out.println("// " + title);
      System.out.println();
    }

    private static void printItem(final Item item) {
      System.out.println("// " + item.comment);
      System.out.printf("mode %s() = CSR[0x%03X]%n", item.name.toUpperCase(), item.index);
      System.out.printf("  init = { csr_index = 0x%03X; }%n", item. index);
      System.out.printf("  syntax = format(\"%s\")%n", item.name);
      System.out.println("  image = format(\"%12s\", csr_index)");
      System.out.println();
    }
  }
}
