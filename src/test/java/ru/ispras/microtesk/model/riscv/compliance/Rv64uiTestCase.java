/*
 * Copyright 2018 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless requared by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.microtesk.model.riscv.compliance;

import org.junit.Assert;
import org.junit.Test;
import ru.ispras.microtesk.model.riscv.RiscVTest;
import ru.ispras.microtesk.options.Option;
import ru.ispras.microtesk.test.Statistics;

public final class Rv64uiTestCase extends RiscVTest {
  private static final String BASE = "compliance/rv64ui/";

  private void test(final String file) {
    setCommandLineOption(Option.VERBOSE);
    final Statistics statistics = run(BASE + file);
    Assert.assertNotNull(statistics);
  }

  @Test
  public void testAdd() {
    test("add.rb");
  }
  
  @Test
  public void testAddw() {
    test("addw.rb");
  }

  @Test
  public void testAddi() {
    test("addi.rb");
  }
  
  @Test
  public void testAddiw() {
    test("addiw.rb");
  }

  @Test
  public void testAnd() {
    test("and.rb");
  }

  @Test
  public void testAndi() {
    test("andi.rb");
  }

  @Test
  public void testAuipc() {
    test("auipc.rb");
  }

  @Test
  public void testBeq() {
    test("beq.rb");
  }

  @Test
  public void testBge() {
    test("bge.rb");
  }

  @Test
  public void testBgeu() {
    test("bgeu.rb");
  }

  @Test
  public void testBlt() {
    test("blt.rb");
  }

  @Test
  public void testBltu() {
    test("bltu.rb");
  }

  @Test
  public void testBne() {
    test("bne.rb");
  }

  @Test
  public void testFencei() {
    test("fence_i.rb");
  }

  @Test
  public void testJal() {
    test("jal.rb");
  }

  @Test
  public void testJalr() {
    test("jalr.rb");
  }

  @Test
  public void testLb() {
    test("lb.rb");
  }

  @Test
  public void testLbu() {
    test("lbu.rb");
  }
  
  @Test
  public void testLd() {
    test("ld.rb");
  }

  @Test
  public void testLh() {
    test("lh.rb");
  }
  
  @Test
  public void testLhu() {
    test("lhu.rb");
  }

  @Test
  public void testLui() {
    test("lui.rb");
  }

  @Test
  public void testLw() {
    test("lw.rb");
  }
  
  @Test
  public void testLwu() {
    test("lwu.rb");
  }

  @Test
  public void testOr() {
    test("or.rb");
  }

  @Test
  public void testOri() {
    test("ori.rb");
  }

  @Test
  public void testSb() {
    test("sb.rb");
  }
  
  @Test
  public void testSd() {
    test("sd.rb");
  }

  @Test
  public void testSh() {
    test("sh.rb");
  }

  @Test
  public void testSimple() {
   test("simple.rb");
  }

  @Test
  public void testSll() {
    test("sll.rb");
  }
  
  @Test
  public void testSllw() {
    test("sllw.rb");
  }

  @Test
  public void testSlli() {
    test("slli.rb");
  }
  
  @Test
  public void testSlliw() {
    test("slliw.rb");
  }

  @Test
  public void testSlt() {
    test("slt.rb");
  }

  @Test
  public void testSlti() {
    test("slti.rb");
  }

  @Test
  public void testSltiu() {
    test("sltiu.rb");
  }

  @Test
  public void testSltu() {
    test("sltu.rb");
  }

  @Test
  public void testSra() {
    test("sra.rb");
  }
  
  @Test
  public void testSraw() {
    test("sraw.rb");
  }

  @Test
  public void testSrai() {
    test("srai.rb");
  }
  
  @Test
  public void testSraiw() {
    test("sraiw.rb");
  }

  @Test
  public void testSrl() {
    test("srl.rb");
  }
  
  @Test
  public void testSrlw() {
    test("srlw.rb");
  }

  @Test
  public void testSrli() {
    test("srli.rb");
  }
  
  @Test
  public void testSrliw() {
    test("srliw.rb");
  }

  @Test
  public void testSub() {
    test("sub.rb");
  }
  
  @Test
  public void testSubw() {
    test("subw.rb");
  }

  @Test
  public void testSw() {
    test("sw.rb");
  }

  @Test
  public void testXor() {
    test("xor.rb");
  }

  @Test
  public void testXori() {
    test("xori.rb");
  }
}
