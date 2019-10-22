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

public final class Rv64umTestCase extends RiscVTest {
  private static final String BASE = "compliance/rv64um/";

  private void test(final String file) {
    setCommandLineOption(Option.VERBOSE);
    final Statistics statistics = run(BASE + file);
    Assert.assertNotNull(statistics);
  }

  @Test
  public void testDiv() {
    test("div.rb");
  }
  
  @Test
  public void testDivw() {
    test("divw.rb");
  }

  @Test
  public void testDivu() {
    test("divu.rb");
  }
  
  @Test
  public void testDivuw() {
    test("divuw.rb");
  }

  @Test
  public void testMul() {
    test("mul.rb");
  }
  
  @Test
  public void testMulh() {
    test("mulh.rb");
  }

  @Test
  public void testMulhsu() {
    test("mulhsu.rb");
  }

  @Test
  public void testMulhu() {
    test("mulhu.rb");
  }
  
  @Test
  public void testMulw() {
    test("mulw.rb");
  }

  @Test
  public void testRem() {
    test("rem.rb");
  }
  
  @Test
  public void testRemw() {
    test("remw.rb");
  }

  @Test
  public void testRemu() {
    test("remu.rb");
  }
  
  @Test
  public void testRemuw() {
    test("remuw.rb");
  }
}
