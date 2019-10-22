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

package ru.ispras.microtesk.model.riscv.debug;

import org.junit.Assert;
import org.junit.Test;

import ru.ispras.microtesk.model.riscv.RiscVTest;
import ru.ispras.microtesk.options.Option;
import ru.ispras.microtesk.test.Statistics;

public final class DebugTestCase extends RiscVTest {
  private static final String BASE = "debug/";

  private void test(final String file) {
    setCommandLineOption(Option.VERBOSE);
    setCommandLineOption(Option.DEBUG_PRINT);

    final Statistics statistics = run(BASE + file);
    Assert.assertNotNull(statistics);
  }
  
  @Test
  public void testJalr() {
    test("debug_jalr.rb");
  }
  
  @Test
  public void testLa() {
    test("debug_la.rb");
  }

  @Test
  public void testLdSd() {
    test("debug_ld_sd.rb");
  }
  
  @Test
  public void testLdSdSv39() {
    test("debug_ld_sd_sv39.rb");
  }
  
  @Test
  public void testLdSdSv48() {
    test("debug_ld_sd_sv48.rb");
  }
  
  @Test
  public void testLi() {
    test("debug_li.rb");
  }
  
  @Test
  public void testLwSw() {
    test("debug_lw_sw.rb");
  }
  
  @Test
  public void testLwSwSv32() {
    test("debug_lw_sw_sv32.rb");
  }
  
  @Test
  public void testRv32a() {
    test("debug_rv32a.rb");
  }
  
  @Test
  public void testRv32d() {
    test("debug_rv32d.rb");
  }
  
  @Test
  public void testRv32f() {
    test("debug_rv32f.rb");
  }
  
  @Test
  public void testRv32f2() {
    test("debug_rv32f2.rb");
  }
  
  @Test
  public void testRv32i() {
    test("debug_rv32i.rb");
  }
  
  @Test
  public void testRv32m() {
    test("debug_rv32m.rb");
  }
  
  @Test
  public void testRv32v() {
    test("debug_rv32v.rb");
  }
  
  @Test
  public void testRv64a() {
    test("debug_rv64a.rb");
  }
  
  @Test
  public void testRv64d() {
    test("debug_rv64d.rb");
  }
  
  @Test
  public void testRv64f() {
    test("debug_rv64f.rb");
  }
  
  @Test
  public void testRv64i() {
    test("debug_rv64i.rb");
  }
  
  @Test
  public void testRv64m() {
    test("debug_rv64m.rb");
  }
  
  @Test
  public void testRvc() {
    test("debug_rvc.rb");
  }
}
