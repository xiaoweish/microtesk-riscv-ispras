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

public final class Rv64uaTestCase extends RiscVTest {
  private static final String BASE = "compliance/rv64ua/";
  
  private void test(final String file) {
    setCommandLineOption(Option.VERBOSE);
    final Statistics statistics = run(BASE + file);
    Assert.assertNotNull(statistics);
  }
  
  @Test
  public void testAmoaddd() {
    test("amoadd_d.rb");
  }

  @Test
  public void testAmoaddw() {
    test("amoadd_w.rb");
  }
  
  @Test
  public void testAmoandd() {
    test("amoand_d.rb");
  }
  
  @Test
  public void testAmoandw() {
    test("amoand_w.rb");
  }
  
  @Test
  public void testAmomaxud() {
    test("amomaxu_d.rb");
  }
  
  @Test
  public void testAmomaxuw() {
    test("amomaxu_w.rb");
  }

  @Test
  public void testAmomaxd() {
    test("amomax_d.rb");
  }

  @Test
  public void testAmomaxw() {
    test("amomax_w.rb");
  }
  
  @Test
  public void testAmominud() {
    test("amominu_d.rb");
  }
  
  @Test
  public void testAmominuw() {
    test("amominu_w.rb");
  }
  
  @Test
  public void testAmomind() {
    test("amomin_d.rb");
  }
  
  @Test
  public void testAmominw() {
    test("amomin_w.rb");
  }
  
  @Test
  public void testAmoord() {
    test("amoor_d.rb");
  }
  
  @Test
  public void testAmoorw() {
    test("amoor_w.rb");
  }
  
  @Test
  public void testAmoswapd() {
    test("amoswap_d.rb");
  }
  
  @Test
  public void testAmoswapw() {
    test("amoswap_w.rb");
  }
  
  @Test
  public void testAmoxord() {
    test("amoxor_d.rb");
  }

  @Test
  public void testAmoxorw() {
    test("amoxor_w.rb");
  }

  @Test
  public void testLrsc() {
    test("lrsc.rb");
  }
}