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

public final class Rv32uvTestCase extends RiscVTest {
  private static final String BASE = "compliance/rv32uv/";

  private void test(final String file) {
    setCommandLineOption(Option.VERBOSE);
    setCommandLineOption(Option.SELF_CHECKS);
  
    final Statistics statistics = run(BASE + file);
    Assert.assertNotNull(statistics);
  }
  
  @Test
  public void testVaddVl32e32m4d1() {
    test("rv32v_vadd_vl32e32m4d1_selfcheck.rb");
  }
  
  @Test
  public void testVdivVl32e32m4d1() {
    test("rv32v_vdiv_vl32e32m4d1_selfcheck.rb");
  }
  
  @Test
  public void testVmulVl32e32m4d1() {
    test("rv32v_vmul_vl32e32m4d1_selfcheck.rb");
  }
  
  @Test
  public void testVsubVl32e32m4d1() {
    test("rv32v_vsub_vl32e32m4d1_selfcheck.rb");
  }
}
