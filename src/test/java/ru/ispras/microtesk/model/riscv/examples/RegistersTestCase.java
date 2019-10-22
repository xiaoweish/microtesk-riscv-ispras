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

package ru.ispras.microtesk.model.riscv.examples;

import org.junit.Assert;
import org.junit.Test;

import ru.ispras.microtesk.model.riscv.RiscVTest;
import ru.ispras.microtesk.options.Option;
import ru.ispras.microtesk.test.Statistics;

public final class RegistersTestCase extends RiscVTest {
  private static final String BASE = "examples/registers/";
  
  private void test(final String file) {
    setCommandLineOption(Option.VERBOSE);
    final Statistics statistics = run(BASE + file);
    Assert.assertNotNull(statistics);
  }
  
  @Test
  public void testRegister() {
    test("register.rb");
  }
  
  @Test
  public void testRegisterAllocation() {
    test("register_allocation.rb");
  }
  
  @Test
  public void testRegisterExcludeRetain() {
    test("register_exclude_retain.rb");
  }
  
  @Test
  public void testRegisterReservationAuto() {
    test("register_reservation_auto.rb");
  }
  
  @Test
  public void testRegisterReservationManual() {
    test("register_reservation_manual.rb");
  }
}
