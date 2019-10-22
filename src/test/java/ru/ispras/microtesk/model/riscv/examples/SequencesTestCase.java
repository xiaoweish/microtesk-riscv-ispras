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
import ru.ispras.microtesk.test.Statistics;

public final class SequencesTestCase extends RiscVTest {
  private static final String BASE = "examples/sequences/";
  
  private void test(final String file) {
    final Statistics statistics = run(BASE + file);
    Assert.assertNotNull(statistics);
  }
  
  private void test(
      final String file,
      final int numberOfPrograms,
      final int numberOfSequences,
      final int numberOfInstructions) {
    final Statistics statistics = run(BASE + file);

    Assert.assertNotNull(statistics);
    Assert.assertEquals(numberOfPrograms, statistics.getPrograms());
    Assert.assertEquals(numberOfSequences, statistics.getSequences());
    Assert.assertEquals(numberOfInstructions, statistics.getInstructions());
  }
  
  @Test
  public void testArithmetic() {
    test("arithmetic.rb");
  }
  
  @Test
  public void testAtomic() {
    test("atomic.rb", 1, 3, 113);
  }
  
  @Test
  public void testBlock() {
    test("block.rb");
  }
  
  @Test
  public void testGroup() {
    test("group.rb");
  }
  
  @Test
  public void testIterate() {
    test("iterate.rb", 1, 24, 140);
  }
  
  @Test
  public void testNitems() {
    test("nitems.rb", 1, 10, 533);
  }
  
  @Test
  public void testSequence() {
    test("sequence.rb", 1, 7, 186);
  }
}
