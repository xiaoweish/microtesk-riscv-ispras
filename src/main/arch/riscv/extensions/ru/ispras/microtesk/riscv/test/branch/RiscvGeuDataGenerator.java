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

package ru.ispras.microtesk.riscv.test.branch;

import ru.ispras.fortress.randomizer.Randomizer;
import ru.ispras.testbase.TestBaseQuery;
import ru.ispras.testbase.TestData;
import ru.ispras.testbase.knowledge.iterator.Iterator;

/**
 * {@link RiscvGeuDataGenerator} is a test data generator for BGEU-family instructions.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class RiscvGeuDataGenerator extends RiscvBranchDataGenerator {
  @Override
  public Iterator<TestData> generateThen(final TestBaseQuery query) {
    // rs1 is always unknown because it is chosen to be used as a stream register.
    Long rs1 = null;
    Long rs2 = getValue("rs2", query);

    if (null == rs2) {
      rs2 = Randomizer.get().nextLongRange(0, MAX_VALUE);
    }

    rs1 = Randomizer.get().nextLongRange(rs2, MAX_VALUE);
    return generate(query, rs1, rs2);
  }

  @Override
  public Iterator<TestData> generateElse(final TestBaseQuery query) {
    // rs1 is always unknown because it is chosen to be used as a stream register.
    Long rs1 = null;
    Long rs2 = getValue("rs2", query);

    if (null == rs2) {
      rs2 = Randomizer.get().nextLongRange(1, MAX_VALUE);
    }

    rs1 = Randomizer.get().nextLongRange(0, rs2 - 1);
    return generate(query, rs1, rs2);
  }
}
