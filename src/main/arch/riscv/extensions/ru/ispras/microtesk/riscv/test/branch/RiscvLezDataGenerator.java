/*
 * Copyright 2018-2019 ISP RAS (http://www.ispras.ru)
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

import ru.ispras.testbase.TestBaseQuery;
import ru.ispras.testbase.TestData;
import ru.ispras.testbase.knowledge.branch.blez.BlezThenElseGenerator;
import ru.ispras.testbase.knowledge.integer.IntNumber;
import ru.ispras.testbase.knowledge.iterator.Iterator;

/**
 * {@link RiscvLezDataGenerator} is a test data generator for BLEZ instructions.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public final class RiscvLezDataGenerator extends RiscvBranchDataGenerator {
  @Override
  public Iterator<TestData> generateThen(final TestBaseQuery query) {
    final IntNumber[] operands = getOperands(query, 1);
    return getTestData(query, BlezThenElseGenerator.generateOperandsThen(operands));
  }

  @Override
  public Iterator<TestData> generateElse(final TestBaseQuery query) {
    final IntNumber[] operands = getOperands(query, 1);
    return getTestData(query, BlezThenElseGenerator.generateOperandsElse(operands));
  }
}
