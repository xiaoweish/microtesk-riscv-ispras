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
import ru.ispras.testbase.generator.DataGenerator;
import ru.ispras.testbase.knowledge.iterator.EmptyIterator;
import ru.ispras.testbase.knowledge.iterator.Iterator;

/**
 * {@link RiscvGotoDataGenerator} is a test data generator for BEQ instructions.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class RiscvGotoDataGenerator implements DataGenerator {
  @Override
  public boolean isSuitable(final TestBaseQuery query) {
    return true;
  }

  @Override
  public Iterator<TestData> generate(final TestBaseQuery query) {
    return EmptyIterator.<TestData>get();
  }
}
