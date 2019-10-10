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

import java.math.BigInteger;
import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.randomizer.Randomizer;
import ru.ispras.testbase.TestBaseQuery;
import ru.ispras.testbase.TestData;
import ru.ispras.testbase.knowledge.iterator.Iterator;

/**
 * {@link RiscvLtuDataGenerator} is a test data generator for BLTU-family instructions.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public final class RiscvLtuDataGenerator extends RiscvBranchDataGenerator {
  private static final BigInteger MAX = BigInteger.ONE.shiftLeft(64).subtract(BigInteger.ONE);

  @Override
  public Iterator<TestData> generateThen(final TestBaseQuery query) {
    // rs1 is always unknown because it is chosen to be used as a stream register.
    // BitVector rs1BitVector = null; // getValueAsBitVector("rs1", query);
    BitVector rs2BitVector = getValueAsBitVector("rs2", query);

    final BigInteger rs2 = null != rs2BitVector
        ? rs2BitVector.bigIntegerValue(false)
        : Randomizer.get().nextBigIntegerRange(BigInteger.ONE, MAX);

    final BigInteger rs1 =
        Randomizer.get().nextBigIntegerRange(BigInteger.ZERO, rs2.subtract(BigInteger.ONE));

    return generate(query, rs1.longValue(), rs2.longValue());
  }

  @Override
  public Iterator<TestData> generateElse(final TestBaseQuery query) {
    // rs1 is always unknown because it is chosen to be used as a stream register.
    // BitVector rs1BitVector = null; // getValueAsBitVector("rs1", query);
    BitVector rs2BitVector = getValueAsBitVector("rs2", query);

    final BigInteger rs2 = null != rs2BitVector
        ? rs2BitVector.bigIntegerValue(false)
        : Randomizer.get().nextBigIntegerRange(BigInteger.ZERO, MAX);

    final BigInteger rs1 =
        Randomizer.get().nextBigIntegerRange(rs2, MAX);

    return generate(query, rs1.longValue(), rs2.longValue());
  }
}
