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

import ru.ispras.fortress.data.types.bitvector.BitVector;
import ru.ispras.fortress.expression.ExprUtils;
import ru.ispras.fortress.expression.Node;
import ru.ispras.fortress.expression.NodeValue;
import ru.ispras.fortress.expression.NodeVariable;
import ru.ispras.fortress.randomizer.Randomizer;
import ru.ispras.fortress.util.InvariantChecks;
import ru.ispras.fortress.util.Pair;
import ru.ispras.microtesk.test.engine.branch.BranchDataGenerator;
import ru.ispras.testbase.TestBaseContext;
import ru.ispras.testbase.TestBaseQuery;
import ru.ispras.testbase.TestData;
import ru.ispras.testbase.knowledge.iterator.Iterator;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * {@link RiscvBranchDataGenerator} is a base class for the RISC-V branch instructions' generators.
 *
 * @author <a href="mailto:andrewt@ispras.ru">Andrei Tatarnikov</a>
 */
public abstract class RiscvBranchDataGenerator extends BranchDataGenerator {

  protected static long positiveValue() {
    return Randomizer.get().nextLongRange(1, Long.MAX_VALUE);
  }

  protected static long negativeValue() {
    return Randomizer.get().nextLongRange(Long.MIN_VALUE, -1);
  }

  protected static long nonPositiveValue() {
    return Randomizer.get().nextLongRange(Long.MIN_VALUE, 0);
  }

  protected static long nonNegativeValue() {
    return Randomizer.get().nextLongRange(0, Long.MAX_VALUE);
  }

  protected static Long generateEqual(Long rs1, Long rs2) {
    if (rs1 == null) {
      rs1 = rs2;
    } else if (rs2 == null) {
      rs2 = rs1;
    } else {
      InvariantChecks.checkTrue(rs1.equals(rs2), "Incorrect values defined");
    }
    if (rs1 == null) {
      return Randomizer.get().nextLong();
    }
    return rs1;
  }

  protected static Pair<Long, Long> generateDistinct(Long rs1, Long rs2) {
    if (rs1 == null && rs2 == null) {
      rs1 = Randomizer.get().nextLong();
      rs2 = distinctValue(rs1);
    } else if (rs1 == null) {
      rs1 = distinctValue(rs2);
    } else if (rs2 == null) {
      rs2 = distinctValue(rs1);
    } else {
      InvariantChecks.checkFalse(rs1.equals(rs2), "Incorrect values defined");
    }

    return new Pair<>(rs1, rs2);
  }

  protected static long distinctValue(final long x) {
    long value = x;
    do {
      value = Randomizer.get().nextLong();
    } while (value == x);
    return value;
  }

  protected static Iterator<TestData> generate(final TestBaseQuery query, final long rs) {
    final String op = getInstructionName(query);
    return generate(query, Collections.singletonMap(op + ".rs", rs));
  }

  protected static Long getValue(final String name, final TestBaseQuery query) {
    final BitVector value = getValueAsBitVector(name, query);
    return null != value ? value.longValue() : null;
  }

  protected static BitVector getValueAsBitVector(final String name, final TestBaseQuery query) {
    final String op = getInstructionName(query);
    final Node node = query.getBindings().get(op + "." + name);

    InvariantChecks.checkNotNull(node, name);
    InvariantChecks.checkTrue(ExprUtils.isVariable(node) || ExprUtils.isValue(node), name);

    if (ExprUtils.isValue(node)) {
      final NodeValue value = (NodeValue) node;
      return value.getBitVector();
    }

    final NodeVariable var = (NodeVariable) node;
    if (var.getData().hasValue()) {
      return var.getData().getValue(BitVector.class);
    }

    return null;
  }

  protected static Iterator<TestData> generate(
      final TestBaseQuery query,
      final long rs,
      final long rt) {
    final String op  = getInstructionName(query);
    final Map<String, Long> values = new HashMap<>();
    values.put(op + ".rs1", rs);
    values.put(op + ".rs2", rt);

    return generate(query, values);
  }

  private static String getInstructionName(final TestBaseQuery query) {
    return query.getContext().get(TestBaseContext.INSTRUCTION).toString();
  }
}
