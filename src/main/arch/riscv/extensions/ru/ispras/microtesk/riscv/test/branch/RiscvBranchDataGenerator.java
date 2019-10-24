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
import ru.ispras.testbase.knowledge.basis.GeneratorResult;
import ru.ispras.testbase.knowledge.branch.IfThenElseGenerator;
import ru.ispras.testbase.knowledge.integer.IntNumber;
import ru.ispras.testbase.knowledge.iterator.Iterator;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * {@link RiscvBranchDataGenerator} is a base class for the RISC-V branch instructions' generators.
 *
 * @author <a href="mailto:kamkin@ispras.ru">Alexander Kamkin</a>
 */
public abstract class RiscvBranchDataGenerator extends BranchDataGenerator {
  protected static final long MAX_VALUE = Integer.MAX_VALUE;
  protected static final long MIN_VALUE = Integer.MIN_VALUE;

  protected static IntNumber[] getOperands(
      final TestBaseQuery query,
      final int numberOfOperands) {
    InvariantChecks.checkTrue(numberOfOperands == 1 || numberOfOperands == 2);
    final IntNumber[] operands = new IntNumber[numberOfOperands];

    if (numberOfOperands == 1) {
      operands[0] = getValue("rs", query);
    } else {
      operands[1] = getValue("rs1", query);
      operands[1] = getValue("rs2", query);
    }

    return operands;
  }

  protected static Iterator<TestData> getTestData(
      final TestBaseQuery query,
      final GeneratorResult<IntNumber> result) {
    final String op  = getInstructionName(query);
    final Map<String, Long> values;

    final IntNumber[] operands = result.operands;
    if (operands.length == 1) {
      values = Collections.singletonMap(op + ".rs", operands[0].getValue(true));
    } else {
      values = new HashMap<>();
      values.put(op + ".rs1", operands[0].getValue(true));
      values.put(op + ".rs2", operands[1].getValue(true));
    }
    
    return generate(query, values);
  }

  private static IntNumber getValue(final String name, final TestBaseQuery query) {
    final String op = getInstructionName(query);
    final Node node = query.getBindings().get(op + "." + name);
    
    InvariantChecks.checkNotNull(node, name);
    InvariantChecks.checkTrue(ExprUtils.isVariable(node) || ExprUtils.isValue(node), name);
    
    if (ExprUtils.isValue(node)) {
      final NodeValue value = (NodeValue) node;
      return new IntNumber(IfThenElseGenerator.FORMAT, value.getBitVector().longValue());
    }
    
    final NodeVariable variable = (NodeVariable) node;
    if (variable.getData().hasValue()) {
      final BitVector value = variable.getData().getValue(BitVector.class);
      return new IntNumber(IfThenElseGenerator.FORMAT, value.longValue());
    }
    
    return null;
  }

  private static String getInstructionName(final TestBaseQuery query) {
    return query.getContext().get(TestBaseContext.INSTRUCTION).toString();
  }
}
