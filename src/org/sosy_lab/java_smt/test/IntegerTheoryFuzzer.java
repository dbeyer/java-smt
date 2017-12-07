/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package org.sosy_lab.java_smt.test;

import java.util.Random;
import java.util.stream.IntStream;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

/** Fuzzer over the theory of integers. */
class IntegerTheoryFuzzer {

  private final IntegerFormulaManager ifmgr;
  private IntegerFormula[] vars = new IntegerFormula[0];
  private final Random r;
  private static final String varNameTemplate = "VAR_";
  private int maxConstant;

  IntegerTheoryFuzzer(FormulaManager fmgr, Random pR) {
    ifmgr = fmgr.getIntegerFormulaManager();
    r = pR;
  }

  public IntegerFormula fuzz(int formulaSize, int pMaxConstant) {
    IntegerFormula[] args =
        IntStream.range(0, formulaSize)
            .mapToObj(i -> ifmgr.makeVariable(varNameTemplate + i))
            .toArray(IntegerFormula[]::new);
    return fuzz(formulaSize, pMaxConstant, args);
  }

  public IntegerFormula fuzz(int formulaSize, int pMaxConstant, IntegerFormula... pVars) {
    vars = pVars;
    maxConstant = pMaxConstant;
    return recFuzz(formulaSize);
  }

  private IntegerFormula recFuzz(int pFormulaSize) {
    if (pFormulaSize == 1) {

      if (r.nextBoolean()) {
        return getConstant();

      } else {
        return getVar();
      }

    } else if (pFormulaSize == 2) {
      return ifmgr.negate(getVar());
    } else {

      // One token taken by the operator.
      pFormulaSize -= 1;

      // Pivot \in [1, formulaSize - 1]
      int pivot = 1 + r.nextInt(pFormulaSize - 1);
      switch (r.nextInt(3)) {
        case 0:
          return ifmgr.add(recFuzz(pivot), recFuzz(pFormulaSize - pivot));
        case 1:
          return ifmgr.subtract(recFuzz(pivot), recFuzz(pFormulaSize - pivot));
        case 2:

          // Multiplication by a constant.
          return ifmgr.multiply(getConstant(), recFuzz(pFormulaSize - 1));
        default:
          throw new UnsupportedOperationException("Unexpected state");
      }
    }
  }

  private IntegerFormula getConstant() {
    return ifmgr.makeNumber((long) r.nextInt(2 * maxConstant) - maxConstant);
  }

  private IntegerFormula getVar() {
    return vars[r.nextInt(vars.length)];
  }
}
