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
package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IExpression;
import ap.parser.ITerm;
import ap.types.Sort;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class PrincessArrayFormulaManager
    extends AbstractArrayFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  private final PrincessEnvironment env;

  PrincessArrayFormulaManager(
      FormulaCreator<IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration>
          pFormulaCreator) {
    super(pFormulaCreator);
    env = pFormulaCreator.getEnv();
  }

  @Override
  protected IExpression select(IExpression pArray, IExpression pIndex) {
    return env.makeSelect((ITerm) pArray, (ITerm) pIndex);
  }

  @Override
  protected IExpression store(IExpression pArray, IExpression pIndex, IExpression pValue) {
    return env.makeStore((ITerm) pArray, (ITerm) pIndex, (ITerm) pValue);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> IExpression internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {

    // other types in arrays are not supported in princess
    // TODO: check
    assert pIndexType.isIntegerType() && pElementType.isIntegerType();

    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Sort arrayType = toSolverType(arrayFormulaType);

    return getFormulaCreator().makeVariable(arrayType, pName);
  }

  @Override
  protected IExpression equivalence(IExpression pArray1, IExpression pArray2) {
    return ap.parser.IExpression.Eq$.MODULE$.apply((ITerm) pArray1, (ITerm) pArray2);
  }
}
