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

package org.sosy_lab.java_smt.solvers.Solverless;

import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.UFManager;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessUFManager extends AbstractUFManager<DummyFormula, DummyFunction, FormulaTypesForChecking,
    DummyEnv> {
  protected SolverLessUFManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName,
      FormulaType<T> pReturnType,
      FormulaType<?>... pArgs) {
    return super.declareUF(pName, pReturnType, pArgs);
  }

  @Override
  public <T extends Formula> T callUF(FunctionDeclaration<T> funcType, Formula... args) {
    return super.callUF(funcType, args);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name,
      FormulaType<T> pReturnType,
      List<Formula> pArgs) {
    return super.declareAndCallUF(name, pReturnType, pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name,
      FormulaType<T> pReturnType,
      Formula... pArgs) {
    return super.declareAndCallUF(name, pReturnType, pArgs);
  }
}
