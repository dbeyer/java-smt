/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.stp;

import com.google.common.collect.Collections2;
import java.util.Collection;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

public final class StpFormulaManager extends AbstractFormulaManager<Expr, Type, VC, Long> {

  protected StpFormulaManager(
      StpFormulaCreator pFormulaCreator,
      StpUFManager pUFManager,
      StpBooleanFormulaManager pBooleanManager,
      @Nullable StpBitvectorFormulaManager pBitvectorManager,
      @Nullable StpArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pUFManager,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        null,
        null,
        pArrayManager);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    Expr expr = StpJavaApi.vc_parseExpr(getEnvironment(), pS);
    return getFormulaCreator().encapsulateBoolean(expr);
  }

  static Expr getStpTerm(Formula pT) {
    return ((StpFormula) pT).getTerm();
  }

  static Expr[] getStpTerm(Collection<? extends Formula> pFormulas) {

    return Collections2.transform(pFormulas, StpFormulaManager::getStpTerm).toArray(new Expr[0]);
  }

  @Override
  public Appender dumpFormula(Expr pT) {
    // TODO Auto-generated method stub
    return null;
  }
}
