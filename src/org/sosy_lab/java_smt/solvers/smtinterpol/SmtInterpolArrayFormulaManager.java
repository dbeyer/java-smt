// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

class SmtInterpolArrayFormulaManager
    extends AbstractArrayFormulaManager<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> {

  private final SmtInterpolEnvironment env;

  SmtInterpolArrayFormulaManager(SmtInterpolFormulaCreator pCreator) {
    super(pCreator);
    env = pCreator.getEnv();
  }

  @Override
  protected Term select(Term pArray, Term pIndex) {
    return env.term("select", pArray, pIndex);
  }

  @Override
  protected Term store(Term pArray, Term pIndex, Term pValue) {
    return env.term("store", pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Term internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {

    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Sort smtInterpolArrayType = toSolverType(arrayFormulaType);

    return getFormulaCreator().makeVariable(smtInterpolArrayType, pName);
  }

  @Override
  protected Term equivalence(Term pArray1, Term pArray2) {
    return env.term("=", pArray1, pArray2);
  }
}
