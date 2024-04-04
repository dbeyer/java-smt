// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.Kind;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

@SuppressWarnings("MethodTypeParameterName")
public class CVC5ArrayFormulaManager extends AbstractArrayFormulaManager<Term, Sort, TermManager,
    Term> {

  private final TermManager termManager;

  public CVC5ArrayFormulaManager(CVC5FormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
    termManager = pFormulaCreator.getEnv();
  }

  @Override
  protected Term select(Term pArray, Term pIndex) {
    return termManager.mkTerm(Kind.SELECT, pArray, pIndex);
  }

  @Override
  protected Term store(Term pArray, Term pIndex, Term pValue) {
    return termManager.mkTerm(Kind.STORE, pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Term internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final Sort cvc5ArrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return getFormulaCreator().makeVariable(cvc5ArrayType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Term internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType, Term defaultElement) {
    final Sort cvc5ArrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return termManager.mkConstArray(cvc5ArrayType, defaultElement);
  }

  @Override
  protected Term equivalence(Term pArray1, Term pArray2) {
    return termManager.mkTerm(Kind.EQUAL, pArray1, pArray2);
  }
}
