// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class CVC5IntegerFormulaManager
    extends CVC5NumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  CVC5IntegerFormulaManager(CVC5FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Sort getNumeralType() {
    return getFormulaCreator().getIntegerType();
  }

  @Override
  protected Term makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected Term makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  public Term divide(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.INTS_DIVISION, pParam1, pParam2);
  }

  @Override
  protected Term modularCongruence(Term pNumber1, Term pNumber2, long pModulo) {
    return modularCongruence(pNumber1, pNumber2, BigInteger.valueOf(pModulo));
  }

  @Override
  protected Term modularCongruence(Term pNumber1, Term pNumber2, BigInteger pModulo) {
    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    if (BigInteger.ZERO.compareTo(pModulo) < 0) {
      Term n = makeNumberImpl(pModulo);
      Term x = subtract(pNumber1, pNumber2);
      return termManager.mkTerm(
          Kind.EQUAL,
          x,
          termManager.mkTerm(Kind.MULT, n, termManager.mkTerm(Kind.INTS_DIVISION, x, n)));
    }
    return termManager.mkBoolean(true);
  }

  @Override
  protected Term makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  protected Term makeNumberImpl(String pI) {
    if (!INTEGER_NUMBER.matcher(pI).matches()) {
      throw new NumberFormatException("Number is not an integer value: " + pI);
    }
    try {
      return termManager.mkInteger(pI);
    } catch (CVC5ApiException e) {
      throw new NumberFormatException("Number is not an integer value: " + pI);
    }
  }

  @Override
  protected Term makeVariableImpl(String pI) {
    return formulaCreator.makeVariable(getFormulaCreator().getIntegerType(), pI);
  }
}
