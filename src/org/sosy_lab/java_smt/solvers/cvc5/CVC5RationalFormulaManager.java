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
import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class CVC5RationalFormulaManager
    extends CVC5NumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  CVC5RationalFormulaManager(
      CVC5FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Sort getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  protected Term makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected Term makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
  }

  @Override
  public Term divide(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.DIVISION, pParam1, pParam2);
  }

  @Override
  protected Term floor(Term pNumber) {
    return termManager.mkTerm(Kind.TO_INTEGER, pNumber);
  }
}
