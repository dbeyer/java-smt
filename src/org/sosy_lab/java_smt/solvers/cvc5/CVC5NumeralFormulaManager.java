// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static io.github.cvc5.Kind.ADD;
import static io.github.cvc5.Kind.DIVISION;
import static io.github.cvc5.Kind.INTS_DIVISION;
import static io.github.cvc5.Kind.INTS_MODULUS;
import static io.github.cvc5.Kind.MULT;
import static io.github.cvc5.Kind.SUB;

import com.google.common.collect.ImmutableSet;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.math.BigInteger;
import java.util.List;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class CVC5NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Term, Sort, TermManager, ParamFormulaType, ResultFormulaType, Term> {

  /**
   * CVC4 fails hard when creating Integers/Rationals instead of throwing an exception for invalid
   * number format. Thus lets check the format.
   */
  public static final Pattern INTEGER_NUMBER = Pattern.compile("(-)?(\\d)+");

  public static final Pattern RATIONAL_NUMBER = Pattern.compile("(-)?(\\d)+(.)?(\\d)*");

  /**
   * Operators for arithmetic functions that return a numeric value. Remove if not needed after
   * tests!
   */
  @SuppressWarnings("unused")
  private static final ImmutableSet<Kind> NUMERIC_FUNCTIONS =
      ImmutableSet.of(ADD, SUB, MULT, DIVISION, INTS_DIVISION, INTS_MODULUS);

  protected final TermManager termManager;

  CVC5NumeralFormulaManager(CVC5FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    termManager = pCreator.getEnv();
  }

  protected abstract Sort getNumeralType();

  @Override
  protected boolean isNumeral(Term pVal) {
    // There seems to be no way of checking if a Term is const in CVC5
    return pVal.isIntegerValue() || pVal.isRealValue();
  }

  /**
   * Check whether the current term is numeric and the value of a term is determined by only
   * numerals, i.e. no variable is contained. This method should check as precisely as possible the
   * situations in which CVC5 supports arithmetic operations like multiplications.
   *
   * <p>Example: TRUE for "1", "2+3", "ite(x,2,3) and FALSE for "x", "x+2", "ite(1=2,x,0)"
   */
  /* Enable if needed!
  boolean consistsOfNumerals(Term val) {
    Set<Term> finished = new HashSet<>();
    Deque<Term> waitlist = new ArrayDeque<>();
    waitlist.add(val);
    while (!waitlist.isEmpty()) {
      Term e = waitlist.pop();
      if (!finished.add(e)) {
        continue;
      }
      if (isNumeral(e)) {
        // true, skip and check others
      } else if (NUMERIC_FUNCTIONS.contains(e.getKind())) {
        Iterables.addAll(waitlist, e);
      } else if (ITE.equals(e.getKind())) {
        // ignore condition, just use the if- and then-case
        waitlist.add(e.getChild(1));
        waitlist.add(e.getChild(2));
      } else {
        return false;
      }
    }
    return true;
  }
  */

  @Override
  protected Term makeNumberImpl(long i) {
    // we connot use "new Rational(long)", because it uses "unsigned long".
    return makeNumberImpl(Long.toString(i));
  }

  @Override
  protected Term makeNumberImpl(BigInteger pI) {
    return makeNumberImpl(pI.toString());
  }

  @Override
  protected Term makeNumberImpl(String pI) {
    if (!RATIONAL_NUMBER.matcher(pI).matches()) {
      throw new NumberFormatException("number is not an rational value: " + pI);
    }
    try {
      return termManager.mkReal(pI);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid rational number with input Sring: " + pI + ".", e);
    }
  }

  @Override
  protected Term makeVariableImpl(String varName) {
    Sort type = getNumeralType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Term multiply(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.MULT, pParam1, pParam2);
    /*
     * In CVC4 we had to check if the terms consist of only numerals, if this
     * fails we have to do it again!
    if (consistsOfNumerals(pParam1) || consistsOfNumerals(pParam2)) {
      return solver.mkTerm(Kind.MULT, pParam1, pParam2);
    } else {
      return super.multiply(pParam1, pParam2);
    }
    */
  }

  @Override
  protected Term modulo(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.INTS_MODULUS, pParam1, pParam2);
  }

  @Override
  protected Term negate(Term pParam1) {
    return termManager.mkTerm(Kind.NEG, pParam1);
  }

  @Override
  protected Term add(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.ADD, pParam1, pParam2);
  }

  @Override
  protected Term subtract(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.SUB, pParam1, pParam2);
  }

  @Override
  protected Term equal(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.GT, pParam1, pParam2);
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.GEQ, pParam1, pParam2);
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.LT, pParam1, pParam2);
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.LEQ, pParam1, pParam2);
  }

  @Override
  protected Term distinctImpl(List<Term> pParam) {
    return termManager.mkTerm(Kind.DISTINCT, pParam.toArray(new Term[0]));
  }
}
