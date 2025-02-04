// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;

/**
 * Similar to the other Abstract*FormulaManager classes in this package, this class serves as a
 * helper for implementing {@link NumeralFormulaManager}. It handles all the unwrapping and wrapping
 * from {@link Formula} instances to solver-specific formula representations, such that the concrete
 * class needs to handle only its own internal types.
 *
 * @implSpec The method {@link #getFormulaType()} must be safe to be called from the constructor
 *     (the default implementations of {@link org.sosy_lab.java_smt.api.IntegerFormulaManager} and
 *     {@link org.sosy_lab.java_smt.api.RationalFormulaManager} satisfy this).
 */
@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractNumeralFormulaManager<
        TFormulaInfo,
        TType,
        TEnv,
        ParamFormulaType extends NumeralFormula,
        ResultFormulaType extends NumeralFormula,
        TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements NumeralFormulaManager<ParamFormulaType, ResultFormulaType> {

  public enum NonLinearArithmetic {
    USE,
    APPROXIMATE_FALLBACK,
    APPROXIMATE_ALWAYS,
  }

  private final NonLinearArithmetic nonLinearArithmetic;

  private final TFuncDecl multUfDecl;
  private final TFuncDecl divUfDecl;
  private final TFuncDecl modUfDecl;

  protected AbstractNumeralFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator);
    nonLinearArithmetic = checkNotNull(pNonLinearArithmetic);

    multUfDecl = createBinaryFunction("*");
    divUfDecl = createBinaryFunction("/");
    modUfDecl = createBinaryFunction("%");
  }

  private TFuncDecl createBinaryFunction(String name) {
    TType formulaType = toSolverType(getFormulaType());
    return formulaCreator.declareUFImpl(
        getFormulaType() + "_" + name + "_",
        formulaType,
        ImmutableList.of(formulaType, formulaType));
  }

  private TFormulaInfo makeUf(TFuncDecl decl, TFormulaInfo t1, TFormulaInfo t2) {
    return formulaCreator.callFunctionImpl(decl, ImmutableList.of(t1, t2));
  }

  protected ResultFormulaType wrap(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulate(getFormulaType(), pTerm);
  }

  /** Check whether the argument is a numeric constant (including negated constants). */
  protected abstract boolean isNumeral(TFormulaInfo val);

  @Override
  public ResultFormulaType makeNumber(long i) {
    return wrap(makeNumberImpl(i));
  }

  protected abstract TFormulaInfo makeNumberImpl(long i);

  @Override
  public ResultFormulaType makeNumber(BigInteger i) {
    return wrap(makeNumberImpl(i));
  }

  protected abstract TFormulaInfo makeNumberImpl(BigInteger i);

  @Override
  public ResultFormulaType makeNumber(String i) {
    return wrap(makeNumberImpl(i));
  }

  protected abstract TFormulaInfo makeNumberImpl(String i);

  @Override
  public ResultFormulaType makeNumber(Rational pRational) {
    return wrap(makeNumberImpl(pRational));
  }

  protected TFormulaInfo makeNumberImpl(Rational pRational) {
    return makeNumberImpl(pRational.toString());
  }

  @Override
  public ResultFormulaType makeNumber(double pNumber) {
    return wrap(makeNumberImpl(pNumber));
  }

  protected abstract TFormulaInfo makeNumberImpl(double pNumber);

  @Override
  public ResultFormulaType makeNumber(BigDecimal pNumber) {
    return wrap(makeNumberImpl(pNumber));
  }

  protected abstract TFormulaInfo makeNumberImpl(BigDecimal pNumber);

  /**
   * This method tries to represent a BigDecimal using only BigInteger. It can be used for
   * implementing {@link #makeNumber(BigDecimal)} when the current theory supports only integers and
   * division by constants.
   */
  protected final TFormulaInfo decimalAsInteger(BigDecimal val) {
    if (val.scale() <= 0) {
      // actually an integral number
      return makeNumberImpl(convertBigDecimalToBigInteger(val));

    } else {
      // represent x.y by xy / (10^z) where z is the number of digits in y
      // (the "scale" of a BigDecimal)

      BigDecimal n = val.movePointRight(val.scale()); // this is "xy"
      BigInteger numerator = convertBigDecimalToBigInteger(n);

      BigDecimal d = BigDecimal.ONE.scaleByPowerOfTen(val.scale()); // this is "10^z"
      BigInteger denominator = convertBigDecimalToBigInteger(d);
      assert denominator.signum() > 0;

      return divide(makeNumberImpl(numerator), makeNumberImpl(denominator));
    }
  }

  private static BigInteger convertBigDecimalToBigInteger(BigDecimal d)
      throws NumberFormatException {
    try {
      return d.toBigIntegerExact();
    } catch (ArithmeticException e) {
      NumberFormatException nfe =
          new NumberFormatException("Cannot represent BigDecimal " + d + " as BigInteger");
      nfe.initCause(e);
      throw nfe;
    }
  }

  @Override
  public ResultFormulaType makeVariable(String pVar) {
    return wrap(makeVariableImpl(FormulaCreator.escapeName(pVar)));
  }

  protected abstract TFormulaInfo makeVariableImpl(String i);

  @Override
  public ResultFormulaType negate(ParamFormulaType pNumber) {
    TFormulaInfo param1 = extractInfo(pNumber);
    return wrap(negate(param1));
  }

  protected abstract TFormulaInfo negate(TFormulaInfo pParam1);

  @Override
  public ResultFormulaType add(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(add(param1, param2));
  }

  protected abstract TFormulaInfo add(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public ResultFormulaType sum(List<ParamFormulaType> operands) {
    return wrap(sumImpl(Lists.transform(operands, this::extractInfo)));
  }

  protected TFormulaInfo sumImpl(List<TFormulaInfo> operands) {
    TFormulaInfo result = makeNumberImpl(0);
    for (TFormulaInfo operand : operands) {
      result = add(result, operand);
    }
    return result;
  }

  @Override
  public ResultFormulaType subtract(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(subtract(param1, param2));
  }

  protected abstract TFormulaInfo subtract(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public ResultFormulaType divide(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    TFormulaInfo result;
    // division is always non-linear for ints, and for rationals if param2 is not a constant:
    // http://smtlib.cs.uiowa.edu/logics-all.shtml#LIA
    // http://smtlib.cs.uiowa.edu/logics-all.shtml#LRA
    if (nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_ALWAYS
        && (getFormulaType().equals(FormulaType.IntegerType) || !isNumeral(param2))) {
      result = makeUf(divUfDecl, param1, param2);
    } else {
      try {
        result = divide(param1, param2);
      } catch (UnsupportedOperationException e) {
        if (nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_FALLBACK) {
          result = makeUf(divUfDecl, param1, param2);
        } else {
          assert nonLinearArithmetic == NonLinearArithmetic.USE;
          throw e;
        }
      }
    }
    return wrap(result);
  }

  /**
   * If a solver does not support this operation, e.g. because of missing support for non-linear
   * arithmetics, we throw UnsupportedOperationException.
   *
   * @param pParam1 the dividend
   * @param pParam2 the divisor
   */
  protected TFormulaInfo divide(TFormulaInfo pParam1, TFormulaInfo pParam2) {
    throw new UnsupportedOperationException();
  }

  public ResultFormulaType modulo(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    TFormulaInfo result;
    if (nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_ALWAYS) {
      result = makeUf(modUfDecl, param1, param2);
    } else {
      try {
        result = modulo(param1, param2);
      } catch (UnsupportedOperationException e) {
        if (nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_FALLBACK) {
          result = makeUf(modUfDecl, param1, param2);
        } else {
          assert nonLinearArithmetic == NonLinearArithmetic.USE;
          throw e;
        }
      }
    }
    return wrap(result);
  }

  /**
   * If a solver does not support this operation, e.g. because of missing support for non-linear
   * arithmetics, we throw UnsupportedOperationException.
   *
   * @param pParam1 the dividend
   * @param pParam2 the divisor
   */
  protected TFormulaInfo modulo(TFormulaInfo pParam1, TFormulaInfo pParam2) {
    throw new UnsupportedOperationException();
  }

  public BooleanFormula modularCongruence(
      ParamFormulaType pNumber1, ParamFormulaType pNumber2, long pModulo) {
    Preconditions.checkArgument(pModulo > 0, "modular congruence needs a positive modulo.");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(modularCongruence(param1, param2, pModulo));
  }

  public BooleanFormula modularCongruence(
      ParamFormulaType pNumber1, ParamFormulaType pNumber2, BigInteger pModulo) {
    Preconditions.checkArgument(
        pModulo.signum() > 0, "modular congruence needs a positive modulo.");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(modularCongruence(param1, param2, pModulo));
  }

  /**
   * @param a first operand
   * @param b second operand
   * @param m the modulus
   * @return the formula representing {@code a = b (mod m)}
   */
  protected TFormulaInfo modularCongruence(TFormulaInfo a, TFormulaInfo b, BigInteger m) {
    throw new UnsupportedOperationException();
  }

  /**
   * @param a first operand
   * @param b second operand
   * @param m the modulus
   * @return the formula representing {@code a = b (mod m)}
   */
  protected TFormulaInfo modularCongruence(TFormulaInfo a, TFormulaInfo b, long m) {
    throw new UnsupportedOperationException();
  }

  @Override
  public ResultFormulaType multiply(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);
    TFormulaInfo result;
    if (nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_ALWAYS
        && !isNumeral(param1)
        && !isNumeral(param2)) {
      result = makeUf(multUfDecl, param1, param2);
    } else {
      try {
        result = multiply(param1, param2);
      } catch (UnsupportedOperationException e) {
        if (nonLinearArithmetic == NonLinearArithmetic.APPROXIMATE_FALLBACK) {
          result = makeUf(multUfDecl, param1, param2);
        } else {
          assert nonLinearArithmetic == NonLinearArithmetic.USE
              : "unexpected handling of nonlinear arithmetics: " + nonLinearArithmetic;
          throw e;
        }
      }
    }
    return wrap(result);
  }

  /**
   * If a solver does not support this operation, e.g. because of missing support for non-linear
   * arithmetics, we throw UnsupportedOperationException.
   *
   * @param pParam1 first factor
   * @param pParam2 second factor
   */
  protected TFormulaInfo multiply(TFormulaInfo pParam1, TFormulaInfo pParam2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula equal(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(equal(param1, param2));
  }

  protected abstract TFormulaInfo equal(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula distinct(List<ParamFormulaType> pNumbers) {
    return wrapBool(distinctImpl(Lists.transform(pNumbers, this::extractInfo)));
  }

  protected abstract TFormulaInfo distinctImpl(List<TFormulaInfo> pNumbers);

  @Override
  public BooleanFormula greaterThan(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterThan(param1, param2));
  }

  protected abstract TFormulaInfo greaterThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterOrEquals(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterOrEquals(param1, param2));
  }

  protected abstract TFormulaInfo greaterOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessThan(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessThan(param1, param2));
  }

  protected abstract TFormulaInfo lessThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessOrEquals(ParamFormulaType pNumber1, ParamFormulaType pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessOrEquals(param1, param2));
  }

  protected abstract TFormulaInfo lessOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public IntegerFormula floor(ParamFormulaType number) {
    if (getFormulaCreator().getFormulaType(number) == FormulaType.IntegerType) {
      return (IntegerFormula) number;
    } else {
      return getFormulaCreator().encapsulate(FormulaType.IntegerType, floor(extractInfo(number)));
    }
  }

  protected TFormulaInfo floor(TFormulaInfo number) {
    // identity function for integers, method is overridden for rationals
    throw new AssertionError(
        "method should only be called for RationalFormulae, but type is "
            + getFormulaCreator().getFormulaType(number));
  }
}
