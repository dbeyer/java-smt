// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static org.sosy_lab.java_smt.basicimpl.FormulaCreator.escapeName;

import com.google.common.base.Preconditions;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointNumber.Sign;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

/**
 * Similar to the other Abstract*FormulaManager classes in this package, this class serves as a
 * helper for implementing {@link FloatingPointFormulaManager}. It handles all the unwrapping and
 * wrapping from and to the {@link Formula} instances, such that the concrete class needs to handle
 * only its own internal types.
 *
 * <p>For {@link #multiply(FloatingPointFormula, FloatingPointFormula)}, and {@link
 * #divide(FloatingPointFormula, FloatingPointFormula)} this class even offers an implementation
 * based on UFs. Sub-classes are supposed to override them if they can implement these operations
 * more precisely (for example multiplication with constants should be supported by all solvers and
 * implemented by all sub-classes).
 */
@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements FloatingPointFormulaManager {

  private final Map<FloatingPointRoundingMode, TFormulaInfo> roundingModes;

  protected AbstractFloatingPointFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator) {
    super(pCreator);
    roundingModes = new HashMap<>();
  }

  protected abstract TFormulaInfo getDefaultRoundingMode();

  protected abstract TFormulaInfo getRoundingModeImpl(
      FloatingPointRoundingMode pFloatingPointRoundingMode);

  private TFormulaInfo getRoundingMode(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return roundingModes.computeIfAbsent(pFloatingPointRoundingMode, this::getRoundingModeImpl);
  }

  protected FloatingPointFormula wrap(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulateFloatingPoint(pTerm);
  }

  @Override
  public FloatingPointFormula makeNumber(Rational n, FormulaType.FloatingPointType type) {
    return wrap(makeNumberImpl(n.toString(), type, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula makeNumber(
      Rational n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrap(makeNumberImpl(n.toString(), type, getRoundingMode(pFloatingPointRoundingMode)));
  }

  @Override
  public FloatingPointFormula makeNumber(double n, FormulaType.FloatingPointType type) {
    return wrap(makeNumberImpl(n, type, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula makeNumber(
      double n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrap(makeNumberImpl(n, type, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo makeNumberImpl(
      double n, FormulaType.FloatingPointType type, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula makeNumber(BigDecimal n, FormulaType.FloatingPointType type) {
    return wrap(makeNumberImpl(n, type, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigDecimal n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrap(makeNumberImpl(n, type, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected TFormulaInfo makeNumberImpl(
      BigDecimal n, FormulaType.FloatingPointType type, TFormulaInfo pFloatingPointRoundingMode) {
    return makeNumberImpl(n.toPlainString(), type, pFloatingPointRoundingMode);
  }

  @Override
  public FloatingPointFormula makeNumber(String n, FormulaType.FloatingPointType type) {
    return wrap(makeNumberImpl(n, type, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula makeNumber(
      String n, FloatingPointType type, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrap(makeNumberImpl(n, type, getRoundingMode(pFloatingPointRoundingMode)));
  }

  /** directly catch the most common special String constants. */
  protected TFormulaInfo makeNumberImpl(
      String n, FormulaType.FloatingPointType type, TFormulaInfo pFloatingPointRoundingMode) {
    if (n.startsWith("+")) {
      n = n.substring(1);
    }
    switch (n) {
      case "NaN":
      case "-NaN":
        return makeNaNImpl(type);
      case "Infinity":
        return makePlusInfinityImpl(type);
      case "-Infinity":
        return makeMinusInfinityImpl(type);
      default:
        return makeNumberAndRound(n, type, pFloatingPointRoundingMode);
    }
  }

  @Override
  public FloatingPointFormula makeNumber(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type) {
    return wrap(makeNumberImpl(exponent, mantissa, sign, type));
  }

  protected abstract TFormulaInfo makeNumberImpl(
      BigInteger exponent, BigInteger mantissa, Sign sign, FloatingPointType type);

  protected static boolean isNegativeZero(Double pN) {
    Preconditions.checkNotNull(pN);
    return Double.valueOf("-0.0").equals(pN);
  }

  /**
   * Parses the provided string and converts it into a floating-point formula.
   *
   * <p>The input string must represent a valid finite floating-point number. Values such as NaN,
   * Infinity, or -Infinity are not allowed and should be handled before calling this method.
   */
  protected abstract TFormulaInfo makeNumberAndRound(
      String pN, FloatingPointType pType, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula makeVariable(String pVar, FormulaType.FloatingPointType pType) {
    return wrap(makeVariableImpl(escapeName(pVar), pType));
  }

  protected abstract TFormulaInfo makeVariableImpl(
      String pVar, FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makePlusInfinity(FormulaType.FloatingPointType pType) {
    return wrap(makePlusInfinityImpl(pType));
  }

  protected abstract TFormulaInfo makePlusInfinityImpl(FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makeMinusInfinity(FormulaType.FloatingPointType pType) {
    return wrap(makeMinusInfinityImpl(pType));
  }

  protected abstract TFormulaInfo makeMinusInfinityImpl(FormulaType.FloatingPointType pType);

  @Override
  public FloatingPointFormula makeNaN(FormulaType.FloatingPointType pType) {
    return wrap(makeNaNImpl(pType));
  }

  protected abstract TFormulaInfo makeNaNImpl(FormulaType.FloatingPointType pType);

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula pNumber, boolean pSigned, FormulaType<T> pTargetType) {
    return getFormulaCreator()
        .encapsulate(
            pTargetType,
            castToImpl(extractInfo(pNumber), pSigned, pTargetType, getDefaultRoundingMode()));
  }

  @Override
  public <T extends Formula> T castTo(
      FloatingPointFormula number,
      boolean pSigned,
      FormulaType<T> targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return getFormulaCreator()
        .encapsulate(
            targetType,
            castToImpl(
                extractInfo(number),
                pSigned,
                targetType,
                getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo castToImpl(
      TFormulaInfo pNumber,
      boolean pSigned,
      FormulaType<?> pTargetType,
      TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula castFrom(
      Formula pNumber, boolean pSigned, FormulaType.FloatingPointType pTargetType) {
    return wrap(castFromImpl(extractInfo(pNumber), pSigned, pTargetType, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula castFrom(
      Formula number,
      boolean signed,
      FloatingPointType targetType,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrap(
        castFromImpl(
            extractInfo(number), signed, targetType, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo castFromImpl(
      TFormulaInfo pNumber,
      boolean pSigned,
      FormulaType.FloatingPointType pTargetType,
      TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula fromIeeeBitvector(
      BitvectorFormula pNumber, FloatingPointType pTargetType) {
    return wrap(fromIeeeBitvectorImpl(extractInfo(pNumber), pTargetType));
  }

  protected abstract TFormulaInfo fromIeeeBitvectorImpl(
      TFormulaInfo pNumber, FloatingPointType pTargetType);

  @Override
  public BitvectorFormula toIeeeBitvector(FloatingPointFormula pNumber) {
    return getFormulaCreator().encapsulateBitvector(toIeeeBitvectorImpl(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo toIeeeBitvectorImpl(TFormulaInfo pNumber);

  @Override
  public FloatingPointFormula negate(FloatingPointFormula pNumber) {
    TFormulaInfo param1 = extractInfo(pNumber);
    return wrap(negate(param1));
  }

  protected abstract TFormulaInfo negate(TFormulaInfo pParam1);

  @Override
  public FloatingPointFormula abs(FloatingPointFormula pNumber) {
    TFormulaInfo param1 = extractInfo(pNumber);
    return wrap(abs(param1));
  }

  protected abstract TFormulaInfo abs(TFormulaInfo pParam1);

  @Override
  public FloatingPointFormula max(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    return wrap(max(extractInfo(pNumber1), extractInfo(pNumber2)));
  }

  protected abstract TFormulaInfo max(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public FloatingPointFormula min(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    return wrap(min(extractInfo(pNumber1), extractInfo(pNumber2)));
  }

  protected abstract TFormulaInfo min(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public FloatingPointFormula sqrt(FloatingPointFormula pNumber) {
    return wrap(sqrt(extractInfo(pNumber), getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula sqrt(
      FloatingPointFormula number, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrap(sqrt(extractInfo(number), getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo sqrt(TFormulaInfo pNumber, TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula add(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(add(param1, param2, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula add(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    return wrap(
        add(
            extractInfo(number1),
            extractInfo(number2),
            getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo add(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pRoundingMode);

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(subtract(param1, param2, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula subtract(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    TFormulaInfo param1 = extractInfo(number1);
    TFormulaInfo param2 = extractInfo(number2);

    return wrap(subtract(param1, param2, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo subtract(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula divide(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(divide(param1, param2, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula divide(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    TFormulaInfo param1 = extractInfo(number1);
    TFormulaInfo param2 = extractInfo(number2);

    return wrap(divide(param1, param2, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo divide(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(multiply(param1, param2, getDefaultRoundingMode()));
  }

  @Override
  public FloatingPointFormula multiply(
      FloatingPointFormula number1,
      FloatingPointFormula number2,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {
    TFormulaInfo param1 = extractInfo(number1);
    TFormulaInfo param2 = extractInfo(number2);
    return wrap(multiply(param1, param2, getRoundingMode(pFloatingPointRoundingMode)));
  }

  protected abstract TFormulaInfo multiply(
      TFormulaInfo pParam1, TFormulaInfo pParam2, TFormulaInfo pFloatingPointRoundingMode);

  @Override
  public FloatingPointFormula remainder(
      FloatingPointFormula number1, FloatingPointFormula number2) {
    return wrap(remainder(extractInfo(number1), extractInfo(number2)));
  }

  protected abstract TFormulaInfo remainder(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula assignment(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(assignment(param1, param2));
  }

  protected abstract TFormulaInfo assignment(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula equalWithFPSemantics(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(equalWithFPSemantics(param1, param2));
  }

  protected abstract TFormulaInfo equalWithFPSemantics(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterThan(param1, param2));
  }

  protected abstract TFormulaInfo greaterThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterOrEquals(
      FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterOrEquals(param1, param2));
  }

  protected abstract TFormulaInfo greaterOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessThan(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessThan(param1, param2));
  }

  protected abstract TFormulaInfo lessThan(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula lessOrEquals(FloatingPointFormula pNumber1, FloatingPointFormula pNumber2) {
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessOrEquals(param1, param2));
  }

  protected abstract TFormulaInfo lessOrEquals(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula isNaN(FloatingPointFormula pNumber) {
    return wrapBool(isNaN(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isNaN(TFormulaInfo pParam);

  @Override
  public BooleanFormula isInfinity(FloatingPointFormula pNumber) {
    return wrapBool(isInfinity(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isInfinity(TFormulaInfo pParam);

  @Override
  public BooleanFormula isZero(FloatingPointFormula pNumber) {
    return wrapBool(isZero(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isZero(TFormulaInfo pParam);

  @Override
  public BooleanFormula isSubnormal(FloatingPointFormula pNumber) {
    return wrapBool(isSubnormal(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isSubnormal(TFormulaInfo pParam);

  @Override
  public BooleanFormula isNormal(FloatingPointFormula pNumber) {
    return wrapBool(isNormal(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isNormal(TFormulaInfo pParam);

  @Override
  public BooleanFormula isNegative(FloatingPointFormula pNumber) {
    return wrapBool(isNegative(extractInfo(pNumber)));
  }

  protected abstract TFormulaInfo isNegative(TFormulaInfo pParam);

  @Override
  public FloatingPointFormula round(
      FloatingPointFormula pFormula, FloatingPointRoundingMode pRoundingMode) {
    return wrap(round(extractInfo(pFormula), pRoundingMode));
  }

  protected abstract TFormulaInfo round(
      TFormulaInfo pFormula, FloatingPointRoundingMode pRoundingMode);

  protected static String getBvRepresentation(BigInteger integer, int size) {
    char[] values = new char[size];
    for (int i = 0; i < size; i++) {
      values[size - 1 - i] = integer.testBit(i) ? '1' : '0';
    }
    return String.copyValueOf(values);
  }
}
