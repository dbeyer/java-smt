// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class FloatingPointFormulaManagerTest
    extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  // numbers are small enough to be precise with single precision
  private static final int[] SINGLE_PREC_INTS = new int[] {0, 1, 2, 5, 10, 20, 50, 100, 200, 500};

  private static final int NUM_RANDOM_TESTS = 50;

  private FloatingPointType singlePrecType;
  private FloatingPointType doublePrecType;
  private FloatingPointFormula nan;
  private FloatingPointFormula posInf;
  private FloatingPointFormula negInf;
  private FloatingPointFormula zero;
  private FloatingPointFormula one;
  private FloatingPointFormula negZero;

  @Before
  public void init() {
    requireFloats();

    singlePrecType = FormulaType.getSinglePrecisionFloatingPointType();
    doublePrecType = FormulaType.getDoublePrecisionFloatingPointType();
    nan = fpmgr.makeNaN(singlePrecType);
    posInf = fpmgr.makePlusInfinity(singlePrecType);
    negInf = fpmgr.makeMinusInfinity(singlePrecType);
    zero = fpmgr.makeNumber(0.0, singlePrecType);
    negZero = fpmgr.makeNumber(-0.0, singlePrecType);
    one = fpmgr.makeNumber(1.0, singlePrecType);
  }

  @Test
  public void floatingPointType() {
    FloatingPointType type = FormulaType.getFloatingPointType(23, 42);
    FloatingPointFormula var = fpmgr.makeVariable("x", type);
    FloatingPointType result = (FloatingPointType) mgr.getFormulaType(var);

    assertWithMessage("exponent size")
        .that(result.getExponentSize())
        .isEqualTo(type.getExponentSize());
    assertWithMessage("mantissa size")
        .that(result.getMantissaSize())
        .isEqualTo(type.getMantissaSize());
  }

  @Test
  public void negative() throws SolverException, InterruptedException {
    for (double d : new double[] {-1, -2, -0.0, Double.NEGATIVE_INFINITY}) {
      FloatingPointFormula formula = fpmgr.makeNumber(d, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isTautological();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isUnsatisfiable();
      assertEqualsAsFp(fpmgr.negate(formula), fpmgr.abs(formula));
    }
    for (double d : new double[] {1, 2, 0.0, Double.POSITIVE_INFINITY}) {
      FloatingPointFormula formula = fpmgr.makeNumber(d, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isUnsatisfiable();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isTautological();
      assertEqualsAsFp(formula, fpmgr.abs(formula));
    }
  }

  @Test
  public void parser() throws SolverException, InterruptedException {
    for (String s : new String[] {"-1", "-Infinity", "-0", "-0.0", "-0.000"}) {
      FloatingPointFormula formula = fpmgr.makeNumber(s, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isTautological();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isUnsatisfiable();
      assertEqualsAsFp(fpmgr.negate(formula), fpmgr.abs(formula));
    }
    for (String s : new String[] {"1", "Infinity", "0", "0.0", "0.000"}) {
      FloatingPointFormula formula = fpmgr.makeNumber(s, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isUnsatisfiable();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isTautological();
      assertEqualsAsFp(formula, fpmgr.abs(formula));
    }
    for (String s : new String[] {"+1", "+Infinity", "+0", "+0.0", "+0.000"}) {
      FloatingPointFormula formula = fpmgr.makeNumber(s, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isUnsatisfiable();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isTautological();
      assertEqualsAsFp(formula, fpmgr.abs(formula));
    }
    // NaN is not positive and not negative.
    for (String s : new String[] {"NaN", "-NaN", "+NaN"}) {
      FloatingPointFormula formula = fpmgr.makeNumber(s, singlePrecType);
      assertThatFormula(fpmgr.isNegative(formula)).isUnsatisfiable();
      assertThatFormula(fpmgr.isNegative(fpmgr.negate(formula))).isUnsatisfiable();
    }
  }

  @Test
  public void negativeZeroDivision() throws SolverException, InterruptedException {
    BooleanFormula formula =
        fpmgr.equalWithFPSemantics(
            fpmgr.divide(one, negZero, FloatingPointRoundingMode.TOWARD_ZERO),
            fpmgr.makeMinusInfinity(singlePrecType));
    assertThatFormula(formula).isSatisfiable();
    assertThatFormula(bmgr.not(formula)).isUnsatisfiable();
  }

  @Test
  public void nanEqualNanIsUnsat() throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.equalWithFPSemantics(nan, nan)).isUnsatisfiable();
  }

  @Test
  public void nanAssignedNanIsTrue() throws SolverException, InterruptedException {
    assertEqualsAsFormula(nan, nan);
  }

  @Test
  public void infinityOrdering() throws SolverException, InterruptedException {
    BooleanFormula order1 = fpmgr.greaterThan(posInf, zero);
    BooleanFormula order2 = fpmgr.greaterThan(zero, negInf);
    BooleanFormula order3 = fpmgr.greaterThan(posInf, negInf);

    assertThatFormula(bmgr.and(order1, order2, order3)).isTautological();

    assertEqualsAsFp(fpmgr.max(posInf, zero), posInf);
    assertEqualsAsFp(fpmgr.max(posInf, negInf), posInf);
    assertEqualsAsFp(fpmgr.max(negInf, zero), zero);
    assertEqualsAsFp(fpmgr.min(posInf, zero), zero);
    assertEqualsAsFp(fpmgr.min(posInf, negInf), negInf);
    assertEqualsAsFp(fpmgr.min(negInf, zero), negInf);
  }

  @Test
  public void infinityVariableOrdering() throws SolverException, InterruptedException {
    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    BooleanFormula varIsNan = fpmgr.isNaN(var);

    BooleanFormula order1 = fpmgr.greaterOrEquals(posInf, var);
    BooleanFormula order2 = fpmgr.lessOrEquals(negInf, var);

    assertThatFormula(bmgr.or(varIsNan, bmgr.and(order1, order2))).isTautological();
  }

  @Test
  public void sqrt() throws SolverException, InterruptedException {
    for (double d : new double[] {0.25, 1, 2, 4, 9, 15, 1234, 1000000}) {
      assertEqualsAsFp(
          fpmgr.sqrt(fpmgr.makeNumber(d * d, doublePrecType)), fpmgr.makeNumber(d, doublePrecType));
      assertEqualsAsFp(
          fpmgr.sqrt(fpmgr.makeNumber(d, doublePrecType)),
          fpmgr.makeNumber(Math.sqrt(d), doublePrecType));
      assertThatFormula(fpmgr.isNaN(fpmgr.sqrt(fpmgr.makeNumber(-d, doublePrecType))))
          .isTautological();
    }
  }

  @Test
  public void fpRemainderNormal() throws SolverException, InterruptedException {
    assume()
        .withMessage("MathSAT5 does not implement fp.rem")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    for (FloatingPointType prec :
        new FloatingPointType[] {
          singlePrecType, doublePrecType, FormulaType.getFloatingPointType(5, 6),
        }) {

      final FloatingPointFormula numFive = fpmgr.makeNumber(5, prec);
      final FloatingPointFormula numFour = fpmgr.makeNumber(4, prec);
      final FloatingPointFormula numSix = fpmgr.makeNumber(6, prec);

      final FloatingPointFormula numOne = fpmgr.makeNumber(1, prec);
      final FloatingPointFormula numMinusOne = fpmgr.makeNumber(-1, prec);

      assertEqualsAsFormula(fpmgr.remainder(numFive, numFour), numOne);
      assertEqualsAsFormula(fpmgr.remainder(numFive, numSix), numMinusOne);
    }
  }

  @Test
  public void fpRemainderSpecial() throws SolverException, InterruptedException {
    assume()
        .withMessage("MathSAT5 does not implement fp.rem")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    for (FloatingPointType prec :
        new FloatingPointType[] {
          singlePrecType, doublePrecType, FormulaType.getFloatingPointType(5, 6),
        }) {

      final FloatingPointFormula num = fpmgr.makeNumber(42, prec);

      final FloatingPointFormula fpNan = fpmgr.makeNumber("NaN", prec);
      final FloatingPointFormula fpZero = fpmgr.makeNumber("0", prec);
      final FloatingPointFormula fpInf = fpmgr.makePlusInfinity(prec);

      final FloatingPointFormula minusNan = fpmgr.makeNumber("-NaN", prec);
      final FloatingPointFormula minusZero = fpmgr.makeNumber("0", prec);
      final FloatingPointFormula minusInf = fpmgr.makeMinusInfinity(prec);

      assertEqualsAsFormula(fpmgr.remainder(fpNan, fpNan), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(fpZero, fpZero), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(fpInf, fpInf), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(minusNan, minusNan), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(minusZero, minusZero), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(minusInf, minusInf), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, fpNan), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, fpZero), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, fpInf), num);
      assertEqualsAsFormula(fpmgr.remainder(num, minusNan), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, minusZero), fpNan);
      assertEqualsAsFormula(fpmgr.remainder(num, minusInf), num);
    }
  }

  @Test
  public void specialValueFunctions() throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.isInfinity(posInf)).isTautological();
    assertThatFormula(fpmgr.isNormal(posInf)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(posInf)).isUnsatisfiable();

    assertThatFormula(fpmgr.isInfinity(negInf)).isTautological();
    assertThatFormula(fpmgr.isNormal(negInf)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(negInf)).isUnsatisfiable();

    assertThatFormula(fpmgr.isNaN(nan)).isTautological();
    assertThatFormula(fpmgr.isNormal(nan)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(nan)).isUnsatisfiable();

    assertThatFormula(fpmgr.isZero(zero)).isTautological();
    assertThatFormula(fpmgr.isSubnormal(zero)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(zero)).isUnsatisfiable();

    assertThatFormula(fpmgr.isZero(negZero)).isTautological();
    assertThatFormula(fpmgr.equalWithFPSemantics(zero, negZero)).isTautological();
    assertThatFormula(fpmgr.isSubnormal(negZero)).isUnsatisfiable();
    assertThatFormula(fpmgr.isSubnormal(negZero)).isUnsatisfiable();

    FloatingPointFormula minPosNormalValue = fpmgr.makeNumber(Float.MIN_NORMAL, singlePrecType);
    assertThatFormula(fpmgr.isSubnormal(minPosNormalValue)).isUnsatisfiable();
    assertThatFormula(fpmgr.isNormal(minPosNormalValue)).isSatisfiable();
    assertThatFormula(fpmgr.isZero(minPosNormalValue)).isUnsatisfiable();
  }

  @Test
  public void specialDoubles() throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.assignment(fpmgr.makeNumber(Double.NaN, singlePrecType), nan))
        .isTautological();
    assertThatFormula(
            fpmgr.assignment(fpmgr.makeNumber(Double.POSITIVE_INFINITY, singlePrecType), posInf))
        .isTautological();
    assertThatFormula(
            fpmgr.assignment(fpmgr.makeNumber(Double.NEGATIVE_INFINITY, singlePrecType), negInf))
        .isTautological();
  }

  private void checkEqualityOfNumberConstantsFor(double value, FloatingPointType type)
      throws SolverException, InterruptedException {
    FloatingPointFormula doubleNumber = fpmgr.makeNumber(value, type);
    FloatingPointFormula stringNumber = fpmgr.makeNumber(Double.toString(value), type);
    FloatingPointFormula bigDecimalNumber = fpmgr.makeNumber(BigDecimal.valueOf(value), type);
    FloatingPointFormula rationalNumber =
        fpmgr.makeNumber(Rational.ofBigDecimal(BigDecimal.valueOf(value)), type);

    BooleanFormula eq1 = fpmgr.equalWithFPSemantics(doubleNumber, stringNumber);
    BooleanFormula eq2 = fpmgr.equalWithFPSemantics(doubleNumber, bigDecimalNumber);

    BooleanFormula eq3 = fpmgr.equalWithFPSemantics(doubleNumber, rationalNumber);
    assertThatFormula(bmgr.and(eq1, eq2, eq3)).isTautological();
  }

  @Test
  @SuppressWarnings("FloatingPointLiteralPrecision")
  public void numberConstants() throws SolverException, InterruptedException {
    checkEqualityOfNumberConstantsFor(1.0, singlePrecType);
    checkEqualityOfNumberConstantsFor(-5.877471754111438E-39, singlePrecType);
    checkEqualityOfNumberConstantsFor(-5.877471754111438E-39, doublePrecType);
    checkEqualityOfNumberConstantsFor(3.4028234663852886e+38, singlePrecType);
    checkEqualityOfNumberConstantsFor(3.4028234663852886e+38, doublePrecType);

    // check unequality for large types
    FloatingPointType nearDouble = FormulaType.getFloatingPointType(12, 52);
    FloatingPointFormula h1 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(309).multiply(BigDecimal.valueOf(1.0001)), nearDouble);
    FloatingPointFormula h2 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(309).multiply(BigDecimal.valueOf(1.0002)), nearDouble);
    assertThatFormula(fpmgr.equalWithFPSemantics(h1, h2)).isUnsatisfiable();

    // check equality for short types
    FloatingPointType smallType = FormulaType.getFloatingPointType(4, 4);
    FloatingPointFormula i1 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(50).multiply(BigDecimal.valueOf(1.001)), smallType);
    FloatingPointFormula i2 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(50).multiply(BigDecimal.valueOf(1.002)), smallType);
    FloatingPointFormula inf = fpmgr.makePlusInfinity(smallType);
    assertEqualsAsFp(i1, i2);
    assertEqualsAsFp(i1, inf);
    assertEqualsAsFp(i2, inf);
    assertThatFormula(fpmgr.isInfinity(i1)).isTautological();
    assertThatFormula(fpmgr.isInfinity(i2)).isTautological();

    // and some negative numbers
    FloatingPointFormula ni1 =
        fpmgr.makeNumber(
            BigDecimal.TEN.pow(50).multiply(BigDecimal.valueOf(1.001)).negate(), smallType);
    FloatingPointFormula ni2 =
        fpmgr.makeNumber(
            BigDecimal.TEN.pow(50).multiply(BigDecimal.valueOf(1.002)).negate(), smallType);
    FloatingPointFormula ninf = fpmgr.makeMinusInfinity(smallType);
    assertEqualsAsFp(ni1, ni2);
    assertEqualsAsFp(ni1, ninf);
    assertEqualsAsFp(ni2, ninf);
    assertThatFormula(fpmgr.isInfinity(ni1)).isTautological();
    assertThatFormula(fpmgr.isInfinity(ni2)).isTautological();
    assertThatFormula(fpmgr.isNegative(ni1)).isTautological();
    assertThatFormula(fpmgr.isNegative(ni2)).isTautological();

    // check equality for short types
    FloatingPointType smallType2 = FormulaType.getFloatingPointType(4, 4);
    FloatingPointFormula j1 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(500).multiply(BigDecimal.valueOf(1.001)), smallType2);
    FloatingPointFormula j2 =
        fpmgr.makeNumber(BigDecimal.TEN.pow(500).multiply(BigDecimal.valueOf(1.002)), smallType2);
    FloatingPointFormula jnf = fpmgr.makePlusInfinity(smallType);
    assertEqualsAsFp(j1, j2);
    assertEqualsAsFp(j1, jnf);
    assertEqualsAsFp(j2, jnf);
    assertThatFormula(fpmgr.isInfinity(j1)).isTautological();
    assertThatFormula(fpmgr.isInfinity(j2)).isTautological();

    // and some negative numbers
    FloatingPointFormula nj1 =
        fpmgr.makeNumber(
            BigDecimal.TEN.pow(500).multiply(BigDecimal.valueOf(1.001)).negate(), smallType2);
    FloatingPointFormula nj2 =
        fpmgr.makeNumber(
            BigDecimal.TEN.pow(500).multiply(BigDecimal.valueOf(1.002)).negate(), smallType2);
    FloatingPointFormula njnf = fpmgr.makeMinusInfinity(smallType);
    assertEqualsAsFp(nj1, nj2);
    assertEqualsAsFp(nj1, njnf);
    assertEqualsAsFp(nj2, njnf);
    assertThatFormula(fpmgr.isInfinity(nj1)).isTautological();
    assertThatFormula(fpmgr.isInfinity(nj2)).isTautological();
    assertThatFormula(fpmgr.isNegative(nj1)).isTautological();
    assertThatFormula(fpmgr.isNegative(nj2)).isTautological();

    // Z3 supports at least FloatingPointType(15, 112). Larger types seem to be rounded.
    if (!ImmutableSet.of(Solvers.Z3, Solvers.CVC4).contains(solver)) {
      // check unequality for very large types
      FloatingPointType largeType = FormulaType.getFloatingPointType(100, 100);
      FloatingPointFormula k1 =
          fpmgr.makeNumber(BigDecimal.TEN.pow(200).multiply(BigDecimal.valueOf(1.001)), largeType);
      FloatingPointFormula k2 =
          fpmgr.makeNumber(BigDecimal.TEN.pow(200).multiply(BigDecimal.valueOf(1.002)), largeType);
      assertThatFormula(fpmgr.equalWithFPSemantics(k1, k2)).isUnsatisfiable();
    }
  }

  @Test
  public void numberConstantsNearInf() throws SolverException, InterruptedException {
    checkNearInf(4, 4, 252); // 2**(2**(4-1)) - max(0,2**(2**(4-1)-2-4))
    checkNearInf(5, 4, 254); // 2**(2**(4-1)) - max(0,2**(2**(4-1)-2-5))
    checkNearInf(6, 4, 255); // 2**(2**(4-1)) - max(0,2**(2**(4-1)-2-6))
    checkNearInf(7, 4, 256); // 2**(2**(4-1)) - max(0,?)
    checkNearInf(10, 4, 256); // 2**(2**(4-1)) - max(0,?)

    if (Solvers.CVC4 != solverToUse()) {
      // It seems as if CVC4/symfpu can not handle numbers with size of mantissa < exponent
      // TODO check this!
      checkNearInf(4, 5, 64512); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-4))
      checkNearInf(4, 6, 4227858432L); // 2**(2**(6-1)) - max(0,2**(2**(6-1)-2-4))
    }

    checkNearInf(5, 5, 65024); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-5))
    checkNearInf(6, 5, 65280); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-6))
    checkNearInf(7, 5, 65408); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-7))
    checkNearInf(10, 5, 65520); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-10))
    checkNearInf(14, 5, 65535); // 2**(2**(5-1)) - max(0,2**(2**(5-1)-2-14))
    checkNearInf(15, 5, 65536); // 2**(2**(5-1)) - max(0,?)

    checkNearInf(10, 6, 4293918720L); // 2**(2**(6-1)) - max(0,2**(2**(6-1)-2-10))
    checkNearInf(16, 6, 4294950912L); // 2**(2**(6-1)) - max(0,2**(2**(6-1)-2-16))
  }

  private void checkNearInf(int mantissa, int exponent, long value)
      throws SolverException, InterruptedException {
    FloatingPointType type = FormulaType.getFloatingPointType(exponent, mantissa);
    FloatingPointFormula fp1 = fpmgr.makeNumber(BigDecimal.valueOf(value), type);
    assertThatFormula(fpmgr.isInfinity(fp1)).isTautological();
    FloatingPointFormula fp2 = fpmgr.makeNumber(BigDecimal.valueOf(value - 1), type);
    assertThatFormula(fpmgr.isInfinity(fp2)).isUnsatisfiable();
  }

  @Test
  public void numberConstantsNearMinusInf() throws SolverException, InterruptedException {
    checkNearMinusInf(4, 4, -252);
    checkNearMinusInf(5, 4, -254);
    checkNearMinusInf(6, 4, -255);
    checkNearMinusInf(7, 4, -256);
    checkNearMinusInf(10, 4, -256);

    if (Solvers.CVC4 != solverToUse()) {
      // It seems as if CVC4/symfpu can not handle numbers with size of mantissa < exponent
      // TODO check this!
      checkNearMinusInf(4, 5, -64512);
      checkNearMinusInf(4, 6, -4227858432L);
    }

    checkNearMinusInf(5, 5, -65024);
    checkNearMinusInf(6, 5, -65280);
    checkNearMinusInf(7, 5, -65408);
    checkNearMinusInf(10, 5, -65520);
    checkNearMinusInf(14, 5, -65535);
    checkNearMinusInf(15, 5, -65536);

    checkNearMinusInf(10, 6, -4293918720L);
    checkNearMinusInf(16, 6, -4294950912L);
  }

  private void checkNearMinusInf(int mantissa, int exponent, long value)
      throws SolverException, InterruptedException {
    FloatingPointType type = FormulaType.getFloatingPointType(exponent, mantissa);
    FloatingPointFormula fp1 = fpmgr.makeNumber(BigDecimal.valueOf(value), type);
    assertThatFormula(fpmgr.isInfinity(fp1)).isTautological();
    FloatingPointFormula fp2 = fpmgr.makeNumber(BigDecimal.valueOf(value + 1), type);
    assertThatFormula(fpmgr.isInfinity(fp2)).isUnsatisfiable();
  }

  @Test
  @SuppressWarnings("FloatingPointLiteralPrecision")
  public void cast() throws SolverException, InterruptedException {
    FloatingPointFormula doublePrecNumber = fpmgr.makeNumber(1.5, doublePrecType);
    FloatingPointFormula singlePrecNumber = fpmgr.makeNumber(1.5, singlePrecType);

    FloatingPointFormula narrowedNumber = fpmgr.castTo(doublePrecNumber, true, singlePrecType);
    FloatingPointFormula widenedNumber = fpmgr.castTo(singlePrecNumber, true, doublePrecType);

    assertEqualsAsFp(narrowedNumber, singlePrecNumber);
    assertEqualsAsFp(widenedNumber, doublePrecNumber);

    FloatingPointFormula doublePrecSmallNumber =
        fpmgr.makeNumber(5.877471754111438E-39, doublePrecType);
    FloatingPointFormula singlePrecSmallNumber =
        fpmgr.makeNumber(5.877471754111438E-39, singlePrecType);
    FloatingPointFormula widenedSmallNumber =
        fpmgr.castTo(singlePrecSmallNumber, true, doublePrecType);
    assertEqualsAsFp(widenedSmallNumber, doublePrecSmallNumber);
  }

  @Test
  public void bvToFpSinglePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      bvToFp(i, singlePrecType);
    }
  }

  @Test
  public void bvToFpDoublePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      bvToFp(i, doublePrecType);
    }
  }

  private void bvToFp(int i, FloatingPointType prec) throws SolverException, InterruptedException {
    BitvectorFormula bv = bvmgr.makeBitvector(32, i);
    FloatingPointFormula fp = fpmgr.makeNumber(i, prec);

    FloatingPointFormula signedBvToFp = fpmgr.castFrom(bv, true, prec);
    FloatingPointFormula unsignedBvToFp = fpmgr.castFrom(bv, false, prec);

    assertEqualsAsFp(fp, signedBvToFp);
    assertEqualsAsFp(fp, unsignedBvToFp);
  }

  /** check whether rounded input is equal to result with rounding-mode. */
  private void round0(
      double value, double toZero, double pos, double neg, double tiesEven, double tiesAway)
      throws SolverException, InterruptedException {
    FloatingPointFormula f = fpmgr.makeNumber(value, singlePrecType);

    // check types
    assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.TOWARD_ZERO)))
        .isEqualTo(singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.TOWARD_POSITIVE)))
        .isEqualTo(singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.TOWARD_NEGATIVE)))
        .isEqualTo(singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN)))
        .isEqualTo(singlePrecType);
    if (solver != Solvers.MATHSAT5) { // Mathsat does not support NEAREST_TIES_AWAY
      assertThat(mgr.getFormulaType(fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_AWAY)))
          .isEqualTo(singlePrecType);
    }

    // check values
    assertEqualsAsFp(
        fpmgr.makeNumber(toZero, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_ZERO));

    assertEqualsAsFp(
        fpmgr.makeNumber(pos, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_POSITIVE));

    assertEqualsAsFp(
        fpmgr.makeNumber(neg, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.TOWARD_NEGATIVE));

    assertEqualsAsFp(
        fpmgr.makeNumber(tiesEven, singlePrecType),
        fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN));

    if (solver != Solvers.MATHSAT5) { // Mathsat does not support NEAREST_TIES_AWAY
      assertEqualsAsFp(
          fpmgr.makeNumber(tiesAway, singlePrecType),
          fpmgr.round(f, FloatingPointRoundingMode.NEAREST_TIES_AWAY));
    }
  }

  private void assertEqualsAsFp(FloatingPointFormula f1, FloatingPointFormula f2)
      throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.equalWithFPSemantics(f1, f2)).isTautological();
  }

  private void assertEqualsAsFormula(FloatingPointFormula f1, FloatingPointFormula f2)
      throws SolverException, InterruptedException {
    assertThatFormula(fpmgr.assignment(f1, f2)).isTautological();
  }

  @Test
  public void round() throws SolverException, InterruptedException {
    requireIntegers();

    // constants
    round0(0, 0, 0, 0, 0, 0);
    round0(1, 1, 1, 1, 1, 1);
    round0(-1, -1, -1, -1, -1, -1);

    // positive odd
    round0(1.1, 1, 2, 1, 1, 1);
    round0(1.5, 1, 2, 1, 2, 2);
    round0(1.9, 1, 2, 1, 2, 2);

    // positive even
    round0(10.1, 10, 11, 10, 10, 10);
    round0(10.5, 10, 11, 10, 10, 11);
    round0(10.9, 10, 11, 10, 11, 11);

    // negative odd
    round0(-1.1, -1, -1, -2, -1, -1);
    round0(-1.5, -1, -1, -2, -2, -2);
    round0(-1.9, -1, -1, -2, -2, -2);

    // negative even
    round0(-10.1, -10, -10, -11, -10, -10);
    round0(-10.5, -10, -10, -11, -10, -11);
    round0(-10.9, -10, -10, -11, -11, -11);
  }

  @Test
  public void bvToFpMinusOne() throws SolverException, InterruptedException {
    requireBitvectors();

    BitvectorFormula bvOne = bvmgr.makeBitvector(32, -1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    // A 32bit value "-1" when interpreted as unsigned is 2^31 - 1
    FloatingPointFormula fpMinInt = fpmgr.makeNumber(Math.pow(2, 32) - 1, singlePrecType);

    FloatingPointFormula unsignedBvToFpOne = fpmgr.castFrom(bvOne, false, singlePrecType);
    FloatingPointFormula signedBvToFpOne = fpmgr.castFrom(bvOne, true, singlePrecType);

    assertEqualsAsFp(fpOne, signedBvToFpOne);
    assertEqualsAsFp(fpMinInt, unsignedBvToFpOne);
  }

  @Test
  public void fpToBvSimpleNumbersSinglePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      fpToBv(i, singlePrecType);
    }
  }

  @Test
  public void fpToBvSimpleNegativeNumbersSinglePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      fpToBv(-i, singlePrecType);
    }
  }

  @Test
  public void fpToBvSimpleNumbersDoublePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      fpToBv(i, doublePrecType);
    }
  }

  @Test
  public void fpToBvSimpleNegativeNumbersDoublePrec() throws SolverException, InterruptedException {
    requireBitvectors();
    for (int i : SINGLE_PREC_INTS) {
      fpToBv(-i, doublePrecType);
    }
  }

  private void fpToBv(int i, FloatingPointType prec) throws SolverException, InterruptedException {
    BitvectorFormula bv = bvmgr.makeBitvector(prec.getTotalSize(), i);
    FloatingPointFormula fp = fpmgr.makeNumber(i, prec);

    BitvectorFormula fpToBv =
        fpmgr.castTo(fp, true, FormulaType.getBitvectorTypeWithSize(prec.getTotalSize()));
    assertThatFormula(bvmgr.equal(bv, fpToBv)).isTautological();
  }

  @Test
  public void rationalToFpOne() throws SolverException, InterruptedException {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(1.0, singlePrecType);

    FloatingPointFormula ratToFpOne = fpmgr.castFrom(ratOne, true, singlePrecType);
    FloatingPointFormula unsignedRatToFpOne = fpmgr.castFrom(ratOne, false, singlePrecType);
    assertThat(unsignedRatToFpOne).isEqualTo(ratToFpOne);

    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, ratToFpOne)).isSatisfiable();
  }

  @Test
  public void rationalToFpMinusOne() throws SolverException, InterruptedException {
    requireRationals();
    requireBitvectors();

    NumeralFormula ratOne = rmgr.makeNumber(-1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    FloatingPointFormula ratToFpOne = fpmgr.castFrom(ratOne, true, singlePrecType);
    FloatingPointFormula unsignedRatToFpOne = fpmgr.castFrom(ratOne, false, singlePrecType);
    assertThat(unsignedRatToFpOne).isEqualTo(ratToFpOne);

    assertThatFormula(fpmgr.equalWithFPSemantics(fpOne, ratToFpOne)).isSatisfiable();
  }

  @Test
  public void fpToRationalOne() throws SolverException, InterruptedException {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(1.0, singlePrecType);

    NumeralFormula fpToRatOne = fpmgr.castTo(fpOne, true, FormulaType.RationalType);

    assertThatFormula(rmgr.equal(ratOne, fpToRatOne)).isSatisfiable();
  }

  @Test
  public void fpToRationalMinusOne() throws SolverException, InterruptedException {
    requireRationals();

    NumeralFormula ratOne = rmgr.makeNumber(-1);
    FloatingPointFormula fpOne = fpmgr.makeNumber(-1.0, singlePrecType);

    NumeralFormula fpToRatOne = fpmgr.castTo(fpOne, true, FormulaType.RationalType);

    assertThatFormula(rmgr.equal(ratOne, fpToRatOne)).isSatisfiable();
  }

  @Test
  public void fpTraversal() {
    assertThat(mgr.extractVariables(zero)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(zero)).isEmpty();

    assertThat(mgr.extractVariables(one)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(one)).isEmpty();

    assertThat(mgr.extractVariables(posInf)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(posInf)).isEmpty();

    assertThat(mgr.extractVariables(nan)).isEmpty();
    assertThat(mgr.extractVariablesAndUFs(nan)).isEmpty();

    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    assertThat(mgr.extractVariables(var)).containsExactly("x", var);
    assertThat(mgr.extractVariablesAndUFs(var)).containsExactly("x", var);
  }

  @Test
  public void fpTraversalWithRoundingMode() {
    FloatingPointFormula two = fpmgr.makeNumber(2.0, singlePrecType);
    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    FloatingPointFormula mult = fpmgr.multiply(two, var);
    assertThat(mgr.extractVariables(mult)).containsExactly("x", var);
    assertThat(mgr.extractVariablesAndUFs(mult)).containsExactly("x", var);
  }

  @Test
  public void fpIeeeConversionTypes() {
    assume()
        .withMessage("FP-to-BV conversion not available for CVC4 and CVC5")
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5);

    FloatingPointFormula var = fpmgr.makeVariable("var", singlePrecType);
    assertThat(mgr.getFormulaType(fpmgr.toIeeeBitvector(var)))
        .isEqualTo(FormulaType.getBitvectorTypeWithSize(32));
  }

  @Test
  public void fpIeeeConversion() throws SolverException, InterruptedException {
    assume()
        .withMessage("FP-to-BV conversion not available for CVC4 and CVC5")
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5);

    FloatingPointFormula var = fpmgr.makeVariable("var", singlePrecType);
    assertThatFormula(
            fpmgr.assignment(
                var, fpmgr.fromIeeeBitvector(fpmgr.toIeeeBitvector(var), singlePrecType)))
        .isTautological();
  }

  @Test
  public void ieeeFpConversion() throws SolverException, InterruptedException {
    assume()
        .withMessage("FP-to-BV conversion not available for CVC4 and CVC5")
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5);

    BitvectorFormula var = bvmgr.makeBitvector(32, 123456789);
    assertThatFormula(
            bvmgr.equal(var, fpmgr.toIeeeBitvector(fpmgr.fromIeeeBitvector(var, singlePrecType))))
        .isTautological();
  }

  /**
   * Map the function over the input list and prove the returned assertions.
   *
   * @param args A list of arguments to the function
   * @param f A function that takes values from the list and returns assertions
   */
  private <T> void proveForAll(List<T> args, Function<T, BooleanFormula> f)
      throws InterruptedException, SolverException {
    try (ProverEnvironment prover = context.newProverEnvironment()) {
      for (T value : args) {
        prover.addConstraint(f.apply(value));
        assertThat(prover).isSatisfiable();
      }
    }
  }

  @Test
  public void checkIeeeBv2FpConversion32() throws SolverException, InterruptedException {
    proveForAll(
        // makeFP(value.float) == fromBV(makeBV(value.bits))
        getListOfFloats(),
        pFloat ->
            fpmgr.equalWithFPSemantics(
                fpmgr.makeNumber(pFloat, singlePrecType),
                fpmgr.fromIeeeBitvector(
                    bvmgr.makeBitvector(32, Float.floatToRawIntBits(pFloat)), singlePrecType)));
  }

  @Test
  public void checkIeeeBv2FpConversion64() throws SolverException, InterruptedException {
    proveForAll(
        // makeFP(value.float) == fromBV(makeBV(value.bits))
        getListOfDoubles(),
        pDouble ->
            fpmgr.equalWithFPSemantics(
                fpmgr.makeNumber(pDouble, doublePrecType),
                fpmgr.fromIeeeBitvector(
                    bvmgr.makeBitvector(64, Double.doubleToRawLongBits(pDouble)), doublePrecType)));
  }

  @Test
  public void checkIeeeFp2BvConversion32() throws SolverException, InterruptedException {
    assume()
        .withMessage("FP-to-BV conversion not available for CVC4 and CVC5")
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5);

    proveForAll(
        // makeBV(value.bits) == fromFP(makeFP(value.float))
        getListOfFloats(),
        pFloat ->
            bvmgr.equal(
                bvmgr.makeBitvector(32, Float.floatToRawIntBits(pFloat)),
                fpmgr.toIeeeBitvector(fpmgr.makeNumber(pFloat, singlePrecType))));
  }

  @Test
  public void checkIeeeFp2BvConversion64() throws SolverException, InterruptedException {
    assume()
        .withMessage("FP-to-BV conversion not available for CVC4 and CVC5")
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.CVC5);

    proveForAll(
        // makeBV(value.bits) == fromFP(makeFP(value.float))
        getListOfFloats(),
        pDouble ->
            bvmgr.equal(
                bvmgr.makeBitvector(64, Double.doubleToRawLongBits(pDouble)),
                fpmgr.toIeeeBitvector(fpmgr.makeNumber(pDouble, doublePrecType))));
  }

  private List<Float> getListOfFloats() {
    List<Float> flts =
        Lists.newArrayList(
            2.139922e-34f, // normal
            8.345803E-39f, // subnormal
            // Float.NaN, // NaN is no unique bitvector
            Float.MIN_NORMAL,
            Float.MIN_VALUE,
            Float.MAX_VALUE,
            Float.POSITIVE_INFINITY,
            Float.NEGATIVE_INFINITY,
            0.0f,
            1f,
            -1f,
            2f,
            -2f);

    if (solverToUse() != Solvers.MATHSAT5) {
      flts.add(-0.0f); // MathSat5 fails for NEGATIVE_ZERO
    }

    for (int i = 1; i < 10; i++) {
      for (int j = 1; j < 10; j++) {
        flts.add((float) (i * Math.pow(10, j)));
        flts.add((float) (-i * Math.pow(10, j)));
      }
    }

    Random rand = new Random(0);
    for (int i = 0; i < NUM_RANDOM_TESTS; i++) {
      float flt = Float.intBitsToFloat(rand.nextInt());
      if (!Float.isNaN(flt)) {
        flts.add(flt);
      }
    }

    return flts;
  }

  private List<Double> getListOfDoubles() {
    List<Double> dbls =
        Lists.newArrayList(
            // Double.NaN, // NaN is no unique bitvector
            Double.MIN_NORMAL,
            Double.MIN_VALUE,
            Double.MAX_VALUE,
            Double.POSITIVE_INFINITY,
            Double.NEGATIVE_INFINITY,
            0.0,
            1d,
            -1d,
            2d,
            -2d);

    if (solverToUse() != Solvers.MATHSAT5) {
      dbls.add(-0.0); // MathSat5 fails for NEGATIVE_ZERO
    }

    for (int i = 1; i < 10; i++) {
      for (int j = 1; j < 10; j++) {
        dbls.add(i * Math.pow(10, j));
        dbls.add(-i * Math.pow(10, j));
      }
    }

    Random rand = new Random(0);
    for (int i = 0; i < NUM_RANDOM_TESTS; i++) {
      double d = Double.longBitsToDouble(rand.nextLong());
      if (!Double.isNaN(d)) {
        dbls.add(d);
      }
    }

    return dbls;
  }

  @Test
  public void fpModelContent() throws SolverException, InterruptedException {
    FloatingPointFormula zeroVar = fpmgr.makeVariable("zero", singlePrecType);
    BooleanFormula zeroEq = fpmgr.assignment(zeroVar, zero);

    FloatingPointFormula oneVar = fpmgr.makeVariable("one", singlePrecType);
    BooleanFormula oneEq = fpmgr.assignment(oneVar, one);

    FloatingPointFormula nanVar = fpmgr.makeVariable("nan", singlePrecType);
    BooleanFormula nanEq = fpmgr.assignment(nanVar, nan);

    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(zeroEq);
      prover.push(oneEq);
      prover.push(nanEq);

      assertThat(prover).isSatisfiable();

      try (Model model = prover.getModel()) {

        FloatingPointNumber oneValue = model.evaluate(oneVar);
        ValueAssignment oneAssignment =
            new ValueAssignment(oneVar, one, oneEq, "one", oneValue, ImmutableList.of());

        FloatingPointNumber zeroValue = model.evaluate(zeroVar);
        ValueAssignment zeroAssignment =
            new ValueAssignment(zeroVar, zero, zeroEq, "zero", zeroValue, ImmutableList.of());

        FloatingPointNumber nanValue = model.evaluate(nanVar);
        ValueAssignment nanAssignment =
            new ValueAssignment(nanVar, nan, nanEq, "nan", nanValue, ImmutableList.of());

        assertThat(model.asList()).containsExactly(zeroAssignment, oneAssignment, nanAssignment);
      }
    }
  }

  @Test
  public void fpModelValue() throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bmgr.makeTrue());

      assertThat(prover).isSatisfiable();

      try (Model model = prover.getModel()) {
        assertThat(model.asList()).isEmpty();

        for (float f :
            new float[] {
              0,
              1,
              2,
              3,
              4,
              256,
              1000,
              1024,
              -1,
              -2,
              -3,
              -4,
              -1000,
              -1024,
              Float.NEGATIVE_INFINITY,
              Float.POSITIVE_INFINITY,
              Float.MAX_VALUE,
              Float.MIN_VALUE,
              Float.MIN_NORMAL,
            }) {
          FloatingPointNumber fiveValue = model.evaluate(fpmgr.makeNumber(f, singlePrecType));
          assertThat(fiveValue.floatValue()).isEqualTo(f);
          assertThat(fiveValue.doubleValue()).isEqualTo((double) f);
        }
      }
    }
  }

  @Test
  @SuppressWarnings({"unchecked", "resource"})
  public void fpInterpolation() throws SolverException, InterruptedException {
    requireInterpolation();
    assume()
        .withMessage("MathSAT5 does not support floating-point interpolation")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    FloatingPointFormula var = fpmgr.makeVariable("x", singlePrecType);
    BooleanFormula f1 = fpmgr.equalWithFPSemantics(var, zero);
    BooleanFormula f2 = bmgr.not(fpmgr.isZero(var));
    try (InterpolatingProverEnvironment<Object> prover =
        (InterpolatingProverEnvironment<Object>) context.newProverEnvironmentWithInterpolation()) {
      Object itpGroup1 = prover.push(f1);
      prover.push(f2);

      assertThat(prover).isUnsatisfiable();

      BooleanFormula itp = prover.getInterpolant(ImmutableList.of(itpGroup1));
      assertThatFormula(f1).implies(itp);
      assertThatFormula(bmgr.and(itp, f2)).isUnsatisfiable();
    }
  }

  @Test
  public void failOnInvalidString() {
    assertThrows(Exception.class, () -> fpmgr.makeNumber("a", singlePrecType));
  }

  @Test
  public void fpFrom32BitPattern() throws SolverException, InterruptedException {
    proveForAll(
        getListOfFloats(),
        pFloat -> {
          // makeFP(value.bits.sign, value.bits.exponent, value.bits.mantissa) = makeFP(value.float)
          int bits = Float.floatToRawIntBits(pFloat);
          int exponent = (bits >>> 23) & 0xFF;
          int mantissa = bits & 0x7FFFFF;
          boolean sign = bits < 0; // equal to: (bits >>> 31) & 0x1
          final FloatingPointFormula fpFromBv =
              fpmgr.makeNumber(
                  BigInteger.valueOf(exponent), BigInteger.valueOf(mantissa), sign, singlePrecType);
          final FloatingPointFormula fp = fpmgr.makeNumber(pFloat, singlePrecType);
          return fpmgr.assignment(fpFromBv, fp);
        });
  }

  @Test
  public void fpFrom64BitPattern() throws SolverException, InterruptedException {
    proveForAll(
        // makeFP(value.bits.sign, value.bits.exponent, value.bits.mantissa) = makeFP(value.float)
        getListOfDoubles(),
        pDouble -> {
          long bits = Double.doubleToRawLongBits(pDouble);
          long exponent = (bits >>> 52) & 0x7FF;
          long mantissa = bits & 0xFFFFFFFFFFFFFL;
          boolean sign = bits < 0; // equal to: (doubleBits >>> 63) & 1;
          final FloatingPointFormula fpFromBv =
              fpmgr.makeNumber(
                  BigInteger.valueOf(exponent), BigInteger.valueOf(mantissa), sign, doublePrecType);
          final FloatingPointFormula fp = fpmgr.makeNumber(pDouble, doublePrecType);
          return fpmgr.assignment(fpFromBv, fp);
        });
  }

  @Test
  public void fpFromNumberIntoTooNarrowType() throws SolverException, InterruptedException {
    // near zero rounds to zero, if precision is too narrow
    for (double nearZero : new double[] {Double.MIN_VALUE, Float.MIN_VALUE / 2d}) {
      assertThatFormula(
              fpmgr.equalWithFPSemantics(zero, fpmgr.makeNumber(nearZero, singlePrecType)))
          .isTautological();
      assertThatFormula(
              fpmgr.equalWithFPSemantics(negZero, fpmgr.makeNumber(-nearZero, singlePrecType)))
          .isTautological();
    }

    // near infinity rounds to infinity, if precision is too narrow
    for (double nearInf : new double[] {Double.MAX_VALUE, Float.MAX_VALUE * 2d}) {
      assertThatFormula(
              fpmgr.equalWithFPSemantics(posInf, fpmgr.makeNumber(nearInf, singlePrecType)))
          .isTautological();
      assertThatFormula(
              fpmgr.equalWithFPSemantics(negInf, fpmgr.makeNumber(-nearInf, singlePrecType)))
          .isTautological();
    }
  }
}
