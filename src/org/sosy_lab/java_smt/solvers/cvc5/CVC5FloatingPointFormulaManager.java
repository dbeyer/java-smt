// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.collect.ImmutableList;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Op;
import io.github.cvc5.RoundingMode;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.basicimpl.AbstractFloatingPointFormulaManager;

public class CVC5FloatingPointFormulaManager
    extends AbstractFloatingPointFormulaManager<Term, Sort, TermManager, Term> {

  private final TermManager termManager;
  private final Solver solver;
  private final Term roundingMode;

  protected CVC5FloatingPointFormulaManager(
      CVC5FormulaCreator pCreator, FloatingPointRoundingMode pFloatingPointRoundingMode) {
    super(pCreator);
    termManager = pCreator.getEnv();
    solver = pCreator.getSolver();
    roundingMode = getRoundingModeImpl(pFloatingPointRoundingMode);
  }

  @Override
  protected Term getDefaultRoundingMode() {
    return roundingMode;
  }

  @Override
  protected Term getRoundingModeImpl(FloatingPointRoundingMode pFloatingPointRoundingMode) {
    switch (pFloatingPointRoundingMode) {
      case NEAREST_TIES_TO_EVEN:
        return termManager.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN);
      case NEAREST_TIES_AWAY:
        return termManager.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_AWAY);
      case TOWARD_POSITIVE:
        return termManager.mkRoundingMode(RoundingMode.ROUND_TOWARD_POSITIVE);
      case TOWARD_NEGATIVE:
        return termManager.mkRoundingMode(RoundingMode.ROUND_TOWARD_NEGATIVE);
      case TOWARD_ZERO:
        return termManager.mkRoundingMode(RoundingMode.ROUND_TOWARD_ZERO);
      default:
        throw new AssertionError(
            "Unexpected rounding mode encountered: " + pFloatingPointRoundingMode);
    }
  }

  @Override
  protected Term makeNumberImpl(double pN, FloatingPointType pType, Term pRoundingMode) {
    return makeNumberImpl(Double.toString(pN), pType, pRoundingMode);
  }

  @Override
  protected Term makeNumberImpl(
      BigInteger exponent, BigInteger mantissa, boolean signBit, FloatingPointType type) {
    try {
      final String signStr = signBit ? "1" : "0";
      final String exponentStr = getBvRepresentation(exponent, type.getExponentSize());
      final String mantissaStr = getBvRepresentation(mantissa, type.getMantissaSize());
      final String bitvecForm = signStr + exponentStr + mantissaStr;

      final Term bv =
          termManager.mkBitVector(
              type.getExponentSize() + type.getMantissaSize() + 1, bitvecForm, 2);
      return termManager.mkFloatingPoint(type.getExponentSize(), type.getMantissaSize() + 1, bv);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException("You tried creating a invalid bitvector", e);
    }
  }

  @Override
  protected Term makeNumberAndRound(String pN, FloatingPointType pType, Term pRoundingMode) {
    try {
      if (isNegativeZero(Double.valueOf(pN))) {
        return termManager.mkFloatingPointNegZero(
            pType.getExponentSize(), pType.getMantissaSize() + 1);
      }
    } catch (CVC5ApiException | NumberFormatException e) {
      // ignore and fallback to floating point from rational numbers
    }

    try {
      Rational rationalValue = toRational(pN);
      Op realToFp =
          termManager.mkOp(
              Kind.FLOATINGPOINT_TO_FP_FROM_REAL,
              pType.getExponentSize(),
              pType.getMantissaSize() + 1);
      Term term =
          termManager.mkTerm(realToFp, pRoundingMode, termManager.mkReal(rationalValue.toString()));
      // simplification removes the cast from real to fp and return a bit-precise fp-number.
      return solver.simplify(term);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid floating point with exponent size "
              + pType.getExponentSize()
              + ", mantissa size "
              + pType.getMantissaSize()
              + " and value "
              + pN
              + ".",
          e);
    }
  }

  /**
   * Try to convert a String numeral into a Rational.
   *
   * <p>If we do not check all invalid formatted numbers in our own code, CVC5 will fail hard and
   * immediately terminate the whole program.
   */
  private Rational toRational(String pN) throws NumberFormatException {
    try {
      // first try something like -123.567
      return Rational.ofBigDecimal(new BigDecimal(pN));

    } catch (NumberFormatException e1) {
      try {
        // then try something like -123/456
        return org.sosy_lab.common.rationals.Rational.ofString(pN);

      } catch (NumberFormatException e2) {
        // we cannot handle the number
        throw new NumberFormatException("invalid numeral: " + pN);
      }
    }
  }

  @Override
  protected Term makeVariableImpl(String varName, FloatingPointType pType) {
    return formulaCreator.makeVariable(formulaCreator.getFloatingPointType(pType), varName);
  }

  @Override
  protected Term makePlusInfinityImpl(FloatingPointType pType) {
    try {
      return termManager.mkFloatingPointPosInf(
          pType.getExponentSize(), pType.getMantissaSize() + 1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid positive floating point +infinity with exponent size "
              + pType.getExponentSize()
              + " and mantissa size "
              + pType.getMantissaSize()
              + ".",
          e);
    }
  }

  @Override
  protected Term makeMinusInfinityImpl(FloatingPointType pType) {
    try {
      return termManager.mkFloatingPointNegInf(
          pType.getExponentSize(), pType.getMantissaSize() + 1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid negative floating point -infinity with exponent size "
              + pType.getExponentSize()
              + " and mantissa size "
              + pType.getMantissaSize()
              + ".",
          e);
    }
  }

  @Override
  protected Term makeNaNImpl(FloatingPointType pType) {
    try {
      return termManager.mkFloatingPointNaN(pType.getExponentSize(), pType.getMantissaSize() + 1);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid NaN with exponent size "
              + pType.getExponentSize()
              + " and mantissa size "
              + pType.getMantissaSize()
              + ".",
          e);
    }
  }

  // FP -> other type
  @Override
  protected Term castToImpl(
      Term pNumber, boolean pSigned, FormulaType<?> pTargetType, Term pRoundingMode) {
    try {
      if (pTargetType.isFloatingPointType()) {
        Op fpToFp =
            termManager.mkOp(
                Kind.FLOATINGPOINT_TO_FP_FROM_FP,
                ((FloatingPointType) pTargetType).getExponentSize(),
                ((FloatingPointType) pTargetType).getMantissaSize() + 1);
        return termManager.mkTerm(fpToFp, pRoundingMode, pNumber);

      } else if (pTargetType.isBitvectorType()) {
        BitvectorType targetType = (BitvectorType) pTargetType;
        Kind kind = pSigned ? Kind.FLOATINGPOINT_TO_SBV : Kind.FLOATINGPOINT_TO_UBV;
        Op operation = termManager.mkOp(kind, targetType.getSize());
        return termManager.mkTerm(operation, pRoundingMode, pNumber);

      } else if (pTargetType.isRationalType()) {
        return termManager.mkTerm(Kind.FLOATINGPOINT_TO_REAL, pNumber);

      } else {
        return genericCast(pNumber, pTargetType);
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid cast from "
              + pNumber
              + " into a "
              + pTargetType
              + ". Check that the target type can hold the source type. (Note: for target FP types"
              + " 1 bit is missing in this debug message)",
          e);
    }
  }

  // other type -> FP
  @Override
  protected Term castFromImpl(
      Term pNumber, boolean pSigned, FloatingPointType pTargetType, Term pRoundingMode) {
    FormulaType<?> formulaType = getFormulaCreator().getFormulaType(pNumber);
    try {
      if (formulaType.isFloatingPointType()) {
        return castToImpl(pNumber, pSigned, pTargetType, pRoundingMode);

      } else if (formulaType.isRationalType()) {
        Op realToFp =
            termManager.mkOp(
                Kind.FLOATINGPOINT_TO_FP_FROM_REAL,
                pTargetType.getExponentSize(),
                pTargetType.getMantissaSize() + 1);

        return termManager.mkTerm(realToFp, pRoundingMode, pNumber);

      } else if (formulaType.isBitvectorType()) {
        if (pSigned) {
          Op realToSBv =
              termManager.mkOp(
                  Kind.FLOATINGPOINT_TO_FP_FROM_SBV,
                  pTargetType.getExponentSize(),
                  pTargetType.getMantissaSize() + 1);
          return termManager.mkTerm(realToSBv, pRoundingMode, pNumber);
        } else {
          Op realToUBv =
              termManager.mkOp(
                  Kind.FLOATINGPOINT_TO_FP_FROM_UBV,
                  pTargetType.getExponentSize(),
                  pTargetType.getMantissaSize() + 1);
          return termManager.mkTerm(realToUBv, pRoundingMode, pNumber);
        }

      } else {
        // Generic cast was removed in the 1.0.0 version
        return genericCast(pNumber, pTargetType);
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid cast from "
              + pNumber
              + " into a FloatingPoint with exponent size "
              + pTargetType.getExponentSize()
              + " and mantissa size "
              + pTargetType.getMantissaSize()
              + ".",
          e);
    }
  }

  private Term genericCast(Term pNumber, FormulaType<?> pTargetType) {
    Sort type = pNumber.getSort();

    FormulaType<?> argType = getFormulaCreator().getFormulaType(pNumber);
    Term castFuncDecl =
        getFormulaCreator()
            .declareUFImpl(
                "__cast_" + argType + "_to_" + pTargetType,
                toSolverType(pTargetType),
                ImmutableList.of(type));
    return termManager.mkTerm(Kind.APPLY_UF, castFuncDecl, pNumber);
  }

  @Override
  protected Term negate(Term pParam1) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_NEG, pParam1);
  }

  @Override
  protected Term abs(Term pParam1) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_ABS, pParam1);
  }

  @Override
  protected Term max(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_MAX, pParam1, pParam2);
  }

  @Override
  protected Term min(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_MIN, pParam1, pParam2);
  }

  @Override
  protected Term sqrt(Term pParam1, Term pRoundingMode) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_SQRT, pRoundingMode, pParam1);
  }

  @Override
  protected Term add(Term pParam1, Term pParam2, Term pRoundingMode) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_ADD, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Term subtract(Term pParam1, Term pParam2, Term pRoundingMode) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_SUB, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Term divide(Term pParam1, Term pParam2, Term pRoundingMode) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_DIV, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Term multiply(Term pParam1, Term pParam2, Term pRoundingMode) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_MULT, pRoundingMode, pParam1, pParam2);
  }

  @Override
  protected Term remainder(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_REM, pParam1, pParam2);
  }

  @Override
  protected Term assignment(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Term equalWithFPSemantics(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_EQ, pParam1, pParam2);
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_GT, pParam1, pParam2);
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_GEQ, pParam1, pParam2);
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_LT, pParam1, pParam2);
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_LEQ, pParam1, pParam2);
  }

  @Override
  protected Term isNaN(Term pParam1) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_IS_NAN, pParam1);
  }

  @Override
  protected Term isInfinity(Term pParam1) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_IS_INF, pParam1);
  }

  @Override
  protected Term isZero(Term pParam1) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_IS_ZERO, pParam1);
  }

  @Override
  protected Term isSubnormal(Term pParam1) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_IS_SUBNORMAL, pParam1);
  }

  @Override
  protected Term isNormal(Term pParam) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_IS_NORMAL, pParam);
  }

  @Override
  protected Term isNegative(Term pParam) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_IS_NEG, pParam);
  }

  @Override
  protected Term fromIeeeBitvectorImpl(Term bitvector, FloatingPointType pTargetType) {
    int mantissaSize = pTargetType.getMantissaSize();
    int exponentSize = pTargetType.getExponentSize();
    int size = pTargetType.getTotalSize();
    assert size == mantissaSize + exponentSize + 1;

    Op signExtract;
    Op exponentExtract;
    Op mantissaExtract;
    try {
      signExtract = termManager.mkOp(Kind.BITVECTOR_EXTRACT, size - 1, size - 1);
      exponentExtract = termManager.mkOp(Kind.BITVECTOR_EXTRACT, size - 2, mantissaSize);
      mantissaExtract = termManager.mkOp(Kind.BITVECTOR_EXTRACT, mantissaSize - 1, 0);
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "You tried creating a invalid bitvector extract in term " + bitvector + ".", e);
    }

    Term sign = termManager.mkTerm(signExtract, bitvector);
    Term exponent = termManager.mkTerm(exponentExtract, bitvector);
    Term mantissa = termManager.mkTerm(mantissaExtract, bitvector);

    return termManager.mkTerm(Kind.FLOATINGPOINT_FP, sign, exponent, mantissa);
  }

  @Override
  protected Term toIeeeBitvectorImpl(Term pNumber) {
    // TODO possible work-around: use a tmp-variable "TMP" and add an
    // additional constraint "pNumer == fromIeeeBitvectorImpl(TMP)" for it in all use-cases.
    // --> This has to be done on user-side, not in JavaSMT.
    throw new UnsupportedOperationException("FP to IEEE-BV is not supported");
  }

  @Override
  protected Term round(Term pFormula, FloatingPointRoundingMode pRoundingMode) {
    return termManager.mkTerm(Kind.FLOATINGPOINT_RTI, getRoundingModeImpl(pRoundingMode), pFormula);
  }
}
