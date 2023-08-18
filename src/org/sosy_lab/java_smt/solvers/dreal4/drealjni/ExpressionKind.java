// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (https://www.swig.org).
 * Version 4.1.1
 *
 * Do not make changes to this file unless you know what you are doing - modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */
package org.sosy_lab.java_smt.solvers.dreal4.drealjni;

public final class ExpressionKind {
  public static final ExpressionKind CONSTANT = new ExpressionKind("Constant");
  public static final ExpressionKind REAL_CONSTANT = new ExpressionKind("RealConstant");
  public static final ExpressionKind VAR = new ExpressionKind("Var");
  public static final ExpressionKind ADD = new ExpressionKind("Add");
  public static final ExpressionKind MUL = new ExpressionKind("Mul");
  public static final ExpressionKind DIV = new ExpressionKind("Div");
  public static final ExpressionKind LOG = new ExpressionKind("Log");
  public static final ExpressionKind ABS = new ExpressionKind("Abs");
  public static final ExpressionKind EXP = new ExpressionKind("Exp");
  public static final ExpressionKind SQRT = new ExpressionKind("Sqrt");
  public static final ExpressionKind POW = new ExpressionKind("Pow");
  public static final ExpressionKind SIN = new ExpressionKind("Sin");
  public static final ExpressionKind COS = new ExpressionKind("Cos");
  public static final ExpressionKind TAN = new ExpressionKind("Tan");
  public static final ExpressionKind ASIN = new ExpressionKind("Asin");
  public static final ExpressionKind ACOS = new ExpressionKind("Acos");
  public static final ExpressionKind ATAN = new ExpressionKind("Atan");
  public static final ExpressionKind ATAN2 = new ExpressionKind("Atan2");
  public static final ExpressionKind SINH = new ExpressionKind("Sinh");
  public static final ExpressionKind COSH = new ExpressionKind("Cosh");
  public static final ExpressionKind TANH = new ExpressionKind("Tanh");
  public static final ExpressionKind MIN = new ExpressionKind("Min");
  public static final ExpressionKind MAX = new ExpressionKind("Max");
  public static final ExpressionKind ITE = new ExpressionKind("IfThenElse");
  public static final ExpressionKind NAN = new ExpressionKind("NaN");
  public static final ExpressionKind UF =
      new ExpressionKind("UninterpretedFunction");

  public int swigValue() {
    return swigValue;
  }

  @Override
  public String toString() {
    return swigName;
  }

  public static ExpressionKind swigToEnum(int swigValue) {
    if (swigValue < swigValues.length
        && swigValue >= 0
        && swigValues[swigValue].swigValue == swigValue) {
      return swigValues[swigValue];
    }
    for (int i = 0; i < swigValues.length; i++) {
      if (swigValues[i].swigValue == swigValue) {
        return swigValues[i];
      }
    }
    throw new IllegalArgumentException(
        "No enum " + ExpressionKind.class + " with value " + swigValue);
  }

  private ExpressionKind(String swigName) {
    this.swigName = swigName;
    this.swigValue = swigNext++;
  }

  @SuppressWarnings({"unused", "StaticAssignmentInConstructor"})
  private ExpressionKind(String swigName, int swigValue) {
    this.swigName = swigName;
    this.swigValue = swigValue;
    swigNext = swigValue + 1;
  }

  @SuppressWarnings({"unused", "StaticAssignmentInConstructor"})
  private ExpressionKind(String swigName, ExpressionKind swigEnum) {
    this.swigName = swigName;
    this.swigValue = swigEnum.swigValue;
    swigNext = this.swigValue + 1;
  }

  private static ExpressionKind[] swigValues = {
    CONSTANT,
    REAL_CONSTANT,
    VAR,
    ADD,
    MUL,
    DIV,
    LOG,
    ABS,
    EXP,
    SQRT,
    POW,
    SIN,
    COS,
    TAN,
    ASIN,
    ACOS,
    ATAN,
    ATAN2,
    SINH,
    COSH,
    TANH,
    MIN,
    MAX,
    ITE,
    NAN,
    UF
  };
  private static int swigNext = 0;
  private final int swigValue;
  private final String swigName;
}
