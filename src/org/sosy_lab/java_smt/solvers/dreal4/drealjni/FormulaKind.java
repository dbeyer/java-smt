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

public final class FormulaKind {
  public static final FormulaKind FALSE = new FormulaKind("False");
  public static final FormulaKind TRUE = new FormulaKind("True");
  public static final FormulaKind VAR = new FormulaKind("Var");
  public static final FormulaKind EQ = new FormulaKind("Eq");
  public static final FormulaKind NEQ = new FormulaKind("Neq");
  public static final FormulaKind GT = new FormulaKind("Gt");
  public static final FormulaKind GEQ = new FormulaKind("Geq");
  public static final FormulaKind LT = new FormulaKind("Lt");
  public static final FormulaKind LEQ = new FormulaKind("Leq");
  public static final FormulaKind AND = new FormulaKind("And");
  public static final FormulaKind OR = new FormulaKind("Or");
  public static final FormulaKind NOT = new FormulaKind("Not");
  public static final FormulaKind FORALL = new FormulaKind("Forall");

  public final int swigValue() {
    return swigValue;
  }

  @Override
  public String toString() {
    return swigName;
  }

  public static FormulaKind swigToEnum(int swigValue) {
    if (swigValue < swigValues.length
        && swigValue >= 0
        && swigValues[swigValue].swigValue == swigValue) {
      return swigValues[swigValue];
    }
    for (int i = 0; i < swigValues.length; i++) {
      {
        if (swigValues[i].swigValue == swigValue) {
          return swigValues[i];
        }
      }
    }
    throw new IllegalArgumentException("No enum " + FormulaKind.class + " with value " + swigValue);
  }

  private FormulaKind(String swigName) {
    this.swigName = swigName;
    this.swigValue = swigNext++;
  }

  @SuppressWarnings({"unused", "StaticAssignmentInConstructor"})
  private FormulaKind(String swigName, int swigValue) {
    this.swigName = swigName;
    this.swigValue = swigValue;
    swigNext = swigValue + 1;
  }

  @SuppressWarnings({"unused", "StaticAssignmentInConstructor"})
  private FormulaKind(String swigName, FormulaKind swigEnum) {
    this.swigName = swigName;
    this.swigValue = swigEnum.swigValue;
    swigNext = this.swigValue + 1;
  }

  private static FormulaKind[] swigValues = {
    FALSE, TRUE, VAR, EQ, NEQ, GT, GEQ, LT, LEQ, AND, OR, NOT, FORALL
  };
  private static int swigNext = 0;
  private final int swigValue;
  private final String swigName;
}
