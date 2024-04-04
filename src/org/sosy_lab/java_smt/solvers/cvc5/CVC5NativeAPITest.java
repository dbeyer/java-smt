// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.truth.Truth.assertThat;
import static org.junit.Assert.assertThrows;

import com.google.common.base.Preconditions;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Op;
import io.github.cvc5.Result;
import io.github.cvc5.RoundingMode;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;

/*
 * Please note that CVC5 does not have a native variable cache!
 * Each variable created is a new one with a new internal id, even if they are named the same.
 * As a result, checking equality on 2 formulas that are build with new variables
 *  that are named the same results in false!
 * Additionally, CVC5 only supports quantifier elimination for LIA and LRA.
 * However, it might run endlessly in some cases if you try quantifier elimination on array
 * theories!
 */
public class CVC5NativeAPITest {

  private static final String INVALID_GETVALUE_STRING_SAT =
      "Cannot get value unless after a SAT or UNKNOWN response.";

  private static final String INVALID_TERM_BOUND_VAR =
      "Cannot process term .* with free variables: .*";

  private static final String INVALID_MODEL_STRING =
      "Cannot get model unless after a SAT or UNKNOWN response.";

  @BeforeClass
  public static void loadCVC5() {
    try {
      CVC5SolverContext.loadLibrary(NativeLibraries::loadLibrary);
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("CVC5 is not available", e);
    }
  }

  private Term x;
  private Term array;
  private Term aAtxEq0;
  private Term aAtxEq1;

  private TermManager termManager;
  private Solver solver;

  @Before
  public void init() throws CVC5ApiException {
    termManager = new TermManager();
    solver = createEnvironment();
  }

  private Solver createEnvironment() throws CVC5ApiException {
    Solver newSolver = new Solver(termManager);
    newSolver.setLogic("ALL");

    // options
    newSolver.setOption("incremental", "true");
    newSolver.setOption("produce-models", "true");
    newSolver.setOption("finite-model-find", "true");
    newSolver.setOption("sets-ext", "true");
    newSolver.setOption("output-language", "smtlib2");
    newSolver.setOption("strings-exp", "true");

    return newSolver;
  }

  @After
  public void freeEnvironment() {
    solver.deletePointer();
    termManager.deletePointer();
  }

  /*
   * Check how to get types/values etc. from constants, variables etc. in CVC5.
   * You can get the values of constants via toString()
   * and the name of variables via toString().
   * One can use getOp() on a Term to get its operator.
   * This operator can be used to create the same Term again with the same arguments.
   * The Ids match.
   */
  @Test
  public void checkGetValueAndType() throws CVC5ApiException {
    // Constant values (NOT Kind,CONSTANT!)
    assertThat(termManager.mkBoolean(false).isBooleanValue()).isTrue();
    assertThat(termManager.mkInteger(0).isIntegerValue()).isTrue();
    assertThat(termManager.mkInteger(999).isIntegerValue()).isTrue();
    assertThat(termManager.mkInteger(-1).isIntegerValue()).isTrue();
    assertThat(termManager.mkInteger("0").isIntegerValue()).isTrue();
    assertThat(termManager.mkString("").isStringValue()).isTrue();
    // Note: toString on String values does not equal the value!!
    assertThat(termManager.mkString("").toString()).isNotEqualTo("");
    assertThat(termManager.mkString("").getStringValue()).isEqualTo("");
    // Variables (named const, because thats not confusing....)
    // Variables (Consts) return false if checked for value!
    assertThat(termManager.mkConst(termManager.getBooleanSort()).isBooleanValue()).isFalse();
    assertThat(termManager.mkConst(termManager.getIntegerSort()).isIntegerValue()).isFalse();
    // To check for variables we have to check for value and type
    assertThat(termManager.mkConst(termManager.getBooleanSort()).getSort().isBoolean()).isTrue();

    // Test consts (variables). Consts are always false when checked for isTypedValue(), if you try
    // getTypedValue() on it anyway an exception is raised. This persists after sat. The only way of
    // checking and geting the values is via Kind.CONSTANT, type = sort and getValue()
    Term intVar = termManager.mkConst(termManager.getIntegerSort(), "int_const");
    assertThat(intVar.isIntegerValue()).isFalse();
    assertThat(intVar.getSort().isInteger()).isTrue();
    Exception e = assertThrows(io.github.cvc5.CVC5ApiException.class, intVar::getIntegerValue);
    assertThat(e.toString())
        .contains(
            "Invalid argument 'int_const' for '*d_node', expected Term to be an integer value when"
                + " calling getIntegerValue()");
    // Build a formula such that is has a value, assert and check sat and then check again
    Term equality = termManager.mkTerm(Kind.EQUAL, intVar, termManager.mkInteger(1));
    solver.assertFormula(equality);
    // Is sat, no need to check
    solver.checkSat();
    assertThat(intVar.isIntegerValue()).isFalse();
    assertThat(intVar.getSort().isInteger()).isTrue();
    assertThat(intVar.getKind()).isEqualTo(Kind.CONSTANT);
    assertThat(intVar.getKind()).isNotEqualTo(Kind.VARIABLE);
    assertThat(solver.getValue(intVar).toString()).isEqualTo("1");
    // Op test
    assertThat(equality.getOp().toString()).isEqualTo("EQUAL");
    assertThat(
            termManager.mkTerm(equality.getOp(), intVar, termManager.mkInteger(1)).getId()
                == equality.getId())
        .isTrue();
    // Note that variables (Kind.VARIABLES) are bound variables!
    assertThat(termManager.mkVar(termManager.getIntegerSort()).getKind()).isEqualTo(Kind.VARIABLE);
    assertThat(termManager.mkVar(termManager.getIntegerSort()).getKind())
        .isNotEqualTo(Kind.CONSTANT);
    // Uf return sort is codomain
    // Uf unapplied are CONSTANT
    Sort intToBoolSort =
        termManager.mkFunctionSort(termManager.getIntegerSort(), termManager.getBooleanSort());
    assertThat(intToBoolSort.getFunctionCodomainSort().isBoolean()).isTrue();
    Term uf1 = termManager.mkConst(intToBoolSort);
    assertThat(uf1.getKind()).isNotEqualTo(Kind.VARIABLE);
    assertThat(uf1.getKind()).isEqualTo(Kind.CONSTANT);
    assertThat(uf1.getKind()).isNotEqualTo(Kind.APPLY_UF);
    assertThat(intToBoolSort.isFunction()).isTrue();
    assertThat(uf1.getSort().isFunction()).isTrue();
    // arity 1
    assertThat(uf1.getSort().getFunctionArity()).isEqualTo(1);
    // apply the uf, the kind is now APPLY_UF
    Term appliedUf1 = termManager.mkTerm(Kind.APPLY_UF, new Term[] {uf1, intVar});
    assertThat(appliedUf1.getKind()).isNotEqualTo(Kind.VARIABLE);
    assertThat(appliedUf1.getKind()).isNotEqualTo(Kind.CONSTANT);
    assertThat(appliedUf1.getKind()).isEqualTo(Kind.APPLY_UF);
    assertThat(appliedUf1.getSort().isFunction()).isFalse();
    // The ufs sort is always the returntype
    assertThat(appliedUf1.getSort()).isEqualTo(termManager.getBooleanSort());
    assertThat(appliedUf1.getNumChildren()).isEqualTo(2);
    // The first child is the UF
    assertThat(appliedUf1.getChild(0).getSort()).isEqualTo(intToBoolSort);
    // The second child onwards are the arguments
    assertThat(appliedUf1.getChild(1).getSort()).isEqualTo(termManager.getIntegerSort());
  }

  /*
   *  Try to convert real -> int -> bv -> fp; which fails at the fp step.
   *  Use Kind.FLOATINGPOINT_TO_FP_REAL instead!
   */
  @Test
  public void checkFPConversion() throws CVC5ApiException {
    Term oneFourth = termManager.mkReal("1/4");
    Term intOneFourth = termManager.mkTerm(Kind.TO_INTEGER, oneFourth);
    Term bvOneFourth =
        termManager.mkTerm(termManager.mkOp(Kind.INT_TO_BITVECTOR, 32), intOneFourth);

    Exception e =
        assertThrows(
            io.github.cvc5.CVC5ApiException.class,
            () -> termManager.mkFloatingPoint(8, 24, bvOneFourth));
    assertThat(e.toString())
        .contains(
            "Invalid argument '((_ int2bv 32) (to_int (/ 1 4)))' for 'val', expected bit-vector"
                + " constant");
  }

  @Test
  public void checkSimpleUnsat() {
    solver.assertFormula(termManager.mkBoolean(false));
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isUnsat()).isTrue();
  }

  @Test
  public void checkSimpleSat() {
    solver.assertFormula(termManager.mkBoolean(true));
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleEqualitySat() {
    Term one = termManager.mkInteger(1);
    Term assertion = termManager.mkTerm(Kind.EQUAL, one, one);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleEqualityUnsat() {
    Term zero = termManager.mkInteger(0);
    Term one = termManager.mkInteger(1);
    Term assertion = termManager.mkTerm(Kind.EQUAL, zero, one);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleInequalityUnsat() {
    Term one = termManager.mkInteger(1);
    Term assertion = termManager.mkTerm(Kind.NOT, termManager.mkTerm(Kind.EQUAL, one, one));
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleInequalitySat() {
    Term zero = termManager.mkInteger(0);
    Term one = termManager.mkInteger(1);
    Term assertion = termManager.mkTerm(Kind.NOT, termManager.mkTerm(Kind.EQUAL, zero, one));
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleLIAEqualitySat() {
    Term one = termManager.mkInteger(1);
    Term two = termManager.mkInteger(2);
    Term assertion = termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, one, one), two);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleLIAEqualityUnsat() {
    Term one = termManager.mkInteger(1);
    Term assertion = termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, one, one), one);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleLIASat() {
    // x + y = 4 AND x * y = 4
    Term four = termManager.mkInteger(4);
    Term varX = termManager.mkConst(termManager.getIntegerSort(), "x");
    Term varY = termManager.mkConst(termManager.getIntegerSort(), "y");
    Term assertion1 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.MULT, varX, varY), four);
    Term assertion2 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, varX, varY), four);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
    assertThat(getInt(varX) + getInt(varY)).isEqualTo(4);
    assertThat(getInt(varX) * getInt(varY)).isEqualTo(4);
  }

  /** Helper to get to int values faster. */
  private int getInt(Term cvc5Term) {
    String string = solver.getValue(cvc5Term).toString();
    return Integer.parseInt(string);
  }

  @Test
  public void checkSimpleLIAUnsat() {
    // x + y = 1 AND x * y = 1
    Term one = termManager.mkInteger(1);
    Term varX = termManager.mkConst(termManager.getIntegerSort(), "x");
    Term varY = termManager.mkConst(termManager.getIntegerSort(), "y");
    Term assertion1 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.MULT, varX, varY), one);
    Term assertion2 = termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, varX, varY), one);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkLIAModel() {
    // 1 + 2 = var
    // it follows that var = 3
    Term one = termManager.mkInteger(1);
    Term two = termManager.mkInteger(2);
    Term var = termManager.mkConst(termManager.getIntegerSort());
    Term assertion = termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, one, two), var);
    solver.assertFormula(assertion);
    Result result = solver.checkSat();
    assertThat(result.isSat()).isTrue();
    Term assertionValue = solver.getValue(assertion);
    assertThat(assertionValue.toString()).isEqualTo("true");
    assertThat(solver.getValue(var).toString()).isEqualTo("3");
  }

  @Test
  public void checkSimpleLIRAUnsat2() {
    // x + y = 4 AND x * y = 4
    Term threeHalf = termManager.mkReal(3, 2);
    Term varX = termManager.mkConst(termManager.getRealSort(), "x");
    Term varY = termManager.mkConst(termManager.getRealSort(), "y");
    Term assertion1 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.MULT, varX, varY), threeHalf);
    Term assertion2 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, varX, varY), threeHalf);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleLIRASat() {
    // x + y = 8/5 AND x > 0 AND y > 0 AND x < 8/5 AND y < 8/5
    Term zero = termManager.mkReal(0);
    Term eightFifth = termManager.mkReal(8, 5);
    Term varX = termManager.mkConst(termManager.getRealSort(), "x");
    Term varY = termManager.mkConst(termManager.getRealSort(), "y");
    Term assertion1 = termManager.mkTerm(Kind.GT, varX, zero);
    Term assertion2 = termManager.mkTerm(Kind.GT, varY, zero);
    Term assertion3 = termManager.mkTerm(Kind.LT, varX, eightFifth);
    Term assertion4 = termManager.mkTerm(Kind.LT, varY, eightFifth);
    Term assertion5 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, varX, varY), eightFifth);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    solver.assertFormula(assertion3);
    solver.assertFormula(assertion4);
    solver.assertFormula(assertion5);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  /** Real uses the same operators as int (plain plus, mult etc.). */
  @Test
  public void checkSimpleLRASat() {
    // x * y = 8/5 AND x < 4/5
    Term fourFifth = termManager.mkReal(4, 5);
    Term eightFifth = termManager.mkReal(8, 5);
    Term varX = termManager.mkConst(termManager.getRealSort(), "x");
    Term varY = termManager.mkConst(termManager.getRealSort(), "y");

    Term assertion1 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.MULT, varX, varY), eightFifth);
    Term assertion2 = termManager.mkTerm(Kind.LT, varX, fourFifth);

    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  /** Exponents may only be natural number constants. */
  @Test
  public void checkSimplePow() {
    // x ^ 2 = 4 AND x ^ 3 = 8
    Term two = termManager.mkReal(2);
    Term three = termManager.mkReal(3);
    Term four = termManager.mkReal(4);
    Term eight = termManager.mkReal(8);
    Term varX = termManager.mkConst(termManager.getRealSort(), "x");
    Term assertion1 = termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.POW, varX, two), four);
    Term assertion2 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.POW, varX, three), eight);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  // TODO: schreibe test von fp variable nach real bzw. umgekehrt. ALso fp formel -> real formel

  @Test
  public void checkSimpleFPSat() throws CVC5ApiException {
    // x * y = 1/4
    Term rmTerm = termManager.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_AWAY);
    Op mkRealOp = termManager.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_REAL, 8, 24);
    Term oneFourth = termManager.mkTerm(mkRealOp, rmTerm, termManager.mkReal(1, 4));

    Term varX = termManager.mkConst(termManager.mkFloatingPointSort(8, 24), "x");
    Term varY = termManager.mkConst(termManager.mkFloatingPointSort(8, 24), "y");
    Term assertion1 =
        termManager.mkTerm(
            Kind.FLOATINGPOINT_EQ,
            termManager.mkTerm(Kind.FLOATINGPOINT_MULT, rmTerm, varX, varY),
            oneFourth);

    solver.assertFormula(assertion1);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleFPUnsat() throws CVC5ApiException {
    // x * y = 1/4 AND x > 0 AND y < 0
    Term rmTerm = termManager.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_AWAY);
    Op mkRealOp = termManager.mkOp(Kind.FLOATINGPOINT_TO_FP_FROM_REAL, 8, 24);
    Term oneFourth = termManager.mkTerm(mkRealOp, rmTerm, termManager.mkReal(1, 4));
    Term zero = termManager.mkTerm(mkRealOp, rmTerm, termManager.mkReal(0));

    Term varX = termManager.mkConst(termManager.mkFloatingPointSort(8, 24), "x");
    Term varY = termManager.mkConst(termManager.mkFloatingPointSort(8, 24), "y");
    Term assertion1 =
        termManager.mkTerm(
            Kind.FLOATINGPOINT_EQ,
            termManager.mkTerm(Kind.FLOATINGPOINT_MULT, rmTerm, varX, varY),
            oneFourth);
    Term assertion2 = termManager.mkTerm(Kind.FLOATINGPOINT_GT, varX, zero);
    Term assertion3 = termManager.mkTerm(Kind.FLOATINGPOINT_LT, varY, zero);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    solver.assertFormula(assertion3);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleLRAUnsat() {
    // x + y = x * y AND x - 1 = 0
    Term zero = termManager.mkInteger(0);
    Term one = termManager.mkInteger(1);
    Term varX = termManager.mkConst(termManager.getRealSort(), "x");
    Term varY = termManager.mkConst(termManager.getRealSort(), "y");
    Term assertion1 =
        termManager.mkTerm(
            Kind.EQUAL,
            termManager.mkTerm(Kind.MULT, varX, varY),
            termManager.mkTerm(Kind.ADD, varX, varY));
    Term assertion2 =
        termManager.mkTerm(
            Kind.EQUAL,
            termManager.mkTerm(Kind.SUB, varX, termManager.mkTerm(Kind.TO_REAL, one)),
            termManager.mkTerm(Kind.TO_REAL, zero));
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleLRAUnsat2() {
    // x + y = 3/2 AND x * y = 3/2
    Term threeHalf = termManager.mkReal(3, 2);
    Term varX = termManager.mkConst(termManager.getRealSort(), "x");
    Term varY = termManager.mkConst(termManager.getRealSort(), "y");
    Term assertion1 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.MULT, varX, varY), threeHalf);
    Term assertion2 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, varX, varY), threeHalf);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleIncrementalSolving() throws CVC5ApiException {
    // x + y = 3/2 AND x * y = 3/2 (AND x - 1 = 0)
    Term zero = termManager.mkInteger(0);
    Term one = termManager.mkInteger(1);
    Term threeHalf = termManager.mkReal(3, 2);
    Term varX = termManager.mkConst(termManager.getRealSort(), "x");
    Term varY = termManager.mkConst(termManager.getRealSort(), "y");
    // this alone is SAT
    Term assertion1 =
        termManager.mkTerm(
            Kind.EQUAL,
            termManager.mkTerm(Kind.MULT, varX, varY),
            termManager.mkTerm(Kind.ADD, varX, varY));
    // both 2 and 3 make it UNSAT (either one)
    Term assertion2 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.ADD, varX, varY), threeHalf);
    Term assertion3 =
        termManager.mkTerm(
            Kind.EQUAL,
            termManager.mkTerm(Kind.SUB, varX, termManager.mkTerm(Kind.TO_REAL, one)),
            termManager.mkTerm(Kind.TO_REAL, zero));
    solver.push();
    solver.assertFormula(assertion1);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
    solver.push();
    solver.assertFormula(assertion2);
    satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
    solver.pop();
    satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
    solver.push();
    solver.assertFormula(assertion3);
    satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
    solver.pop();
    satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  /** Note that model and getValue are seperate! */
  @Test
  public void checkInvalidModelGetValue() {
    Term assertion = termManager.mkBoolean(false);
    solver.assertFormula(assertion);
    Result result = solver.checkSat();
    assertThat(result.isSat()).isFalse();
    Exception e =
        assertThrows(
            io.github.cvc5.CVC5ApiRecoverableException.class, () -> solver.getValue(assertion));
    assertThat(e.toString()).contains(INVALID_GETVALUE_STRING_SAT);
  }

  /** The getModel() call needs an array of sorts and terms. */
  @Test
  public void checkGetModelUnsat() {
    Term assertion = termManager.mkBoolean(false);
    solver.assertFormula(assertion);
    Sort[] sorts = new Sort[] {termManager.getBooleanSort()};
    Term[] terms = new Term[] {assertion};
    Result result = solver.checkSat();
    assertThat(result.isSat()).isFalse();

    Exception e =
        assertThrows(
            io.github.cvc5.CVC5ApiRecoverableException.class, () -> solver.getModel(sorts, terms));
    assertThat(e.toString()).contains(INVALID_MODEL_STRING);
  }

  /**
   * The getModel() call needs an array of sorts and terms. This tests invalid sort parameters.
   * Sort: The list of uninterpreted sorts that should be printed in the model. Vars: The list of
   * free constants that should be printed in the model. A subset of these may be printed based on
   * isModelCoreSymbol.
   */
  @Test
  public void checkGetModelSatInvalidSort() {
    Term assertion = termManager.mkBoolean(true);
    solver.assertFormula(assertion);
    Sort[] sorts = new Sort[] {termManager.getBooleanSort()};
    Term[] terms = new Term[] {assertion};
    Result result = solver.checkSat();
    assertThat(result.isSat()).isTrue();
    Exception e =
        assertThrows(
            io.github.cvc5.CVC5ApiRecoverableException.class, () -> solver.getModel(sorts, terms));
    assertThat(e.toString()).contains("Expecting an uninterpreted sort as argument to getModel.");
  }

  /** Same as checkGetModelSatInvalidSort but with invalid term. */
  @Test
  public void checkGetModelSatInvalidTerm() {
    Term assertion = termManager.mkBoolean(true);
    solver.assertFormula(assertion);
    Sort[] sorts = new Sort[] {};
    Term[] terms = new Term[] {assertion};
    Result result = solver.checkSat();
    assertThat(result.isSat()).isTrue();
    Exception e =
        assertThrows(
            io.github.cvc5.CVC5ApiRecoverableException.class, () -> solver.getModel(sorts, terms));
    assertThat(e.toString()).contains("Expecting a free constant as argument to getModel.");
  }

  @Test
  public void checkGetModelSat() {
    Term assertion = termManager.mkConst(termManager.getBooleanSort());
    solver.assertFormula(assertion);
    Sort[] sorts = new Sort[] {};
    Term[] terms = new Term[] {assertion};
    Result result = solver.checkSat();
    assertThat(result.isSat()).isTrue();
    String model = solver.getModel(sorts, terms);
    // The toString of vars (consts) is the internal variable id
    assertThat(model).contains("(\n" + "(define-fun " + assertion + " () Bool true)\n" + ")");
  }

  /**
   * The getModel() call needs an array of sorts and terms. This tests what happens if you put empty
   * arrays into it.
   */
  @Test
  public void checkInvalidGetModel() {
    Term assertion = termManager.mkBoolean(false);
    solver.assertFormula(assertion);
    Result result = solver.checkSat();
    assertThat(result.isSat()).isFalse();
    Sort[] sorts = new Sort[1];
    Term[] terms = new Term[1];
    assertThrows(NullPointerException.class, () -> solver.getModel(sorts, terms));
  }

  /** It does not matter if you take an int or array or bv here, all result in the same error. */
  @Test
  public void checkInvalidTypeOperationsAssert() throws CVC5ApiException {
    Sort bvSort = termManager.mkBitVectorSort(16);
    Term bvVar = termManager.mkConst(bvSort, "bla");
    Term assertion = termManager.mkTerm(Kind.BITVECTOR_AND, bvVar, bvVar);

    Exception e =
        assertThrows(io.github.cvc5.CVC5ApiException.class, () -> solver.assertFormula(assertion));
    assertThat(e.toString()).contains("Expected term with sort Bool");
  }

  /** It does not matter if you take an int or array or bv here, all result in the same error. */
  @Test
  public void checkInvalidTypeOperationsCheckSat() throws CVC5ApiException {
    Sort bvSort = termManager.mkBitVectorSort(16);
    Term bvVar = termManager.mkConst(bvSort);
    Term intVar = termManager.mkConst(termManager.getIntegerSort());
    Term arrayVar =
        termManager.mkConst(
            termManager.mkArraySort(termManager.getIntegerSort(), termManager.getIntegerSort()));

    Exception e =
        assertThrows(
            io.github.cvc5.CVC5ApiException.class,
            () -> termManager.mkTerm(Kind.AND, bvVar, bvVar));
    assertThat(e.toString()).contains("expecting a Boolean subexpression");

    e =
        assertThrows(
            io.github.cvc5.CVC5ApiException.class,
            () -> termManager.mkTerm(Kind.AND, intVar, intVar));
    assertThat(e.toString()).contains("expecting a Boolean subexpression");

    e =
        assertThrows(
            io.github.cvc5.CVC5ApiException.class,
            () -> termManager.mkTerm(Kind.AND, arrayVar, arrayVar));
    assertThat(e.toString()).contains("expecting a Boolean subexpression");
  }

  @Test
  public void checkBvInvalidZeroWidthAssertion() {
    Exception e =
        assertThrows(io.github.cvc5.CVC5ApiException.class, () -> termManager.mkBitVector(0, 1));
    assertThat(e.toString()).contains("Invalid argument '0' for 'size', expected a bit-width > 0");
  }

  @Test
  public void checkBvInvalidNegativeWidthCheckAssertion() {
    Exception e =
        assertThrows(io.github.cvc5.CVC5ApiException.class, () -> termManager.mkBitVector(-1, 1));
    assertThat(e.toString()).contains("Expected size '-1' to be non negative.");
  }

  @Test
  public void checkSimpleBvEqualitySat() throws CVC5ApiException {
    // 1 + 0 = 1 with bitvectors
    Term bvOne = termManager.mkBitVector(16, 1);
    Term bvZero = termManager.mkBitVector(16, 0);
    Term assertion =
        termManager.mkTerm(
            Kind.EQUAL, termManager.mkTerm(Kind.BITVECTOR_ADD, bvZero, bvOne), bvOne);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkSimpleBvEqualityUnsat() throws CVC5ApiException {
    // 0 + 1 = 2 UNSAT with bitvectors
    Term bvZero = termManager.mkBitVector(16, 0);
    Term bvOne = termManager.mkBitVector(16, 1);
    Term bvTwo = termManager.mkBitVector(16, 2);
    Term assertion =
        termManager.mkTerm(
            Kind.EQUAL, termManager.mkTerm(Kind.BITVECTOR_ADD, bvZero, bvOne), bvTwo);
    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkSimpleBvUnsat() throws CVC5ApiException {
    // var + 1 = 0 & var < max bitvector & var > 0; both < and > signed
    // Because of bitvector nature its UNSAT now

    Term bvVar = termManager.mkConst(termManager.mkBitVectorSort(16), "bvVar");
    Term bvOne = termManager.mkBitVector(16, 1);
    Term bvZero = termManager.mkBitVector(16, 0);
    Term assertion1 =
        termManager.mkTerm(
            Kind.EQUAL, termManager.mkTerm(Kind.BITVECTOR_ADD, bvVar, bvOne), bvZero);
    // mkMaxSigned(16);
    Term assertion2 = termManager.mkTerm(Kind.BITVECTOR_SLT, bvVar, makeMaxCVC5Bitvector(16, true));
    Term assertion3 = termManager.mkTerm(Kind.BITVECTOR_SGT, bvVar, bvZero);
    solver.assertFormula(assertion1);
    solver.assertFormula(assertion2);
    solver.assertFormula(assertion3);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Ignore
  public void checkBvDistinct() throws CVC5ApiException {
    Sort bvSort = termManager.mkBitVectorSort(6);
    List<Term> bvs = new ArrayList<>();
    for (int i = 0; i < 64; i++) {
      bvs.add(termManager.mkConst(bvSort, "a" + i + "_"));
    }

    // TODO: this got worse in the 1.0.0 release and now this runs endlessly as well, check in later
    // version again.
    Term distinct2 = termManager.mkTerm(Kind.DISTINCT, bvs.toArray(new Term[0]));
    solver.assertFormula(distinct2);
    assertThat(solver.checkSat().isSat()).isTrue();
    solver.resetAssertions();

    // TODO: The following runs endlessly; recheck for new versions!
    /*
      bvs.add(solver.mkConst(bvSort, "b" + "_"));
      Term distinct3 = solver.mkTerm(Kind.DISTINCT, bvs.toArray(new Term[0]));
      solver.assertFormula(distinct3);
      assertThat(solver.checkSat().isSat()).isFalse();
    */
  }

  /*
   * CVC5 fails some easy quantifier tests.
   */
  @Test
  public void checkQuantifierExistsIncomplete() {
    // (not exists x . not b[x] = 0) AND (b[123] = 0) is SAT

    setupArrayQuant();
    Term zero = termManager.mkInteger(0);

    Term xBound = termManager.mkVar(termManager.getIntegerSort(), "x");
    Term quantifiedVars = termManager.mkTerm(Kind.VARIABLE_LIST, xBound);
    Term aAtxEq0s = aAtxEq0.substitute(x, xBound);
    Term exists =
        termManager.mkTerm(Kind.EXISTS, quantifiedVars, termManager.mkTerm(Kind.NOT, aAtxEq0s));
    Term notExists = termManager.mkTerm(Kind.NOT, exists);

    Term select123 = termManager.mkTerm(Kind.SELECT, array, termManager.mkInteger(123));
    Term selectEq0 = termManager.mkTerm(Kind.EQUAL, select123, zero);
    Term assertion = termManager.mkTerm(Kind.AND, notExists, selectEq0);

    // CVC5 does not allow non quantifier formulas as the top most formula
    Exception e =
        assertThrows(io.github.cvc5.CVC5ApiException.class, () -> solver.assertFormula(assertion));
    assertThat(e.getMessage().strip()).matches(INVALID_TERM_BOUND_VAR);
  }

  @Test
  public void checkQuantifierEliminationLIA() {
    // build formula: (forall x . ((x < 5) | (7 < x + y)))
    // quantifier-free equivalent: (2 < y) or (>= y 3)
    setupArrayQuant();

    Term three = termManager.mkInteger(3);
    Term five = termManager.mkInteger(5);
    Term seven = termManager.mkInteger(7);

    Term y = termManager.mkConst(termManager.getIntegerSort(), "y");

    Term first = termManager.mkTerm(Kind.LT, x, five);
    Term second = termManager.mkTerm(Kind.LT, seven, termManager.mkTerm(Kind.ADD, x, y));
    Term body = termManager.mkTerm(Kind.OR, first, second);

    Term xBound = termManager.mkVar(termManager.getIntegerSort(), "xBound");
    Term quantifiedVars = termManager.mkTerm(Kind.VARIABLE_LIST, xBound);

    Term bodySubst = body.substitute(x, xBound);
    Term assertion = termManager.mkTerm(Kind.FORALL, quantifiedVars, bodySubst);

    Term result = solver.getQuantifierElimination(assertion);

    Term resultCheck = termManager.mkTerm(Kind.GEQ, y, three);
    assertThat(result.toString()).isEqualTo(resultCheck.toString());
  }

  @Test
  public void checkQuantifierAndModelWithUf() throws CVC5ApiException {
    Term var = termManager.mkConst(termManager.getIntegerSort(), "var");
    // start with a normal, free variable!
    Term boundVar = termManager.mkConst(termManager.getIntegerSort(), "boundVar");
    Term varIsOne = termManager.mkTerm(Kind.EQUAL, var, termManager.mkInteger(4));
    // try not to use 0 as this is the default value for CVC5 models
    Term boundVarIsTwo = termManager.mkTerm(Kind.EQUAL, boundVar, termManager.mkInteger(2));
    Term boundVarIsThree = termManager.mkTerm(Kind.EQUAL, boundVar, termManager.mkInteger(3));

    String func = "func";
    Sort intSort = termManager.getIntegerSort();

    Sort ufSort = termManager.mkFunctionSort(intSort, intSort);
    Term uf = termManager.mkConst(ufSort, func);
    Term funcAtBoundVar = termManager.mkTerm(Kind.APPLY_UF, uf, boundVar);

    Term body =
        termManager.mkTerm(
            Kind.AND, boundVarIsTwo, termManager.mkTerm(Kind.EQUAL, var, funcAtBoundVar));

    // This is the bound variable used for boundVar
    Term boundVarBound = termManager.mkVar(termManager.getIntegerSort(), "boundVar");
    Term quantifiedVars = termManager.mkTerm(Kind.VARIABLE_LIST, boundVarBound);
    // Subst all boundVar variables with the bound version
    Term bodySubst = body.substitute(boundVar, boundVarBound);
    Term quantFormula = termManager.mkTerm(Kind.EXISTS, quantifiedVars, bodySubst);

    // var = 4 & boundVar = 3 & exists boundVar . ( boundVar = 2 & f(boundVar) = var )
    Term overallFormula = termManager.mkTerm(Kind.AND, varIsOne, boundVarIsThree, quantFormula);

    solver.assertFormula(overallFormula);

    Result satCheck = solver.checkSat();

    // SAT
    assertThat(satCheck.isSat()).isTrue();

    // check Model
    // var = 4 & boundVar = 3 & exists boundVar . ( boundVar = 2 & f(2) = 4 )
    // It seems like CVC5 can't return quantified variables,
    // therefore we can't get a value for the uf!
    assertThat(solver.getValue(var).toString()).isEqualTo("4");
    assertThat(solver.getValue(boundVar).toString()).isEqualTo("3");
    // funcAtBoundVar and body do not have boundVars in them!
    assertThat(solver.getValue(funcAtBoundVar).toString()).isEqualTo("4");
    assertThat(solver.getValue(body).toString()).isEqualTo("false");
    // The function is a applied uf
    assertThat(funcAtBoundVar.getKind()).isEqualTo(Kind.APPLY_UF);
    assertThat(funcAtBoundVar.getSort()).isEqualTo(termManager.getIntegerSort());
    assertThat(funcAtBoundVar.hasSymbol()).isFalse();
    assertThat(solver.getValue(funcAtBoundVar).toString()).isEqualTo("4");
    // The function has 2 children, 1st is the function, 2nd is the argument
    assertThat(funcAtBoundVar.getNumChildren()).isEqualTo(2);
    assertThat(funcAtBoundVar.toString()).isEqualTo("(func boundVar)");
    assertThat(funcAtBoundVar.getChild(0).toString()).isEqualTo("func");
    assertThat(funcAtBoundVar.getChild(1).toString()).isEqualTo("boundVar");
    // Now the same function within the body with the bound var substituted
    // A quantifier has 2 children, the second is the body
    assertThat(quantFormula.getNumChildren()).isEqualTo(2);
    // The body is the AND formula from above, the right child is var = func
    // The right child of var = func is the func
    Term funcModel = quantFormula.getChild(1).getChild(1).getChild(1);
    // This too is a applied uf
    assertThat(funcModel.getKind()).isEqualTo(Kind.APPLY_UF);
    // This should have the same SMTLIB2 string as the declaration
    assertThat(funcModel.toString()).isEqualTo(funcAtBoundVar.toString());
    // But the argument should be a bound var
    // You can not get a value for the entire function Term as it contains a bound var! (see below)
    assertThat(funcModel.getNumChildren()).isEqualTo(2);
    assertThat(funcModel.getChild(0).hasSymbol()).isTrue();
    assertThat(funcModel.getChild(0).getSymbol()).isEqualTo("func");
    // For some reason the function in an UF is CONSTANT type after a SAT call but if you try to get
    // the value it changes and is no longer the same as before, but a
    // LAMBDA Kind with the argument (in some internal string representation + its type) and the
    // result. You can get the result as the second child (child 1)
    assertThat(funcModel.getChild(0).getKind()).isEqualTo(Kind.CONSTANT);
    // Without getValue the Kind and num of children is fine
    assertThat(funcModel.getChild(0).getNumChildren()).isEqualTo(0);
    // The Sort is the function sort (which is the lambda)
    assertThat(funcModel.getChild(0).getSort()).isEqualTo(funcAtBoundVar.getChild(0).getSort());
    assertThat(solver.getValue(funcModel.getChild(0)).getNumChildren()).isEqualTo(2);
    assertThat(solver.getValue(funcModel.getChild(0)).getKind()).isEqualTo(Kind.LAMBDA);
    assertThat(solver.getValue(funcModel.getChild(0)).toString())
        .isEqualTo("(lambda ((_arg_1 Int)) 4)");

    assertThat(solver.getValue(funcModel.getChild(0)).getChild(1).toString()).isEqualTo("4");
    // The function parameter is fine
    assertThat(funcModel.getChild(1).toString()).isEqualTo("boundVar");
    // Now it is a VARIABLE (bound variables in CVC5)
    assertThat(funcModel.getChild(1).getKind()).isEqualTo(Kind.VARIABLE);

    // CVC5 does not allow the usage of getValue() on bound vars!
    Exception e =
        assertThrows(io.github.cvc5.CVC5ApiException.class, () -> solver.getValue(boundVarBound));
    assertThat(e.getMessage().strip()).matches(INVALID_TERM_BOUND_VAR);
    e = assertThrows(io.github.cvc5.CVC5ApiException.class, () -> solver.getValue(bodySubst));
    assertThat(e.getMessage().strip()).matches(INVALID_TERM_BOUND_VAR);
  }

  /** CVC5 does not support Array quantifier elimination. This would run endlessly! */
  @Ignore
  @Test
  public void checkArrayQuantElim() {
    setupArrayQuant();
    Term body = termManager.mkTerm(Kind.OR, aAtxEq0, aAtxEq1);

    Term xBound = termManager.mkVar(termManager.getIntegerSort(), "x_b");
    Term quantifiedVars = termManager.mkTerm(Kind.VARIABLE_LIST, xBound);
    Term bodySubst = body.substitute(x, xBound);
    Term assertion = termManager.mkTerm(Kind.FORALL, quantifiedVars, bodySubst);

    Term result = solver.getQuantifierElimination(assertion);
    String resultString =
        "(forall ((x_b Int)) (let ((_let_0 (select a x_b))) (or (= _let_0 0) (= _let_0 1))) )";
    assertThat(result.toString()).isEqualTo(resultString);
  }

  /** CVC5 does support Bv quantifier elim.! */
  @Test
  public void checkQuantifierEliminationBV() throws CVC5ApiException {
    // build formula: exists y : bv[2]. x * y = 1
    // quantifier-free equivalent: x = 1 | x = 3
    // or extract_0_0 x = 1

    // Note from CVC5: a witness expression; first parameter is a BOUND_VAR_LIST, second is the
    // witness body"

    int width = 2;

    Term xBv = termManager.mkConst(termManager.mkBitVectorSort(width), "x_bv");
    Term yBv = termManager.mkConst(termManager.mkBitVectorSort(width), "y_bv");
    Term mult = termManager.mkTerm(Kind.BITVECTOR_MULT, xBv, yBv);
    Term body = termManager.mkTerm(Kind.EQUAL, mult, termManager.mkBitVector(2, 1));

    Term xBound = termManager.mkVar(termManager.mkBitVectorSort(width), "y_bv");
    Term quantifiedVars = termManager.mkTerm(Kind.VARIABLE_LIST, xBound);
    Term bodySubst = body.substitute(yBv, xBound);
    Term assertion = termManager.mkTerm(Kind.EXISTS, quantifiedVars, bodySubst);

    Term quantElim = solver.getQuantifierElimination(assertion);

    assertThat(quantElim.toString())
        .isEqualTo(
            "(= (bvmul x_bv (witness ((x0 (_ BitVec 2))) (or (= (bvmul x_bv x0) #b01) (not (="
                + " (concat #b0 ((_ extract 0 0) (bvor x_bv (bvneg x_bv)))) #b01))))) #b01)");

    // TODO: formely you could get a better result Term by using getValue(). But now getValue() only
    // works after SAT since 1.0.0 and then getValue() prints trivial statements like false.
  }

  @Test
  public void checkArraySat() {
    // ((x = 123) & (select(arr, 5) = 123)) => ((select(arr, 5) = x) & (x = 123))
    Term five = termManager.mkInteger(5);
    Term oneTwoThree = termManager.mkInteger(123);

    Term xInt = termManager.mkConst(termManager.getIntegerSort(), "x_int");

    Sort arraySort =
        termManager.mkArraySort(termManager.getIntegerSort(), termManager.getIntegerSort());
    Term arr = termManager.mkConst(arraySort, "arr");

    Term xEq123 = termManager.mkTerm(Kind.EQUAL, xInt, oneTwoThree);
    Term selAat5Eq123 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.SELECT, arr, five), oneTwoThree);
    Term selAat5EqX =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.SELECT, arr, five), xInt);

    Term leftAnd = termManager.mkTerm(Kind.AND, xEq123, selAat5Eq123);
    Term rightAnd = termManager.mkTerm(Kind.AND, xEq123, selAat5EqX);
    Term impl = termManager.mkTerm(Kind.IMPLIES, leftAnd, rightAnd);

    solver.assertFormula(impl);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkArrayUnsat() {
    // (x = 123) & (select(arr, 5) = 123) & (select(arr, 5) != x)
    Term five = termManager.mkInteger(5);
    Term oneTwoThree = termManager.mkInteger(123);

    Term xInt = termManager.mkConst(termManager.getIntegerSort(), "x_int");

    Sort arraySort =
        termManager.mkArraySort(termManager.getIntegerSort(), termManager.getIntegerSort());
    Term arr = termManager.mkConst(arraySort, "arr");

    Term xEq123 = termManager.mkTerm(Kind.EQUAL, xInt, oneTwoThree);
    Term selAat5Eq123 =
        termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.SELECT, arr, five), oneTwoThree);
    Term selAat5NotEqX =
        termManager.mkTerm(
            Kind.NOT,
            termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.SELECT, arr, five), xInt));

    Term assertion = termManager.mkTerm(Kind.AND, xEq123, selAat5Eq123, selAat5NotEqX);

    solver.assertFormula(assertion);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkUnsatCore() {
    solver.setOption("produce-unsat-cores", "true");
    solver.setOption("produce-proofs", "true");
    // (a & b) & (not(a OR b))
    // Enable UNSAT Core first!
    solver.setOption("produce-unsat-cores", "true");

    Sort boolSort = termManager.getBooleanSort();
    Term a = termManager.mkConst(boolSort, "a");
    Term b = termManager.mkConst(boolSort, "b");

    Term aAndb = termManager.mkTerm(Kind.AND, a, b);
    Term notaOrb = termManager.mkTerm(Kind.NOT, termManager.mkTerm(Kind.OR, a, b));

    solver.assertFormula(aAndb);
    solver.assertFormula(notaOrb);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();

    Term[] unsatCore = solver.getUnsatCore();

    // UnsatCores are iterable
    for (Term e : unsatCore) {
      assertThat(e.toString()).isIn(Arrays.asList("(not (or a b))", "(and a b)"));
    }
  }

  @Test
  public void checkCustomTypesAndUFs() {
    // 0 <= f(x)
    // 0 <= f(y)
    // f(x) + f(y) <= 1
    // not p(0)
    // p(f(y))
    Term zero = termManager.mkInteger(0);
    Term one = termManager.mkInteger(1);

    Sort boolSort = termManager.getBooleanSort();
    Sort intSort = termManager.getIntegerSort();

    // You may use custom sorts just like bool or int
    Sort mySort = termManager.mkParamSort("f");
    // Sort for UFs later
    Sort mySortToInt = termManager.mkFunctionSort(mySort, intSort);
    Sort intToBool = termManager.mkFunctionSort(intSort, boolSort);

    Term xTyped = termManager.mkConst(mySort, "x");
    Term yTyped = termManager.mkConst(mySort, "y");

    // declare UFs
    Term f = termManager.mkConst(mySortToInt, "f");
    Term p = termManager.mkConst(intToBool, "p");

    // Apply UFs
    Term fx = termManager.mkTerm(Kind.APPLY_UF, f, xTyped);
    Term fy = termManager.mkTerm(Kind.APPLY_UF, f, yTyped);
    Term sum = termManager.mkTerm(Kind.ADD, fx, fy);
    Term p0 = termManager.mkTerm(Kind.APPLY_UF, p, zero);
    Term pfy = termManager.mkTerm(Kind.APPLY_UF, p, fy);

    // Make some assumptions
    Term assumptions1 =
        termManager.mkTerm(
            Kind.AND,
            termManager.mkTerm(Kind.LEQ, zero, fx),
            termManager.mkTerm(Kind.LEQ, zero, fy),
            termManager.mkTerm(Kind.LEQ, sum, one));

    Term assumptions2 = termManager.mkTerm(Kind.AND, p0.notTerm(), pfy);

    solver.assertFormula(assumptions1);
    solver.assertFormula(assumptions2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkBooleanUFDeclaration() {
    Sort boolSort = termManager.getBooleanSort();
    Sort intSort = termManager.getIntegerSort();

    // arg is bool, return is int
    Sort ufSort = termManager.mkFunctionSort(boolSort, intSort);
    Term uf = termManager.mkConst(ufSort, "fun_bi");
    Term ufTrue = termManager.mkTerm(Kind.APPLY_UF, uf, termManager.mkTrue());
    Term ufFalse = termManager.mkTerm(Kind.APPLY_UF, uf, termManager.mkFalse());

    Term assumptions =
        termManager.mkTerm(Kind.NOT, termManager.mkTerm(Kind.EQUAL, ufTrue, ufFalse));

    solver.assertFormula(assumptions);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
  }

  @Test
  public void checkLIAUfsUnsat() {
    // 0 <= f(x)
    // 0 <= f(y)
    // f(x) + f(y) = x
    // f(x) + f(y) = y
    // f(x) = x + 1
    // f(y) = y - 1
    Term zero = termManager.mkInteger(0);
    Term one = termManager.mkInteger(1);

    Sort intSort = termManager.getIntegerSort();

    // Sort for UFs later
    Sort intToInt = termManager.mkFunctionSort(intSort, intSort);

    Term xInt = termManager.mkConst(intSort, "x");
    Term yInt = termManager.mkConst(intSort, "y");

    // declare UFs
    Term f = termManager.mkConst(intToInt, "f");

    // Apply UFs
    Term fx = termManager.mkTerm(Kind.APPLY_UF, f, xInt);
    Term fy = termManager.mkTerm(Kind.APPLY_UF, f, yInt);
    Term plus = termManager.mkTerm(Kind.ADD, fx, fy);

    // Make some assumptions
    Term assumptions1 =
        termManager.mkTerm(
            Kind.AND,
            termManager.mkTerm(Kind.LEQ, zero, fx),
            termManager.mkTerm(Kind.EQUAL, plus, xInt),
            termManager.mkTerm(Kind.LEQ, zero, fy));

    Term assumptions2 =
        termManager.mkTerm(
            Kind.AND,
            termManager.mkTerm(Kind.EQUAL, fx, termManager.mkTerm(Kind.ADD, xInt, one)),
            termManager.mkTerm(Kind.EQUAL, fy, termManager.mkTerm(Kind.SUB, yInt, one)),
            termManager.mkTerm(Kind.EQUAL, plus, yInt));

    solver.assertFormula(assumptions1);
    solver.assertFormula(assumptions2);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isFalse();
  }

  @Test
  public void checkLIAUfsSat() {
    // f(x) = x + 1
    // f(y) = y - 1
    // x = y -> f(x) + f(y) = x AND f(x) + f(y) = y
    Term one = termManager.mkInteger(1);

    Sort intSort = termManager.getIntegerSort();

    // Sort for UFs later
    Sort intToInt = termManager.mkFunctionSort(intSort, intSort);

    Term xInt = termManager.mkConst(intSort, "x");
    Term yInt = termManager.mkConst(intSort, "y");

    // declare UFs
    Term f = termManager.mkConst(intToInt, "f");

    // Apply UFs
    Term fx = termManager.mkTerm(Kind.APPLY_UF, f, xInt);
    Term fy = termManager.mkTerm(Kind.APPLY_UF, f, yInt);
    Term plus = termManager.mkTerm(Kind.ADD, fx, fy);

    Term plusEqx = termManager.mkTerm(Kind.EQUAL, plus, xInt);
    Term plusEqy = termManager.mkTerm(Kind.EQUAL, plus, yInt);
    Term xEqy = termManager.mkTerm(Kind.EQUAL, yInt, xInt);
    Term xEqyImplplusEqxAndy =
        termManager.mkTerm(Kind.IMPLIES, xEqy, termManager.mkTerm(Kind.AND, plusEqx, plusEqy));

    Term assumptions =
        termManager.mkTerm(
            Kind.AND,
            termManager.mkTerm(Kind.EQUAL, fx, termManager.mkTerm(Kind.ADD, xInt, one)),
            termManager.mkTerm(Kind.EQUAL, fy, termManager.mkTerm(Kind.SUB, yInt, one)),
            xEqyImplplusEqxAndy);

    solver.assertFormula(assumptions);
    Result satCheck = solver.checkSat();
    assertThat(satCheck.isSat()).isTrue();
    assertThat(solver.getValue(fx).toString()).isEqualTo("0");
  }

  @Test
  public void checkStringCompare() {
    Term var1 = termManager.mkConst(termManager.getStringSort(), "0");
    Term var2 = termManager.mkConst(termManager.getStringSort(), "1");

    Term f =
        termManager
            .mkTerm(Kind.STRING_LEQ, var1, var2)
            .andTerm(termManager.mkTerm(Kind.STRING_LEQ, var2, var1));

    // Thats no problem
    solver.assertFormula(f);
    assertThat(solver.checkSat().isSat()).isTrue();

    // implying that 1 <= 2 & 2 <= 1 -> 1 = 2 however runs indefinitely
    /*
    Term implication = f.notTerm().orTerm(solver.mkTerm(Kind.EQUAL, var2, var1));
    solver.assertFormula(implication.notTerm());
    assertThat(solver.checkSat().isUnsat()).isTrue();
    */
  }

  /** Sets up array and quantifier based formulas for tests. */
  private void setupArrayQuant() {
    Term zero = termManager.mkInteger(0);
    Term one = termManager.mkInteger(1);

    x = termManager.mkVar(termManager.getIntegerSort(), "x");

    Sort arraySort =
        termManager.mkArraySort(termManager.getIntegerSort(), termManager.getIntegerSort());
    array = termManager.mkVar(arraySort, "a");

    aAtxEq0 = termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.SELECT, array, x), zero);
    aAtxEq1 = termManager.mkTerm(Kind.EQUAL, termManager.mkTerm(Kind.SELECT, array, x), one);
  }

  /**
   * For some reason CVC5 does not provide API to create max (or min) size signed/unsigned
   * bitvectors.
   *
   * @param width of the bitvector term.
   * @param signed true if signed. false for unsigned.
   * @return Max size bitvector term.
   */
  private Term makeMaxCVC5Bitvector(int width, boolean signed) throws CVC5ApiException {
    String bitvecString;
    if (signed) {
      bitvecString = String.valueOf(new char[width - 1]).replace("\0", "1");
      bitvecString = "0" + bitvecString;
    } else {
      bitvecString = String.valueOf(new char[width]).replace("\0", "1");
    }
    return termManager.mkBitVector(width, bitvecString, 2);
  }

  @Test
  public void termAccessAfterModelClosed() throws CVC5ApiException {
    Solver secondSolver = createEnvironment();
    Term v = termManager.mkConst(termManager.getIntegerSort(), "v");
    Term one = termManager.mkInteger(1);
    Term eq = termManager.mkTerm(Kind.EQUAL, v, one); // v==1

    secondSolver.assertFormula(eq);
    Result result = secondSolver.checkSat();
    assertThat(result.isSat()).isTrue();

    Term valueV = secondSolver.getValue(v);
    Preconditions.checkNotNull(valueV);

    System.out.println(valueV);
  }

  @Test
  public void checkCVC5InterpolationMethod() {
    solver.setOption("produce-interpolants", "true");
    Term xp = termManager.mkConst(termManager.getIntegerSort(), "xp");
    Term y = termManager.mkConst(termManager.getIntegerSort(), "y");

    Term ip0 = termManager.mkTerm(Kind.GT, xp, y);
    Term ip1 = termManager.mkTerm(Kind.EQUAL, xp, termManager.mkInteger(0));
    Term ip2 = termManager.mkTerm(Kind.GT, y, termManager.mkInteger(0));

    Term a = ip0;
    Term b = termManager.mkTerm(Kind.AND, ip1, ip2);

    assertThat(!interpolateAndCheck(solver, a, b).isNull()).isTrue();
  }

  /**
   * Interpolates Terms after CVC5 and checks the Definition of Craig-Interpolation for the
   * interpolation.
   *
   * @return Interpolantion of interpolantA and interpolantB after CVC5 Interpolation Definition
   */
  private Term interpolateAndCheck(Solver solverP, Term interpolantA, Term interpolantB) {
    // solver.setOption("produce-interpolants", "true");
    solverP.assertFormula(interpolantA);
    System.out.println(
        "Interpolation Pair:\n" + interpolantA + "\n" + termManager.mkTerm(Kind.NOT, interpolantB));
    Term interpolation = solverP.getInterpolant(termManager.mkTerm(Kind.NOT, interpolantB));
    System.out.println("Interpolation: " + interpolation);
    solverP.resetAssertions();
    Term cvc51 = termManager.mkTerm(Kind.IMPLIES, interpolantA, interpolation);
    Term cvc52 =
        termManager.mkTerm(Kind.IMPLIES, interpolation, termManager.mkTerm(Kind.NOT, interpolantB));

    solverP.assertFormula(cvc51);
    solverP.assertFormula(cvc52);
    if (solverP.checkSat().isUnsat()) {
      System.out.println("Does not satisfy CVC5 Interpolation Definition");
      return null;
    }

    solverP.resetAssertions();
    solverP.assertFormula(termManager.mkTerm(Kind.NOT, termManager.mkTerm(Kind.AND, cvc51, cvc52)));
    if (solverP.checkSat().isSat()) {
      System.out.println("Does not satisfy generally CVC5 Interpolation Definition");
      return null;
    }

    solverP.resetAssertions();
    Term craig1 = termManager.mkTerm(Kind.IMPLIES, interpolantA, interpolation);
    Term craig2 =
        termManager.mkTerm(
            Kind.EQUAL,
            termManager.mkTerm(Kind.AND, interpolation, interpolantB),
            termManager.mkBoolean(false));
    solverP.assertFormula(craig1);
    solverP.assertFormula(craig2);
    if (solverP.checkSat().isUnsat()) {
      System.out.println("Does not satisfy Craig Interpolation Definition");
      return null;
    }
    solverP.resetAssertions();
    solverP.assertFormula(
        termManager.mkTerm(Kind.NOT, termManager.mkTerm(Kind.AND, craig1, craig2)));
    if (solverP.checkSat().isSat()) {
      System.out.println("Does not satisfy generally Craig Interpolation Definition");
      return null;
    }
    System.out.println("------------");
    return interpolation;
  }

  @Test
  @Ignore // Does not terminate
  public void testSimpleInterpolation() {
    // Out of InterpolatingProverTest.java
    // Line: 65
    solver.setOption("produce-interpolants", "true");
    Term xprime = termManager.mkConst(termManager.getIntegerSort(), "x");
    Term y = termManager.mkConst(termManager.getIntegerSort(), "y");
    Term z = termManager.mkConst(termManager.getIntegerSort(), "z");
    Term f1 =
        termManager.mkTerm(
            Kind.EQUAL, y, termManager.mkTerm(Kind.MULT, termManager.mkInteger(2), xprime));
    Term f2 =
        termManager.mkTerm(
            Kind.EQUAL,
            y,
            termManager.mkTerm(
                Kind.ADD,
                termManager.mkInteger(1),
                termManager.mkTerm(Kind.MULT, z, termManager.mkInteger(2))));
    interpolateAndCheck(solver, f1, f2);
  }

  @Test
  public void testBitvectorSortinVariableCache() throws CVC5ApiException {
    Map<String, Term> variablesCache = new HashMap<>();
    String name = "__ADDRESS_OF_main::i@";
    Sort sort = termManager.mkBitVectorSort(32);
    System.out.println(sort);
    System.out.println("--------");
    Term exp = variablesCache.computeIfAbsent(name, n -> termManager.mkConst(sort, name));
    Preconditions.checkArgument(
        sort.equals(exp.getSort()),
        "symbol name %s with sort %s already in use for different sort %s with value %s as String",
        name,
        sort,
        exp.getSort(),
        exp);
  }
}
