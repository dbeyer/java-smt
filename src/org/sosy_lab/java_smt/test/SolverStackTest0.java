// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static junit.framework.TestCase.assertEquals;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

@SuppressWarnings("resource")
public abstract class SolverStackTest0 extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  protected abstract BasicProverEnvironment<?> newEnvironmentForTest(
      SolverContext pContext, ProverOptions... options);

  protected void requireTheoryCombination() {}

  private static final UniqueIdGenerator index = new UniqueIdGenerator(); // to get different names

  private void requireMultipleStackSupport() {
    assume()
        .withMessage("Solver does not support multiple stacks yet")
        .that(solver)
        .isNotEqualTo(Solvers.BOOLECTOR);
  }

  protected final void requireUfValuesInModel() {
    assume()
        .withMessage(
            "Integration of solver does not support retrieving values for UFs from a model")
        .that(solver)
        .isNotEqualTo(Solvers.Z3);
  }

  @Test
  public void simpleStackTestBool() throws SolverException, InterruptedException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);

    int i = index.getFreshId();
    BooleanFormula a = bmgr.makeVariable("bool_a" + i);
    BooleanFormula b = bmgr.makeVariable("bool_b" + i);
    BooleanFormula or = bmgr.or(a, b);

    stack.push(or); // L1
    assertThat(stack.size()).isEqualTo(1);
    assertThat(stack).isSatisfiable();
    BooleanFormula c = bmgr.makeVariable("bool_c" + i);
    BooleanFormula d = bmgr.makeVariable("bool_d" + i);
    BooleanFormula and = bmgr.and(c, d);

    stack.push(and); // L2
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isSatisfiable();

    BooleanFormula notOr = bmgr.not(or);

    stack.push(notOr); // L3
    assertThat(stack.size()).isEqualTo(3);
    assertThat(stack).isUnsatisfiable(); // "or" AND "not or" --> UNSAT

    stack.pop(); // L2
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isSatisfiable();

    stack.pop(); // L1
    assertThat(stack.size()).isEqualTo(1);
    assertThat(stack).isSatisfiable();

    // we are lower than before creating c and d.
    // however we assume that they are usable now (this violates SMTlib).
    stack.push(and); // L2
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isSatisfiable();

    stack.pop(); // L1
    assertThat(stack.size()).isEqualTo(1);
    assertThat(stack).isSatisfiable();

    stack.push(notOr); // L2
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isUnsatisfiable(); // "or" AND "not or" --> UNSAT

    stack.pop(); // L1
    assertThat(stack.size()).isEqualTo(1);
    assertThat(stack).isSatisfiable();

    stack.pop(); // L0 empty stack
    assertThat(stack.size()).isEqualTo(0);
  }

  @Test
  public void singleStackTestInteger() throws SolverException, InterruptedException {
    requireIntegers();

    BasicProverEnvironment<?> env = newEnvironmentForTest(context);
    simpleStackTestNum(imgr, env);
  }

  @Test
  public void singleStackTestRational() throws SolverException, InterruptedException {
    requireRationals();
    requireTheoryCombination();

    BasicProverEnvironment<?> env = newEnvironmentForTest(context);
    simpleStackTestNum(rmgr, env);
  }

  private <X extends NumeralFormula, Y extends X> void simpleStackTestNum(
      NumeralFormulaManager<X, Y> nmgr, BasicProverEnvironment<?> stack)
      throws SolverException, InterruptedException {
    int i = index.getFreshId();
    X a = nmgr.makeVariable("num_a" + i);
    X b = nmgr.makeVariable("num_b" + i);
    BooleanFormula leqAB = nmgr.lessOrEquals(a, b);

    stack.push(leqAB); // L1
    assertThat(stack.size()).isEqualTo(1);
    assertThat(stack).isSatisfiable();
    X c = nmgr.makeVariable("num_c" + i);
    X d = nmgr.makeVariable("num_d" + i);
    BooleanFormula eqCD = nmgr.lessOrEquals(c, d);

    stack.push(eqCD); // L2
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isSatisfiable();

    BooleanFormula gtAB = nmgr.greaterThan(a, b);

    stack.push(gtAB); // L3
    assertThat(stack.size()).isEqualTo(3);
    assertThat(stack).isUnsatisfiable(); // "<=" AND ">" --> UNSAT

    stack.pop(); // L2
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isSatisfiable();

    stack.pop(); // L1
    assertThat(stack.size()).isEqualTo(1);
    assertThat(stack).isSatisfiable();

    // we are lower than before creating c and d.
    // however we assume that they are usable now (this violates SMTlib).
    stack.push(eqCD); // L2
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isSatisfiable();

    stack.pop(); // L1
    assertThat(stack.size()).isEqualTo(1);
    assertThat(stack).isSatisfiable();

    stack.push(gtAB); // L2
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isUnsatisfiable(); // "or" AND "not or" --> UNSAT

    stack.pop(); // L1
    assertThat(stack.size()).isEqualTo(1);
    assertThat(stack).isSatisfiable();

    stack.pop(); // L0 empty stack
    assertThat(stack.size()).isEqualTo(0);
  }

  @Test
  public void stackTest() {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    assertThrows(RuntimeException.class, stack::pop);
  }

  @Test
  public void stackTest2() throws InterruptedException, SolverException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    stack.push();
    assertThat(stack.size()).isEqualTo(1);
    stack.pop();
    assertThat(stack.size()).isEqualTo(0);
  }

  @Test
  public void stackTest3() throws InterruptedException, SolverException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    stack.push();
    assertThat(stack.size()).isEqualTo(1);
    stack.pop();
    assertThat(stack.size()).isEqualTo(0);
    stack.push();
    assertThat(stack.size()).isEqualTo(1);
    stack.pop();
    assertThat(stack.size()).isEqualTo(0);
  }

  @Test
  public void stackTest4() throws InterruptedException, SolverException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    stack.push();
    stack.push();
    assertThat(stack.size()).isEqualTo(2);
    stack.pop();
    stack.pop();
    assertThat(stack.size()).isEqualTo(0);
  }

  @Test
  public void largeStackUsageTest() throws InterruptedException, SolverException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    for (int i = 0; i < 20; i++) {
      assertThat(stack.size()).isEqualTo(i);
      stack.push();
      stack.addConstraint(
          bmgr.equivalence(bmgr.makeVariable("X" + i), bmgr.makeVariable("X" + (i + 1))));
      stack.addConstraint(
          bmgr.equivalence(bmgr.makeVariable("Y" + i), bmgr.makeVariable("Y" + (i + 1))));
      stack.addConstraint(bmgr.equivalence(bmgr.makeVariable("X" + i), bmgr.makeVariable("Y" + i)));
    }
    assertThat(stack.isUnsat()).isFalse();
  }

  @Test
  public void largerStackUsageTest() throws InterruptedException, SolverException {
    int n = 1000;
    if (ImmutableList.of(Solvers.PRINCESS, Solvers.OPENSMT).contains(solverToUse())) {
      n = 50; // some solvers are slower, so we use a smaller number
    }

    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    for (int i = 0; i < n; i++) {
      assertThat(stack.size()).isEqualTo(i);
      stack.push();
      stack.addConstraint(
          bmgr.equivalence(bmgr.makeVariable("X" + i), bmgr.makeVariable("X" + (i + 1))));
      stack.addConstraint(
          bmgr.equivalence(bmgr.makeVariable("Y" + i), bmgr.makeVariable("Y" + (i + 1))));
      stack.addConstraint(bmgr.equivalence(bmgr.makeVariable("X" + i), bmgr.makeVariable("Y" + i)));
    }
    assertThat(stack.isUnsat()).isFalse();
  }

  @Test
  public void stackTest5() throws InterruptedException, SolverException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    stack.push();
    stack.pop();
    assertThat(stack.size()).isEqualTo(0);
    assertThrows(RuntimeException.class, stack::pop);
  }

  @Test
  public void stackTestUnsat() throws InterruptedException, SolverException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context, ProverOptions.GENERATE_MODELS);
    assertThat(stack).isSatisfiable();
    stack.push();
    stack.addConstraint(bmgr.makeFalse());
    assertThat(stack).isUnsatisfiable();
    stack.push();
    stack.addConstraint(bmgr.makeFalse());
    assertThat(stack.size()).isEqualTo(2);
    assertThat(stack).isUnsatisfiable();
    stack.pop();
    assertThat(stack).isUnsatisfiable();
    stack.pop();
    assertThat(stack.size()).isEqualTo(0);
    assertThat(stack).isSatisfiable();
  }

  @Test
  public void stackTestUnsat2() throws InterruptedException, SolverException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context, ProverOptions.GENERATE_MODELS);
    assertThat(stack).isSatisfiable();
    stack.push();
    stack.addConstraint(bmgr.makeTrue());
    assertThat(stack).isSatisfiable();
    stack.push();
    stack.addConstraint(bmgr.makeFalse());
    assertThat(stack).isUnsatisfiable();
    stack.push();
    assertThat(stack.size()).isEqualTo(3);
    stack.addConstraint(bmgr.makeFalse());
    assertThat(stack).isUnsatisfiable();
    stack.pop();
    assertThat(stack).isUnsatisfiable();
    stack.pop();
    assertThat(stack).isSatisfiable();
    stack.pop();
    assertThat(stack.size()).isEqualTo(0);
    assertThat(stack).isSatisfiable();
  }

  /** Create a symbol on a level and pop this level. Symbol must remain valid and usable! */
  @SuppressWarnings("unused")
  @Test
  public void symbolsOnStackTest() throws InterruptedException, SolverException {
    requireModel();

    BasicProverEnvironment<?> stack = newEnvironmentForTest(context, ProverOptions.GENERATE_MODELS);

    assertEquals(0, stack.size());
    stack.push();
    assertEquals(1, stack.size());
    BooleanFormula q1 = bmgr.makeVariable("q");
    stack.addConstraint(q1);
    assertThat(stack).isSatisfiable();
    Model m1 = stack.getModel();
    assertThat(m1.asList()).isNotEmpty();
    stack.pop();
    assertEquals(0, stack.size());

    stack.push();
    assertEquals(1, stack.size());
    BooleanFormula q2 = bmgr.makeVariable("q");
    assertThat(q2).isEqualTo(q1);
    stack.addConstraint(q1);
    assertThat(stack).isSatisfiable();
    Model m2 = stack.getModel();
    assertThat(m2.asList()).isNotEmpty();
    stack.pop();
    assertEquals(0, stack.size());
  }

  @Test
  public void constraintTestBool1() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("bool_a");

    try (BasicProverEnvironment<?> stack = newEnvironmentForTest(context)) {
      stack.addConstraint(a);
      assertThat(stack.size()).isEqualTo(0);
      assertThat(stack).isSatisfiable();
    }

    try (BasicProverEnvironment<?> stack2 = newEnvironmentForTest(context)) {
      stack2.addConstraint(bmgr.not(a));
      assertThat(stack2.size()).isEqualTo(0);
      assertThat(stack2).isSatisfiable();
    }
  }

  @Test
  public void constraintTestBool2() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("bool_a");

    try (BasicProverEnvironment<?> stack = newEnvironmentForTest(context)) {
      stack.push(a);
      assertThat(stack.size()).isEqualTo(1);
      assertThat(stack).isSatisfiable();
    }

    try (BasicProverEnvironment<?> stack2 = newEnvironmentForTest(context)) {
      stack2.addConstraint(bmgr.not(a));
      assertThat(stack2.size()).isEqualTo(0);
      assertThat(stack2).isSatisfiable();
    }
  }

  @Test
  public void constraintTestBool3() throws SolverException, InterruptedException {
    BooleanFormula a = bmgr.makeVariable("bool_a");

    try (BasicProverEnvironment<?> stack = newEnvironmentForTest(context)) {
      assertThat(stack.size()).isEqualTo(0);
      stack.push(a);
      assertThat(stack.size()).isEqualTo(1);
      assertThat(stack).isSatisfiable();
    }

    try (BasicProverEnvironment<?> stack2 = newEnvironmentForTest(context)) {
      assertThat(stack2.size()).isEqualTo(0);
      assertThrows(RuntimeException.class, stack2::pop);
    }
  }

  @Test
  public void constraintTestBool4() throws SolverException, InterruptedException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    stack.addConstraint(bmgr.makeVariable("bool_a"));
    assertThat(stack).isSatisfiable();
    assertThat(stack.size()).isEqualTo(0);
    assertThrows(RuntimeException.class, stack::pop);
  }

  @Test
  public void satTestBool5() throws SolverException, InterruptedException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context);
    assertThat(stack.size()).isEqualTo(0);
    assertThat(stack).isSatisfiable();
  }

  @Test
  public void dualStackTest() throws SolverException, InterruptedException {
    requireMultipleStackSupport();

    BooleanFormula a = bmgr.makeVariable("bool_a");
    BooleanFormula not = bmgr.not(a);

    BasicProverEnvironment<?> stack1 = newEnvironmentForTest(context);
    stack1.push(a); // L1
    stack1.push(a); // L2
    assertThat(stack1.size()).isEqualTo(2);
    BasicProverEnvironment<?> stack2 = newEnvironmentForTest(context);
    stack1.pop(); // L1
    stack1.pop(); // L0
    assertThat(stack1.size()).isEqualTo(0);

    stack1.push(a); // L1
    assertThat(stack1.size()).isEqualTo(1);
    assertThat(stack1).isSatisfiable();

    stack2.push(not); // L1
    assertThat(stack2.size()).isEqualTo(1);
    assertThat(stack2).isSatisfiable();

    stack1.pop(); // L0
    stack2.pop(); // L0
    assertThat(stack1.size()).isEqualTo(0);
    assertThat(stack2.size()).isEqualTo(0);
  }

  @Test
  public void dualStackTest2() throws SolverException, InterruptedException {
    requireMultipleStackSupport();

    BooleanFormula a = bmgr.makeVariable("bool_a");
    BooleanFormula not = bmgr.not(a);

    BasicProverEnvironment<?> stack1 = newEnvironmentForTest(context);
    BasicProverEnvironment<?> stack2 = newEnvironmentForTest(context);
    stack1.push(a); // L1
    stack1.push(bmgr.makeBoolean(true)); // L2
    assertThat(stack1).isSatisfiable();
    stack2.push(not); // L1
    assertThat(stack1.size()).isEqualTo(2);
    assertThat(stack2.size()).isEqualTo(1);
    assertThat(stack2).isSatisfiable();
    stack1.pop(); // L1
    assertThat(stack1).isSatisfiable();
    stack1.pop(); // L1
    assertThat(stack1).isSatisfiable();
    stack2.pop(); // L1
    assertThat(stack2).isSatisfiable();
    assertThat(stack1).isSatisfiable();
    assertThat(stack1.size()).isEqualTo(0);
    assertThat(stack2.size()).isEqualTo(0);
  }

  @Test
  public void multiStackTest() throws SolverException, InterruptedException {
    requireMultipleStackSupport();
    int limit = 10;

    BooleanFormula a = bmgr.makeVariable("bool_a");
    BooleanFormula not = bmgr.not(a);

    List<BasicProverEnvironment<?>> stacks = new ArrayList<>();
    for (int i = 0; i < limit; i++) {
      stacks.add(newEnvironmentForTest(context));
    }

    for (int i = 0; i < limit; i++) {
      stacks.get(i).push(a); // L1
      stacks.get(i).push(bmgr.makeBoolean(true));
      assertThat(stacks.get(i)).isSatisfiable();
      assertThat(stacks.get(i).size()).isEqualTo(2);

      stacks.get(i).push();
      stacks.get(i).push();
      assertThat(stacks.get(i).size()).isEqualTo(4);
      stacks.get(i).pop();
      stacks.get(i).pop();
    }

    for (int i = 0; i < limit; i++) {
      stacks.get(i).push(not);
      assertThat(stacks.get(i)).isUnsatisfiable();
      assertThat(stacks.get(i).size()).isEqualTo(3);
      stacks.get(i).pop();
      assertThat(stacks.get(i).size()).isEqualTo(2);
    }

    for (int i = 0; i < limit; i++) {
      stacks.get(i).pop();
      assertThat(stacks.get(i).size()).isEqualTo(1);
      stacks.get(i).close();
    }
  }

  @Test(expected = IllegalStateException.class)
  @SuppressWarnings("CheckReturnValue")
  public void avoidDualStacksIfNotSupported() throws InterruptedException, SolverException {
    assume()
        .withMessage("Solver does not support multiple stacks yet")
        .that(solver)
        .isEqualTo(Solvers.BOOLECTOR);

    BasicProverEnvironment<?> stack1 = newEnvironmentForTest(context);
    stack1.push(bmgr.makeTrue());

    // creating a new environment is not allowed with non-empty stack -> fail
    newEnvironmentForTest(context);
  }

  /**
   * This test checks that an SMT solver uses "global declarations": regardless of the stack at
   * declaration time, declarations always live for the full lifetime of the solver (i.e., they do
   * not get deleted on pop()). This is contrary to the SMTLib standard, but required by us, e.g.
   * for BMC with induction (where we create new formulas while there is something on the stack).
   */
  @Test
  public void dualStackGlobalDeclarations() throws SolverException, InterruptedException {
    // Create non-empty stack
    BasicProverEnvironment<?> stack1 = newEnvironmentForTest(context);
    stack1.push(bmgr.makeVariable("bool_a"));

    // Declare b while non-empty stack exists
    final String varName = "bool_b";
    final BooleanFormula b = bmgr.makeVariable(varName);

    // Clear stack (without global declarations b gets deleted)
    stack1.push(b);
    assertThat(stack1).isSatisfiable();
    stack1.pop();
    stack1.pop();
    assertThat(stack1.size()).isEqualTo(0);
    stack1.close();
    assertThrows(IllegalStateException.class, stack1::size);

    // Check that "b" (the reference to the old formula)
    // is equivalent to a new formula with the same variable
    assertThatFormula(b).isEquivalentTo(bmgr.makeVariable(varName));
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void modelForUnsatFormula() throws SolverException, InterruptedException {
    requireIntegers();
    try (BasicProverEnvironment<?> stack = newEnvironmentForTest(context)) {
      stack.push(imgr.greaterThan(imgr.makeVariable("a"), imgr.makeNumber(0)));
      stack.push(imgr.lessThan(imgr.makeVariable("a"), imgr.makeNumber(0)));
      assertThat(stack).isUnsatisfiable();

      assertThrows(Exception.class, stack::getModel);
    }
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void modelForUnsatFormula2() throws SolverException, InterruptedException {
    requireIntegers();
    try (BasicProverEnvironment<?> stack = newEnvironmentForTest(context)) {
      stack.push(imgr.greaterThan(imgr.makeVariable("a"), imgr.makeNumber(0)));
      assertThat(stack).isSatisfiable();
      stack.push(imgr.lessThan(imgr.makeVariable("a"), imgr.makeNumber(0)));
      assertThat(stack).isUnsatisfiable();

      assertThrows(Exception.class, stack::getModel);
    }
  }

  @Test
  public void modelForSatFormula() throws SolverException, InterruptedException {
    requireIntegers();
    try (BasicProverEnvironment<?> stack =
        newEnvironmentForTest(context, ProverOptions.GENERATE_MODELS)) {
      IntegerFormula a = imgr.makeVariable("a");
      stack.push(imgr.greaterThan(a, imgr.makeNumber(0)));
      stack.push(imgr.lessThan(a, imgr.makeNumber(2)));
      assertThat(stack).isSatisfiable();

      Model model = stack.getModel();
      assertThat(model.evaluate(a)).isEqualTo(BigInteger.ONE);
    }
  }

  @Test
  public void modelForSatFormulaWithLargeValue() throws SolverException, InterruptedException {
    requireIntegers();
    try (BasicProverEnvironment<?> stack =
        newEnvironmentForTest(context, ProverOptions.GENERATE_MODELS)) {
      BigInteger val = BigInteger.TEN.pow(1000);
      IntegerFormula a = imgr.makeVariable("a");
      stack.push(imgr.equal(a, imgr.makeNumber(val)));
      assertThat(stack).isSatisfiable();

      Model model = stack.getModel();
      assertThat(model.evaluate(a)).isEqualTo(val);
    }
  }

  @Test
  public void modelForSatFormulaWithUF() throws SolverException, InterruptedException {
    requireIntegers();
    requireTheoryCombination();

    try (BasicProverEnvironment<?> stack =
        newEnvironmentForTest(context, ProverOptions.GENERATE_MODELS)) {
      IntegerFormula zero = imgr.makeNumber(0);
      IntegerFormula varA = imgr.makeVariable("a");
      IntegerFormula varB = imgr.makeVariable("b");
      stack.push(imgr.equal(varA, zero));
      stack.push(imgr.equal(varB, zero));
      FunctionDeclaration<IntegerFormula> uf =
          fmgr.declareUF("uf", FormulaType.IntegerType, FormulaType.IntegerType);
      stack.push(imgr.equal(fmgr.callUF(uf, varB), zero));
      assertThat(stack).isSatisfiable();

      Model model = stack.getModel();

      // actual type of object is not defined, thus do string matching:
      assertThat(model.evaluate(varA)).isEqualTo(BigInteger.ZERO);
      assertThat(model.evaluate(varB)).isEqualTo(BigInteger.ZERO);

      requireUfValuesInModel();

      assertThat(model.evaluate(fmgr.callUF(uf, imgr.makeNumber(BigDecimal.ZERO))))
          .isEqualTo(BigInteger.ZERO);
    }
  }

  @Test
  @SuppressWarnings("resource")
  public void multiCloseTest() throws SolverException, InterruptedException {
    BasicProverEnvironment<?> stack = newEnvironmentForTest(context, ProverOptions.GENERATE_MODELS);
    try {
      // do something on the stack
      stack.push();
      stack.pop();
      stack.push(bmgr.equivalence(bmgr.makeVariable("a"), bmgr.makeTrue()));
      assertThat(stack).isSatisfiable();
      stack.push();

    } finally {
      // close the stack several times, closing should be idempotent
      for (int i = 0; i < 10; i++) {
        stack.close();
        assertThrows(IllegalStateException.class, stack::size);
        assertThrows(IllegalStateException.class, stack::push);
        assertThrows(IllegalStateException.class, stack::pop);
      }
    }
  }
}
