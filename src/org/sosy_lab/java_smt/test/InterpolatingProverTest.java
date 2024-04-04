// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.collect.Iterables.getLast;
import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import org.junit.Test;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.cvc5.CVC5BooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

/** This class contains some simple Junit-tests to check the interpolation-API of our solvers. */
@SuppressWarnings({"resource", "LocalVariableName"})
public class InterpolatingProverTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  // INFO: OpenSmt only support interpolation for QF_LIA, QF_LRA and QF_UF
  @Override
  protected Logics logicToUse() {
    return Logics.QF_LIA;
  }

  /** Generate a prover environment depending on the parameter above. */
  @SuppressWarnings("unchecked")
  private <T> InterpolatingProverEnvironment<T> newEnvironmentForTest() {
    requireInterpolation();
    return (InterpolatingProverEnvironment<T>) context.newProverEnvironmentWithInterpolation();
  }

  private static final UniqueIdGenerator index = new UniqueIdGenerator(); // to get different names

  @Test
  @SuppressWarnings("CheckReturnValue")
  public <T> void simpleInterpolation() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s runs into timeout on this test", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    try (InterpolatingProverEnvironment<T> prover = newEnvironmentForTest()) {
      IntegerFormula x = imgr.makeVariable("x");
      IntegerFormula y = imgr.makeVariable("y");
      /* INFO: Due to limitations in OpenSMT we need to use a simpler formular for this solver
       * Setting z=x means that the original formula `2x ≠ 1+2z`simplifies to `0 ≠ 1`,
       * which is trivially true.
       *
       * https://github.com/usi-verification-and-security/opensmt/issues/638
       */
      IntegerFormula z = solverToUse() == Solvers.OPENSMT ? x : imgr.makeVariable("z");

      BooleanFormula f1 = imgr.equal(y, imgr.multiply(imgr.makeNumber(2), x));
      BooleanFormula f2 =
          imgr.equal(y, imgr.add(imgr.makeNumber(1), imgr.multiply(z, imgr.makeNumber(2))));

      prover.push(f1);
      T id2 = prover.push(f2);
      boolean check = prover.isUnsat();

      assertWithMessage("formulas must be contradicting").that(check).isTrue();
      prover.getInterpolant(ImmutableList.of(id2));
      // we actually only check for a successful execution here, the result is irrelevant.
    }
  }

  @Test
  @SuppressWarnings("unchecked")
  public <T> void emptyInterpolationGroup() throws SolverException, InterruptedException {
    try (InterpolatingProverEnvironment<T> prover = newEnvironmentForTest()) {
      IntegerFormula x = imgr.makeVariable("x");
      IntegerFormula y = imgr.makeVariable("y");
      /* INFO: Due to limitations in OpenSMT we need to use a simpler formula for this solver
       * Setting z=x means that the original formula `2x ≠ 1+2z`simplifies to `0 ≠ 1`,
       * which is trivially true.
       *
       * https://github.com/usi-verification-and-security/opensmt/issues/638
       */
      IntegerFormula z = solverToUse() == Solvers.OPENSMT ? x : imgr.makeVariable("z");

      BooleanFormula f1 = imgr.equal(y, imgr.multiply(imgr.makeNumber(2), x));
      BooleanFormula f2 =
          imgr.equal(y, imgr.add(imgr.makeNumber(1), imgr.multiply(z, imgr.makeNumber(2))));
      T id1 = prover.push(f1);
      T id2 = prover.push(f2);
      assertThat(prover.isUnsat()).isTrue();

      BooleanFormula emptyB = prover.getInterpolant(ImmutableList.of(id1, id2));
      assertThat(bmgr.isFalse(emptyB)).isTrue();
      BooleanFormula emptyA = prover.getInterpolant(ImmutableList.of());
      assertThat(bmgr.isTrue(emptyA)).isTrue();
    }
  }

  @Test
  public <T> void binaryInterpolation() throws SolverException, InterruptedException {
    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);

    // build formula:  1 = A = B = C = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula C = imgr.equal(b, c);
    BooleanFormula D = imgr.equal(c, zero);

    T TA = stack.push(A);
    T TB = stack.push(B);
    T TC = stack.push(C);
    T TD = stack.push(D);

    assertThat(stack).isUnsatisfiable();

    BooleanFormula itp = stack.getInterpolant(ImmutableList.of());
    BooleanFormula itpA = stack.getInterpolant(ImmutableList.of(TA));
    BooleanFormula itpAB = stack.getInterpolant(ImmutableList.of(TA, TB));
    BooleanFormula itpABC = stack.getInterpolant(ImmutableList.of(TA, TB, TC));
    BooleanFormula itpD = stack.getInterpolant(ImmutableList.of(TD));
    BooleanFormula itpDC = stack.getInterpolant(ImmutableList.of(TD, TC));
    BooleanFormula itpDCB = stack.getInterpolant(ImmutableList.of(TD, TC, TB));
    BooleanFormula itpABCD = stack.getInterpolant(ImmutableList.of(TA, TB, TC, TD));

    stack.close();

    // special cases: start and end of sequence might need special handling in the solver
    assertThat(bmgr.makeBoolean(true)).isEqualTo(itp);
    assertThat(bmgr.makeBoolean(false)).isEqualTo(itpABCD);

    // we check here the stricter properties for sequential interpolants,
    // but this simple example should work for all solvers
    checkItpSequence(ImmutableList.of(A, B, C, D), ImmutableList.of(itpA, itpAB, itpABC));
    checkItpSequence(ImmutableList.of(D, C, B, A), ImmutableList.of(itpD, itpDC, itpDCB));
  }

  @Test
  public <T> void binaryInterpolationWithConstantFalse()
      throws SolverException, InterruptedException {
    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    // build formula:  [false, false]
    BooleanFormula A = bmgr.makeBoolean(false);
    BooleanFormula B = bmgr.makeBoolean(false);
    BooleanFormula C = bmgr.makeBoolean(false);

    T TA = stack.push(A);
    T TB = stack.push(B);
    T TC = stack.push(C);

    assertThat(stack).isUnsatisfiable();

    assertThat(stack.getInterpolant(ImmutableList.of())).isEqualTo(bmgr.makeBoolean(true));
    // some interpolant needs to be FALSE, however, it can be at arbitrary position.
    assertThat(
            ImmutableList.of(
                stack.getInterpolant(ImmutableList.of(TA)),
                stack.getInterpolant(ImmutableList.of(TB)),
                stack.getInterpolant(ImmutableList.of(TC))))
        .contains(bmgr.makeBoolean(false));
    assertThat(
            ImmutableList.of(
                stack.getInterpolant(ImmutableList.of(TA, TB)),
                stack.getInterpolant(ImmutableList.of(TB, TC)),
                stack.getInterpolant(ImmutableList.of(TC, TA))))
        .contains(bmgr.makeBoolean(false));
    assertThat(stack.getInterpolant(ImmutableList.of(TA, TB, TC)))
        .isEqualTo(bmgr.makeBoolean(false));

    stack.close();
  }

  @Test
  public <T> void binaryBVInterpolation1() throws SolverException, InterruptedException {
    requireBitvectors();

    assume()
        .withMessage("Solver %s runs into timeout on this test", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();
    int width = 8;

    BitvectorFormula n130 = bvmgr.makeBitvector(width, 130);

    BitvectorFormula a = bvmgr.makeVariable(width, "a" + i);
    BitvectorFormula b = bvmgr.makeVariable(width, "b" + i);
    BitvectorFormula c = bvmgr.makeVariable(width, "c" + i);

    // build formula:  b = a + 130, b > a, c = b + 130, c > b
    BooleanFormula A = bvmgr.equal(b, bvmgr.add(a, n130));
    BooleanFormula B = bvmgr.greaterThan(b, a, false);
    BooleanFormula C = bvmgr.equal(c, bvmgr.add(b, n130));
    BooleanFormula D = bvmgr.greaterThan(c, b, false);

    T TA = stack.push(A);
    T TB = stack.push(B);
    T TC = stack.push(C);
    T TD = stack.push(D);

    assertThat(stack).isUnsatisfiable();

    BooleanFormula itp = stack.getInterpolant(ImmutableList.of());
    BooleanFormula itpA = stack.getInterpolant(ImmutableList.of(TA));
    BooleanFormula itpAB = stack.getInterpolant(ImmutableList.of(TA, TB));
    BooleanFormula itpABC = stack.getInterpolant(ImmutableList.of(TA, TB, TC));
    BooleanFormula itpD = stack.getInterpolant(ImmutableList.of(TD));
    BooleanFormula itpDC = stack.getInterpolant(ImmutableList.of(TD, TC));
    BooleanFormula itpDCB = stack.getInterpolant(ImmutableList.of(TD, TC, TB));
    BooleanFormula itpABCD = stack.getInterpolant(ImmutableList.of(TA, TB, TC, TD));

    stack.close();

    // special cases: start and end of sequence might need special handling in the solver
    assertThat(bmgr.makeBoolean(true)).isEqualTo(itp);
    assertThat(bmgr.makeBoolean(false)).isEqualTo(itpABCD);

    // we check here the stricter properties for sequential interpolants,
    // but this simple example should work for all solvers
    checkItpSequence(ImmutableList.of(A, B, C, D), ImmutableList.of(itpA, itpAB, itpABC));
    checkItpSequence(ImmutableList.of(D, C, B, A), ImmutableList.of(itpD, itpDC, itpDCB));
  }

  private void requireTreeItp() {
    requireInterpolation();
    assume()
        .withMessage("Solver does not support tree-interpolation.")
        .that(solver)
        .isAnyOf(Solvers.SMTINTERPOL, Solvers.PRINCESS);
  }

  @Test
  public <T> void sequentialInterpolation() throws SolverException, InterruptedException {
    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    requireIntegers();

    assume()
        .withMessage("Solver %s runs into timeout on this test", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);

    // build formula:  1 = A = B = C = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula C = imgr.equal(b, c);
    BooleanFormula D = imgr.equal(c, zero);

    T TA = stack.push(A);
    T TB = stack.push(B);
    T TC = stack.push(C);
    T TD = stack.push(D);

    assertThat(stack).isUnsatisfiable();

    List<BooleanFormula> itps1 = stack.getSeqInterpolants0(ImmutableList.of(TA, TB, TC, TD));
    List<BooleanFormula> itps2 = stack.getSeqInterpolants0(ImmutableList.of(TD, TC, TB, TA));
    List<BooleanFormula> itps3 = stack.getSeqInterpolants0(ImmutableList.of(TA, TC, TB, TD));
    List<BooleanFormula> itps4 =
        stack.getSeqInterpolants(
            Lists.transform(ImmutableList.of(TA, TA, TA, TB, TC, TD, TD), ImmutableSet::of));
    List<BooleanFormula> itps5 =
        stack.getSeqInterpolants(
            Lists.transform(ImmutableList.of(TA, TA, TB, TC, TD, TA, TD), ImmutableSet::of));
    List<BooleanFormula> itps6 =
        stack.getSeqInterpolants(
            Lists.transform(ImmutableList.of(TB, TC, TD, TA, TA, TA, TD), ImmutableSet::of));

    stack.close();

    checkItpSequence(ImmutableList.of(A, B, C, D), itps1);
    checkItpSequence(ImmutableList.of(D, C, B, A), itps2);
    checkItpSequence(ImmutableList.of(A, C, B, D), itps3);
    checkItpSequence(ImmutableList.of(A, A, A, B, C, D, D), itps4);
    checkItpSequence(ImmutableList.of(A, A, B, C, D, A, D), itps5);
    checkItpSequence(ImmutableList.of(B, C, D, A, A, A, D), itps6);
  }

  @Test
  public <T> void sequentialInterpolationIsNotRepeatedIndividualInterpolation()
      throws SolverException, InterruptedException {
    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    requireIntegers();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula thousand = imgr.makeNumber(1000);

    IntegerFormula i3 = imgr.makeVariable("i3");
    IntegerFormula i4 = imgr.makeVariable("i4");

    BooleanFormula A = imgr.equal(i3, zero);
    BooleanFormula B = bmgr.and(imgr.lessThan(i3, thousand), imgr.equal(i4, imgr.add(i3, one)));
    BooleanFormula C = imgr.greaterThan(i4, thousand);

    T TA = stack.push(A);
    T TB = stack.push(B);
    T TC = stack.push(C);

    assertThat(stack).isUnsatisfiable();

    List<BooleanFormula> itpSeq = stack.getSeqInterpolants0(ImmutableList.of(TA, TB, TC));

    BooleanFormula itp1 = stack.getInterpolant(ImmutableList.of(TA));
    BooleanFormula itp2 = stack.getInterpolant(ImmutableList.of(TA, TB));

    stack.close();

    // sequential interpolation should always work as expected
    checkItpSequence(ImmutableList.of(A, B, C), itpSeq);

    if (solverToUse() == Solvers.CVC5) {
      assertThatFormula(A).implies(itp1);
      assertThatFormula(bmgr.and(A, B)).implies(itp2);
      assertThatFormula(bmgr.and(itp1, B, C)).isUnsatisfiable();
      assertThatFormula(bmgr.and(itp2, C)).isUnsatisfiable();

      // this is a counterexample for sequential interpolation via individual interpolants:
      assertThatFormula(bmgr.not(bmgr.implication(bmgr.and(itp1, B), itp2))).isSatisfiable();

    } else {
      // other solvers satisfy this condition,
      // because they internally use the same proof for all interpolation queries
      checkItpSequence(ImmutableList.of(A, B, C), List.of(itp1, itp2));
    }
  }

  @Test
  public <T> void sequentialInterpolationWithoutPartition()
      throws SolverException, InterruptedException {
    requireIntegers();
    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    stack.push(imgr.equal(imgr.makeNumber(0), imgr.makeNumber(1)));
    assertThat(stack).isUnsatisfiable();

    // empty list of partition
    assertThrows(
        IllegalArgumentException.class, () -> stack.getSeqInterpolants(ImmutableList.of()));
  }

  @Test
  public <T> void sequentialInterpolationWithOnePartition()
      throws SolverException, InterruptedException {
    requireIntegers();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula a = imgr.makeVariable("a" + i);

    // build formula:  1 = A = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, zero);

    T TA = stack.push(A);
    T TB = stack.push(B);

    assertThat(stack).isUnsatisfiable();

    // list of one partition
    List<T> partition = ImmutableList.of(TA, TB);
    List<BooleanFormula> itps = stack.getSeqInterpolants(ImmutableList.of(partition));
    assertThat(itps).isEmpty();
  }

  @SuppressWarnings("unchecked")
  @Test
  public <T> void sequentialInterpolationWithFewPartitions()
      throws SolverException, InterruptedException {
    requireIntegers();
    assume().that(solverToUse()).isNotEqualTo(Solvers.CVC5); // Will run forever

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula a = imgr.makeVariable("a" + i);

    // build formula:  1 = A = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, zero);

    T TA = stack.push(A);
    T TB = stack.push(B);

    assertThat(stack).isUnsatisfiable();

    Set<T> partition = ImmutableSet.of(TA, TB);
    List<BooleanFormula> itps1 = stack.getSeqInterpolants(ImmutableList.of(partition));
    List<BooleanFormula> itps2 = stack.getSeqInterpolants0(ImmutableList.of(TA, TB));
    List<BooleanFormula> itps3 = stack.getSeqInterpolants0(ImmutableList.of(TB, TA));

    stack.close();

    checkItpSequence(ImmutableList.of(bmgr.and(A, B)), itps1);
    checkItpSequence(ImmutableList.of(A, B), itps2);
    checkItpSequence(ImmutableList.of(B, A), itps3);
  }

  @Test
  public <T> void sequentialBVInterpolation() throws SolverException, InterruptedException {
    requireBitvectors();

    assume()
        .withMessage("Solver %s runs into timeout on this test", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();
    int width = 8;

    BitvectorFormula zero = bvmgr.makeBitvector(width, 0);
    BitvectorFormula one = bvmgr.makeBitvector(width, 1);

    BitvectorFormula a = bvmgr.makeVariable(width, "a" + i);
    BitvectorFormula b = bvmgr.makeVariable(width, "b" + i);
    BitvectorFormula c = bvmgr.makeVariable(width, "c" + i);

    // build formula:  1 = A = B = C = 0
    BooleanFormula A = bvmgr.equal(one, a);
    BooleanFormula B = bvmgr.equal(a, b);
    BooleanFormula C = bvmgr.equal(b, c);
    BooleanFormula D = bvmgr.equal(c, zero);

    T TA = stack.push(A);
    T TB = stack.push(B);
    T TC = stack.push(C);
    T TD = stack.push(D);

    assertThat(stack).isUnsatisfiable();

    List<BooleanFormula> itps1 = stack.getSeqInterpolants0(ImmutableList.of(TA, TB, TC, TD));
    List<BooleanFormula> itps2 = stack.getSeqInterpolants0(ImmutableList.of(TD, TC, TB, TA));
    List<BooleanFormula> itps3 = stack.getSeqInterpolants0(ImmutableList.of(TA, TC, TB, TD));
    List<BooleanFormula> itps4 =
        stack.getSeqInterpolants0(ImmutableList.of(TA, TA, TA, TB, TC, TD, TD));
    List<BooleanFormula> itps5 =
        stack.getSeqInterpolants0(ImmutableList.of(TA, TA, TB, TC, TD, TA, TD));
    List<BooleanFormula> itps6 =
        stack.getSeqInterpolants0(ImmutableList.of(TB, TC, TD, TA, TA, TA, TD));

    stack.close();

    checkItpSequence(ImmutableList.of(A, B, C, D), itps1);
    checkItpSequence(ImmutableList.of(D, C, B, A), itps2);
    checkItpSequence(ImmutableList.of(A, C, B, D), itps3);
    checkItpSequence(ImmutableList.of(A, A, A, B, C, D, D), itps4);
    checkItpSequence(ImmutableList.of(A, A, B, C, D, A, D), itps5);
    checkItpSequence(ImmutableList.of(B, C, D, A, A, A, D), itps6);
  }

  @Test
  public void treeInterpolation() throws SolverException, InterruptedException {

    requireTreeItp();

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);
    IntegerFormula d = imgr.makeVariable("d" + i);

    // build formula:  1 = A = B = C = D = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula C = imgr.equal(b, c);
    BooleanFormula D = imgr.equal(c, d);
    BooleanFormula E = imgr.equal(d, zero);

    testTreeInterpolants0(A, B, C, D, E);
    testTreeInterpolants0(A, B, C, E, D);
    testTreeInterpolants0(A, B, D, C, E);
    testTreeInterpolants0(A, B, D, E, C);
    testTreeInterpolants0(A, B, E, C, D);
    testTreeInterpolants0(A, B, E, D, C);

    testTreeInterpolants0(bmgr.not(A), A, A, A, A);
    testTreeInterpolants0(bmgr.not(A), A, A, A, B);
    testTreeInterpolants0(bmgr.not(A), A, A, B, A);
    testTreeInterpolants0(bmgr.not(A), A, B, A, A);
    testTreeInterpolants0(bmgr.not(A), A, A, B, B);
    testTreeInterpolants0(bmgr.not(A), A, B, B, B);

    testTreeInterpolants1(A, B, C, D, E);
    testTreeInterpolants1(A, B, C, E, D);
    testTreeInterpolants1(A, B, D, C, E);
    testTreeInterpolants1(A, B, D, E, C);
    testTreeInterpolants1(A, B, E, C, D);
    testTreeInterpolants1(A, B, E, D, C);

    testTreeInterpolants1(bmgr.not(A), A, A, A, A);
    testTreeInterpolants1(bmgr.not(A), A, A, A, B);
    testTreeInterpolants1(bmgr.not(A), A, A, B, A);
    testTreeInterpolants1(bmgr.not(A), A, B, A, A);
    testTreeInterpolants1(bmgr.not(A), A, A, B, B);
    testTreeInterpolants1(bmgr.not(A), A, B, B, B);

    testTreeInterpolants2(A, B, C, D, E);
    testTreeInterpolants2(A, B, C, E, D);
    testTreeInterpolants2(A, B, D, C, E);
    testTreeInterpolants2(A, B, D, E, C);
    testTreeInterpolants2(A, B, E, C, D);
    testTreeInterpolants2(A, B, E, D, C);

    testTreeInterpolants2(bmgr.not(A), A, A, A, A);
    testTreeInterpolants2(bmgr.not(A), A, A, A, B);
    testTreeInterpolants2(bmgr.not(A), A, A, B, A);
    testTreeInterpolants2(bmgr.not(A), A, B, A, A);
    testTreeInterpolants2(bmgr.not(A), A, A, B, B);
    testTreeInterpolants2(bmgr.not(A), A, B, B, B);
  }

  private <T> void testTreeInterpolants0(
      BooleanFormula pA, BooleanFormula pB, BooleanFormula pC, BooleanFormula pD, BooleanFormula pE)
      throws SolverException, InterruptedException {

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    T TA = stack.push(pA);
    T TB = stack.push(pB);
    T TC = stack.push(pC);
    T TD = stack.push(pD);
    T TE = stack.push(pE);

    assertThat(stack).isUnsatisfiable();

    // we build a very simple tree:
    // A  D
    // |  |
    // B  E
    // | /
    // C
    List<BooleanFormula> itps =
        stack.getTreeInterpolants0(
            ImmutableList.of(TA, TB, TD, TE, TC), // post-order
            new int[] {0, 0, 2, 2, 0}); // left-most node in current subtree

    stack.close();

    assertThatFormula(pA).implies(itps.get(0));
    assertThatFormula(bmgr.and(itps.get(0), pB)).implies(itps.get(1));
    assertThatFormula(pD).implies(itps.get(2));
    assertThatFormula(bmgr.and(itps.get(2), pE)).implies(itps.get(3));
    assertThatFormula(bmgr.and(itps.get(1), itps.get(3), pC)).implies(bmgr.makeBoolean(false));
  }

  private <T> void testTreeInterpolants1(
      BooleanFormula pA, BooleanFormula pB, BooleanFormula pC, BooleanFormula pD, BooleanFormula pE)
      throws SolverException, InterruptedException {

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    T TA = stack.push(pA);
    T TB = stack.push(pB);
    T TC = stack.push(pC);
    T TD = stack.push(pD);
    T TE = stack.push(pE);

    assertThat(stack).isUnsatisfiable();

    // we build a simple tree:
    // ABCD
    // \|//
    //  E
    List<BooleanFormula> itps =
        stack.getTreeInterpolants0(
            ImmutableList.of(TA, TB, TC, TD, TE), // post-order
            new int[] {0, 1, 2, 3, 0}); // left-most node in current subtree

    stack.close();

    assertThatFormula(pA).implies(itps.get(0));
    assertThatFormula(pB).implies(itps.get(1));
    assertThatFormula(pC).implies(itps.get(2));
    assertThatFormula(pD).implies(itps.get(3));
    assertThatFormula(bmgr.and(itps.get(0), itps.get(1), itps.get(2), itps.get(3), pE))
        .implies(bmgr.makeBoolean(false));
  }

  private <T> void testTreeInterpolants2(
      BooleanFormula pA, BooleanFormula pB, BooleanFormula pC, BooleanFormula pD, BooleanFormula pE)
      throws SolverException, InterruptedException {

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    T TA = stack.push(pA);
    T TB = stack.push(pB);
    T TC = stack.push(pC);
    T TD = stack.push(pD);
    T TE = stack.push(pE);

    assertThat(stack).isUnsatisfiable();

    // we build a simple degenerated tree:
    // A
    // |
    // B
    // |
    // C
    // |
    // D
    // |
    // E
    List<BooleanFormula> itps =
        stack.getTreeInterpolants0(
            ImmutableList.of(TA, TB, TC, TD, TE), // post-order
            new int[] {0, 0, 0, 0, 0}); // left-most node in current subtree

    stack.close();

    assertThatFormula(pA).implies(itps.get(0));
    assertThatFormula(bmgr.and(itps.get(0), pB)).implies(itps.get(1));
    assertThatFormula(bmgr.and(itps.get(1), pC)).implies(itps.get(2));
    assertThatFormula(bmgr.and(itps.get(2), pD)).implies(itps.get(3));
    assertThatFormula(bmgr.and(itps.get(3), pE)).implies(bmgr.makeBoolean(false));
  }

  @Test
  public <T> void treeInterpolation2() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula five = imgr.makeNumber(5);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);
    IntegerFormula d = imgr.makeVariable("d" + i);
    IntegerFormula e = imgr.makeVariable("e" + i);

    // build formula:  1 = A = B = C = D+1 and D = E = 5
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula R1 = imgr.equal(b, c);
    BooleanFormula C = imgr.equal(c, imgr.add(d, one));
    BooleanFormula R2 = imgr.equal(d, e);
    BooleanFormula D = imgr.equal(e, five);

    T TA = stack.push(A);
    T TB = stack.push(B);
    T TC = stack.push(C);
    T TD = stack.push(D);
    T TR1 = stack.push(R1);
    T TR2 = stack.push(R2);

    assertThat(stack).isUnsatisfiable();

    // we build a simple tree:
    // A
    // |
    // B  C
    // | /
    // R1 D
    // | /
    // R2
    List<BooleanFormula> itps =
        stack.getTreeInterpolants0(
            ImmutableList.of(TA, TB, TC, TR1, TD, TR2), // post-order
            new int[] {0, 0, 2, 0, 4, 0}); // left-most node in current subtree

    stack.close();

    assertThatFormula(A).implies(itps.get(0));
    assertThatFormula(bmgr.and(itps.get(0), B)).implies(itps.get(1));
    assertThatFormula(C).implies(itps.get(2));
    assertThatFormula(bmgr.and(itps.get(1), itps.get(2), R1)).implies(itps.get(3));
    assertThatFormula(D).implies(itps.get(4));
    assertThatFormula(bmgr.and(itps.get(3), itps.get(4), R2)).implies(bmgr.makeBoolean(false));
  }

  @SuppressWarnings("unchecked")
  @Test
  public <T> void treeInterpolation3() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula five = imgr.makeNumber(5);

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);
    IntegerFormula d = imgr.makeVariable("d" + i);
    IntegerFormula e = imgr.makeVariable("e" + i);

    // build formula:  1 = A = B = C = D+1 and D = E = 5
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula R1 = imgr.equal(b, c);
    BooleanFormula C = imgr.equal(c, imgr.add(d, one));
    BooleanFormula R2 = imgr.equal(d, e);
    BooleanFormula D = imgr.equal(e, five);

    Set<T> TB = ImmutableSet.of(stack.push(A), stack.push(B));
    Set<T> TR1 = ImmutableSet.of(stack.push(R1));
    Set<T> TC = ImmutableSet.of(stack.push(A), stack.push(C));
    Set<T> TR2 = ImmutableSet.of(stack.push(R2));
    Set<T> TD = ImmutableSet.of(stack.push(A), stack.push(D));

    assertThat(stack).isUnsatisfiable();

    // we build a simple tree:
    // A+B A+C
    //  | /
    //  R1 A+D
    //  | /
    //  R2
    List<BooleanFormula> itps =
        stack.getTreeInterpolants(
            ImmutableList.of(TB, TC, TR1, TD, TR2), // post-order
            new int[] {0, 1, 0, 3, 0}); // left-most node in current subtree

    assertThat(itps).hasSize(4);

    stack.close();

    assertThatFormula(bmgr.and(A, B)).implies(itps.get(0));
    assertThatFormula(bmgr.and(A, C)).implies(itps.get(1));
    assertThatFormula(bmgr.and(itps.get(0), itps.get(1), R1)).implies(itps.get(2));
    assertThatFormula(bmgr.and(A, D)).implies(itps.get(3));
    assertThatFormula(bmgr.and(itps.get(2), itps.get(3), R2)).implies(bmgr.makeBoolean(false));
  }

  @Test
  public <T> void treeInterpolation4() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);

    // build formula: a=9 & b+c=a & b=1 & c=2
    BooleanFormula bEquals1 = imgr.equal(b, imgr.makeNumber(1));
    BooleanFormula cEquals2 = imgr.equal(c, imgr.makeNumber(2));
    BooleanFormula bPlusCEqualsA = imgr.equal(imgr.add(b, c), a);
    BooleanFormula aEquals9 = imgr.equal(a, imgr.makeNumber(9));

    T TbEquals1 = stack.push(bEquals1);
    T TcEquals2 = stack.push(cEquals2);
    T TbPlusCEqualsA = stack.push(bPlusCEqualsA);
    T TaEquals9 = stack.push(aEquals9);

    assertThat(stack).isUnsatisfiable();

    // we build a simple tree:
    // b=1 c=2
    // | /
    // b+c=a
    // |
    // a=9
    List<BooleanFormula> itps =
        stack.getTreeInterpolants0(
            ImmutableList.of(TbEquals1, TcEquals2, TbPlusCEqualsA, TaEquals9), // post-order
            new int[] {0, 1, 0, 0}); // left-most node in current subtree

    assertThat(itps).hasSize(3);

    stack.close();

    assertThatFormula(bEquals1).implies(itps.get(0));
    assertThatFormula(cEquals2).implies(itps.get(1));
    assertThatFormula(bmgr.and(itps.get(0), itps.get(1), bPlusCEqualsA)).implies(itps.get(2));
    assertThatFormula(bmgr.and(itps.get(2), aEquals9)).implies(bmgr.makeBoolean(false));
  }

  @Test
  public <T> void treeInterpolationForSequence() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula a = imgr.makeVariable("a" + i);

    // build formula: 1 = A = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, zero);

    List<T> formulas = ImmutableList.of(stack.push(A), stack.push(B));

    assertThat(stack).isUnsatisfiable();

    List<BooleanFormula> itp = stack.getTreeInterpolants0(formulas, new int[] {0, 0});
    assertThat(itp).hasSize(1);
  }

  @Test
  public <T> void treeInterpolationBranching() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula a = imgr.makeVariable("a" + i);
    IntegerFormula b = imgr.makeVariable("b" + i);
    IntegerFormula c = imgr.makeVariable("c" + i);
    IntegerFormula d = imgr.makeVariable("d" + i);
    IntegerFormula e = imgr.makeVariable("e" + i);

    // build formula: 1 = A = B = C = D = E = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, b);
    BooleanFormula C = imgr.equal(b, c);
    BooleanFormula D = imgr.equal(c, d);
    BooleanFormula E = imgr.equal(d, e);
    BooleanFormula F = imgr.equal(e, zero);

    List<T> formulas =
        ImmutableList.of(
            stack.push(A),
            stack.push(B),
            stack.push(C),
            stack.push(D),
            stack.push(E),
            stack.push(F));

    assertThat(stack).isUnsatisfiable();

    List<BooleanFormula> itp = stack.getTreeInterpolants0(formulas, new int[] {0, 1, 2, 3, 4, 0});
    assertThat(itp).hasSize(5);
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings({"unchecked", "varargs", "CheckReturnValue"})
  public <T> void treeInterpolationMalFormed1() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    BooleanFormula A = imgr.equal(imgr.makeNumber(0), imgr.makeNumber(1));
    Set<T> TA = ImmutableSet.of(stack.push(A));
    assertThat(stack).isUnsatisfiable();

    stack.getTreeInterpolants(ImmutableList.of(TA), new int[] {0, 0});
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings({"unchecked", "varargs", "CheckReturnValue"})
  public <T> void treeInterpolationMalFormed2() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    BooleanFormula A = imgr.equal(imgr.makeNumber(0), imgr.makeNumber(1));
    Set<T> TA = ImmutableSet.of(stack.push(A));
    assertThat(stack).isUnsatisfiable();

    stack.getTreeInterpolants(ImmutableList.of(TA), new int[] {4});
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings({"unchecked", "varargs", "CheckReturnValue"})
  public <T> void treeInterpolationMalFormed3() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    BooleanFormula A = imgr.equal(imgr.makeNumber(0), imgr.makeNumber(1));
    Set<T> TA = ImmutableSet.of(stack.push(A));
    assertThat(stack).isUnsatisfiable();

    stack.getTreeInterpolants(ImmutableList.of(TA, TA), new int[] {1, 0});
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings("CheckReturnValue")
  public <T> void treeInterpolationMalFormed4() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    BooleanFormula A = imgr.equal(imgr.makeNumber(0), imgr.makeNumber(1));
    T TA = stack.push(A);
    assertThat(stack).isUnsatisfiable();

    stack.getTreeInterpolants0(ImmutableList.of(TA, TA, TA), new int[] {0, 1, 1});
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings("CheckReturnValue")
  public <T> void treeInterpolationMalFormed5() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    BooleanFormula A = imgr.equal(imgr.makeNumber(0), imgr.makeNumber(1));
    T TA = stack.push(A);
    assertThat(stack).isUnsatisfiable();

    stack.getTreeInterpolants0(ImmutableList.of(TA, TA, TA), new int[] {0, 1, 2});
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings("CheckReturnValue")
  public <T> void treeInterpolationMalFormed6() throws SolverException, InterruptedException {

    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    BooleanFormula A = imgr.equal(imgr.makeNumber(0), imgr.makeNumber(1));
    T TA = stack.push(A);
    assertThat(stack).isUnsatisfiable();

    stack.getTreeInterpolants0(ImmutableList.of(TA, TA, TA), new int[] {0, 2, 0});
  }

  @Test
  public <T> void treeInterpolationWithoutPartition() throws SolverException, InterruptedException {
    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    stack.push(imgr.equal(imgr.makeNumber(0), imgr.makeNumber(1)));
    assertThat(stack).isUnsatisfiable();

    // empty list of partition
    assertThrows(
        IllegalArgumentException.class,
        () -> stack.getTreeInterpolants(ImmutableList.of(), new int[] {}));
  }

  @Test
  public <T> void treeInterpolationWithOnePartition() throws SolverException, InterruptedException {
    requireTreeItp();

    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    int i = index.getFreshId();

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    IntegerFormula a = imgr.makeVariable("a" + i);

    // build formula:  1 = A = 0
    BooleanFormula A = imgr.equal(one, a);
    BooleanFormula B = imgr.equal(a, zero);

    T TA = stack.push(A);
    T TB = stack.push(B);

    assertThat(stack).isUnsatisfiable();

    // list of one partition
    List<T> partition = ImmutableList.of(TA, TB);
    List<BooleanFormula> itps =
        stack.getTreeInterpolants(ImmutableList.of(partition), new int[] {0});
    assertThat(itps).isEmpty();
  }

  @Test
  public <T> void bigSeqInterpolationTest() throws InterruptedException, SolverException {
    requireBitvectors();
    requireInterpolation();

    assume()
        .withMessage("Solver %s runs into timeout on this test", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    int bvWidth = 32;
    BitvectorFormula bv0 = bvmgr.makeBitvector(bvWidth, 0);
    BitvectorFormula bv1 = bvmgr.makeBitvector(bvWidth, 1);
    BitvectorFormula bv2 = bvmgr.makeBitvector(bvWidth, 2);
    BitvectorFormula bv4 = bvmgr.makeBitvector(bvWidth, 4);
    BitvectorFormula bv8 = bvmgr.makeBitvector(bvWidth, 8);

    BitvectorFormula t2 = bvmgr.makeVariable(bvWidth, "tmp3");
    BitvectorFormula p = bvmgr.makeVariable(bvWidth, "ADDRESS_OF_main::pathbuf");
    BitvectorFormula p2 = bvmgr.makeVariable(bvWidth, "glob2::pathbuf2");
    BitvectorFormula p3 = bvmgr.makeVariable(bvWidth, "glob2::p3");
    BitvectorFormula p4 = bvmgr.makeVariable(bvWidth, "glob2::pathlim2");
    BitvectorFormula b = bvmgr.makeVariable(bvWidth, "main::bound2");
    BitvectorFormula c = bvmgr.makeVariable(bvWidth, "VERIFIER_assert::cond2");

    BooleanFormula f1Internal1 =
        bmgr.and(
            bvmgr.lessThan(bv0, p, true),
            bvmgr.equal(bvmgr.remainder(p, bv4, false), bvmgr.remainder(bv0, bv4, false)),
            bvmgr.lessThan(bv0, bvmgr.add(p, bv8), true));

    BooleanFormula f1Internal2 =
        bvmgr.equal(bvmgr.remainder(p, bv4, false), bvmgr.remainder(bv0, bv4, false));

    BooleanFormula f1Internal3 = bvmgr.lessThan(bv0, bvmgr.add(p, bv8), true);

    BooleanFormula f1Internal5 =
        bvmgr.equal(
            b, bvmgr.subtract(bvmgr.add(p, bvmgr.multiply(bv2, bv4)), bvmgr.multiply(bv1, bv4)));

    BooleanFormula f1Internal6 =
        bvmgr.equal(
            t2, bvmgr.subtract(bvmgr.add(p, bvmgr.multiply(bv2, bv4)), bvmgr.multiply(bv1, bv4)));

    BooleanFormula f1Internal7 = bvmgr.equal(p2, p);

    BooleanFormula f1 =
        bmgr.and(
            f1Internal1,
            f1Internal2,
            f1Internal3,
            f1Internal5,
            f1Internal6,
            f1Internal7,
            bvmgr.equal(p3, p2));

    BooleanFormula f2 =
        bmgr.and(
            bvmgr.lessOrEquals(p3, p4, true),
            bvmgr.equal(c, bmgr.ifThenElse(bvmgr.lessOrEquals(p3, t2, true), bv1, bv0)),
            bvmgr.equal(c, bv0));

    try (InterpolatingProverEnvironment<T> prover = newEnvironmentForTest()) {
      T id1 = prover.push(f2);
      T id2 = prover.push(f1);
      assertThat(prover).isUnsatisfiable();
      @SuppressWarnings("unused")
      List<BooleanFormula> interpolants = prover.getSeqInterpolants0(ImmutableList.of(id1, id2));
    }
  }

  @Test
  public <T> void testTrivialInterpolation() throws InterruptedException, SolverException {
    requireInterpolation();
    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();
    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");

    // build formula "1 = A = 0", then check interpolant
    BooleanFormula A = bmgr.and(imgr.equal(a, zero), imgr.equal(a, one));
    T p1 = stack.push(A);
    assertThat(stack).isUnsatisfiable();
    BooleanFormula interpol1 = stack.getInterpolant(ImmutableList.of(p1));
    assertThatFormula(interpol1).isEqualTo(bmgr.makeFalse());
    stack.pop();

    // build formulas "a < 0" and "b < 0 && 1 < b", then check interpolant
    BooleanFormula B1 = imgr.lessThan(a, zero);
    BooleanFormula B2 = bmgr.and(imgr.lessThan(b, zero), imgr.lessThan(one, b));
    T p2 = stack.push(B1);
    stack.push(B2);
    assertThat(stack).isUnsatisfiable();
    BooleanFormula interpol2 = stack.getInterpolant(ImmutableList.of(p2));
    assertThatFormula(interpol2).isEqualTo(bmgr.makeTrue());
  }

  private void checkItpSequence(List<BooleanFormula> formulas, List<BooleanFormula> itps)
      throws SolverException, InterruptedException {

    assertWithMessage(
            "there should be N-1 interpolants for N formulas, but we got %s for %s", itps, formulas)
        .that(formulas.size() - 1 == itps.size())
        .isTrue();

    if (!itps.isEmpty()) {
      assertThatFormula(formulas.get(0)).implies(itps.get(0));
      for (int i = 1; i < formulas.size() - 1; i++) {
        assertThatFormula(bmgr.and(itps.get(i - 1), formulas.get(i))).implies(itps.get(i));
      }
      assertThatFormula(bmgr.and(getLast(itps), getLast(formulas)))
          .implies(bmgr.makeBoolean(false));
    }
  }

  @SuppressWarnings({"unchecked", "unused"})
  @Test
  public <T> void testInvalidToken() throws InterruptedException, SolverException {
    requireInterpolation();
    InterpolatingProverEnvironment<T> stack = newEnvironmentForTest();

    // create and push formulas and solve them
    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula a = imgr.makeVariable("a");
    T p1 = stack.push(imgr.lessThan(a, zero));
    T p2 = stack.push(imgr.lessThan(one, a));
    assertThat(stack).isUnsatisfiable();

    // try to solve with a null-token
    List<T> lst = new ArrayList<>();
    lst.add(null);
    assertThrows(IllegalArgumentException.class, () -> stack.getInterpolant(lst));

    // create an invalid interpolation token
    final Object p3;
    switch (solverToUse()) {
      case CVC5:
        p3 = ((CVC5BooleanFormulaManager) bmgr).makeVariableImpl("c");
        break;
      case MATHSAT5:
        p3 = 12345;
        break;
      case OPENSMT:
        p3 = 12347;
        break;
      case PRINCESS:
        p3 = 12349;
        break;
      case SMTINTERPOL:
        p3 = "some string";
        break;
      default:
        p3 = null; // unexpected solver for interpolation
    }

    // and try to solve with the token
    assertThrows(
        IllegalArgumentException.class, () -> stack.getInterpolant(ImmutableList.of((T) p3)));
  }

  /*
   * This tests that 2 formulas that are equal but not the same are treated that way by the
   * interpolation procedure. (Asserting the 2 formulas on the stack should return 2 distinct itp
   *  points, that are then treated as distinct itp points by the interpolation.)
   */
  @Test
  public <T> void issue381InterpolationTest1() throws InterruptedException, SolverException {
    try (InterpolatingProverEnvironment<T> prover = newEnvironmentForTest()) {
      var x = imgr.makeVariable("x");
      var one = imgr.makeNumber(1);
      var eq = imgr.equal(one, x);
      var lt1 = imgr.lessThan(one, x);
      var lt2 = imgr.lessThan(one, x);
      assertThat(lt1).isEqualTo(lt2);

      var eqT = prover.addConstraint(eq);
      var ltT1 = prover.addConstraint(lt1);
      var ltT2 = prover.addConstraint(lt2);
      assertThat(ltT1).isNotEqualTo(ltT2);
      assertThat(prover.isUnsat()).isTrue();

      var itps = prover.getSeqInterpolants0(ImmutableList.of(eqT, ltT1));
      assertThat(itps).isNotNull();
    }
  }

  /*
   * This tests that 2 formulas that are equal but not the same are treated that way by the
   * interpolation procedure. (Asserting the 2 formulas on the stack should return 2 distinct itp
   *  points, that are then treated as distinct itp points by the interpolation.)
   */
  @Test
  public <T> void issue381InterpolationTest2() throws InterruptedException, SolverException {
    try (InterpolatingProverEnvironment<T> prover = newEnvironmentForTest()) {
      var x = imgr.makeVariable("x");
      var one = imgr.makeNumber(1);
      var eq = imgr.equal(one, x);
      var lt1 = imgr.lessThan(one, x);
      var lt2 = imgr.lessThan(one, x);
      assertThat(lt1).isEqualTo(lt2);

      var eqT = prover.addConstraint(eq);
      var ltT1 = prover.addConstraint(lt1);
      var ltT2 = prover.addConstraint(lt2);
      assertThat(ltT1).isNotEqualTo(ltT2);
      assertThat(prover.isUnsat()).isTrue();

      var itps = prover.getSeqInterpolants0(ImmutableList.of(eqT, ltT2));
      assertThat(itps).isNotNull();
    }
  }

  /*
   * This tests that 2 formulas that are equal but not the same are treated that way by the
   * interpolation procedure. (Asserting the 2 formulas on the stack should return 2 distinct itp
   *  points, that are then treated as distinct itp points by the interpolation.)
   */
  @Test
  public <T> void issue381InterpolationTest3() throws InterruptedException, SolverException {
    try (InterpolatingProverEnvironment<T> prover = newEnvironmentForTest()) {
      var x = imgr.makeVariable("x");
      var one = imgr.makeNumber(1);
      var eq = imgr.equal(one, x);
      var lt1 = imgr.lessThan(one, x);
      var lt2 = imgr.lessThan(one, x);
      assertThat(lt1).isEqualTo(lt2);

      var eqT = prover.addConstraint(eq);
      var ltT1 = prover.addConstraint(lt1);
      var ltT2 = prover.addConstraint(lt2);
      assertThat(ltT1).isNotEqualTo(ltT2);
      assertThat(prover.isUnsat()).isTrue();

      var itps = prover.getInterpolant(ImmutableList.of(eqT));
      assertThat(itps).isNotNull();
    }
  }
}
