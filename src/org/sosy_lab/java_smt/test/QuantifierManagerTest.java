// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE", justification = "test code")
@RunWith(Parameterized.class)
public class QuantifierManagerTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solverUnderTest;

  @Override
  protected Solvers solverToUse() {
    return solverUnderTest;
  }

  private IntegerFormula x;
  private ArrayFormula<IntegerFormula, IntegerFormula> a;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula a_at_x_eq_1;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula a_at_x_eq_0;

  @SuppressWarnings("checkstyle:membername")
  private BooleanFormula forall_x_a_at_x_eq_0;

  @Before
  public void setUp() {
    requireIntegers();
    requireArrays();
    requireQuantifiers();

    x = imgr.makeVariable("x");
    a = amgr.makeArray("a", FormulaType.IntegerType, FormulaType.IntegerType);

    a_at_x_eq_1 = imgr.equal(amgr.select(a, x), imgr.makeNumber(1));
    a_at_x_eq_0 = imgr.equal(amgr.select(a, x), imgr.makeNumber(0));

    forall_x_a_at_x_eq_0 = qmgr.forall(ImmutableList.of(x), a_at_x_eq_0);
  }

  private SolverException handleSolverException(SolverException e) throws SolverException {
    // The tests in this class use quantifiers and thus solver failures are expected.
    // We do not ignore all SolverExceptions in order to not hide bugs,
    // but only for Princess which is known to not be able to solve all tests here.
    if (solverUnderTest == Solvers.PRINCESS) {
      assume().withMessage(e.getMessage()).fail();
    }
    throw e;
  }

  private static final UniqueIdGenerator index = new UniqueIdGenerator(); // to get different names

  @Test
  public void testForallArrayConjunctUnsat() throws SolverException, InterruptedException {
    // (forall x . b[x] = 0) AND (b[123] = 1) is UNSAT
    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testForallArrayConjunctSat() throws SolverException, InterruptedException {
    // (forall x . b[x] = 0) AND (b[123] = 0) is SAT
    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));
    try {
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testForallArrayDisjunct1() throws SolverException, InterruptedException {
    // (forall x . b[x] = 0) AND (b[123] = 1 OR b[123] = 0) is SAT
    BooleanFormula f =
        bmgr.and(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            bmgr.or(
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)),
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0))));

    try {
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testForallArrayDisjunctSat2() throws SolverException, InterruptedException {
    // (forall x . b[x] = 0) OR (b[123] = 1) is SAT
    BooleanFormula f =
        bmgr.or(
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testNotExistsArrayConjunct1() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) AND (b[123] = 1) is UNSAT
    BooleanFormula f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    try {
      assertThatFormula(f).isUnsatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testNotExistsArrayConjunct2() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) AND (b[123] = 0) is SAT
    BooleanFormula f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));
    try {
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testNotExistsArrayConjunct3() throws SolverException, InterruptedException {
    // (not exists x . b[x] = 0) AND (b[123] = 0) is UNSAT
    BooleanFormula f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), a_at_x_eq_0)),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0)));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testNotExistsArrayDisjunct1() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) AND (b[123] = 1 OR b[123] = 0) is SAT
    BooleanFormula f =
        bmgr.and(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            bmgr.or(
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)),
                imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(0))));
    try {
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testNotExistsArrayDisjunct2() throws SolverException, InterruptedException {
    // (not exists x . not b[x] = 0) OR (b[123] = 1) is SAT
    BooleanFormula f =
        bmgr.or(
            bmgr.not(qmgr.exists(ImmutableList.of(x), bmgr.not(a_at_x_eq_0))),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testExistsArrayConjunct1() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) AND (b[123] = 1) is SAT
    BooleanFormula f =
        bmgr.and(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_0),
            imgr.equal(amgr.select(a, imgr.makeNumber(123)), imgr.makeNumber(1)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testExistsArrayConjunct2() throws SolverException, InterruptedException {
    // (exists x . b[x] = 1) AND  (forall x . b[x] = 0) is UNSAT

    // Boolector has no working quantifier at the moment. They will be implemented later
    assume().that(solverUnderTest).isEqualTo(Solvers.BOOLECTOR);
    BooleanFormula f =
        bmgr.and(qmgr.exists(ImmutableList.of(x), a_at_x_eq_1), forall_x_a_at_x_eq_0);
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testExistsArrayConjunct3() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) AND  (forall x . b[x] = 0) is SAT

    // Boolector has no working quantifier at the moment. They will be implemented later
    assume().that(solverUnderTest).isEqualTo(Solvers.BOOLECTOR);
    BooleanFormula f =
        bmgr.and(qmgr.exists(ImmutableList.of(x), a_at_x_eq_0), forall_x_a_at_x_eq_0);
    try {
      assertThatFormula(f).isSatisfiable();
    } catch (SolverException e) {
      throw handleSolverException(e);
    }
  }

  @Test
  public void testExistsArrayDisjunct1() throws SolverException, InterruptedException {
    // (exists x . b[x] = 0) OR  (forall x . b[x] = 1) is SAT

    // Boolector has no working quantifier at the moment. They will be implemented later
    assume().that(solverUnderTest).isEqualTo(Solvers.BOOLECTOR);
    BooleanFormula f =
        bmgr.or(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_0),
            qmgr.forall(ImmutableList.of(x), a_at_x_eq_1));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testExistsArrayDisjunct2() throws SolverException, InterruptedException {
    // (exists x . b[x] = 1) OR (exists x . b[x] = 1) is SAT

    // Boolector has no working quantifier at the moment. They will be implemented later
    assume().that(solverUnderTest).isEqualTo(Solvers.BOOLECTOR);
    BooleanFormula f =
        bmgr.or(
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_1),
            qmgr.exists(ImmutableList.of(x), a_at_x_eq_1));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testContradiction() throws SolverException, InterruptedException {
    // forall x . x = x+1  is UNSAT

    requireIntegers();
    BooleanFormula f =
        qmgr.forall(ImmutableList.of(x), imgr.equal(x, imgr.add(x, imgr.makeNumber(1))));
    assertThatFormula(f).isUnsatisfiable();
  }

  @Test
  public void testSimple() throws SolverException, InterruptedException {
    // forall x . x+2 = x+1+1  is SAT
    requireIntegers();
    BooleanFormula f =
        qmgr.forall(
            ImmutableList.of(x),
            imgr.equal(
                imgr.add(x, imgr.makeNumber(2)),
                imgr.add(imgr.add(x, imgr.makeNumber(1)), imgr.makeNumber(1))));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testBlah() throws SolverException, InterruptedException {
    requireIntegers();
    IntegerFormula z = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    BooleanFormula f =
        qmgr.forall(ImmutableList.of(z), qmgr.exists(ImmutableList.of(y), imgr.equal(z, y)));
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testEquals() {
    requireIntegers();
    BooleanFormula f1 = qmgr.exists(ImmutableList.of(imgr.makeVariable("x")), a_at_x_eq_1);
    BooleanFormula f2 = qmgr.exists(ImmutableList.of(imgr.makeVariable("x")), a_at_x_eq_1);

    assertThat(f1).isEqualTo(f2);
  }

  @Test
  public void testQELight() throws InterruptedException {
    requireIntegers();
    assume().that(solverToUse()).isEqualTo(Solvers.Z3);
    // exists y : (y=4 && x=y+3) --> simplified: x=7
    IntegerFormula y = imgr.makeVariable("y");
    BooleanFormula f1 =
        qmgr.exists(
            y,
            bmgr.and(
                imgr.equal(y, imgr.makeNumber(4)), imgr.equal(x, imgr.add(y, imgr.makeNumber(3)))));
    BooleanFormula out = mgr.applyTactic(f1, Tactic.QE_LIGHT);
    assertThat(out).isEqualTo(imgr.equal(x, imgr.makeNumber(7)));
  }

  @Test
  public void testIntrospectionForall() {
    // Boolector has no working quantifier at the moment. They will be implemented later
    assume().that(solverUnderTest).isEqualTo(Solvers.BOOLECTOR);
    BooleanFormula forall = qmgr.forall(ImmutableList.of(x), a_at_x_eq_0);

    final AtomicBoolean isQuantifier = new AtomicBoolean(false);
    final AtomicBoolean isForall = new AtomicBoolean(false);
    final AtomicInteger numBound = new AtomicInteger(0);

    // Test introspection with visitors.
    mgr.visit(
        forall,
        new DefaultFormulaVisitor<Void>() {
          @Override
          protected Void visitDefault(Formula f) {
            return null;
          }

          @Override
          public Void visitQuantifier(
              BooleanFormula f,
              Quantifier quantifier,
              List<Formula> boundVariables,
              BooleanFormula body) {
            isForall.set(quantifier == Quantifier.FORALL);
            isQuantifier.set(true);
            numBound.set(boundVariables.size());
            return null;
          }
        });
  }

  @Test
  public void testIntrospectionExists() {
    // Boolector has no working quantifier at the moment. They will be implemented later
    assume().that(solverUnderTest).isEqualTo(Solvers.BOOLECTOR);
    BooleanFormula exists = qmgr.exists(ImmutableList.of(x), a_at_x_eq_0);
    final AtomicBoolean isQuantifier = new AtomicBoolean(false);
    final AtomicBoolean isForall = new AtomicBoolean(false);
    final List<Formula> boundVars = new ArrayList<>();

    // Test introspection with visitors.
    mgr.visit(
        exists,
        new DefaultFormulaVisitor<Void>() {
          @Override
          protected Void visitDefault(Formula f) {
            return null;
          }

          @Override
          public Void visitQuantifier(
              BooleanFormula f,
              Quantifier quantifier,
              List<Formula> boundVariables,
              BooleanFormula body) {
            assertThat(isQuantifier.get()).isFalse();
            isForall.set(quantifier == Quantifier.FORALL);
            isQuantifier.set(true);
            boundVars.addAll(boundVariables);
            return null;
          }
        });
    assertThat(isQuantifier.get()).isTrue();
    assertThat(isForall.get()).isFalse();

    assume()
        .withMessage("Quantifier introspection in JavaSMT for Princess is currently not complete.")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);
    assertThat(boundVars).hasSize(1);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testEmpty() {
    // Boolector has no working quantifier at the moment. They will be implemented later
    assume().that(solverUnderTest).isEqualTo(Solvers.BOOLECTOR);
    assume()
        .withMessage("TODO: The JavaSMT code for Princess explicitly allows this.")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    // An empty list of quantified variables throws an exception.
    @SuppressWarnings("unused")
    BooleanFormula quantified = qmgr.exists(ImmutableList.of(), bmgr.makeVariable("b"));
  }

  @Test
  public void checkQuantifierElimination() throws InterruptedException, SolverException {
    // build formula: (forall x . ((x < 5) | (7 < x + y)))
    // quantifier-free equivalent: (2 < y)
    requireIntegers();
    IntegerFormula xx = imgr.makeVariable("x");
    IntegerFormula yy = imgr.makeVariable("y");
    BooleanFormula f =
        qmgr.forall(
            xx,
            bmgr.or(
                imgr.lessThan(xx, imgr.makeNumber(5)),
                imgr.lessThan(imgr.makeNumber(7), imgr.add(xx, yy))));
    BooleanFormula qFreeF = qmgr.eliminateQuantifiers(f);
    assertThatFormula(qFreeF).isEquivalentTo(imgr.lessThan(imgr.makeNumber(2), yy));
  }

  @Test
  public void checkBVQuantifierElimination() throws InterruptedException, SolverException {
    requireBitvectors();

    // build formula: exists y : bv[2]. x * y = 1
    // quantifier-free equivalent: x = 1 | x = 3
    //                      or     extract_0_0 x = 1

    // Boolector has no working quantifier at the moment. They will be implemented later
    assume().that(solverUnderTest).isEqualTo(Solvers.BOOLECTOR);
    int i = index.getFreshId();
    int width = 2;

    BitvectorFormula xx = bvmgr.makeVariable(width, "x" + i);
    BitvectorFormula yy = bvmgr.makeVariable(width, "y" + i);
    BooleanFormula f =
        qmgr.exists(yy, bvmgr.equal(bvmgr.multiply(xx, yy), bvmgr.makeBitvector(width, 1)));
    BooleanFormula qFreeF = qmgr.eliminateQuantifiers(f);

    assertThatFormula(qFreeF)
        .isEquivalentTo(bvmgr.equal(bvmgr.extract(xx, 0, 0, false), bvmgr.makeBitvector(1, 1)));
  }
}
