// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import com.google.common.truth.Truth;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

public class SolverThreadLocalityTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {
  private ExecutorService executor;

  private HardIntegerFormulaGenerator hardProblem;
  private static final int DEFAULT_PROBLEM_SIZE = 8;

  private static final Collection<Solvers> SOLVERS_NOT_SUPPORTING_FORMULA_THREAD_SHARING =
      ImmutableList.of(); // TODO: Remove this

  @Before
  public void makeThreads() {
    executor = Executors.newFixedThreadPool(2);
  }

  @Before
  public void initProblemGenerator() {
    hardProblem = new HardIntegerFormulaGenerator(imgr, bmgr);
  }

  @After
  public void releaseThreads() {
    // All threads should have terminated by now as we always wait in the test
    if (executor != null) {
      executor.shutdownNow();
    }
  }

  @Test
  public void allLocalTest() throws InterruptedException, SolverException {
    requireIntegers();

    BooleanFormula formula = hardProblem.generate(DEFAULT_PROBLEM_SIZE);

    try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
      prover.push(formula);
      assertThat(prover).isUnsatisfiable();
    }
  }

  @Test
  public void nonLocalContextTest()
      throws ExecutionException, InterruptedException, SolverException {
    requireIntegers();

    // generate a new context in another thread, i.e., non-locally
    Future<SolverContext> result = executor.submit(() -> factory.generateContext());

    try (SolverContext newContext = result.get()) {
      FormulaManager newMgr = newContext.getFormulaManager();

      BooleanFormulaManager newBmgr = newMgr.getBooleanFormulaManager();
      IntegerFormulaManager newImgr = newMgr.getIntegerFormulaManager();

      HardIntegerFormulaGenerator newHardProblem =
          new HardIntegerFormulaGenerator(newImgr, newBmgr);

      // FIXME: Exception for CVC5 (related to bug #310?)
      // io.github.cvc5.CVC5ApiException:
      // Invalid call to 'cvc5::SortKind cvc5::Sort::getKind() const', expected non-null object
      //   at io.github.cvc5.Sort.getKind
      //       (Native Method)
      //   at io.github.cvc5.Sort.getKind
      //       (Sort.java:93)
      //   at ..
      BooleanFormula formula = newHardProblem.generate(DEFAULT_PROBLEM_SIZE);

      try (BasicProverEnvironment<?> prover = newContext.newProverEnvironment()) {
        prover.push(formula);
        assertThat(prover).isUnsatisfiable();
      }
    }
  }

  @Test
  public void nonLocalFormulaTest()
      throws InterruptedException, SolverException, ExecutionException {
    requireIntegers();

    // generate a new formula in another thread, i.e., non-locally
    Future<BooleanFormula> result =
        executor.submit(
            () -> {
              // FIXME: Exception for CVC5 (related to bug #310?)
              // io.github.cvc5.CVC5ApiException:
              // Invalid call to 'cvc5::SortKind cvc5::Sort::getKind() const', expected non-null
              // object
              //   at io.github.cvc5.Sort.getKind
              //       (Native Method)
              //   at io.github.cvc5.Sort.getKind
              //       (Sort.java:93)
              //   at ..
              return hardProblem.generate(DEFAULT_PROBLEM_SIZE);
            });

    BooleanFormula formula = result.get();

    try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
      prover.push(formula);
      assertThat(prover).isUnsatisfiable();
    }
  }

  @Test
  public void nonLocalProverTest() throws InterruptedException, ExecutionException {
    requireIntegers();
    BooleanFormula formula = hardProblem.generate(DEFAULT_PROBLEM_SIZE);

    // generate a new prover in another thread, i.e., non-locally
    Future<?> task =
        executor.submit(
            () -> {
              try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
                // FIXME: Exception for CVC5
                // io.github.cvc5.CVC5ApiException:
                // Given term is not associated with the node manager of this solver
                //   at io.github.cvc5.Solver.assertFormula
                //       (Native Method)
                //   at io.github.cvc5.Solver.assertFormula
                //       (Solver.java:1455)
                //   at org.sosy_lab.java_smt.solvers.cvc5.CVC5AbstractProver.addConstraintImpl
                //       (CVC5AbstractProver.java:114)
                //   at org.sosy_lab.java_smt.basicimpl.AbstractProver.addConstraint
                //       (AbstractProver.java:108)
                //   at ..
                prover.push(formula);
                assertThat(prover).isUnsatisfiable();
              } catch (SolverException | InterruptedException exception) {
                throw new RuntimeException(exception);
              }
            });

    assert task.get() == null;
  }

  @Test
  public void nonLocalFormulaTranslationTest() throws Throwable {
    // Test that even when using translation, the thread local problem persists for CVC5
    requireIntegers();

    BooleanFormula formula = hardProblem.generate(DEFAULT_PROBLEM_SIZE);

    // generate a new prover in another thread, i.e., non-locally
    Future<?> task;
    if (SOLVERS_NOT_SUPPORTING_FORMULA_THREAD_SHARING.contains(solverToUse())) {
      task =
          executor.submit(
              () ->
                  assertThrows(
                      io.github.cvc5.CVC5ApiException.class,
                      () -> {
                        try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
                          prover.push(
                              context
                                  .getFormulaManager()
                                  .translateFrom(formula, context.getFormulaManager()));
                          assertThat(prover).isUnsatisfiable();
                        } catch (SolverException | InterruptedException exception) {
                          throw new RuntimeException(exception);
                        }
                      }));
      Truth.assertThat(task.get()).isInstanceOf(io.github.cvc5.CVC5ApiException.class);

    } else {
      task =
          executor.submit(
              () -> {
                try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
                  prover.push(
                      context
                          .getFormulaManager()
                          .translateFrom(formula, context.getFormulaManager()));
                  assertThat(prover).isUnsatisfiable();
                } catch (SolverException | InterruptedException exception) {
                  throw new RuntimeException(exception);
                }
              });
      Truth.assertThat(task.get()).isNull();
    }
  }

  @Override
  protected Logics logicToUse() {
    return Logics.QF_LIA;
  }

  // Make sure that the solver returned a valid interpolant for the two formulas
  private void checkInterpolant(
      BooleanFormula formulaA, BooleanFormula formulaB, BooleanFormula itp)
      throws SolverException, InterruptedException {
    assertThatFormula(formulaA).implies(itp);
    assertThatFormula(bmgr.and(itp, formulaB)).implies(bmgr.makeBoolean(false));
  }

  @SuppressWarnings({"unchecked", "resource"})
  @Test
  public <T> void localInterpolationTest() throws InterruptedException, SolverException {
    requireIntegers();
    requireInterpolation();

    BooleanFormula f1 = imgr.lessThan(imgr.makeVariable("A"), imgr.makeVariable("B"));
    BooleanFormula f2 = imgr.lessThan(imgr.makeVariable("B"), imgr.makeVariable("A"));

    try (InterpolatingProverEnvironment<T> prover =
        (InterpolatingProverEnvironment<T>) context.newProverEnvironmentWithInterpolation()) {
      prover.push(f1);
      T id2 = prover.push(f2);

      assertThat(prover).isUnsatisfiable();

      BooleanFormula itp = prover.getInterpolant(ImmutableList.of(id2));
      checkInterpolant(f2, f1, itp);

      prover.pop();
      prover.push(itp);

      assertThat(prover).isUnsatisfiable();
    }
  }

  @SuppressWarnings({"unchecked", "resource"})
  @Test
  public <T> void nonLocalInterpolationTest() throws InterruptedException, ExecutionException {
    requireIntegers();
    requireInterpolation();

    BooleanFormula f1 = imgr.lessThan(imgr.makeVariable("A"), imgr.makeVariable("B"));
    BooleanFormula f2 = imgr.lessThan(imgr.makeVariable("B"), imgr.makeVariable("A"));

    try (InterpolatingProverEnvironment<T> prover =
        (InterpolatingProverEnvironment<T>) context.newProverEnvironmentWithInterpolation()) {
      T id1 = prover.push(f1);

      // push a formula in another thread, i.e., non-locally
      Future<?> task1 =
          executor.submit(
              () -> {
                try {
                  // FIXME: Exception for CVC5
                  // java.lang.IllegalStateException:
                  // You tried to use push() on an CVC5 assertion stack illegally.
                  //   at org.sosy_lab.java_smt.solvers.cvc5.CVC5AbstractProver.pushImpl
                  //       (CVC5AbstractProver.java:89)
                  //   at org.sosy_lab.java_smt.basicimpl.AbstractProver.push
                  //       (AbstractProver.java:88)
                  //   at ..
                  prover.push(f2);
                  assertThat(prover).isUnsatisfiable();

                } catch (SolverException | InterruptedException exception) {
                  throw new RuntimeException(exception);
                }
              });

      assert task1.get() == null;

      // compute/check interpolants in different threads, i.e., non-locally
      Future<BooleanFormula> task2 =
          executor.submit(
              () -> {
                BooleanFormula interpol = prover.getInterpolant(ImmutableList.of(id1));
                Future<?> task3 =
                    executor.submit(
                        () -> {
                          try {
                            checkInterpolant(f1, f2, interpol);
                          } catch (SolverException | InterruptedException exception) {
                            throw new RuntimeException(exception);
                          }
                        });
                assert task3.get() == null;
                return interpol;
              });

      BooleanFormula itp = task2.get();
      prover.pop();

      // use interpolants in another thread, i.e., non-locally
      Future<?> task4 =
          executor.submit(
              () -> {
                try {
                  prover.pop();

                  prover.push(itp);
                  prover.push(f2);

                  assertThat(prover).isUnsatisfiable();
                } catch (SolverException | InterruptedException exception) {
                  throw new RuntimeException(exception);
                }
              });

      assert task4.get() == null;
    }
  }

  @Test
  public void wrongContextTest()
      throws InterruptedException, SolverException, InvalidConfigurationException {
    assume()
        .that(solverToUse())
        .isNoneOf(
            Solvers.OPENSMT,
            Solvers.MATHSAT5,
            Solvers.SMTINTERPOL,
            Solvers.Z3,
            Solvers.PRINCESS,
            Solvers.BOOLECTOR,
            Solvers.BITWUZLA);

    // FIXME: This test tries to use a formula that was created in a different context. We expect
    //  this test to fail for most solvers, but there should be a unique error message.
    //  Right now we get:
    //  OpenSMT claims the formula is satisfiable:
    //    expected to be : unsatisfiable
    //    but was        : org.sosy_lab.java_smt.solvers.opensmt.OpenSmtTheoremProver@10d59286
    //    which is       : satisfiable
    //    which has model:
    //  MathSAT5 thows an IllegalStateExpression:
    //    msat_solve returned "unknown": polarity information is meaningful only for terms of
    //    type Bool
    //  SMTInterpol thows an de.uni_freiburg.informatik.ultimate.logic.SMTLIBException:
    //    Asserted terms created with incompatible theory
    //  Z3 throws an com.microsoft.z3.Z3Exception:
    //    invalid argument
    //  Princess throws an java.util.NoSuchElementException:
    //    key not found: i@15
    //  Boolector crashes with a segfault:
    //    boolector_assert: argument 'exp' belongs to different Boolector instance
    //  Bitwuzla:
    //    java.lang.IllegalArgumentException: invalid call to
    //    'void bitwuzla::Bitwuzla::assert_formula(const bitwuzla::Term&)',
    //    mismatching term manager for asserted formula
    //
    // To fix this issue, we would need to track which formula was created in which context,
    // which might result in quite some management and memory overhead.
    // We might want to see this as very low priority, as there is no real benefit for the user,
    // except having a nice error message.

    // Boolector and Bitwuzla do not support integers, so we have to use two different versions
    // for this test.
    BooleanFormula formula =
        List.of(Solvers.BOOLECTOR, Solvers.BITWUZLA).contains(solverToUse())
            ? bmgr.makeFalse()
            : hardProblem.generate(DEFAULT_PROBLEM_SIZE);

    try (SolverContext newContext = factory.generateContext()) {
      try (BasicProverEnvironment<?> prover =
          newContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
        // Trying to add a formula from our global context to the newly created solver context.
        prover.push(formula);
        assertThat(prover).isUnsatisfiable();
      }
    }
  }
}
