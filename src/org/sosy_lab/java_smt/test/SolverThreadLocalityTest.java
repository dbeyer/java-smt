// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.ImmutableList;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
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

  @Before
  public void makeThreads() {
    executor = Executors.newFixedThreadPool(2);
  }

  @After
  public void releaseThreads() {
    // All threads should have terminated by now as we always wait in the test cases
    executor.shutdownNow();
  }

  @Test
  public void allLocalTest() throws InterruptedException, SolverException {
    requireIntegers();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula formula = gen.generate(8);

    try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
      prover.push(formula);
      assertThat(prover).isUnsatisfiable();
    }
  }

  @SuppressWarnings("resource")
  @Test
  public void nonlocalContextTest()
      throws ExecutionException, InterruptedException, SolverException {
    requireIntegers();

    assume().that(solverToUse()).isNotEqualTo(Solvers.CVC5);

    Future<SolverContext> result =
        executor.submit(
            () -> {
              try {
                return factory.generateContext();
              } catch (InvalidConfigurationException e) {
                throw new RuntimeException(e);
              }
            });

    try (SolverContext newContext = result.get()) {
      FormulaManager newMgr = newContext.getFormulaManager();

      BooleanFormulaManager newBmgr = newMgr.getBooleanFormulaManager();
      IntegerFormulaManager newImgr = newMgr.getIntegerFormulaManager();

      HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(newImgr, newBmgr);

      // FIXME: Exception for CVC5 (related to bug #310?)
      // io.github.cvc5.CVC5ApiException:
      // Invalid call to 'cvc5::SortKind cvc5::Sort::getKind() const', expected non-null object
      //   at io.github.cvc5.Sort.getKind
      //       (Native Method)
      //   at io.github.cvc5.Sort.getKind
      //       (Sort.java:93)
      //   at ..
      BooleanFormula formula = gen.generate(8);

      try (BasicProverEnvironment<?> prover = newContext.newProverEnvironment()) {
        prover.push(formula);
        assertThat(prover).isUnsatisfiable();
      }
    }
  }

  @SuppressWarnings("resource")
  @Test
  public void nonlocalFormulaTest()
      throws InterruptedException, SolverException, ExecutionException {
    requireIntegers();

    assume().that(solverToUse()).isNotEqualTo(Solvers.CVC5);

    Future<BooleanFormula> result =
        executor.submit(
            () -> {
              HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);

              // FIXME: Exception for CVC5 (related to bug #310?)
              // io.github.cvc5.CVC5ApiException:
              // Invalid call to 'cvc5::SortKind cvc5::Sort::getKind() const', expected non-null
              // object
              //   at io.github.cvc5.Sort.getKind
              //       (Native Method)
              //   at io.github.cvc5.Sort.getKind
              //       (Sort.java:93)
              //   at ..
              return gen.generate(8);
            });

    BooleanFormula formula = result.get();

    try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
      prover.push(formula);
      assertThat(prover).isUnsatisfiable();
    }
  }

  @Test
  public void nonlocalProverTest() throws InterruptedException, ExecutionException {
    requireIntegers();

    assume().that(solverToUse()).isNotEqualTo(Solvers.CVC5);

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula formula = gen.generate(8);

    try (BasicProverEnvironment<?> prover = context.newProverEnvironment()) {
      Future<?> task =
          executor.submit(
              () -> {
                try {
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
                } catch (SolverException | InterruptedException pE) {
                  throw new RuntimeException(pE);
                }
              });
      assert task.get() == null;
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
  public <T> void nonlocalInterpolationTest() throws InterruptedException, ExecutionException {
    requireIntegers();
    requireInterpolation();

    assume().that(solverToUse()).isNotEqualTo(Solvers.CVC5);

    BooleanFormula f1 = imgr.lessThan(imgr.makeVariable("A"), imgr.makeVariable("B"));
    BooleanFormula f2 = imgr.lessThan(imgr.makeVariable("B"), imgr.makeVariable("A"));

    try (InterpolatingProverEnvironment<T> prover =
        (InterpolatingProverEnvironment<T>) context.newProverEnvironmentWithInterpolation()) {
      T id1 = prover.push(f1);

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

                } catch (SolverException | InterruptedException pE) {
                  throw new RuntimeException(pE);
                }
              });

      assert task1.get() == null;

      Future<BooleanFormula> itp =
          executor.submit(
              () -> {
                BooleanFormula interpol = prover.getInterpolant(ImmutableList.of(id1));
                Future<?> task2 =
                    executor.submit(
                        () -> {
                          try {
                            checkInterpolant(f1, f2, interpol);
                          } catch (SolverException | InterruptedException pE) {
                            throw new RuntimeException(pE);
                          }
                        });
                assert task2.get() == null;
                return interpol;
              });

      executor.awaitTermination(100, TimeUnit.MILLISECONDS);
      prover.pop();

      Future<?> task3 =
          executor.submit(
              () -> {
                try {
                  prover.pop();

                  prover.push(itp.get());
                  prover.push(f2);

                  assertThat(prover).isUnsatisfiable();
                } catch (SolverException | InterruptedException | ExecutionException pE) {
                  throw new RuntimeException(pE);
                }
              });

      assert task3.get() == null;
    }
  }

  @SuppressWarnings("resource")
  @Test
  public void wrongContextTest() throws InterruptedException, SolverException {
    assume()
        .that(solverToUse())
        .isNoneOf(
            Solvers.OPENSMT,
            Solvers.MATHSAT5,
            Solvers.SMTINTERPOL,
            Solvers.Z3,
            Solvers.PRINCESS,
            Solvers.BOOLECTOR);

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

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);

    // Boolector does not support integer, so we have to use two different versions for this test.
    BooleanFormula formula =
        solverToUse() == Solvers.BOOLECTOR ? bmgr.makeFalse() : gen.generate(8);

    try (SolverContext newContext = factory.generateContext()) {
      try (BasicProverEnvironment<?> prover =
          newContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
        // Trying to add a formula from our global context to the newly created solver context.
        prover.push(formula);
        assertThat(prover).isUnsatisfiable();
      }
    } catch (InvalidConfigurationException e) {
      throw new RuntimeException(e);
    }
  }
}
