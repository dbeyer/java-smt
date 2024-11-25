// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static org.sosy_lab.java_smt.test.ProverEnvironmentSubject.assertThat;

import com.google.common.collect.Lists;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.junit.Test;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/** Test that we can request evaluations from models. */
public class ModelEvaluationTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  /**
   * This is the default boolean value for unknown model evaluations. For unknown model evaluation
   * for variables or formulas, the solver can return NULL or a default value.
   */
  private static final boolean DEFAULT_MODEL_BOOLEAN = false;

  /**
   * This is the default integer value for unknown model evaluations. For unknown model evaluation
   * for variables or formulas, the solver can return NULL or a default value.
   */
  private static final int DEFAULT_MODEL_INT = 0;

  /**
   * This is the default String value for unknown model evaluations. For unknown model evaluation
   * for variables or formulas, the solver can return NULL or a default value.
   */
  private static final String DEFAULT_MODEL_STRING = "";

  private static int problemSize;

  @Override
  protected ConfigurationBuilder createTestConfigBuilder() {
    problemSize = solverToUse() == Solvers.PRINCESS ? 10 : 50; // Princess is too slow.
    ConfigurationBuilder builder = super.createTestConfigBuilder();
    if (solverToUse() == Solvers.MATHSAT5) {
      builder.setOption("solver.mathsat5.furtherOptions", "model_generation=true");
    }
    return builder;
  }

  @Test
  public void testGetSmallIntegersEvaluation1() throws SolverException, InterruptedException {
    requireIntegers();
    evaluateInModel(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(10)),
        imgr.add(imgr.makeVariable("y"), imgr.makeVariable("z")),
        Lists.newArrayList(null, BigInteger.valueOf(DEFAULT_MODEL_INT)),
        Lists.newArrayList(null, imgr.makeNumber(DEFAULT_MODEL_INT)));
  }

  @Test
  public void testGetSmallIntegersEvaluation2() throws SolverException, InterruptedException {
    requireIntegers();
    evaluateInModel(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(10)),
        imgr.add(imgr.makeVariable("y"), imgr.makeNumber(1)),
        Lists.newArrayList(null, BigInteger.ONE),
        Lists.newArrayList(null, imgr.makeNumber(1)));
  }

  @Test
  public void testGetNegativeIntegersEvaluation() throws SolverException, InterruptedException {
    requireIntegers();
    evaluateInModel(
        imgr.equal(imgr.makeVariable("x"), imgr.makeNumber(-10)),
        imgr.add(imgr.makeVariable("y"), imgr.makeNumber(1)),
        Lists.newArrayList(null, BigInteger.ONE),
        Lists.newArrayList(null, imgr.makeNumber(1)));
  }

  @Test
  public void testGetSmallIntegralRationalsEvaluation1()
      throws SolverException, InterruptedException {
    requireRationals();
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(1)),
        rmgr.add(rmgr.makeVariable("y"), rmgr.makeVariable("y")),
        Lists.newArrayList(null, Rational.of(DEFAULT_MODEL_INT)),
        Lists.newArrayList(null, rmgr.makeNumber(DEFAULT_MODEL_INT)));
  }

  @Test
  public void testGetSmallIntegralRationalsEvaluation2()
      throws SolverException, InterruptedException {
    requireRationals();
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(1)),
        rmgr.makeVariable("y"),
        Lists.newArrayList(null, Rational.of(DEFAULT_MODEL_INT)),
        Lists.newArrayList(null, rmgr.makeNumber(DEFAULT_MODEL_INT)));
  }

  @Test
  public void testGetRationalsEvaluation() throws SolverException, InterruptedException {
    requireRationals();
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("1/3"))),
        rmgr.divide(rmgr.makeVariable("y"), rmgr.makeNumber(2)),
        Lists.newArrayList(null, Rational.of(DEFAULT_MODEL_INT)),
        Lists.newArrayList(null, rmgr.makeNumber(DEFAULT_MODEL_INT)));
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("15"))),
        rmgr.makeVariable("x"),
        Lists.newArrayList(null, Rational.of(15)),
        Lists.newArrayList(null, rmgr.makeNumber(15)));
    evaluateInModel(
        rmgr.equal(rmgr.makeVariable("x"), rmgr.makeNumber(Rational.ofString("15"))),
        rmgr.divide(rmgr.makeVariable("x"), rmgr.makeNumber(3)),
        Lists.newArrayList(null, Rational.of(5)),
        Lists.newArrayList(null, rmgr.makeNumber(5)));
  }

  @Test
  public void testGetBooleansEvaluation() throws SolverException, InterruptedException {
    final boolean defaultValue;
    if (solverToUse() == Solvers.OPENSMT) {
      defaultValue = true; // Default value for boolean in OpenSMT is 'true'.
    } else {
      defaultValue = DEFAULT_MODEL_BOOLEAN;
    }

    evaluateInModel(
        bmgr.makeVariable("x"),
        bmgr.makeVariable("y"),
        Lists.newArrayList(null, defaultValue),
        Lists.newArrayList(null, bmgr.makeBoolean(defaultValue)));
  }

  @SuppressWarnings("UnicodeEscape")
  @Test
  public void testGetStringsEvaluation() throws SolverException, InterruptedException {
    requireStrings();

    // empty string
    evaluateInModel(
        smgr.equal(smgr.makeVariable("x"), smgr.makeString("")),
        smgr.makeVariable("x"),
        Lists.newArrayList(""),
        Lists.newArrayList(smgr.makeString("")));

    // normal string
    evaluateInModel(
        smgr.equal(smgr.makeVariable("x"), smgr.makeString("hello WORLD")),
        smgr.makeVariable("x"),
        Lists.newArrayList("hello WORLD"),
        Lists.newArrayList(smgr.makeString("hello WORLD")));

    // Unicode
    evaluateInModel(
        smgr.equal(smgr.makeVariable("x"), smgr.makeString("hello æ@€ \u1234 \\u{4321}")),
        smgr.makeVariable("x"),
        Lists.newArrayList("hello \u00e6@\u20ac \u1234 \u4321"),
        Lists.newArrayList(smgr.makeString("hello \u00e6@\u20ac \u1234 \u4321")));

    // invalid Unicode escape sequences (should be treated as normal characters)
    evaluateInModel(
        smgr.equal(smgr.makeVariable("x"), smgr.makeString("\\u")),
        smgr.makeVariable("x"),
        Lists.newArrayList("\\u"),
        Lists.newArrayList(smgr.makeString("\\u")));

    // foreign variable: x vs y
    evaluateInModel(
        smgr.equal(smgr.makeVariable("x"), smgr.makeString("hello")),
        smgr.makeVariable("y"),
        Lists.newArrayList(null, DEFAULT_MODEL_STRING),
        Lists.newArrayList(null, smgr.makeString(DEFAULT_MODEL_STRING)));
  }

  @Test
  public void testModelGeneration() throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bmgr.and(getConstraints()));
      for (int i = 0; i < problemSize; i++) {
        assertThat(prover).isSatisfiable();
        try (Model m = prover.getModel()) {
          prover.push(getNewConstraints(i, m));
        }
      }
    }
  }

  @Test
  public void testEvaluatorGeneration() throws SolverException, InterruptedException {
    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      prover.push(bmgr.and(getConstraints()));
      for (int i = 0; i < problemSize; i++) {
        assertThat(prover).isSatisfiable();
        try (Evaluator m = prover.getEvaluator()) {
          prover.push(getNewConstraints(i, m));
        }
      }
    }
  }

  @NonNull
  private List<BooleanFormula> getConstraints() {
    List<BooleanFormula> constraints = new ArrayList<>();
    for (int i = 0; i < problemSize; i++) {
      BooleanFormula x = bmgr.makeVariable("x" + i);
      for (int j = 0; j < 5; j++) {
        BooleanFormula y = bmgr.makeVariable("y" + i + "_" + j);
        constraints.add(bmgr.equivalence(x, y));
        constraints.add(bmgr.makeVariable("a" + i + "_" + j));
        constraints.add(bmgr.makeVariable("b" + i + "_" + j));
        constraints.add(bmgr.makeVariable("c" + i + "_" + j));
        constraints.add(bmgr.makeVariable("d" + i + "_" + j));
      }
    }
    return constraints;
  }

  private BooleanFormula getNewConstraints(int i, Evaluator m) {
    BooleanFormula x = bmgr.makeVariable("x" + i);
    // prover.push(m.evaluate(x) ? bmgr.not(x) : x);
    return m.evaluate(x) ? x : bmgr.not(x);
  }
}
