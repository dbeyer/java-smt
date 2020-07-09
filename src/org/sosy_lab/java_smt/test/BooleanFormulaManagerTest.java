// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.truth.Truth;
import java.util.List;
import org.junit.AssumptionViolatedException;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;

/**
 * Uses bitvector theory if there is no integer theory available. Notice: Boolector does not support
 * bitvectors length 1.
 */
@RunWith(Parameterized.class)
public class BooleanFormulaManagerTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  public void testVariableNamedTrue() throws SolverException, InterruptedException {
    BooleanFormula var;
    try {
      var = bmgr.makeVariable("true");
    } catch (RuntimeException e) {
      throw new AssumptionViolatedException("unsupported variable name", e);
    }
    BooleanFormula f = bmgr.equivalence(var, bmgr.makeFalse());
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testVariableNamedFalse() throws SolverException, InterruptedException {
    BooleanFormula var;
    try {
      var = bmgr.makeVariable("false");
    } catch (RuntimeException e) {
      throw new AssumptionViolatedException("unsupported variable name", e);
    }
    BooleanFormula f = bmgr.equivalence(var, bmgr.makeTrue());
    assertThatFormula(f).isSatisfiable();
  }

  @Test
  public void testConjunctionCollector() {
    List<BooleanFormula> terms =
        ImmutableList.of(
            bmgr.makeVariable("a"),
            bmgr.makeTrue(),
            bmgr.makeVariable("b"),
            bmgr.makeVariable("c"));

    // Syntactic equality to ensure that formula structure does not change
    // when users change the method they use for creating disjunctions.
    assertThatFormula(terms.stream().collect(bmgr.toConjunction())).isEqualTo(bmgr.and(terms));
  }

  @Test
  public void testDisjunctionCollector() {
    List<BooleanFormula> terms =
        ImmutableList.of(
            bmgr.makeVariable("a"),
            bmgr.makeFalse(),
            bmgr.makeVariable("b"),
            bmgr.makeVariable("c"));

    // Syntactic equality to ensure that formula structure does not change
    // when users change the method they use for creating disjunctions.
    assertThatFormula(terms.stream().collect(bmgr.toDisjunction())).isEqualTo(bmgr.or(terms));
  }

  @Test
  public void testConjunctionArgsExtractionEmpty() throws SolverException, InterruptedException {
    requireVisitor();
    BooleanFormula input = bmgr.makeBoolean(true);
    Truth.assertThat(bmgr.toConjunctionArgs(input, false)).isEmpty();
    assertThatFormula(bmgr.and(bmgr.toConjunctionArgs(input, false))).isEquivalentTo(input);
  }

  @Test
  public void testConjunctionArgsExtraction() throws SolverException, InterruptedException {
    requireIntegers();
    BooleanFormula input =
        bmgr.and(bmgr.makeVariable("a"), imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x")));
    Truth.assertThat(bmgr.toConjunctionArgs(input, false))
        .isEqualTo(
            ImmutableSet.of(
                bmgr.makeVariable("a"), imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x"))));
    assertThatFormula(bmgr.and(bmgr.toConjunctionArgs(input, false))).isEquivalentTo(input);
  }

  @Test
  public void testConjunctionArgsExtractionRecursive()
      throws SolverException, InterruptedException {
    BooleanFormula input;
    ImmutableSet<BooleanFormula> comparisonSet;
    if (imgr != null) {
      input =
          bmgr.and(
              bmgr.makeVariable("a"),
              bmgr.makeBoolean(true),
              bmgr.and(
                  bmgr.makeVariable("b"),
                  bmgr.makeVariable("c"),
                  bmgr.and(
                      imgr.equal(imgr.makeNumber(2), imgr.makeVariable("y")),
                      bmgr.makeVariable("d"),
                      bmgr.or(bmgr.makeVariable("e"), bmgr.makeVariable("f")))),
              imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x")));

      comparisonSet =
          ImmutableSet.of(
              bmgr.makeVariable("a"),
              bmgr.makeVariable("b"),
              bmgr.makeVariable("c"),
              imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x")),
              imgr.equal(imgr.makeNumber(2), imgr.makeVariable("y")),
              bmgr.makeVariable("d"),
              bmgr.or(bmgr.makeVariable("e"), bmgr.makeVariable("f")));
    } else {
      input =
          bmgr.and(
              bmgr.makeVariable("a"),
              bmgr.makeBoolean(true),
              bmgr.and(
                  bmgr.makeVariable("b"),
                  bmgr.makeVariable("c"),
                  bmgr.and(
                      bvmgr.equal(bvmgr.makeBitvector(2, 2), bvmgr.makeVariable(2, "y")),
                      bmgr.makeVariable("d"),
                      bmgr.or(bmgr.makeVariable("e"), bmgr.makeVariable("f")))),
              bvmgr.equal(bvmgr.makeBitvector(2, 1), bvmgr.makeVariable(2, "x")));

      comparisonSet =
          ImmutableSet.of(
              bmgr.makeVariable("a"),
              bmgr.makeVariable("b"),
              bmgr.makeVariable("c"),
              bvmgr.equal(bvmgr.makeBitvector(2, 1), bvmgr.makeVariable(2, "x")),
              bvmgr.equal(bvmgr.makeBitvector(2, 2), bvmgr.makeVariable(2, "y")),
              bmgr.makeVariable("d"),
              bmgr.or(bmgr.makeVariable("e"), bmgr.makeVariable("f")));
    }
    requireVisitor();
    Truth.assertThat(bmgr.toConjunctionArgs(input, true)).isEqualTo(comparisonSet);
    assertThatFormula(bmgr.and(bmgr.toConjunctionArgs(input, true))).isEquivalentTo(input);
    assertThatFormula(bmgr.and(bmgr.toConjunctionArgs(input, false))).isEquivalentTo(input);
  }

  @Test
  public void testDisjunctionArgsExtractionEmpty() throws SolverException, InterruptedException {
    requireVisitor();
    BooleanFormula input = bmgr.makeBoolean(false);
    Truth.assertThat(bmgr.toDisjunctionArgs(input, false)).isEmpty();
    assertThatFormula(bmgr.or(bmgr.toDisjunctionArgs(input, false))).isEquivalentTo(input);
  }

  @Test
  public void testDisjunctionArgsExtraction() throws SolverException, InterruptedException {
    BooleanFormula input;
    ImmutableSet<BooleanFormula> comparisonSet;
    if (imgr != null) {
      input =
          bmgr.or(bmgr.makeVariable("a"), imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x")));

      comparisonSet =
          ImmutableSet.of(
              bmgr.makeVariable("a"), imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x")));
    } else {
      input =
          bmgr.or(
              bmgr.makeVariable("a"),
              bvmgr.equal(bvmgr.makeBitvector(2, 1), bvmgr.makeVariable(2, "x")));

      comparisonSet =
          ImmutableSet.of(
              bmgr.makeVariable("a"),
              bvmgr.equal(bvmgr.makeBitvector(2, 1), bvmgr.makeVariable(2, "x")));
    }
    requireVisitor();
    Truth.assertThat(bmgr.toDisjunctionArgs(input, false)).isEqualTo(comparisonSet);
    assertThatFormula(bmgr.or(bmgr.toConjunctionArgs(input, false))).isEquivalentTo(input);
  }

  @Test
  public void testDisjunctionArgsExtractionRecursive()
      throws SolverException, InterruptedException {
    BooleanFormula input;
    ImmutableSet<BooleanFormula> comparisonSet;
    if (imgr != null) {
      input =
          bmgr.or(
              bmgr.makeVariable("a"),
              bmgr.makeBoolean(false),
              bmgr.or(
                  bmgr.makeVariable("b"),
                  bmgr.makeVariable("c"),
                  bmgr.or(
                      imgr.equal(imgr.makeNumber(2), imgr.makeVariable("y")),
                      bmgr.makeVariable("d"),
                      bmgr.and(bmgr.makeVariable("e"), bmgr.makeVariable("f")))),
              imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x")));

      comparisonSet =
          ImmutableSet.of(
              bmgr.makeVariable("a"),
              bmgr.makeVariable("b"),
              bmgr.makeVariable("c"),
              imgr.equal(imgr.makeNumber(1), imgr.makeVariable("x")),
              imgr.equal(imgr.makeNumber(2), imgr.makeVariable("y")),
              bmgr.makeVariable("d"),
              bmgr.and(bmgr.makeVariable("e"), bmgr.makeVariable("f")));
    } else {
      input =
          bmgr.or(
              bmgr.makeVariable("a"),
              bmgr.makeBoolean(false),
              bmgr.or(
                  bmgr.makeVariable("b"),
                  bmgr.makeVariable("c"),
                  bmgr.or(
                      bvmgr.equal(bvmgr.makeBitvector(2, 2), bvmgr.makeVariable(2, "y")),
                      bmgr.makeVariable("d"),
                      bmgr.and(bmgr.makeVariable("e"), bmgr.makeVariable("f")))),
              bvmgr.equal(bvmgr.makeBitvector(2, 1), bvmgr.makeVariable(2, "x")));

      comparisonSet =
          ImmutableSet.of(
              bmgr.makeVariable("a"),
              bmgr.makeVariable("b"),
              bmgr.makeVariable("c"),
              bvmgr.equal(bvmgr.makeBitvector(2, 1), bvmgr.makeVariable(2, "x")),
              bvmgr.equal(bvmgr.makeBitvector(2, 2), bvmgr.makeVariable(2, "y")),
              bmgr.makeVariable("d"),
              bmgr.and(bmgr.makeVariable("e"), bmgr.makeVariable("f")));
    }
    requireVisitor();
    Truth.assertThat(bmgr.toDisjunctionArgs(input, true)).isEqualTo(comparisonSet);
    assertThatFormula(bmgr.or(bmgr.toDisjunctionArgs(input, true))).isEquivalentTo(input);
    assertThatFormula(bmgr.or(bmgr.toDisjunctionArgs(input, false))).isEquivalentTo(input);
  }

  @Test
  public void simplificationTest() {
    // Boolector MAY fail (Use internal equals method to check if it does)
    BooleanFormula tru = bmgr.makeBoolean(true);
    BooleanFormula fals = bmgr.makeBoolean(false);
    BooleanFormula x = bmgr.makeVariable("x");
    BooleanFormula y = bmgr.makeVariable("y");

    // AND
    Truth.assertThat(bmgr.and(tru)).isEqualTo(tru);
    Truth.assertThat(bmgr.and(fals)).isEqualTo(fals);
    Truth.assertThat(bmgr.and(x)).isEqualTo(x);
    Truth.assertThat(bmgr.and()).isEqualTo(tru);

    Truth.assertThat(bmgr.and(tru, tru)).isEqualTo(tru);
    Truth.assertThat(bmgr.and(tru, x)).isEqualTo(x);
    Truth.assertThat(bmgr.and(fals, x)).isEqualTo(fals);
    Truth.assertThat(bmgr.and(x, x)).isEqualTo(x);

    Truth.assertThat(bmgr.and(tru, tru, tru)).isEqualTo(tru);
    Truth.assertThat(bmgr.and(fals, fals, fals)).isEqualTo(fals);
    Truth.assertThat(bmgr.and(fals, x, x)).isEqualTo(fals);
    Truth.assertThat(bmgr.and(tru, x, tru)).isEqualTo(x);

    Truth.assertThat(bmgr.and(tru, tru, x, fals, y, tru, x, y)).isEqualTo(fals);

    // recursive simplification needed
    // Truth.assertThat(bmgr.and(x, x, x, y, y)).isEqualTo(bmgr.and(x, y));

    // OR
    Truth.assertThat(bmgr.or(tru)).isEqualTo(tru);
    Truth.assertThat(bmgr.or(fals)).isEqualTo(fals);
    Truth.assertThat(bmgr.or(x)).isEqualTo(x);
    Truth.assertThat(bmgr.or()).isEqualTo(fals);

    Truth.assertThat(bmgr.or(tru, tru)).isEqualTo(tru);
    Truth.assertThat(bmgr.or(tru, x)).isEqualTo(tru);
    Truth.assertThat(bmgr.or(fals, x)).isEqualTo(x);
    Truth.assertThat(bmgr.or(x, x)).isEqualTo(x);

    Truth.assertThat(bmgr.or(fals, fals, fals)).isEqualTo(fals);
    Truth.assertThat(bmgr.or(tru, x, x)).isEqualTo(tru);
    Truth.assertThat(bmgr.or(fals, x, fals)).isEqualTo(x);

    Truth.assertThat(bmgr.or(fals, fals, x, tru, y, fals, x, y)).isEqualTo(tru);
  }
}
