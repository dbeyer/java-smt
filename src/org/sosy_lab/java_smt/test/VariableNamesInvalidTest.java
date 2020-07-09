// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

@RunWith(Parameterized.class)
@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE")
public class VariableNamesInvalidTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  // currently the only invalid String is the empty String

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidBoolVariable() {
    @SuppressWarnings("unused")
    Formula var = bmgr.makeVariable("");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidIntVariable() {
    requireIntegers();
    @SuppressWarnings("unused")
    Formula var = imgr.makeVariable("");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidRatVariable() {
    requireRationals();
    @SuppressWarnings("unused")
    Formula var = rmgr.makeVariable("");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidBVVariable() {
    requireBitvectors();
    @SuppressWarnings("unused")
    Formula var = bvmgr.makeVariable(4, "");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidFloatVariable() {
    requireFloats();
    @SuppressWarnings("unused")
    Formula var = fpmgr.makeVariable("", FormulaType.getSinglePrecisionFloatingPointType());
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidIntArrayVariable() {
    requireIntegers();
    requireArrays();
    @SuppressWarnings("unused")
    Formula var = amgr.makeArray("", FormulaType.IntegerType, FormulaType.IntegerType);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testInvalidBvArrayVariable() {
    requireBitvectors();
    requireArrays();
    @SuppressWarnings("unused")
    Formula var =
        amgr.makeArray(
            "", FormulaType.getBitvectorTypeWithSize(2), FormulaType.getBitvectorTypeWithSize(2));
  }
}
