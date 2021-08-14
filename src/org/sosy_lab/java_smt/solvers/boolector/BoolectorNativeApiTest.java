// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.LibraryLoader;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.solvers.boolector.BoolectorSolverContext.SatSolver;

public class BoolectorNativeApiTest {

  private long btor;

  @BeforeClass
  public static void load() {
    try {
      NativeLibraries.loadLibrary("boolector");
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Boolector is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    btor = BtorJNI.boolector_new();
  }

  @After
  public void freeEnvironment() {
    BtorJNI.boolector_delete(btor);
  }

  // some options have a different name in the API that their internal representation.
  // TODO why?
  // Because for some reason the return value of the get_opt method is not the correct option name
  // (check btortypes.h for correct options)
  private static final ImmutableMap<String, String> ALLOWED_DIFFS =
      ImmutableMap.<String, String>builder()
          .put("BTOR_OPT_ACKERMANNIZE", "BTOR_OPT_ACKERMANN")
          .put("BTOR_OPT_QUANT_DUAL", "BTOR_OPT_QUANT_DUAL_SOLVER")
          .put("BTOR_OPT_QUANT_SYNTHLIMIT", "BTOR_OPT_QUANT_SYNTH_LIMIT")
          .put("BTOR_OPT_QUANT_SYNTHQI", "BTOR_OPT_QUANT_SYNTH_QI")
          .put("BTOR_OPT_QUANT_MS", "BTOR_OPT_QUANT_MINISCOPE")
          .put("BTOR_OPT_QUANT_SYNTHCOMPLETE", "BTOR_OPT_QUANT_SYNTH_ITE_COMPLETE")
          .put("BTOR_OPT_BETA_REDUCE", "BTOR_OPT_BETA_REDUCE")
          .put("BTOR_OPT_DUMP_DIMACS", "BTOR_OPT_PRINT_DIMACS")
          .put("BTOR_OPT_SIMP_NORM_ADDS", "BTOR_OPT_SIMP_NORMAMLIZE_ADDERS")
          .build();

  @Test
  public void optionNameTest() {
    // check whether our enum is identical to Boolector's internal enum
    for (BtorOption option : BtorOption.values()) {
      String optName = BtorJNI.boolector_get_opt_lng(btor, option.getValue());
      String converted = "BTOR_OPT_" + optName.replace("-", "_").replace(":", "_").toUpperCase();
      // System.out.println("our option: " + option + " -- their option: " + optName);
      assertThat(option.name()).isEqualTo(ALLOWED_DIFFS.getOrDefault(converted, converted));
    }
  }

  @Test
  public void satSolverTest() {
    // check whether all sat solvers are available
    for (SatSolver satSolver : SatSolver.values()) {
      long btor1 = BtorJNI.boolector_new();
      BtorJNI.boolector_set_sat_solver(btor1, satSolver.name().toLowerCase());
      long newVar = BtorJNI.boolector_var(btor1, BtorJNI.boolector_bool_sort(btor1), "x");
      BtorJNI.boolector_assert(btor1, newVar);
      int result = BtorJNI.boolector_sat(btor1);
      assertThat(result).isEqualTo(BtorJNI.BTOR_RESULT_SAT_get());
      BtorJNI.boolector_delete(btor1);
    }
  }

  /**
   * For each available solver, we build a context and solver a small formula.
   *
   * <p>This should be sufficient to test whether the sat-solver can be loaded.
   */
  @Test
  public void satSolverBackendTest()
      throws InvalidConfigurationException, InterruptedException, SolverException {

    for (SatSolver satsolver : BoolectorSolverContext.SatSolver.values()) {
      ConfigurationBuilder config =
          Configuration.builder().setOption("solver.boolector.satSolver", satsolver.name());
      try (BoolectorSolverContext context =
          BoolectorSolverContext.create(
              config.build(),
              ShutdownNotifier.createDummy(),
              null,
              1,
              LibraryLoader.defaultLibraryLoader())) {
        BooleanFormulaManager bfmgr = context.getFormulaManager().getBooleanFormulaManager();
        BooleanFormula fa = bfmgr.makeVariable("a");
        BooleanFormula fb = bfmgr.makeVariable("b");
        BooleanFormula fc = bfmgr.makeVariable("c");
        BooleanFormula f1 = bfmgr.or(fa, fb, fc);
        BooleanFormula f2 = bfmgr.and(fa, fb, fc);
        try (ProverEnvironment prover = context.newProverEnvironment()) {
          prover.addConstraint(bfmgr.equivalence(f1, f2));
          assertThat(prover.isUnsat()).isFalse();
        }
      }
    }
  }

  @Test
  public void dumpVariableTest() throws InvalidConfigurationException {
    ConfigurationBuilder config = Configuration.builder();
    try (BoolectorSolverContext context =
        BoolectorSolverContext.create(
            config.build(),
            ShutdownNotifier.createDummy(),
            null,
            1,
            LibraryLoader.defaultLibraryLoader())) {
      FormulaManager mgr = context.getFormulaManager();
      BooleanFormulaManager bfmgr = mgr.getBooleanFormulaManager();
      for (String name : ImmutableList.of("a", "a", "b", "abc", "ABC")) {
        BooleanFormula f = bfmgr.makeVariable(name);
        String s = mgr.dumpFormula(f).toString();
        assertThat(s).contains(String.format("(declare-fun %s () (_ BitVec 1))", name));
        // assertThat(s).contains(String.format("(assert %s)", name)); // assertion not available
      }
    }
  }

  @Test
  public void dumpVariableWithAssertionsOnStackTest()
      throws InvalidConfigurationException, InterruptedException {
    ConfigurationBuilder config = Configuration.builder();
    try (BoolectorSolverContext context =
        BoolectorSolverContext.create(
            config.build(),
            ShutdownNotifier.createDummy(),
            null,
            1,
            LibraryLoader.defaultLibraryLoader())) {
      FormulaManager mgr = context.getFormulaManager();
      BooleanFormulaManager bfmgr = mgr.getBooleanFormulaManager();
      try (ProverEnvironment prover = context.newProverEnvironment()) {
        prover.push(bfmgr.makeVariable("x"));
        for (String name : ImmutableList.of("a", "a", "b", "abc", "ABC")) {
          BooleanFormula f = bfmgr.makeVariable(name);
          String s = mgr.dumpFormula(f).toString();
          // TODO why is there a prefix "BTOR_2@"?
          // Possible reason: we are on the second level of the solver stack.
          // - first level comes from the constructor of ReusableStackTheoremProver.
          // - second level comes from the PUSH above.
          // We do actually not want to have such names in the dump.
          assertThat(s).contains(String.format("(declare-fun BTOR_2@%s () (_ BitVec 1))", name));
          // assertThat(s).contains(String.format("(assert "));
        }
      }
    }
  }

  @Test
  public void repeatedDumpFormulaTest() throws InvalidConfigurationException {
    ConfigurationBuilder config = Configuration.builder();
    try (BoolectorSolverContext context =
        BoolectorSolverContext.create(
            config.build(),
            ShutdownNotifier.createDummy(),
            null,
            1,
            LibraryLoader.defaultLibraryLoader())) {
      FormulaManager mgr = context.getFormulaManager();
      BooleanFormulaManager bfmgr = mgr.getBooleanFormulaManager();
      BooleanFormula fa = bfmgr.makeVariable("a");
      BooleanFormula fb = bfmgr.makeVariable("b");
      BooleanFormula fc = bfmgr.makeVariable("c");
      BooleanFormula f1 = bfmgr.or(fa, bfmgr.and(fb, fc));
      BooleanFormula f2 = bfmgr.or(fa, bfmgr.and(fb, fc));
      String s1 = mgr.dumpFormula(f1).toString();
      // repeat several times to increase probability for non-deterministic behavior
      for (int i = 0; i < 10; i++) {
        assertThat(s1).isEqualTo(mgr.dumpFormula(f2).toString());
      }
    }
  }
}
