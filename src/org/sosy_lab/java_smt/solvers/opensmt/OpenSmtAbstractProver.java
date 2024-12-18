// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.ShutdownHook;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtSolverContext.OpenSMTOptions;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.MainSolver;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SMTConfig;
import org.sosy_lab.java_smt.solvers.opensmt.api.SMTOption;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.Symbol;
import org.sosy_lab.java_smt.solvers.opensmt.api.sstat;

public abstract class OpenSmtAbstractProver<T> extends AbstractProverWithAllSat<T> {

  protected final OpenSmtFormulaCreator creator;
  protected final MainSolver osmtSolver;
  protected final SMTConfig osmtConfig;

  private boolean changedSinceLastSatQuery = false;

  protected OpenSmtAbstractProver(
      OpenSmtFormulaCreator pFormulaCreator,
      FormulaManager pMgr,
      ShutdownNotifier pShutdownNotifier,
      SMTConfig pConfig,
      Set<ProverOptions> pOptions) {
    super(pOptions, pMgr.getBooleanFormulaManager(), pShutdownNotifier);

    creator = pFormulaCreator;

    // BUGFIX: We need to store the SMTConfig reference to make sure the underlying C++ object does
    // not get garbage collected
    osmtConfig = pConfig;
    osmtSolver = new MainSolver(creator.getEnv(), pConfig, "JavaSmt");
  }

  protected static SMTConfig getConfigInstance(
      Set<ProverOptions> pOptions, OpenSMTOptions pSolverOptions, boolean interpolation) {
    SMTConfig config = new SMTConfig();
    config.setOption(":random-seed", new SMTOption(pSolverOptions.randomSeed));
    config.setOption(
        ":produce-models",
        new SMTOption(
            pOptions.contains(ProverOptions.GENERATE_MODELS)
                || pOptions.contains(ProverOptions.GENERATE_ALL_SAT)));
    config.setOption(
        ":produce-unsat-cores",
        new SMTOption(pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)));
    config.setOption(":produce-interpolants", new SMTOption(interpolation));
    if (interpolation) {
      config.setOption(":interpolation-bool-algorithm", new SMTOption(pSolverOptions.algBool));
      config.setOption(":interpolation-euf-algorithm", new SMTOption(pSolverOptions.algUf));
      config.setOption(":interpolation-lra-algorithm", new SMTOption(pSolverOptions.algLra));
    }
    return config;
  }

  final MainSolver getOsmtSolver() {
    return osmtSolver;
  }

  @Override
  protected void pushImpl() {
    setChanged();
    osmtSolver.push();
  }

  @Override
  protected void popImpl() {
    setChanged();
    osmtSolver.pop();
  }

  @Nullable
  protected abstract T addConstraintImpl(PTRef f) throws InterruptedException;

  @Override
  @Nullable
  protected T addConstraintImpl(BooleanFormula pF) throws InterruptedException {
    setChanged();
    PTRef f = creator.extractInfo(pF);
    return addConstraintImpl(f);
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() {
    Preconditions.checkState(!closed);
    checkGenerateModels();

    Model model =
        new OpenSmtModel(
            this, creator, Collections2.transform(getAssertedFormulas(), creator::extractInfo));
    return registerEvaluator(model);
  }

  @Override
  public Evaluator getEvaluator() {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return getEvaluatorWithoutChecks();
  }

  @SuppressWarnings("resource")
  @Override
  protected Evaluator getEvaluatorWithoutChecks() {
    return registerEvaluator(new OpenSmtEvaluator(this, creator));
  }

  protected void setChanged() {
    if (!changedSinceLastSatQuery) {
      changedSinceLastSatQuery = true;
      closeAllEvaluators();
    }
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments()
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    return super.getModelAssignments();
  }

  /**
   * Make sure that the assertions only use features supported by the selected logic. Otherwise,
   * OpenSMT will fail on checking satisfiability without further information, if the selected logic
   * is required for solving process.
   */
  private String getReasonFromSolverFeatures() {
    Logic osmtLogic = creator.getEnv();

    Map<String, PTRef> userDeclarations = new HashMap<>();
    for (PTRef asserted : Collections2.transform(getAssertedFormulas(), creator::extractInfo)) {
      userDeclarations.putAll(creator.extractVariablesAndUFs(asserted, true));
    }

    boolean usesUFs = false;
    boolean usesIntegers = false;
    boolean usesReals = false;
    boolean usesArrays = false;

    for (PTRef term : userDeclarations.values()) {
      SymRef ref = osmtLogic.getSymRef(term);
      Symbol sym = osmtLogic.getSym(ref);

      if (sym.size() > 1) {
        usesUFs = true;
      }

      SRef sort = sym.rsort();
      if (osmtLogic.isArraySort(sort)) {
        usesArrays = true;
      }
      if (sort.equals(creator.getIntegerType())) {
        usesIntegers = true;
      }
      if (sort.equals(creator.getRationalType())) {
        usesReals = true;
      }
    }

    return getReasonFromSolverFeatures(usesUFs, usesIntegers, usesReals, usesArrays);
  }

  protected String getReasonFromSolverFeatures(
      boolean usesUFs, boolean usesIntegers, boolean usesReals, boolean usesArrays) {
    if (usesIntegers && usesReals) {
      return "OpenSMT does not support mixed integer-real arithmetics.";
    }

    List<String> errors = new ArrayList<>();
    if (usesUFs && !creator.getLogic().doesLogicSupportUFs()) {
      errors.add("uninterpreted function");
    }
    if (usesIntegers && !creator.getLogic().doesLogicSupportIntegers()) {
      errors.add("integer");
    }
    if (usesReals && !creator.getLogic().doesLogicSupportReals()) {
      errors.add("real");
    }
    if (usesArrays && !creator.getLogic().doesLogicSupportArrays()) {
      errors.add("array");
    }

    if (errors.isEmpty()) {
      return "Unknown reason.";
    } else {
      return String.format(
          "Assertions use features %s that are not supported by the specified logic %s.",
          errors, creator.getLogic());
    }
  }

  @Override
  @SuppressWarnings("try") // ShutdownHook is never referenced, and this is correct.
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    closeAllEvaluators();
    changedSinceLastSatQuery = false;

    sstat result;
    try (ShutdownHook listener = new ShutdownHook(shutdownNotifier, osmtSolver::stop)) {
      shutdownNotifier.shutdownIfNecessary();
      try {
        result = osmtSolver.check();
      } catch (Exception e) {
        if (e.getMessage().isEmpty()) {
          // OpenSMT does not support all combinations of theories/logics and crashes on
          // unsupported formula instances. We try to provide hints for the crash.
          // Support for logics/features is checked lazily, i.e., only in case of an exception,
          // such that the solver can simplify and try to reason about a query as far as possible.
          // In several cases, the complex logics are not required for reasoning
          // and OpenSMT succeeds with solving a query.
          String reason = String.format(" Most likely reason: %s", getReasonFromSolverFeatures());
          throw new SolverException(
              String.format(
                  "OpenSMT crashed while checking satisfiability. Most likely reason: %s", reason));
        } else {
          throw new SolverException("OpenSMT crashed while checking satisfiability.", e);
        }
      }
      shutdownNotifier.shutdownIfNecessary();
    }

    if (result.equals(sstat.Error())) {
      throw new SolverException("OpenSMT crashed while checking satisfiability.");
    } else if (result.equals(sstat.Undef())) {
      throw new InterruptedException();
    } else {
      return result.equals(sstat.False());
    }
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    Preconditions.checkState(!changedSinceLastSatQuery);

    ImmutableList.Builder<BooleanFormula> result = ImmutableList.builder();
    for (PTRef r : osmtSolver.getUnsatCore()) {
      result.add(creator.encapsulateBoolean(r));
    }
    return result.build();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("OpenSMT does not support solving with assumptions.");
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("OpenSMT does not support solving with assumptions.");
  }

  @Override
  public void close() {
    if (!closed) {
      osmtSolver.delete();
    }
    super.close();
  }
}
