/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.stp;

import java.util.Set;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.junit.AssumptionViolatedException;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class StpSolverContext extends AbstractSolverContext {

  // private StpFormulaManager manager;
  private final StpFormulaCreator formulaCreator;
  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;

  // Context is Validity Checker (VC) in STP
  // private final StpVC stpContext;
  private static final VC vcStpContext;

  static {
    // load the shared library
    try {
      NativeLibraries.loadLibrary("stpJapi");
      vcStpContext = StpNativeApi.getStpContextVC();
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Cannot find at the STP native library", e);
    }
  }

  private StpSolverContext(
      StpFormulaManager pFormulaMgr,
      StpFormulaCreator pFormulaCreator,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier) {
    super(pFormulaMgr);

    this.formulaCreator = pFormulaCreator;
    this.logger = pLogger;
    this.shutdownNotifier = pShutdownNotifier;
  }

  public static StpSolverContext create(
      Configuration config,
      LogManager logger,
      ShutdownNotifier shutdownNotifier,
      @Nullable PathCounterTemplate stpLogfile,
      long randomSeed) {
    //
    // //load the shared library
    // try {
    // NativeLibraries.loadLibrary("stpJapi");
    // } catch (UnsatisfiedLinkError e) {
    // throw new AssumptionViolatedException("Cannot find at the STP native library", e);
    // }

    // Create or setup the 'environment' with supplied parameters and other java-smt defaults
    // vcStpContext // this is the 'env'

    // use the 'environment' to create a FormulaCreator object
    StpFormulaCreator formulaCreator = new StpFormulaCreator(vcStpContext);

    // use the FormulaCreator object to create FormulaManager object for all supported Theories
    StpBooleanFormulaManager booleanFrmMgr = new StpBooleanFormulaManager(formulaCreator);
    StpUFManager functionFrmMgr = new StpUFManager(formulaCreator);
    StpArrayFormulaManager arrayFrmMgr = new StpArrayFormulaManager(formulaCreator);
    StpBitvectorFormulaManager bitvectorFrmMgr = new StpBitvectorFormulaManager(formulaCreator);

    // Create the main FormulaManager to manage all supported Formula types
    StpFormulaManager formulaMgr =
        new StpFormulaManager(
            formulaCreator, functionFrmMgr, booleanFrmMgr, bitvectorFrmMgr, arrayFrmMgr);

    // Create the SolverContext with the FormulaCreator and main FormulaManager Objects
    return new StpSolverContext(formulaMgr, formulaCreator, logger, shutdownNotifier);
  }

  public StpFormulaCreator getFormulaCreator() {
    return this.formulaCreator;
  }

  @Override
  public String getVersion() {
    return StpNativeApi.getStpVersion();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.STP;
  }

  @Override
  public void close() {
    logger.log(Level.FINER, "Freeing STP environment resources");
    // stpJapi.vc_Destroy(formulaCreator.getEnv()); //TODO: use this and make vcStpContext
    // non-static
    StpJavaApi.vc_Destroy(vcStpContext);
  }

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> proverOptions) {
    return new StpTheoremProver(this, shutdownNotifier, formulaCreator, proverOptions);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    // TODO stub
    throw new UnsupportedOperationException("Interpolating Prover for STP is not implemented yet");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> proverOptions) {

    // TODO I need to confirm about this
    throw new UnsupportedOperationException("Support for optimization in STP not implemented yet");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    // TODO I am not sure about this
    return false;
  }

  public VC createEnvironment(Long conf) {
    // create a new VC context or reuse existing one
    return formulaCreator.getEnv();
  }
}
