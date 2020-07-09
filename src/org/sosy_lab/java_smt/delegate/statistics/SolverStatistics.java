// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import java.util.concurrent.atomic.AtomicInteger;
import org.sosy_lab.common.time.TimeSpan;

public class SolverStatistics {

  // prover operations
  final AtomicInteger provers = new AtomicInteger();
  final AtomicInteger pop = new AtomicInteger();
  final AtomicInteger push = new AtomicInteger();
  final AtomicInteger constraint = new AtomicInteger();
  final AtomicInteger model = new AtomicInteger();
  final AtomicInteger unsatCore = new AtomicInteger();

  final TimerPool unsat = new TimerPool();
  final TimerPool allSat = new TimerPool();
  final TimerPool interpolation = new TimerPool();

  // manager operations
  final AtomicInteger visits = new AtomicInteger();
  final AtomicInteger booleanOperations = new AtomicInteger();
  final AtomicInteger numericOperations = new AtomicInteger();
  final AtomicInteger arrayOperations = new AtomicInteger();
  final AtomicInteger slOperations = new AtomicInteger();
  final AtomicInteger ufOperations = new AtomicInteger();
  final AtomicInteger quantifierOperations = new AtomicInteger();
  final AtomicInteger bvOperations = new AtomicInteger();
  final AtomicInteger fpOperations = new AtomicInteger();
  final AtomicInteger typeOperations = new AtomicInteger();

  // model operations
  final AtomicInteger modelEvaluations = new AtomicInteger();
  final AtomicInteger modelListings = new AtomicInteger();

  SolverStatistics() {}

  // visible access methods
  public int getNumberOfProverEnvironments() {
    return provers.get();
  }

  public int getNumberOfPopQueries() {
    return pop.get();
  }

  public int getNumberOfPushQueries() {
    return push.get();
  }

  public int getNumberOfAddConstraintQueries() {
    return constraint.get();
  }

  public int getNumberOfModelQueries() {
    return model.get();
  }

  public int getNumberOfUnsatCoreQueries() {
    return unsatCore.get();
  }

  public int getNumberOfIsUnsatQueries() {
    return unsat.getNumberOfIntervals();
  }

  public TimeSpan getSumTimeOfIsUnsatQueries() {
    return unsat.getSumTime();
  }

  public TimeSpan getMaxTimeOfIsUnsatQueries() {
    return unsat.getMaxTime();
  }

  public int getNumberOfAllSatQueries() {
    return allSat.getNumberOfIntervals();
  }

  public TimeSpan getSumTimeOfAllSatQueries() {
    return allSat.getSumTime();
  }

  public TimeSpan getMaxTimeOfAllSatQueries() {
    return allSat.getMaxTime();
  }

  public int getNumberOfInterpolationQueries() {
    return interpolation.getNumberOfIntervals();
  }

  public TimeSpan getSumTimeOfInterpolationQueries() {
    return interpolation.getSumTime();
  }

  public TimeSpan getMaxTimeOfInterpolationQueries() {
    return interpolation.getMaxTime();
  }

  public int getNumberOfBooleanOperations() {
    return booleanOperations.get();
  }

  public int getNumberOfVisits() {
    return visits.get();
  }

  public int getNumberOfNumericOperations() {
    return numericOperations.get();
  }

  public int getNumberOfArrayOperations() {
    return arrayOperations.get();
  }

  public int getNumberOfSLOperations() {
    return slOperations.get();
  }

  public int getNumberOfUFOperations() {
    return ufOperations.get();
  }

  public int getNumberOfQuantifierOperations() {
    return quantifierOperations.get();
  }

  public int getNumberOfBVOperations() {
    return bvOperations.get();
  }

  public int getNumberOfFPOperations() {
    return fpOperations.get();
  }

  public int getNumberOfModelEvaluationQueries() {
    return modelEvaluations.get();
  }

  public int getNumberOfModelListings() {
    return modelListings.get();
  }
}
