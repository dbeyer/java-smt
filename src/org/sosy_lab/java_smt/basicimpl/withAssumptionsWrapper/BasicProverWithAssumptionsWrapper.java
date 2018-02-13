/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;

public class BasicProverWithAssumptionsWrapper<T, P extends BasicProverEnvironment<T>>
    implements BasicProverEnvironment<T> {

  protected final P delegate;
  protected final List<BooleanFormula> solverAssumptionsAsFormula = new ArrayList<>();

  BasicProverWithAssumptionsWrapper(P pDelegate) {
    delegate = pDelegate;
  }

  protected void clearAssumptions() {
    for (int i = 0; i < solverAssumptionsAsFormula.size(); i++) {
      delegate.pop();
    }
    solverAssumptionsAsFormula.clear();
  }

  @Override
  public void pop() {
    clearAssumptions();
    delegate.pop();
  }

  @Override
  public T addConstraint(BooleanFormula constraint) throws InterruptedException {
    clearAssumptions();
    return delegate.addConstraint(constraint);
  }

  @Override
  public void push() {
    clearAssumptions();
    delegate.push();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    clearAssumptions();
    return delegate.isUnsat();
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    clearAssumptions();
    solverAssumptionsAsFormula.addAll(assumptions);
    for (BooleanFormula formula : assumptions) {
      registerPushedFormula(delegate.push(formula));
    }
    return delegate.isUnsat();
  }

  /** overridden in sub-class. */
  protected void registerPushedFormula(@SuppressWarnings("unused") T pPushResult) {}

  @Override
  public Model getModel() throws SolverException {
    return delegate.getModel();
  }

  @Override
  public ImmutableList<Model.ValueAssignment> getModelAssignments() throws SolverException {
    return delegate.getModelAssignments();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return delegate.getUnsatCore();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    clearAssumptions();
    return delegate.unsatCoreOverAssumptions(pAssumptions);
    //    if (isUnsatWithAssumptions(pAssumptions)) {
    //      // TODO project to pAssumptions?
    //      return Optional.of(getUnsatCore());
    //    } else {
    //      return Optional.empty();
    //    }
  }

  @Override
  public void close() {
    delegate.close();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> pCallback, List<BooleanFormula> pImportant)
      throws InterruptedException, SolverException {
    clearAssumptions();
    return delegate.allSat(pCallback, pImportant);
  }
}
