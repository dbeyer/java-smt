// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import static com.google.common.base.Preconditions.checkState;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.collect.Collections3;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

@SuppressWarnings("ClassTypeParameterName")
abstract class SmtInterpolAbstractProver<T, AF> extends AbstractProver<T> {

  private boolean closed = false;
  protected final SmtInterpolEnvironment env;
  protected final FormulaCreator<Term, Sort, SmtInterpolEnvironment, FunctionSymbol> creator;
  protected final SmtInterpolFormulaManager mgr;
  protected final Deque<List<AF>> assertedFormulas = new ArrayDeque<>();
  protected final Map<String, Term> annotatedTerms = new HashMap<>(); // Collection of termNames

  private static final String PREFIX = "term_"; // for termnames
  private static final UniqueIdGenerator termIdGenerator =
      new UniqueIdGenerator(); // for different termnames

  SmtInterpolAbstractProver(SmtInterpolFormulaManager pMgr, Set<ProverOptions> options) {
    super(options);
    checkState(
        pMgr.getEnvironment().getStackDepth() == 0,
        "Not allowed to create a new prover environment while solver stack is still non-empty, "
            + "parallel stacks are not supported.");
    mgr = pMgr;
    env = pMgr.createEnvironment();
    creator = pMgr.getFormulaCreator();
  }

  protected boolean isClosed() {
    return closed;
  }

  @Override
  public void push() {
    checkState(!closed);
    assertedFormulas.push(new ArrayList<>());
    env.push(1);
  }

  @Override
  public void pop() {
    checkState(!closed);
    assertedFormulas.pop();
    env.pop(1);
  }

  @Override
  public boolean isUnsat() throws InterruptedException {
    checkState(!closed);
    return !env.checkSat();
  }

  @Override
  public SmtInterpolModel getModel() {
    checkState(!closed);
    checkGenerateModels();
    return new SmtInterpolModel(env.getModel(), creator);
  }

  protected static String generateTermName() {
    return PREFIX + termIdGenerator.getFreshId();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    checkState(!isClosed());
    checkGenerateUnsatCores();
    return getUnsatCore0();
  }

  /**
   * small helper method, because we guarantee that {@link
   * ProverOptions#GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS} is independent of {@link
   * ProverOptions#GENERATE_UNSAT_CORE}.
   */
  private List<BooleanFormula> getUnsatCore0() {
    return Collections3.transformedImmutableListCopy(
        env.getUnsatCore(),
        input -> creator.encapsulateBoolean(annotatedTerms.get(input.toString())));
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws InterruptedException {
    checkState(!isClosed());
    checkGenerateUnsatCoresOverAssumptions();
    push();
    checkState(
        annotatedTerms.isEmpty(),
        "Empty environment required for UNSAT core over assumptions: %s",
        annotatedTerms);
    for (BooleanFormula assumption : assumptions) {
      String termName = generateTermName();
      Term t = mgr.extractInfo(assumption);
      Term annotated = env.annotate(t, new Annotation(":named", termName));
      annotatedTerms.put(termName, t);
      env.assertTerm(annotated);
    }
    Optional<List<BooleanFormula>> result =
        isUnsat() ? Optional.of(getUnsatCore0()) : Optional.empty();
    pop();
    return result;
  }

  @Override
  public void close() {
    checkState(!closed);
    assertedFormulas.clear();
    annotatedTerms.clear();
    env.pop(env.getStackDepth());
    closed = true;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Assumption-solving is not supported.");
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    checkState(!isClosed());
    checkGenerateAllSat();

    Term[] importantTerms = new Term[important.size()];
    int i = 0;
    for (BooleanFormula impF : important) {
      importantTerms[i++] = mgr.extractInfo(impF);
    }
    for (Term[] model : env.checkAllSat(importantTerms)) {
      callback.apply(Collections3.transformedImmutableListCopy(model, creator::encapsulateBoolean));
    }
    return callback.getResult();
  }
}
