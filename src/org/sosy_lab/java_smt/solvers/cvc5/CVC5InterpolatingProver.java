// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class CVC5InterpolatingProver extends CVC5AbstractProver<String>
    implements InterpolatingProverEnvironment<String> {

  private final TermManager termManager = creator.getEnv();

  private final FormulaManager mgr;
  private final Set<ProverOptions> solverOptions;
  private final ImmutableMap<String, String> furtherOptionsMap;
  private final int seed;
  private final CVC5BooleanFormulaManager bmgr;
  private final boolean validateInterpolants;

  CVC5InterpolatingProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      Set<ProverOptions> pOptions,
      FormulaManager pMgr,
      ImmutableMap<String, String> pFurtherOptionsMap,
      boolean pValidateInterpolants) {
    super(pFormulaCreator, pShutdownNotifier, randomSeed, pOptions, pMgr, pFurtherOptionsMap);
    mgr = pMgr;
    solverOptions = pOptions;
    seed = randomSeed;
    bmgr = (CVC5BooleanFormulaManager) mgr.getBooleanFormulaManager();
    validateInterpolants = pValidateInterpolants;
    furtherOptionsMap = pFurtherOptionsMap;
  }

  /**
   * Sets the same solver Options of the Original Solver to the separate solvertoSet, except for
   * produce-interpolants which is set here. From CVC5AbstractProver Line 66
   */
  @Override
  protected void setSolverOptions(
      int randomSeed,
      Set<ProverOptions> pOptions,
      ImmutableMap<String, String> pFurtherOptionsMap,
      Solver pSolver) {
    super.setSolverOptions(randomSeed, pOptions, pFurtherOptionsMap, pSolver);
    pSolver.setOption("produce-interpolants", "true");
  }

  @Override
  protected String addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    return super.addConstraint0(constraint);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<String> pFormulasOfA)
      throws SolverException, InterruptedException {
    checkState(!closed);
    checkArgument(
        getAssertedConstraintIds().containsAll(pFormulasOfA),
        "interpolation can only be done over previously asserted formulas.");

    final Set<Term> assertedFormulas =
        transformedImmutableSetCopy(getAssertedFormulas(), creator::extractInfo);
    final Set<Term> formulasOfA =
        transformedImmutableSetCopy(pFormulasOfA, assertedTerms.peek()::get);
    final Set<Term> formulasOfB = Sets.difference(assertedFormulas, formulasOfA);

    Term itp = getCVC5Interpolation(formulasOfA, formulasOfB);
    return creator.encapsulateBoolean(itp);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(List<? extends Collection<String>> partitions)
      throws SolverException, InterruptedException {
    checkArgument(!partitions.isEmpty(), "at least one partition should be available.");
    final ImmutableSet<String> assertedConstraintIds = getAssertedConstraintIds();
    checkArgument(
        partitions.stream().allMatch(assertedConstraintIds::containsAll),
        "interpolation can only be done over previously asserted formulas.");

    final int n = partitions.size();
    final List<BooleanFormula> itps = new ArrayList<>();
    Term previousItp = termManager.mkTrue();
    for (int i = 1; i < n; i++) {
      Collection<Term> formulasA =
          FluentIterable.from(partitions.get(i - 1))
              .transform(assertedTerms.peek()::get)
              .append(previousItp)
              .toSet();
      Collection<Term> formulasB =
          FluentIterable.concat(partitions.subList(i, n))
              .transform(assertedTerms.peek()::get)
              .toSet();
      Term itp = getCVC5Interpolation(formulasA, formulasB);
      itps.add(creator.encapsulateBoolean(itp));
      previousItp = itp;
    }
    return itps;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<String>> partitionedFormulas, int[] startOfSubTree) {
    throw new UnsupportedOperationException(
        "directly receiving tree interpolants is not supported."
            + "Use another solver or another strategy for interpolants.");
  }

  /**
   * This method computes Craig interpolants for a pair of formulas using CVC5-Interpolation.
   *
   * <p>CVC5's interpolation returns an interpolant I for two input formulas A and B, such that the
   * following holds:
   *
   * <ol>
   *   <li>(A -> I) is valid (1CVC5),
   *   <li>(I -> B) is valid (2CVC5), and
   *   <li>I only contains symbols from A and B (3CVC5).
   * </ol>
   *
   * <p>Craig interpolation returns an interpolant psi for two input formulas phi- and phi+, such
   * that the following holds:
   *
   * <ol>
   *   <li>(phi- -> psi) is valid (1Craig),
   *   <li>(psi && phi+) is unsatisfiable (2Craig), and
   *   <li>psi only contains symbols from phi- and phi+ (3Craig).
   * </ol>
   *
   * <p>We can transform CVC5 interpolation to Craig interpolation by negating the formula B, i.e.,
   * the CVC5 interpolant for input (A, B) represents a Craig interpolant for input (A, not B). Here
   * is a proof for this:
   *
   * <ol>
   *   <li>(1CVC5) <=> (1Craig): holds, due to substitution of A with phi- and I with psi.
   *   <li>(2CVC5) <=> (I -> B) is valid <=> ((not I) || B) is valid <=> (not (I && (not B))) is
   *       valid <=> (I && (not B)) is unsatisfiable <=> (2Craig) holds, due to substitution of I
   *       with psi and (not B) with phi+.
   *   <li>(3CVC5) <=> (3Craig): holds, negation does not change symbols.
   * </ol>
   *
   * <p>Hence, CVC5's interpolation produces an equivalent interpolation result to Craig
   * interpolation, if the input B is negated.
   *
   * <p>Please note, that this method will use a different proof for each call, and thus, a sequence
   * of interpolation queries will most likely not produce sequential Craig interpolants on its own.
   * Therefore, the caller has to use constraints based on previously computed interpolants.
   *
   * @param formulasA formulas for psi- of the interpolation query
   * @param formulasB formulas for psi+ of the interpolation (will be negated internally)
   * @return interpolation result following the definition of Craig interpolation.
   */
  private Term getCVC5Interpolation(Collection<Term> formulasA, Collection<Term> formulasB) {
    Term phiPlus = bmgr.andImpl(formulasA);
    Term phiMinus = bmgr.andImpl(formulasB);

    // Uses a separate Solver instance to leave the original solver-context unmodified
    Solver itpSolver = new Solver(termManager);
    setSolverOptions(seed, solverOptions, furtherOptionsMap, itpSolver);

    Term interpolant;
    try {
      itpSolver.assertFormula(phiPlus);
      interpolant = itpSolver.getInterpolant(termManager.mkTerm(Kind.NOT, phiMinus));
    } finally {
      itpSolver.deletePointer();
    }

    if (validateInterpolants) {
      checkInterpolationCriteria(interpolant, phiPlus, phiMinus);
    }

    return interpolant;
  }

  /**
   * Checks, whether the returned interpolant indeed satisfies Craig-Interpolation and Symbol Usage.
   *
   * @param interpolant the given Interpolant for aTerm and bTerm after Craig Interpolation
   * @param phiPlus the phi+ Term in Craig Interpolation
   * @param phiMinus the phi- Term in Craig Interpolation (before negation for CVC5-Interpolation)
   */
  private void checkInterpolationCriteria(Term interpolant, Term phiPlus, Term phiMinus) {

    // checks that every Symbol of the interpolant appears either in term A or term B
    Set<String> interpolantSymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(interpolant)).keySet();
    Set<String> interpolASymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(phiPlus)).keySet();
    Set<String> interpolBSymbols =
        mgr.extractVariablesAndUFs(creator.encapsulateBoolean(phiMinus)).keySet();
    Set<String> intersection = Sets.intersection(interpolASymbols, interpolBSymbols);
    checkState(
        intersection.containsAll(interpolantSymbols),
        "Interpolant contains symbols %s that are not part of both input formulas.",
        Sets.difference(interpolantSymbols, intersection));

    // build and check both Craig interpolation formulas with the generated interpolant.
    Solver validationSolver = new Solver(termManager);
    // interpolation option is not required for validation
    super.setSolverOptions(seed, solverOptions, furtherOptionsMap, validationSolver);
    try {
      validationSolver.push();
      validationSolver.assertFormula(termManager.mkTerm(Kind.IMPLIES, phiPlus, interpolant));
      checkState(
          validationSolver.checkSat().isSat(),
          "Invalid Craig interpolation: phi+ does not imply the interpolant.");
      validationSolver.pop();

      validationSolver.push();
      validationSolver.assertFormula(termManager.mkTerm(Kind.AND, interpolant, phiMinus));
      checkState(
          validationSolver.checkSat().isUnsat(),
          "Invalid Craig interpolation: interpolant does not contradict phi-.");
      validationSolver.pop();

    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException(
          "Failure when validating interpolant '" + interpolant + "'.", e);

    } finally {
      validationSolver.deletePointer();
    }
  }
}
