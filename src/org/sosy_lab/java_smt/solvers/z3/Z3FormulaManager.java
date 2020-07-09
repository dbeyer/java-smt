// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.microsoft.z3.Native;
import com.microsoft.z3.Z3Exception;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class Z3FormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  private final Z3FormulaCreator formulaCreator;

  @SuppressWarnings("checkstyle:parameternumber")
  Z3FormulaManager(
      Z3FormulaCreator pFormulaCreator,
      Z3UFManager pFunctionManager,
      Z3BooleanFormulaManager pBooleanManager,
      Z3IntegerFormulaManager pIntegerManager,
      Z3RationalFormulaManager pRationalManager,
      Z3BitvectorFormulaManager pBitpreciseManager,
      Z3FloatingPointFormulaManager pFloatingPointManager,
      Z3QuantifiedFormulaManager pQuantifiedManager,
      Z3ArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        pFloatingPointManager,
        pQuantifiedManager,
        pArrayManager,
        null);
    formulaCreator = pFormulaCreator;
  }

  @Override
  public BooleanFormula parse(String str) throws IllegalArgumentException {

    // TODO do we need sorts or decls?
    // the context should know them already,
    // TODO check this
    long[] sortSymbols = new long[0];
    long[] sorts = new long[0];
    long[] declSymbols = new long[0];
    long[] decls = new long[0];
    long e =
        Native.parseSmtlib2String(
            getEnvironment(),
            str,
            sorts.length,
            sortSymbols,
            sorts,
            declSymbols.length,
            declSymbols,
            decls);

    final int size = Native.astVectorSize(getEnvironment(), e);
    Preconditions.checkState(size == 1, "parsing expects exactly one asserted term.");
    final long term = Native.astVectorGet(getEnvironment(), e, 0);
    return getFormulaCreator().encapsulateBoolean(term);
  }

  @Override
  protected BooleanFormula applyQELightImpl(BooleanFormula pF) throws InterruptedException {
    return applyTacticImpl(pF, "qe-light");
  }

  @Override
  protected BooleanFormula applyCNFImpl(BooleanFormula pF) throws InterruptedException {
    return applyTacticImpl(pF, "tseitin-cnf");
  }

  @Override
  protected BooleanFormula applyNNFImpl(BooleanFormula pF) throws InterruptedException {
    return applyTacticImpl(pF, "nnf");
  }

  private BooleanFormula applyTacticImpl(BooleanFormula pF, String tacticName)
      throws InterruptedException {
    long out =
        formulaCreator.applyTactic(getFormulaCreator().getEnv(), extractInfo(pF), tacticName);
    return formulaCreator.encapsulateBoolean(out);
  }

  @Override
  public Appender dumpFormula(final Long expr) {
    assert getFormulaCreator().getFormulaType(expr) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    return Appenders.fromToStringMethod(
        new Object() {
          @Override
          public String toString() {
            // Serializing a solver is a simplest way to dump a formula in Z3,
            // cf https://github.com/Z3Prover/z3/issues/397
            long z3solver = Native.mkSolver(getEnvironment());
            Native.solverIncRef(getEnvironment(), z3solver);
            Native.solverAssert(getEnvironment(), z3solver, expr);
            String serialized = Native.solverToString(getEnvironment(), z3solver);
            Native.solverDecRef(getEnvironment(), z3solver);
            return serialized;
          }
        });
  }

  @Override
  protected Long simplify(Long pF) throws InterruptedException {
    try {
      return Native.simplify(getFormulaCreator().getEnv(), pF);
    } catch (Z3Exception exp) {
      throw formulaCreator.handleZ3Exception(exp);
    }
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    long[] changeFrom = new long[fromToMapping.size()];
    long[] changeTo = new long[fromToMapping.size()];
    int idx = 0;
    for (Map.Entry<? extends Formula, ? extends Formula> e : fromToMapping.entrySet()) {
      changeFrom[idx] = extractInfo(e.getKey());
      changeTo[idx] = extractInfo(e.getValue());
      idx++;
    }
    FormulaType<T> type = getFormulaType(f);
    return getFormulaCreator()
        .encapsulate(
            type,
            Native.substitute(
                getFormulaCreator().getEnv(),
                extractInfo(f),
                fromToMapping.size(),
                changeFrom,
                changeTo));
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula other, FormulaManager otherManager) {
    if (otherManager instanceof Z3FormulaManager) {
      Z3FormulaManager o = (Z3FormulaManager) otherManager;
      long otherZ3Context = o.getEnvironment();
      if (otherZ3Context == getEnvironment()) {

        // Same context.
        return other;
      } else {

        // Z3-to-Z3 translation.
        long translatedAST = Native.translate(otherZ3Context, extractInfo(other), getEnvironment());
        return getFormulaCreator().encapsulateBoolean(translatedAST);
      }
    }
    return super.translateFrom(other, otherManager);
  }
}
