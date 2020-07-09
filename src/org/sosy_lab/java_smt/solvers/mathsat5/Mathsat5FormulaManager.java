// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_apply_substitution;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_from_smtlib2;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_simplify;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_to_smtlib2;

import com.google.common.base.Splitter;
import com.google.common.collect.Collections2;
import com.google.common.primitives.Longs;
import java.io.IOException;
import java.util.Collection;
import java.util.Map;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class Mathsat5FormulaManager extends AbstractFormulaManager<Long, Long, Long, Long> {

  @SuppressWarnings("checkstyle:parameternumber")
  Mathsat5FormulaManager(
      Mathsat5FormulaCreator creator,
      Mathsat5UFManager pFunctionManager,
      Mathsat5BooleanFormulaManager pBooleanManager,
      Mathsat5IntegerFormulaManager pIntegerManager,
      Mathsat5RationalFormulaManager pRationalManager,
      Mathsat5BitvectorFormulaManager pBitpreciseManager,
      Mathsat5FloatingPointFormulaManager pFloatingPointManager,
      Mathsat5ArrayFormulaManager pArrayManager) {
    super(
        creator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitpreciseManager,
        pFloatingPointManager,
        null,
        pArrayManager,
        null);
  }

  static long getMsatTerm(Formula pT) {
    return ((Mathsat5Formula) pT).getTerm();
  }

  static long[] getMsatTerm(Collection<? extends Formula> pFormulas) {
    return Longs.toArray(Collections2.transform(pFormulas, Mathsat5FormulaManager::getMsatTerm));
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    long f = msat_from_smtlib2(getEnvironment(), pS);
    return getFormulaCreator().encapsulateBoolean(f);
  }

  @Override
  public Appender dumpFormula(final Long f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    // Lazy invocation of msat_to_smtlib2 wrapped in an Appender.
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        String msatString = msat_to_smtlib2(getEnvironment(), f);
        // Adjust line breaks: assert needs to be on last line, so we remove all following breaks.
        boolean needsLinebreak = true;
        for (String part : Splitter.on('\n').split(msatString)) {
          out.append(part);
          if (needsLinebreak && part.startsWith("(assert")) {
            needsLinebreak = false;
          }
          if (needsLinebreak) {
            out.append('\n');
          }
        }
      }
    };
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
            msat_apply_substitution(
                getFormulaCreator().getEnv(),
                extractInfo(f),
                fromToMapping.size(),
                changeFrom,
                changeTo));
  }

  @Override
  protected Long simplify(Long f) throws InterruptedException {
    // we need to keep all variables, otherwise we will not return a equisatisfiable formula.
    // TODO we could expand the interface and let the user choose the variables.
    final Map<String, Long> variables = getFormulaCreator().extractVariablesAndUFs(f, true);
    final long[] protectedSymbols = Longs.toArray(variables.values());
    return msat_simplify(getFormulaCreator().getEnv(), f, protectedSymbols);
  }
}
