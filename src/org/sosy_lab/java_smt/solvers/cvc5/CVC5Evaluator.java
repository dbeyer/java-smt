// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import org.sosy_lab.java_smt.basicimpl.AbstractEvaluator;

public class CVC5Evaluator extends AbstractEvaluator<Term, Sort, TermManager> {

  private final Solver solver;

  CVC5Evaluator(CVC5AbstractProver<?> pProver, CVC5FormulaCreator pCreator) {
    super(pProver, pCreator);
    solver = pProver.solver;
  }

  @Override
  public Term evalImpl(Term f) {
    Preconditions.checkState(!isClosed());
    return solver.getValue(f);
  }
}
