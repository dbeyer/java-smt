// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;

public class CVC5QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Term, Sort, TermManager, Term> {

  private final TermManager termManager;
  private final Solver solver;

  protected CVC5QuantifiedFormulaManager(CVC5FormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
    termManager = pFormulaCreator.getEnv();
    solver = new Solver(termManager);
  }

  /*
   * (non-Javadoc) CVC4s quantifier support is dependent on the options used.
   * Without any options it tends to run infinitely on many theories or examples.
   * There are 2 options improving this: full-saturate-quant and sygus-inst.
   * full-saturate-quant is activated in JavaSMT per default.
   * You can try combinations of them, or just one if a query is not solveable.
   * More info on full-saturate-quant: Enables "enumerative instantiation",
   * see: https://homepage.divms.uiowa.edu/~ajreynol/tacas18.pdf
   * More info on sygus-inst: Enables syntax-guided instantiation,
   * see https://homepage.divms.uiowa.edu/~ajreynol/tacas21.pdf
   * This approach tends to work well when the quantified formula involves
   * theories (e.g. strings) where more traditional quantifier instantiation
   * heuristics do not apply.
   * This applies to CVC4 and CVC5!
   */
  @Override
  protected Term eliminateQuantifiers(Term input) throws SolverException, InterruptedException {
    try {
      return solver.getQuantifierElimination(input);
    } catch (RuntimeException e) {
      // quantifier elimination failed, simply return the input
      return input;
    }
  }

  /*
   * Makes the quantifier entered in CVC4/CVC5. Note that CVC4/CVC5 uses bound variables in
   * quantified formulas instead of the normal free vars. We create a bound copy for every var
   * and substitute the free var for the bound var in the body Formula. Note that CVC4/CVC5 uses
   * their internal Lists for the variable list in quantifiers.
   */
  @Override
  public Term mkQuantifier(Quantifier pQ, List<Term> pVars, Term pBody) {
    if (pVars.isEmpty()) {
      throw new IllegalArgumentException("Empty variable list for quantifier.");
    } else {
      List<Term> boundVars = new ArrayList<>();
      Term substBody = pBody;
      // every free needs a bound copy. As the internal Id is different for every variable, even
      // with the same name, this is fine.
      for (Term var : pVars) {
        Term boundCopy = ((CVC5FormulaCreator) formulaCreator).makeBoundCopy(var);
        boundVars.add(boundCopy);
        substBody = substBody.substitute(var, boundCopy);
      }

      Kind quant = pQ == Quantifier.EXISTS ? Kind.EXISTS : Kind.FORALL;
      Term boundVarsList = termManager.mkTerm(Kind.VARIABLE_LIST, boundVars.toArray(new Term[0]));
      return termManager.mkTerm(quant, boundVarsList, substBody);
    }
  }
}
