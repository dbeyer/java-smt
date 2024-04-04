// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.collect.ImmutableMap;
import io.github.cvc5.DatatypeConstructorDecl;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractEnumerationFormulaManager;

public class CVC5EnumerationFormulaManager
    extends AbstractEnumerationFormulaManager<Term, Sort, TermManager, Term> {

  private final TermManager termManager;
  private final Solver solver;

  protected CVC5EnumerationFormulaManager(CVC5FormulaCreator pCreator) {
    super(pCreator);
    termManager = pCreator.getEnv();
    solver = pCreator.getSolver();
  }

  @Override
  protected EnumType declareEnumeration0(EnumerationFormulaType pType) {
    DatatypeConstructorDecl[] constructors =
        pType.getElements().stream()
            .map(termManager::mkDatatypeConstructorDecl)
            .toArray(DatatypeConstructorDecl[]::new);
    Sort enumType = solver.declareDatatype(pType.getName(), constructors);

    // we store the constants for later access
    ImmutableMap.Builder<String, Term> constantsMapping = ImmutableMap.builder();
    for (String element : pType.getElements()) {
      Term decl = enumType.getDatatype().getConstructor(element).getTerm();
      constantsMapping.put(element, termManager.mkTerm(Kind.APPLY_CONSTRUCTOR, decl));
    }
    return new EnumType(pType, enumType, constantsMapping.buildOrThrow());
  }

  @Override
  protected Term equivalenceImpl(Term pF1, Term pF2) {
    return termManager.mkTerm(Kind.EQUAL, pF1, pF2);
  }
}
