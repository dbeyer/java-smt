// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.util.Collection;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

public class CVC5Model extends AbstractModel<Term, Sort, TermManager> {

  private final ImmutableList<ValueAssignment> model;
  private final TermManager termManager;
  private final Solver solver;
  private final ImmutableList<Term> assertedExpressions;

  @SuppressWarnings("unused")
  private final FormulaManager mgr;

  CVC5Model(
      CVC5AbstractProver<?> pProver,
      FormulaManager pMgr,
      CVC5FormulaCreator pCreator,
      Collection<Term> pAssertedExpressions) {
    super(pProver, pCreator);
    termManager = pCreator.getEnv();
    solver = pProver.solver;
    mgr = pMgr;
    assertedExpressions = ImmutableList.copyOf(pAssertedExpressions);

    // We need to generate and save this at construction time as CVC4 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = generateModel();
  }

  @Override
  public Term evalImpl(Term f) {
    Preconditions.checkState(!isClosed());
    return solver.getValue(f);
  }

  private ImmutableList<ValueAssignment> generateModel() {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    // Using creator.extractVariablesAndUFs we wouldn't get accurate information anymore as we
    // translate all bound vars back to their free counterparts in the visitor!
    for (Term expr : assertedExpressions) {
      // creator.extractVariablesAndUFs(expr, true, (name, f) -> builder.add(getAssignment(f)));
      recursiveAssignmentFinder(builder, expr);
    }
    return builder.build().asList();
  }

  // TODO this method is highly recursive and should be rewritten with a proper visitor
  private void recursiveAssignmentFinder(ImmutableSet.Builder<ValueAssignment> builder, Term expr) {
    try {
      Sort sort = expr.getSort();
      Kind kind = expr.getKind();
      if (kind == Kind.VARIABLE || sort.isFunction()) {
        // We don't care about functions, as thats just the function definition and the nested
        // lambda term
        // We don't care about bound vars (not in a UF), as they don't return a value.
        return;
      } else if (kind == Kind.CONSTANT) {
        // Vars and UFs, as well as bound vars in UFs!
        // In CVC5 consts are variables! Free variables (in CVC5s notation, we call them bound
        // variables, created with mkVar() can never have a value!)
        builder.add(getAssignment(expr));
      } else if (kind == Kind.FORALL || kind == Kind.EXISTS) {
        // Body of the quantifier, with bound vars!
        Term body = expr.getChild(1);
        recursiveAssignmentFinder(builder, body);
      } else if (kind == Kind.CONST_STRING
          || kind == Kind.CONST_ARRAY
          || kind == Kind.CONST_BITVECTOR
          || kind == Kind.CONST_BOOLEAN
          || kind == Kind.CONST_FLOATINGPOINT
          || kind == Kind.CONST_RATIONAL
          || kind == Kind.CONST_ROUNDINGMODE
          || kind == Kind.CONST_SEQUENCE) {
        // Constants, do nothing
      } else if (kind == Kind.APPLY_UF) {
        builder.add(getAssignmentForUf(expr));

      } else {
        // Only nested terms (AND, OR, ...) are left
        for (Term child : expr) {
          recursiveAssignmentFinder(builder, child);
        }
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException("Failure visiting the Term '" + expr + "'.", e);
    }
  }

  private ValueAssignment getAssignmentForUf(Term pKeyTerm) {
    // Ufs consist of arguments + 1 child, the first child is the function definition as a lambda
    // and the result, while the remaining children are the arguments. Note: we can't evaluate bound
    // variables!
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    boolean boundFound = false;
    // We don't want the first argument of uf applications as it is the declaration
    for (int i = 1; i < pKeyTerm.getNumChildren(); i++) {
      try {
        Term child = pKeyTerm.getChild(i);
        if (child.getKind().equals(Kind.VARIABLE)) {
          // Remember if we encountered bound variables
          boundFound = true;
          // Bound vars are extremely volatile in CVC5. Nearly every call to them ends in an
          // exception. Also we don't want to substitute them with their non bound values.
          argumentInterpretationBuilder.add(child.toString());
        } else {
          argumentInterpretationBuilder.add(evaluateImpl(child));
        }
      } catch (CVC5ApiException e) {
        throw new IllegalArgumentException("Failure visiting the Term '" + pKeyTerm + "'.", e);
      }
    }

    // In applied UFs the child with the name is the 0th child (as it is the declaration)
    String nameStr;
    try {
      nameStr = pKeyTerm.getChild(0).getSymbol();
    } catch (CVC5ApiException e) {
      nameStr = "UF";
    }

    if (nameStr.startsWith("|") && nameStr.endsWith("|")) {
      nameStr = nameStr.substring(1, nameStr.length() - 1);
    }

    Term valueTerm;
    // You can't get a value if there is a bound variable present
    if (!boundFound) {
      valueTerm = solver.getValue(pKeyTerm);
    } else {
      // But you may be able to get one nested in the function itself for some reason
      try {
        valueTerm = solver.getValue(pKeyTerm.getChild(0)).getChild(1);
      } catch (CVC5ApiException e) {
        throw new IndexOutOfBoundsException(
            "Accessed a non existing UF value while creating a CVC5 model.");
      }
    }

    Formula keyFormula = creator.encapsulateWithTypeOf(pKeyTerm);
    Formula valueFormula = creator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation =
        creator.encapsulateBoolean(termManager.mkTerm(Kind.EQUAL, pKeyTerm, valueTerm));
    Object value = creator.convertValue(pKeyTerm, valueTerm);

    return new ValueAssignment(
        keyFormula, valueFormula, equation, nameStr, value, argumentInterpretationBuilder.build());
  }

  private ValueAssignment getAssignment(Term pKeyTerm) {
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    for (int i = 0; i < pKeyTerm.getNumChildren(); i++) {
      try {
        argumentInterpretationBuilder.add(evaluateImpl(pKeyTerm.getChild(i)));
      } catch (CVC5ApiException e) {
        throw new IndexOutOfBoundsException(
            "Accessed a non existing UF value while creating a CVC5 model.");
      }
    }

    String nameStr = "";
    if (pKeyTerm.hasSymbol()) {
      nameStr = pKeyTerm.getSymbol();
    } else {
      // Default if there is no name
      nameStr = "UNKNOWN_VARIABLE";
    }

    if (nameStr.startsWith("|") && nameStr.endsWith("|")) {
      nameStr = nameStr.substring(1, nameStr.length() - 1);
    }

    Term valueTerm = solver.getValue(pKeyTerm);
    Formula keyFormula = creator.encapsulateWithTypeOf(pKeyTerm);
    Formula valueFormula = creator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation =
        creator.encapsulateBoolean(termManager.mkTerm(Kind.EQUAL, pKeyTerm, valueTerm));
    Object value = creator.convertValue(pKeyTerm, valueTerm);
    return new ValueAssignment(
        keyFormula, valueFormula, equation, nameStr, value, argumentInterpretationBuilder.build());
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }
}
