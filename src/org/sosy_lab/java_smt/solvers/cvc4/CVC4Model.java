// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.SmtEngine;
import edu.stanford.CVC4.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

public class CVC4Model extends CachingAbstractModel<Expr, Type, ExprManager> {

  private final ImmutableList<ValueAssignment> model;
  private final SmtEngine smtEngine;
  private final ImmutableList<Expr> assertedExpressions;
  private final CVC4TheoremProver prover;
  protected boolean closed = false;

  CVC4Model(
      CVC4TheoremProver pProver,
      CVC4FormulaCreator pCreator,
      SmtEngine pSmtEngine,
      Collection<Expr> pAssertedExpressions) {
    super(pCreator);
    smtEngine = pSmtEngine;
    prover = pProver;
    assertedExpressions = ImmutableList.copyOf(pAssertedExpressions);

    // We need to generate and save this at construction time as CVC4 has no functionality to give a
    // persistent reference to the model. If the SMT engine is used somewhere else, the values we
    // get out of it might change!
    model = generateModel();
  }

  @Override
  public Expr evalImpl(Expr f) {
    Preconditions.checkState(!closed);
    return getValue(f);
  }

  /** we need to convert the given expression into the current context. */
  private Expr getValue(Expr f) {
    return prover.exportExpr(smtEngine.getValue(prover.importExpr(f)));
  }

  private ImmutableList<ValueAssignment> generateModel() {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    for (Expr expr : assertedExpressions) {
      creator.extractVariablesAndUFs(expr, true, (name, f) -> builder.add(getAssignment(f)));
    }
    return builder.build().asList();
  }

  private ValueAssignment getAssignment(Expr pKeyTerm) {
    List<Object> argumentInterpretation = new ArrayList<>();
    for (Expr param : pKeyTerm) {
      argumentInterpretation.add(evaluateImpl(param));
    }
    Expr name = pKeyTerm.hasOperator() ? pKeyTerm.getOperator() : pKeyTerm; // extract UF name
    String nameStr = name.toString();
    if (nameStr.startsWith("|") && nameStr.endsWith("|")) {
      nameStr = nameStr.substring(1, nameStr.length() - 1);
    }
    Expr valueTerm = getValue(pKeyTerm);
    Formula keyFormula = creator.encapsulateWithTypeOf(pKeyTerm);
    Formula valueFormula = creator.encapsulateWithTypeOf(valueTerm);
    BooleanFormula equation =
        creator.encapsulateBoolean(creator.getEnv().mkExpr(Kind.EQUAL, pKeyTerm, valueTerm));
    Object value = creator.convertValue(pKeyTerm, valueTerm);
    return new ValueAssignment(
        keyFormula, valueFormula, equation, nameStr, value, argumentInterpretation);
  }

  @Override
  public void close() {
    prover.unregisterModel(this);
    closed = true;
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    return model;
  }
}
