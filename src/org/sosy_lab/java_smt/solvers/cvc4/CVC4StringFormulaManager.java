// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.base.Preconditions;
import edu.stanford.CVC4.CVC4String;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Type;
import edu.stanford.CVC4.vectorExpr;
import java.util.List;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

class CVC4StringFormulaManager extends AbstractStringFormulaManager<Expr, Type, ExprManager, Expr> {

  private final ExprManager exprManager;

  CVC4StringFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    exprManager = pCreator.getEnv();
  }

  @Override
  protected Expr makeStringImpl(String pValue) {
    String str = escapeUnicodeForSmtlib(unescapeUnicodeForSmtlib(pValue));
    return exprManager.mkConst(new CVC4String(str, true));
  }

  @Override
  protected Expr makeVariableImpl(String varName) {
    Type type = getFormulaCreator().getStringType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Expr equal(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Expr greaterThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.STRING_LT, pParam2, pParam1);
  }

  @Override
  protected Expr greaterOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.STRING_LEQ, pParam2, pParam1);
  }

  @Override
  protected Expr lessThan(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.STRING_LT, pParam1, pParam2);
  }

  @Override
  protected Expr lessOrEquals(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.STRING_LEQ, pParam1, pParam2);
  }

  @Override
  protected Expr length(Expr pParam) {
    return exprManager.mkExpr(Kind.STRING_LENGTH, pParam);
  }

  @Override
  protected Expr concatImpl(List<Expr> parts) {
    Preconditions.checkArgument(parts.size() > 1);
    vectorExpr vector = new vectorExpr();
    parts.forEach(vector::add);
    return exprManager.mkExpr(Kind.STRING_CONCAT, vector);
  }

  @Override
  protected Expr prefix(Expr prefix, Expr str) {
    return exprManager.mkExpr(Kind.STRING_PREFIX, prefix, str);
  }

  @Override
  protected Expr suffix(Expr suffix, Expr str) {
    return exprManager.mkExpr(Kind.STRING_SUFFIX, suffix, str);
  }

  @Override
  protected Expr in(Expr str, Expr regex) {
    return exprManager.mkExpr(Kind.STRING_IN_REGEXP, str, regex);
  }

  @Override
  protected Expr contains(Expr str, Expr part) {
    return exprManager.mkExpr(Kind.STRING_STRCTN, str, part);
  }

  @Override
  protected Expr indexOf(Expr str, Expr part, Expr startIndex) {
    return exprManager.mkExpr(Kind.STRING_STRIDOF, str, part, startIndex);
  }

  @Override
  protected Expr charAt(Expr str, Expr index) {
    return exprManager.mkExpr(Kind.STRING_CHARAT, str, index);
  }

  @Override
  protected Expr substring(Expr str, Expr index, Expr length) {
    return exprManager.mkExpr(Kind.STRING_SUBSTR, str, index, length);
  }

  @Override
  protected Expr replace(Expr fullStr, Expr target, Expr replacement) {
    return exprManager.mkExpr(Kind.STRING_STRREPL, fullStr, target, replacement);
  }

  @Override
  protected Expr replaceAll(Expr fullStr, Expr target, Expr replacement) {
    return exprManager.mkExpr(Kind.STRING_STRREPLALL, fullStr, target, replacement);
  }

  @Override
  protected Expr makeRegexImpl(String value) {
    Expr str = makeStringImpl(value);
    return exprManager.mkExpr(Kind.STRING_TO_REGEXP, str);
  }

  @Override
  protected Expr noneImpl() {
    return exprManager.mkExpr(Kind.REGEXP_EMPTY, new vectorExpr());
  }

  @Override
  protected Expr allImpl() {
    return exprManager.mkExpr(Kind.REGEXP_COMPLEMENT, noneImpl());
  }

  @Override
  protected Expr allCharImpl() {
    return exprManager.mkExpr(Kind.REGEXP_SIGMA, new vectorExpr());
  }

  @Override
  protected Expr range(Expr start, Expr end) {
    return exprManager.mkExpr(Kind.REGEXP_RANGE, start, end);
  }

  @Override
  protected Expr concatRegexImpl(List<Expr> parts) {
    Preconditions.checkArgument(parts.size() > 1);
    vectorExpr vector = new vectorExpr();
    parts.forEach(vector::add);
    return exprManager.mkExpr(Kind.REGEXP_CONCAT, vector);
  }

  @Override
  protected Expr union(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.REGEXP_UNION, pParam1, pParam2);
  }

  @Override
  protected Expr intersection(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.REGEXP_INTER, pParam1, pParam2);
  }

  @Override
  protected Expr closure(Expr pParam) {
    return exprManager.mkExpr(Kind.REGEXP_STAR, pParam);
  }

  @Override
  protected Expr complement(Expr pParam) {
    return exprManager.mkExpr(Kind.REGEXP_COMPLEMENT, pParam);
  }

  @Override
  protected Expr difference(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.REGEXP_DIFF, pParam1, pParam2);
  }

  @Override
  protected Expr toIntegerFormula(Expr pParam) {
    return exprManager.mkExpr(Kind.STRING_STOI, pParam);
  }

  @Override
  protected Expr toStringFormula(Expr pParam) {
    return exprManager.mkExpr(Kind.STRING_ITOS, pParam);
  }

  @Override
  protected Expr toCodePoint(Expr pParam) {
    return exprManager.mkExpr(Kind.STRING_TO_CODE, pParam);
  }

  @Override
  protected Expr fromCodePoint(Expr pParam) {
    return exprManager.mkExpr(Kind.STRING_FROM_CODE, pParam);
  }
}
