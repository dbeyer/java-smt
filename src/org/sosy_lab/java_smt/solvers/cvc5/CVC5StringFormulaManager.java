// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import io.github.cvc5.Kind;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.util.List;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

class CVC5StringFormulaManager extends AbstractStringFormulaManager<Term, Sort, TermManager, Term> {

  private final TermManager termManager;

  CVC5StringFormulaManager(CVC5FormulaCreator pCreator) {
    super(pCreator);
    termManager = pCreator.getEnv();
  }

  @Override
  protected Term makeStringImpl(String pValue) {
    return termManager.mkString(escapeUnicodeForSmtlib(pValue), true);
  }

  @Override
  protected Term makeVariableImpl(String varName) {
    Sort type = getFormulaCreator().getStringType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Term equal(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.EQUAL, pParam1, pParam2);
  }

  @Override
  protected Term greaterThan(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.STRING_LT, pParam2, pParam1);
  }

  @Override
  protected Term greaterOrEquals(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.STRING_LEQ, pParam2, pParam1);
  }

  @Override
  protected Term lessThan(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.STRING_LT, pParam1, pParam2);
  }

  @Override
  protected Term lessOrEquals(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.STRING_LEQ, pParam1, pParam2);
  }

  @Override
  protected Term length(Term pParam) {
    return termManager.mkTerm(Kind.STRING_LENGTH, pParam);
  }

  @Override
  protected Term concatImpl(List<Term> parts) {
    Preconditions.checkArgument(parts.size() > 1);
    return termManager.mkTerm(Kind.STRING_CONCAT, parts.toArray(new Term[0]));
  }

  @Override
  protected Term prefix(Term prefix, Term str) {
    return termManager.mkTerm(Kind.STRING_PREFIX, prefix, str);
  }

  @Override
  protected Term suffix(Term suffix, Term str) {
    return termManager.mkTerm(Kind.STRING_SUFFIX, suffix, str);
  }

  @Override
  protected Term in(Term str, Term regex) {
    return termManager.mkTerm(Kind.STRING_IN_REGEXP, str, regex);
  }

  @Override
  protected Term contains(Term str, Term part) {
    return termManager.mkTerm(Kind.STRING_CONTAINS, str, part);
  }

  @Override
  protected Term indexOf(Term str, Term part, Term startIndex) {
    return termManager.mkTerm(Kind.STRING_INDEXOF, str, part, startIndex);
  }

  @Override
  protected Term charAt(Term str, Term index) {
    return termManager.mkTerm(Kind.STRING_CHARAT, str, index);
  }

  @Override
  protected Term substring(Term str, Term index, Term length) {
    return termManager.mkTerm(Kind.STRING_SUBSTR, str, index, length);
  }

  @Override
  protected Term replace(Term fullStr, Term target, Term replacement) {
    return termManager.mkTerm(Kind.STRING_REPLACE, fullStr, target, replacement);
  }

  @Override
  protected Term replaceAll(Term fullStr, Term target, Term replacement) {
    return termManager.mkTerm(Kind.STRING_REPLACE_ALL, fullStr, target, replacement);
  }

  @Override
  protected Term makeRegexImpl(String value) {
    Term str = makeStringImpl(value);
    return termManager.mkTerm(Kind.STRING_TO_REGEXP, str);
  }

  @Override
  protected Term noneImpl() {
    return termManager.mkTerm(Kind.REGEXP_NONE);
  }

  @Override
  protected Term allImpl() {
    return termManager.mkTerm(Kind.REGEXP_COMPLEMENT, noneImpl());
  }

  @Override
  protected Term allCharImpl() {
    return termManager.mkTerm(Kind.REGEXP_ALLCHAR);
  }

  @Override
  protected Term range(Term start, Term end) {
    return termManager.mkTerm(Kind.REGEXP_RANGE, start, end);
  }

  @Override
  protected Term concatRegexImpl(List<Term> parts) {
    Preconditions.checkArgument(parts.size() > 1);
    return termManager.mkTerm(Kind.REGEXP_CONCAT, parts.toArray(new Term[0]));
  }

  @Override
  protected Term union(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.REGEXP_UNION, pParam1, pParam2);
  }

  @Override
  protected Term intersection(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.REGEXP_INTER, pParam1, pParam2);
  }

  @Override
  protected Term closure(Term pParam) {
    return termManager.mkTerm(Kind.REGEXP_STAR, pParam);
  }

  @Override
  protected Term complement(Term pParam) {
    return termManager.mkTerm(Kind.REGEXP_COMPLEMENT, pParam);
  }

  @Override
  protected Term difference(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.REGEXP_DIFF, pParam1, pParam2);
  }

  @Override
  protected Term toIntegerFormula(Term pParam) {
    return termManager.mkTerm(Kind.STRING_TO_INT, pParam);
  }

  @Override
  protected Term toStringFormula(Term pParam) {
    Preconditions.checkArgument(
        pParam.getSort().equals(termManager.getIntegerSort()) || pParam.isIntegerValue(),
        "CVC5 only supports INT to STRING conversion.");
    return termManager.mkTerm(Kind.STRING_FROM_INT, pParam);
  }

  @Override
  protected Term toCodePoint(Term pParam) {
    return termManager.mkTerm(Kind.STRING_TO_CODE, pParam);
  }

  @Override
  protected Term fromCodePoint(Term pParam) {
    return termManager.mkTerm(Kind.STRING_FROM_CODE, pParam);
  }
}
