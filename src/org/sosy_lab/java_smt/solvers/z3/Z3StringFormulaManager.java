// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 AlejandroSerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.primitives.Longs;
import com.microsoft.z3.Native;
import java.util.List;
import org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager;

class Z3StringFormulaManager extends AbstractStringFormulaManager<Long, Long, Long, Long> {

  private final long z3context;

  Z3StringFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    z3context = creator.getEnv();
  }

  @Override
  protected Long makeStringImpl(String pValue) {
    String str = escapeUnicodeForSmtlib(unescapeUnicodeForSmtlib(pValue));
    return Native.mkString(z3context, str);
  }

  @Override
  protected Long makeVariableImpl(String varName) {
    long type = getFormulaCreator().getStringType();
    return getFormulaCreator().makeVariable(type, varName);
  }

  @Override
  protected Long equal(Long pParam1, Long pParam2) {
    return Native.mkEq(z3context, pParam1, pParam2);
  }

  @Override
  protected Long greaterThan(Long pParam1, Long pParam2) {
    return lessThan(pParam2, pParam1);
  }

  @Override
  protected Long greaterOrEquals(Long pParam1, Long pParam2) {
    return lessOrEquals(pParam2, pParam1);
  }

  @Override
  protected Long lessThan(Long pParam1, Long pParam2) {
    return Native.mkStrLt(z3context, pParam1, pParam2);
  }

  @Override
  protected Long lessOrEquals(Long pParam1, Long pParam2) {
    return Native.mkStrLe(z3context, pParam1, pParam2);
  }

  @Override
  protected Long length(Long pParam) {
    return Native.mkSeqLength(z3context, pParam);
  }

  @Override
  protected Long concatImpl(List<Long> parts) {
    Preconditions.checkArgument(!parts.isEmpty());
    return Native.mkSeqConcat(z3context, parts.size(), Longs.toArray(parts));
  }

  @Override
  protected Long prefix(Long prefix, Long str) {
    return Native.mkSeqPrefix(z3context, prefix, str);
  }

  @Override
  protected Long suffix(Long suffix, Long str) {
    return Native.mkSeqSuffix(z3context, suffix, str);
  }

  @Override
  protected Long in(Long str, Long regex) {
    return Native.mkSeqInRe(z3context, str, regex);
  }

  @Override
  protected Long contains(Long str, Long part) {
    return Native.mkSeqContains(z3context, str, part);
  }

  @Override
  protected Long indexOf(Long str, Long part, Long startIndex) {
    return Native.mkSeqIndex(z3context, str, part, startIndex);
  }

  @Override
  protected Long charAt(Long str, Long index) {
    return Native.mkSeqAt(z3context, str, index);
  }

  @Override
  protected Long substring(Long str, Long index, Long length) {
    return Native.mkSeqExtract(z3context, str, index, length);
  }

  @Override
  protected Long replace(Long fullStr, Long target, Long replacement) {
    return Native.mkSeqReplace(z3context, fullStr, target, replacement);
  }

  @Override
  protected Long replaceAll(Long fullStr, Long target, Long replacement) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected Long makeRegexImpl(String value) {
    Long str = makeStringImpl(value);
    return Native.mkSeqToRe(z3context, str);
  }

  @Override
  protected Long noneImpl() {
    return Native.mkReEmpty(z3context, formulaCreator.getRegexType());
  }

  @Override
  protected Long allImpl() {
    return Native.mkReFull(z3context, formulaCreator.getRegexType());
  }

  @Override
  protected Long allCharImpl() {
    return Native.mkReAllchar(z3context, formulaCreator.getRegexType());
  }

  @Override
  protected Long range(Long start, Long end) {
    return Native.mkReRange(z3context, start, end);
  }

  @Override
  protected Long concatRegexImpl(List<Long> parts) {
    if (parts.isEmpty()) {
      return noneImpl();
    }
    return Native.mkReConcat(z3context, parts.size(), Longs.toArray(parts));
  }

  @Override
  protected Long union(Long pParam1, Long pParam2) {
    return Native.mkReUnion(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long intersection(Long pParam1, Long pParam2) {
    return Native.mkReIntersect(z3context, 2, new long[] {pParam1, pParam2});
  }

  @Override
  protected Long closure(Long pParam) {
    return Native.mkReStar(z3context, pParam);
  }

  @Override
  protected Long complement(Long pParam) {
    return Native.mkReComplement(z3context, pParam);
  }

  @Override
  protected Long toIntegerFormula(Long pParam) {
    return Native.mkStrToInt(z3context, pParam);
  }

  @Override
  protected Long toStringFormula(Long pParam) {
    return Native.mkIntToStr(z3context, pParam);
  }

  @Override
  protected Long toCodePoint(Long pParam) {
    return Native.mkStringToCode(z3context, pParam);
  }

  @Override
  protected Long fromCodePoint(Long pParam) {
    return Native.mkStringFromCode(z3context, pParam);
  }
}
