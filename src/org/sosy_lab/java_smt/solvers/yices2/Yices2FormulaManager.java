// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import static com.google.common.base.CharMatcher.inRange;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.YICES_APP_TERM;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvtype_size;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_parse_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_child;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_constructor;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_is_bitvector;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_num_children;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_to_string;

import com.google.common.base.CharMatcher;
import com.google.common.base.Preconditions;
import com.google.common.base.Strings;
import java.io.IOException;
import java.util.Locale;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class Yices2FormulaManager extends AbstractFormulaManager<Integer, Integer, Long, Integer> {

  private static final CharMatcher LETTERS = inRange('a', 'z').or(inRange('A', 'Z'));
  private static final CharMatcher DIGITS = inRange('0', '9');
  private static final CharMatcher ADDITIONAL_CHARS = CharMatcher.anyOf("~!@$%^&*_-+=<>.?/");
  private static final CharMatcher VALID_CHARS =
      LETTERS.or(DIGITS).or(ADDITIONAL_CHARS).precomputed();

  protected Yices2FormulaManager(
      Yices2FormulaCreator pFormulaCreator,
      Yices2UFManager pFunctionManager,
      Yices2BooleanFormulaManager pBooleanManager,
      Yices2IntegerFormulaManager pIntegerManager,
      Yices2RationalFormulaManager pRationalManager,
      Yices2BitvectorFormulaManager pBitvectorManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        pIntegerManager,
        pRationalManager,
        pBitvectorManager,
        null,
        null,
        null,
        null,
        null,
        null);
  }

  static Integer getYicesTerm(Formula pT) {
    return ((Yices2Formula) pT).getTerm();
  }

  @Override
  public Integer parseImpl(String pS) throws IllegalArgumentException {
    // TODO Might expect Yices input language instead of smt-lib2 notation
    return yices_parse_term(pS);
  }

  /** Helper function to (pretty) print yices2 sorts. */
  private String getTypeRepr(int type) {
    if (yices_type_is_bitvector(type)) {
      return "(_ BitVec " + yices_bvtype_size(type) + ")";
    }
    String typeRepr = yices_type_to_string(type);
    return typeRepr.substring(0, 1).toUpperCase(Locale.getDefault()) + typeRepr.substring(1);
  }

  @Override
  public String dumpFormulaImpl(final Integer formula) throws IOException {
    assert getFormulaCreator().getFormulaType(formula) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    StringBuilder out = new StringBuilder();
    Map<String, Formula> varsAndUFs =
        extractVariablesAndUFs(getFormulaCreator().encapsulateWithTypeOf(formula));
    for (Map.Entry<String, Formula> entry : varsAndUFs.entrySet()) {
      final int term = ((Yices2Formula) entry.getValue()).getTerm();
      final int type;
      if (yices_term_constructor(term) == YICES_APP_TERM) {
        // Is an UF. Correct type is carried by first child.
        type = yices_type_of_term(yices_term_child(term, 0));
      } else {
        type = yices_type_of_term(term);
      }
      final int[] types;
      if (yices_type_num_children(type) == 0) {
        types = new int[] {type};
      } else {
        types = yices_type_children(type); // adds children types and then return type
      }
      if (types.length > 0) {
        out.append("(declare-fun ");
        out.append(quote(entry.getKey()));
        out.append(" (");
        for (int i = 0; i < types.length - 1; i++) {
          out.append(getTypeRepr(types[i]));
          if (i + 1 < types.length - 1) {
            out.append(' ');
          }
        }
        out.append(") ");
        out.append(getTypeRepr(types[types.length - 1]));
        out.append(")\n");
      }
    }
    // TODO fold formula to avoid exp. overhead
    out.append("(assert ").append(yices_term_to_string(formula)).append(")");

    return out.toString();
  }

  /**
   * Quote symbols if required.
   *
   * <p>See http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf, Section 3.1.
   * "Symbols"
   */
  private static String quote(String str) {
    Preconditions.checkArgument(!Strings.isNullOrEmpty(str));
    Preconditions.checkArgument(CharMatcher.anyOf("|\\").matchesNoneOf(str));
    Preconditions.checkArgument(FormulaCreator.isValidName(str));

    if (VALID_CHARS.matchesAllOf(str) && !DIGITS.matches(str.charAt(0))) {
      // simple symbol
      return str;
    } else {
      // quoted symbol
      return "|" + str + "|";
    }
  }
}
