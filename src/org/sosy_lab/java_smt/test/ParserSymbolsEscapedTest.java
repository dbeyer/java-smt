/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.basicimpl.FormulaCreator.dequote;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableSet;
import java.util.Collection;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

@RunWith(Parameterized.class)
public class ParserSymbolsEscapedTest extends SolverBasedTest0 {

  public static ImmutableSet<String> TEST_SYMBOLS =
      ImmutableSet.of(
          // Simple symbols from the standard:
          "+",
          "<=",
          "x",
          "plus",
          "**",
          "$",
          "<sas",
          "<adf>",
          "abc77",
          "*$s&6",
          ".kkk",
          ".8",
          "+34",
          "-32",

          // Quoted symbols from the standard:
          "this is a quoted symbol",
          "so is\nthis one",
          "\" can occur too",
          "af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984",

          // Some more edge cases
          "",
          " ",
          ",",
          "'",
          "\n",
          "ꯍ",
          "#b101011",
          "#b2",
          "1",
          ",1",
          "01",
          "1.0",
          "01.0",
          "#xA04",
          "#xR04",
          "#o70",
          "_",
          "forall",
          "assert",
          "define-fun-rec",
          "store",
          "concat",
          "=",
          "true",
          "false",
          "and",
          "or",
          "distinct");

  @Parameters(name = "{0},{1}")
  public static Collection<Object[]> data() {
    ImmutableSet.Builder<Object[]> builder = ImmutableSet.builder();
    for (Solvers solver : Solvers.values()) {
      for (String symbol : FluentIterable.concat(TEST_SYMBOLS)) {
        for (String variant :
            ImmutableSet.of(
                symbol,
                addQuotes(symbol),
                FormulaCreator.escapeName(symbol),
                addQuotes(FormulaCreator.escapeName(symbol)))) {
          builder.add(new Object[] {solver, variant});
        }
      }
    }
    return builder.build();
  }

  @Parameter(0)
  public Solvers solver;

  @Parameter(1)
  public String symbol;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Before
  public void init() {
    requireParser();
  }

  /**
   * <code>True</code> if the symbol is a valid symbol according to the SMTLIB standard.
   *
   * <p>This function is stricter than {@link FormulaCreator#isValidName(String)} and won't allow
   * names such as <code>"a \nb"</code> without any SMTLIB quotes.
   */
  static boolean isValid(String pSymbol) {
    if (pSymbol.length() >= 2 && pSymbol.startsWith("|") && pSymbol.endsWith("|")) {
      return FormulaCreator.isValidName(dequote(pSymbol));
    } else {
      return pSymbol.matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$")
          && FormulaCreator.isValidName(pSymbol);
    }
  }

  /**
   * Add quotes to the symbol
   *
   * <p>Assumes that the symbol is not already quoted.
   */
  static String addQuotes(String pSymbol) {
    return "|" + pSymbol + "|";
  }

  /** Returns <code>True</code> if the symbol is quoted */
  static boolean hasQuotes(String pSymbol) {
    return pSymbol.length() >= 2 && pSymbol.startsWith("|") && pSymbol.endsWith("|");
  }

  /**
   * Parse a variable definition in the SMTLIB format and return the term.
   *
   * <p>Returns a variable or a UF depending on the value of <code>asUfSymbol</code>
   */
  private BooleanFormula parseSymbol(String pSymbol, boolean asUfSymbol) {
    String sort = solver == Solvers.BITWUZLA ? "(_ BitVec 8)" : "Int";
    String query =
        asUfSymbol
            ? String.format(
                "(declare-const c %s)(declare-fun %s (%s) Bool)(assert (%s c))",
                sort, pSymbol, sort, pSymbol)
            : String.format("(declare-const %s Bool)(assert %s)", pSymbol, pSymbol);
    return mgr.parse(query);
  }

  /* Only consider valid SMTLIB symbols for this test */
  private void forValidSymbols(String pSymbol) {
    assume().that(isValid(pSymbol)).isTrue();
  }

  /* Only consider invalid symbols. */
  private void forInvalidSymbols(String pSymbol) {
    assume().that(isValid(pSymbol)).isFalse();
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testEscapedParserValid() {
    forValidSymbols(symbol);
    if (solver == Solvers.BITWUZLA) {
      // TODO Report as a bug
      assume().that(symbol).matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$");
    }
    parseSymbol(symbol, false);
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testEscapedParserValidUf() {
    forValidSymbols(symbol);
    if (solver == Solvers.BITWUZLA) {
      // TODO Report as a bug
      assume().that(symbol).matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$");
    }
    parseSymbol(symbol, true);
  }

  @Test
  public void testEscapedParserInvalid() {
    forInvalidSymbols(symbol);
    if (solver == Solvers.OPENSMT) {
      // TODO Report as a bug
      if (!hasQuotes(symbol)) {
        assume().that(symbol).matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$");
      }
    }
    if (solver == Solvers.SMTINTERPOL) {
      // TODO Report as a bug
      assume().that(dequote(symbol)).isNoneOf("true", "false", "ꯍ");
    }
    if (solver == Solvers.OPENSMT) {
      // TODO Report as a bug
      assume().that(dequote(symbol)).isNoneOf("true", "false");
    }
    assertThrows(IllegalArgumentException.class, () -> parseSymbol(symbol, false));
  }

  @Test
  public void testEscapedVariableVisitor() {
    BooleanFormula f = mgr.getBooleanFormulaManager().makeVariable(symbol);
    ImmutableSet<String> variables = mgr.extractVariables(f).keySet();
    assertThat(variables).containsExactly(symbol);
  }

  @Test
  public void testEscapedDumpAndParse() {
    if (solver == Solvers.BITWUZLA) {
      // TODO This might already be fixed in another branch
      // FIXME Fix the exception handler so that Bitwuzla doesn't crash the JVM
      assume().that(symbol).matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$");
    }
    if (solver == Solvers.PRINCESS) {
      // FIXME Unicode parsing (or printing?) seems to be broken on the Windows test system
      assume().that(dequote(symbol)).isNotEqualTo("ꯍ");
    }
    BooleanFormula f = mgr.getBooleanFormulaManager().makeVariable(symbol);
    BooleanFormula g = mgr.parse(mgr.dumpFormula(f).toString());
    assertThat(f).isEqualTo(g);
  }
}
