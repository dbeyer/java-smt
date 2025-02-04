// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.basicimpl.AbstractStringFormulaManager.unescapeUnicodeForSmtlib;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.util.List;
import java.util.Map;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormula;

@SuppressWarnings("ConstantConditions")
@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE", justification = "test code")
public class StringFormulaManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private static final ImmutableList<String> WORDS =
      ImmutableList.of(
          "",
          "0",
          "1",
          "10",
          "a",
          "b",
          "A",
          "B",
          "aa",
          "Aa",
          "aA",
          "AA",
          "ab",
          "aB",
          "Ab",
          "AB",
          "ac",
          "bb",
          "aaa",
          "Aaa",
          "aAa",
          "aAA",
          "aab",
          "aaabbb",
          "bbbccc",
          "abcde",
          "abdde",
          "abcdf",
          "abchurrdurr",
          "abcdefaaaaa");

  private static final int MAX_SINGLE_CODE_POINT_IN_UTF16 = 0x2FFFF;

  private StringFormula a;
  private StringFormula b;
  private StringFormula ab;
  private StringFormula empty;
  private StringFormula hello;
  private RegexFormula a2z;

  @Before
  public void setup() {
    requireStrings();
    a = smgr.makeString("a");
    b = smgr.makeString("b");
    ab = smgr.makeString("ab");
    empty = smgr.makeString("");
    hello = smgr.makeString("hello");
    a2z = smgr.range('a', 'z');
  }

  // Utility methods

  private void assertEqual(IntegerFormula num1, IntegerFormula num2)
      throws SolverException, InterruptedException {
    assertThatFormula(imgr.equal(num1, num2)).isTautological();
  }

  private void assertDistinct(IntegerFormula num1, IntegerFormula num2)
      throws SolverException, InterruptedException {
    assertThatFormula(imgr.distinct(List.of(num1, num2))).isTautological();
  }

  private void assertEqual(StringFormula str1, StringFormula str2)
      throws SolverException, InterruptedException {
    assertThatFormula(smgr.equal(str1, str2)).isTautological();
  }

  private void assertDistinct(StringFormula str1, StringFormula str2)
      throws SolverException, InterruptedException {
    assertThatFormula(smgr.equal(str1, str2)).isUnsatisfiable();
  }

  private void requireVariableStringLiterals() {
    // FIXME: Remove once support for operations on non-singleton Strings has been added
    // See https://github.com/uuverifiers/ostrich/issues/88
    assume()
        .withMessage(
            "Princess currently requires at least one of the arguments to be a "
                + "singleton string")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);
  }

  // Tests

  @Test
  public void testRegexAll() throws SolverException, InterruptedException {
    RegexFormula regex = smgr.all();
    assertThatFormula(smgr.in(hello, regex)).isSatisfiable();
  }

  @Test
  public void testRegexAll3() throws SolverException, InterruptedException {
    // This is not ALL_CHAR! This matches ".*" literally!
    RegexFormula regex = smgr.makeRegex(".*");
    assertThatFormula(smgr.in(hello, regex)).isUnsatisfiable();
    assertThatFormula(smgr.in(smgr.makeString(".*"), regex)).isSatisfiable();
  }

  @Test
  public void testRegexAllChar() throws SolverException, InterruptedException {
    requireVariableStringLiterals();

    RegexFormula regexAllChar = smgr.allChar();

    assertThatFormula(smgr.in(a, regexAllChar)).isSatisfiable();
    assertThatFormula(smgr.in(ab, regexAllChar)).isUnsatisfiable();
    assertThatFormula(smgr.in(empty, regexAllChar)).isUnsatisfiable();
    assertThatFormula(smgr.in(ab, smgr.times(regexAllChar, 2))).isSatisfiable();
    assertThatFormula(
            smgr.in(smgr.makeVariable("x"), smgr.intersection(smgr.range('9', 'a'), regexAllChar)))
        .isSatisfiable();

    RegexFormula regexDot = smgr.makeRegex(".");
    assertThatFormula(smgr.in(a, regexDot)).isUnsatisfiable();
  }

  @Test
  public void testRegexAllCharUnicode() throws SolverException, InterruptedException {
    requireVariableStringLiterals();

    RegexFormula regexAllChar = smgr.allChar();

    // special single characters.

    // Greek Capital Letter Delta
    assertThatFormula(smgr.in(smgr.makeString("\\u0394"), regexAllChar)).isTautological();
    assertThatFormula(smgr.in(smgr.makeString("Δ"), regexAllChar)).isTautological();
    // CJK Compatibility Ideograph from Basic Multilingual Plane.
    assertThatFormula(smgr.in(smgr.makeString("\\u{fa6a}"), regexAllChar)).isTautological();
    // Xiangqi Black Horse from Supplementary Multilingual Plane
    assertThatFormula(smgr.in(smgr.makeString("\\u{1fa6a}"), regexAllChar)).isTautological();

    // Combining characters are not matched as one character.
    assertThatFormula(smgr.in(smgr.makeString("ab"), regexAllChar)).isUnsatisfiable();
    assertThatFormula(smgr.in(smgr.makeString("abcdefgh"), regexAllChar)).isUnsatisfiable();
    assertThatFormula(smgr.in(smgr.makeString("a\\u0336"), regexAllChar)).isUnsatisfiable();
    assertThatFormula(smgr.in(smgr.makeString("\\n"), regexAllChar)).isUnsatisfiable();

    StringFormula x = smgr.makeVariable("x");
    assertThatFormula(smgr.in(x, smgr.range('a', 'z'))).isSatisfiable();
    assertThatFormula(smgr.in(x, smgr.intersection(smgr.range('a', 'z'), regexAllChar)))
        .isSatisfiable();

    BooleanFormula inRange = smgr.in(x, smgr.range('a', 'Δ'));
    BooleanFormula inRange2 = smgr.in(x, smgr.intersection(smgr.range('a', 'Δ'), regexAllChar));
    if (solverToUse() == Solvers.CVC4) {
      // CVC4 has issues with range and special Unicode characters when solving constraints
      assertThrows(AssertionError.class, () -> assertThatFormula(inRange).isSatisfiable());
      assertThrows(AssertionError.class, () -> assertThatFormula(inRange2).isSatisfiable());
    } else {
      assertThatFormula(inRange).isSatisfiable();
      assertThatFormula(inRange2).isSatisfiable();
    }
  }

  @Test
  public void testStringRegex2() throws SolverException, InterruptedException {
    requireVariableStringLiterals();

    RegexFormula regex = smgr.concat(smgr.closure(a2z), smgr.makeRegex("ll"), smgr.closure(a2z));
    assertThatFormula(smgr.in(hello, regex)).isSatisfiable();
  }

  @Test
  public void testStringRegex3() throws SolverException, InterruptedException {
    RegexFormula regex = smgr.makeRegex(".*ll.*");
    assertThatFormula(smgr.in(hello, regex)).isUnsatisfiable();
  }

  @Test
  public void testEmptyRegex() throws SolverException, InterruptedException {
    RegexFormula regex = smgr.none();
    assertThatFormula(smgr.in(hello, regex)).isUnsatisfiable();
  }

  @Test
  public void testRegexUnion() throws SolverException, InterruptedException {
    RegexFormula regex = smgr.union(smgr.makeRegex("a"), smgr.makeRegex("b"));
    assertThatFormula(smgr.in(a, regex)).isSatisfiable();
    assertThatFormula(smgr.in(b, regex)).isSatisfiable();
    assertThatFormula(smgr.in(smgr.makeString("c"), regex)).isUnsatisfiable();
  }

  @Test
  public void testRegexIntersection() throws SolverException, InterruptedException {
    RegexFormula regex = smgr.intersection(smgr.makeRegex("a"), smgr.makeRegex("b"));
    StringFormula variable = smgr.makeVariable("var");
    assertThatFormula(smgr.in(variable, regex)).isUnsatisfiable();

    regex =
        smgr.intersection(
            smgr.union(smgr.makeRegex("a"), smgr.makeRegex("b")),
            smgr.union(smgr.makeRegex("b"), smgr.makeRegex("c")));
    assertThatFormula(smgr.in(a, regex)).isUnsatisfiable();
    assertThatFormula(smgr.in(b, regex)).isSatisfiable();
  }

  @Test
  public void testRegexDifference() throws SolverException, InterruptedException {
    RegexFormula regex =
        smgr.difference(smgr.union(smgr.makeRegex("a"), smgr.makeRegex("b")), smgr.makeRegex("b"));
    assertThatFormula(smgr.in(a, regex)).isSatisfiable();
    assertThatFormula(smgr.in(b, regex)).isUnsatisfiable();
  }

  @Test
  public void testStringConcat() throws SolverException, InterruptedException {
    StringFormula str1 = smgr.makeString("hello");
    StringFormula str2 = smgr.makeString("world");
    StringFormula concat = smgr.concat(str1, str2);
    StringFormula complete = smgr.makeString("helloworld");

    assertEqual(concat, complete);
  }

  @Test
  public void testStringConcatEmpty() throws SolverException, InterruptedException {
    assertEqual(empty, smgr.concat(ImmutableList.of()));
    assertEqual(empty, smgr.concat(empty));
    assertEqual(empty, smgr.concat(empty, empty));
    assertEqual(empty, smgr.concat(ImmutableList.of(empty, empty, empty, empty)));
  }

  @Test
  public void testStringPrefixSuffixConcat() throws SolverException, InterruptedException {
    // FIXME: Princess will timeout on this test
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);

    // check whether "prefix + suffix == concatenated"
    StringFormula prefix = smgr.makeVariable("prefix");
    StringFormula suffix = smgr.makeVariable("suffix");
    StringFormula concat = smgr.makeVariable("concatenated");

    assertThatFormula(
            bmgr.and(
                smgr.prefix(prefix, concat),
                smgr.suffix(suffix, concat),
                imgr.equal(
                    smgr.length(concat), imgr.add(smgr.length(prefix), smgr.length(suffix)))))
        .implies(smgr.equal(concat, smgr.concat(prefix, suffix)));
  }

  @Test
  public void testStringPrefixSuffix() throws SolverException, InterruptedException {
    // check whether "prefix == suffix iff equal length"
    StringFormula prefix = smgr.makeVariable("prefix");
    StringFormula suffix = smgr.makeVariable("suffix");

    assertThatFormula(bmgr.and(smgr.prefix(prefix, suffix), smgr.suffix(suffix, prefix)))
        .implies(smgr.equal(prefix, suffix));
    assertThatFormula(
            bmgr.and(
                smgr.prefix(prefix, suffix), imgr.equal(smgr.length(prefix), smgr.length(suffix))))
        .implies(smgr.equal(prefix, suffix));
    assertThatFormula(
            bmgr.and(
                smgr.suffix(suffix, prefix), imgr.equal(smgr.length(prefix), smgr.length(suffix))))
        .implies(smgr.equal(prefix, suffix));
  }

  @Test
  public void testStringToIntConversion() throws SolverException, InterruptedException {
    IntegerFormula ten = imgr.makeNumber(10);
    StringFormula zeroStr = smgr.makeString("0");

    for (int i = 0; i < 100; i += 7) {
      StringFormula str = smgr.makeString(Integer.toString(i));
      IntegerFormula num = imgr.makeNumber(i);
      IntegerFormula numInc = imgr.makeNumber(i + 1);

      assertEqual(str, smgr.toStringFormula(num));
      assertDistinct(str, smgr.toStringFormula(numInc));
      assertDistinct(str, smgr.toStringFormula(imgr.add(num, numInc)));

      assertEqual(num, smgr.toIntegerFormula(str));
      assertDistinct(numInc, smgr.toIntegerFormula(str));
      assertEqual(imgr.multiply(num, ten), smgr.toIntegerFormula(smgr.concat(str, zeroStr)));
      assertDistinct(imgr.multiply(numInc, ten), smgr.toIntegerFormula(smgr.concat(str, zeroStr)));

      assertEqual(num, smgr.toIntegerFormula(smgr.toStringFormula(num)));
      assertEqual(numInc, smgr.toIntegerFormula(smgr.toStringFormula(numInc)));
    }
  }

  @Test
  public void testStringToIntConversionCornerCases() throws SolverException, InterruptedException {
    assertEqual(imgr.makeNumber(-1), smgr.toIntegerFormula(smgr.makeString("-1")));
    assertEqual(imgr.makeNumber(-1), smgr.toIntegerFormula(smgr.makeString("-12")));
    assertEqual(imgr.makeNumber(-1), smgr.toIntegerFormula(smgr.makeString("-123")));
    assertEqual(imgr.makeNumber(-1), smgr.toIntegerFormula(smgr.makeString("-1234")));

    assertDistinct(imgr.makeNumber(-12), smgr.toIntegerFormula(smgr.makeString("-1")));
    assertDistinct(imgr.makeNumber(-12), smgr.toIntegerFormula(smgr.makeString("-12")));
    assertDistinct(imgr.makeNumber(-12), smgr.toIntegerFormula(smgr.makeString("-123")));
    assertDistinct(imgr.makeNumber(-12), smgr.toIntegerFormula(smgr.makeString("-1234")));

    assertEqual(imgr.makeNumber(-1), smgr.toIntegerFormula(empty));
    assertEqual(imgr.makeNumber(-1), smgr.toIntegerFormula(a));
    assertEqual(imgr.makeNumber(-1), smgr.toIntegerFormula(smgr.makeString("1a")));
    assertEqual(imgr.makeNumber(-1), smgr.toIntegerFormula(smgr.makeString("a1")));

    assertDistinct(imgr.makeNumber(-12), smgr.toIntegerFormula(empty));
    assertDistinct(imgr.makeNumber(-12), smgr.toIntegerFormula(a));
    assertDistinct(imgr.makeNumber(-12), smgr.toIntegerFormula(smgr.makeString("1a")));
    assertDistinct(imgr.makeNumber(-12), smgr.toIntegerFormula(smgr.makeString("a1")));
  }

  @Test
  public void testIntToStringConversionCornerCases() throws SolverException, InterruptedException {
    assertEqual(smgr.makeString("123"), smgr.toStringFormula(imgr.makeNumber(123)));
    assertEqual(smgr.makeString("1"), smgr.toStringFormula(imgr.makeNumber(1)));
    assertEqual(smgr.makeString("0"), smgr.toStringFormula(imgr.makeNumber(0)));
    assertEqual(empty, smgr.toStringFormula(imgr.makeNumber(-1)));
    assertEqual(empty, smgr.toStringFormula(imgr.makeNumber(-123)));

    assertDistinct(smgr.makeString("1"), smgr.toStringFormula(imgr.makeNumber(-1)));
  }

  @Test
  public void testStringLength() throws SolverException, InterruptedException {
    assertEqual(imgr.makeNumber(0), smgr.length(empty));
    assertEqual(imgr.makeNumber(1), smgr.length(a));
    assertEqual(imgr.makeNumber(2), smgr.length(smgr.makeString("aa")));
    assertEqual(imgr.makeNumber(9), smgr.length(smgr.makeString("aaabbbccc")));

    assertEqual(imgr.makeNumber(1), smgr.length(smgr.makeString("\n")));
    assertEqual(imgr.makeNumber(1), smgr.length(smgr.makeString("\t")));

    assertEqual(imgr.makeNumber(1), smgr.length(smgr.makeString("\\u{20AC}")));
    assertEqual(imgr.makeNumber(1), smgr.length(smgr.makeString("€")));
    assertEqual(imgr.makeNumber(1), smgr.length(smgr.makeString("Δ")));

    assertDistinct(imgr.makeNumber(5), smgr.length(empty));
    assertDistinct(imgr.makeNumber(5), smgr.length(a));
    assertDistinct(imgr.makeNumber(5), smgr.length(smgr.makeString("aa")));
    assertDistinct(imgr.makeNumber(5), smgr.length(smgr.makeString("aaabbbcc")));
  }

  @Test
  public void testStringLengthWithVariable() throws SolverException, InterruptedException {
    StringFormula var = smgr.makeVariable("var");

    assertThatFormula(imgr.equal(imgr.makeNumber(0), smgr.length(var)))
        .implies(smgr.equal(var, empty));

    assertThatFormula(
            bmgr.and(
                imgr.equal(imgr.makeNumber(5), smgr.length(var)),
                smgr.prefix(smgr.makeString("aba"), var),
                smgr.suffix(smgr.makeString("aba"), var)))
        .implies(smgr.equal(smgr.makeVariable("var"), smgr.makeString("ababa")));

    assertThatFormula(
            bmgr.and(
                imgr.equal(imgr.makeNumber(4), smgr.length(var)),
                smgr.prefix(smgr.makeString("aba"), var),
                smgr.suffix(smgr.makeString("aba"), var)))
        .isUnsatisfiable();

    assertThatFormula(
            bmgr.and(
                imgr.equal(imgr.makeNumber(4), smgr.length(var)),
                smgr.prefix(ab, var),
                smgr.suffix(smgr.makeString("ba"), var),
                smgr.equal(smgr.makeString("c"), smgr.charAt(var, imgr.makeNumber(3)))))
        .isUnsatisfiable();

    assertThatFormula(
            bmgr.and(
                imgr.equal(imgr.makeNumber(5), smgr.length(var)),
                smgr.prefix(ab, var),
                smgr.suffix(smgr.makeString("ba"), var),
                smgr.equal(smgr.makeString("c"), smgr.charAt(var, imgr.makeNumber(3)))))
        .implies(smgr.equal(smgr.makeVariable("var"), smgr.makeString("abcba")));
  }

  @Test
  public void testStringLengthPositiv() throws SolverException, InterruptedException {
    assertThatFormula(imgr.lessOrEquals(imgr.makeNumber(0), smgr.length(smgr.makeVariable("x"))))
        .isTautological();
    assertThatFormula(imgr.greaterThan(imgr.makeNumber(0), smgr.length(smgr.makeVariable("x"))))
        .isUnsatisfiable();
  }

  @Test
  public void testStringCompare() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver is quite slow for this example")
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);
    // TODO regression:
    // - CVC5 was able to solve this in v1.0.2, but no longer in v1.0.5

    requireVariableStringLiterals();

    StringFormula var1 = smgr.makeVariable("0");
    StringFormula var2 = smgr.makeVariable("1");
    assertThatFormula(bmgr.and(smgr.lessOrEquals(var1, var2), smgr.greaterOrEquals(var1, var2)))
        .implies(smgr.equal(var1, var2));
    assertThatFormula(smgr.equal(var1, var2))
        .implies(bmgr.and(smgr.lessOrEquals(var1, var2), smgr.greaterOrEquals(var1, var2)));
  }

  /** Test const Strings = String variables + prefix and suffix constraints. */
  @Test
  public void testConstStringEqStringVar() throws SolverException, InterruptedException {
    String string1 = "";
    String string2 = "a";
    String string3 = "ab";
    String string4 = "abcdefghijklmnopqrstuvwxyz";
    StringFormula string1c = smgr.makeString(string1);
    StringFormula string2c = smgr.makeString(string2);
    StringFormula string3c = smgr.makeString(string3);
    StringFormula string4c = smgr.makeString(string4);
    StringFormula string1v = smgr.makeVariable("string1v");
    StringFormula string2v = smgr.makeVariable("string1v");
    StringFormula string3v = smgr.makeVariable("string1v");
    StringFormula string4v = smgr.makeVariable("string1v");

    BooleanFormula formula =
        bmgr.and(
            smgr.equal(string1c, string1v),
            smgr.equal(string2c, string2v),
            smgr.equal(string3c, string3v),
            smgr.equal(string4c, string4v));

    BooleanFormula string1PrefixFormula =
        bmgr.and(
            smgr.prefix(string1c, string1v),
            bmgr.not(smgr.prefix(string2c, string1v)),
            bmgr.not(smgr.prefix(string3c, string1v)),
            bmgr.not(smgr.prefix(string4c, string1v)));

    BooleanFormula string2PrefixFormula =
        bmgr.and(
            smgr.prefix(string1c, string2v),
            smgr.prefix(string2c, string2v),
            bmgr.not(smgr.prefix(string3c, string2v)),
            bmgr.not(smgr.prefix(string4c, string2v)));

    BooleanFormula string3PrefixFormula =
        bmgr.and(
            smgr.prefix(string1c, string3v),
            smgr.prefix(string2c, string3v),
            smgr.prefix(string3c, string3v),
            bmgr.not(smgr.prefix(string4c, string3v)));

    BooleanFormula string4PrefixFormula =
        bmgr.and(
            smgr.prefix(string1c, string4v),
            smgr.prefix(string2c, string4v),
            smgr.prefix(string3c, string4v),
            smgr.prefix(string4c, string4v));

    BooleanFormula string1SuffixFormula =
        bmgr.and(
            smgr.suffix(string1c, string1v),
            bmgr.not(smgr.suffix(string2c, string1v)),
            bmgr.not(smgr.suffix(string3c, string1v)),
            bmgr.not(smgr.suffix(string4c, string1v)));

    BooleanFormula string2SuffixFormula =
        bmgr.and(
            smgr.suffix(string1c, string2v),
            bmgr.not(smgr.suffix(string3c, string2v)),
            bmgr.not(smgr.suffix(string4c, string2v)));

    BooleanFormula string3SuffixFormula =
        bmgr.and(
            smgr.suffix(string1c, string3v),
            smgr.suffix(string3c, string3v),
            bmgr.not(smgr.suffix(string4c, string3v)));

    BooleanFormula string4SuffixFormula =
        bmgr.and(smgr.suffix(string1c, string4v), smgr.suffix(string4c, string4v));

    assertThatFormula(bmgr.and(formula))
        .implies(
            bmgr.and(
                string1PrefixFormula,
                string2PrefixFormula,
                string3PrefixFormula,
                string4PrefixFormula,
                string1SuffixFormula,
                string2SuffixFormula,
                string3SuffixFormula,
                string4SuffixFormula));
  }

  /** Test String variables with negative length (UNSAT). */
  @Test
  public void testStringVariableLengthNegative() throws SolverException, InterruptedException {
    StringFormula stringVariable1 = smgr.makeVariable("zeroLength");
    StringFormula stringVariable2 = smgr.makeVariable("negLength");

    // SAT + UNSAT Formula -> UNSAT
    assertThatFormula(
            bmgr.and(
                imgr.equal(smgr.length(stringVariable1), imgr.makeNumber(0)),
                imgr.equal(smgr.length(stringVariable2), imgr.makeNumber(-100))))
        .isUnsatisfiable();
    // UNSAT below
    assertThatFormula(imgr.equal(smgr.length(stringVariable2), imgr.makeNumber(-1)))
        .isUnsatisfiable();
    assertThatFormula(imgr.equal(smgr.length(stringVariable2), imgr.makeNumber(-100)))
        .isUnsatisfiable();
  }

  /**
   * Test String formulas with inequalities in the negative range.
   *
   * <p>-10000 < stringVariable length < 0 -> UNSAT
   *
   * <p>-10000 < stringVariable length < -1 -> UNSAT
   *
   * <p>-10000 <= stringVariable length <= -1 -> UNSAT
   *
   * <p>-10000 <= stringVariable length <= 0 AND stringVariable != "" -> UNSAT
   *
   * <p>-10000 <= stringVariable length <= 0 -> SAT implies stringVariable = ""
   */
  @Test
  public void testStringLengthInequalityNegativeRange()
      throws SolverException, InterruptedException {
    StringFormula stringVariable = smgr.makeVariable("stringVariable");
    IntegerFormula stringVariableLength = smgr.length(stringVariable);
    IntegerFormula minusTenThousand = imgr.makeNumber(-10000);
    IntegerFormula minusOne = imgr.makeNumber(-1);
    IntegerFormula zero = imgr.makeNumber(0);

    // -10000 < stringVariable length < 0 -> UNSAT
    assertThatFormula(
            bmgr.and(
                imgr.lessThan(minusTenThousand, stringVariableLength),
                imgr.lessThan(stringVariableLength, zero)))
        .isUnsatisfiable();
    // -10000 < stringVariable length < -1 -> UNSAT
    assertThatFormula(
            bmgr.and(
                imgr.lessThan(minusTenThousand, stringVariableLength),
                imgr.lessThan(stringVariableLength, minusOne)))
        .isUnsatisfiable();
    // -10000 <= stringVariable length <= -1 -> UNSAT
    assertThatFormula(
            bmgr.and(
                imgr.lessOrEquals(minusTenThousand, stringVariableLength),
                imgr.lessOrEquals(stringVariableLength, minusOne)))
        .isUnsatisfiable();
    // -10000 <= stringVariable length <= 0 AND stringVariable != "" -> UNSAT
    assertThatFormula(
            bmgr.and(
                imgr.lessOrEquals(minusTenThousand, stringVariableLength),
                imgr.lessOrEquals(stringVariableLength, zero),
                bmgr.not(smgr.equal(stringVariable, empty))))
        .isUnsatisfiable();
    // -10000 <= stringVariable length <= 0 -> SAT implies stringVariable = ""
    assertThatFormula(
            bmgr.and(
                imgr.lessOrEquals(minusTenThousand, stringVariableLength),
                imgr.lessOrEquals(stringVariableLength, zero)))
        .implies(smgr.equal(stringVariable, empty));
  }

  /**
   * Test String formulas with inequalities in the negative range.
   *
   * <p>0 < stringVariable length < 1 -> UNSAT
   *
   * <p>0 < stringVariable length < 2 -> SAT
   *
   * <p>0 <= stringVariable length < 1 -> SAT implies stringVariable = ""
   *
   * <p>1 < stringVariable length < 3 -> SAT implies stringVariable length = 2
   */
  @Test
  public void testStringLengthInequalityPositiveRange()
      throws SolverException, InterruptedException {
    StringFormula stringVariable = smgr.makeVariable("stringVariable");
    IntegerFormula stringVariableLength = smgr.length(stringVariable);
    IntegerFormula three = imgr.makeNumber(3);
    IntegerFormula two = imgr.makeNumber(2);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula zero = imgr.makeNumber(0);

    // 0 < stringVariable length < 1 -> UNSAT
    assertThatFormula(
            bmgr.and(
                imgr.lessThan(zero, stringVariableLength),
                imgr.lessThan(stringVariableLength, one)))
        .isUnsatisfiable();
    // 0 < stringVariable length < 2 -> SAT
    assertThatFormula(
            bmgr.and(
                imgr.lessThan(zero, stringVariableLength),
                imgr.lessThan(stringVariableLength, two)))
        .isSatisfiable();
    // 0 <= stringVariable length < 1 -> SAT implies stringVariable = ""
    assertThatFormula(
            bmgr.and(
                imgr.lessOrEquals(zero, stringVariableLength),
                imgr.lessThan(stringVariableLength, one)))
        .implies(smgr.equal(stringVariable, empty));
    // 1 < stringVariable length < 3 -> SAT implies stringVariable length = 2
    assertThatFormula(
            bmgr.and(
                imgr.lessThan(one, stringVariableLength),
                imgr.lessThan(stringVariableLength, three)))
        .implies(imgr.equal(smgr.length(stringVariable), two));
  }

  /** Test simple String lexicographic ordering (< <= > >=) for constant Strings. */
  @Test
  public void testSimpleConstStringLexicographicOrdering()
      throws SolverException, InterruptedException {
    List<String> words = ImmutableList.sortedCopyOf(WORDS);

    for (int i = 1; i < words.size(); i++) {
      StringFormula word1 = smgr.makeString(words.get(i - 1));
      StringFormula word2 = smgr.makeString(words.get(i));

      assertThatFormula(smgr.lessThan(word1, word1)).isUnsatisfiable();
      assertThatFormula(smgr.lessOrEquals(word1, word1)).isTautological();
      assertThatFormula(smgr.greaterOrEquals(word1, word1)).isTautological();
      assertEqual(word1, word1);

      assertThatFormula(smgr.lessThan(word1, word2)).isTautological();
      assertThatFormula(smgr.lessOrEquals(word1, word2)).isTautological();
      assertThatFormula(smgr.greaterThan(word1, word2)).isUnsatisfiable();
      assertThatFormula(smgr.greaterOrEquals(word1, word2)).isUnsatisfiable();
    }
  }

  /** Test simple String lexicographic ordering (< <= > >=) for String variables. */
  @Test
  public void testSimpleStringVariableLexicographicOrdering()
      throws SolverException, InterruptedException {
    StringFormula abc = smgr.makeString("abc");
    StringFormula abd = smgr.makeString("abd");
    StringFormula abe = smgr.makeString("abe");
    StringFormula abaab = smgr.makeString("abaab");
    StringFormula abbab = smgr.makeString("abbab");
    StringFormula abcab = smgr.makeString("abcab");
    StringFormula stringVariable = smgr.makeVariable("stringVariable");

    assertThatFormula(
            bmgr.and(
                smgr.lessThan(a, stringVariable),
                smgr.lessThan(stringVariable, b),
                imgr.equal(imgr.makeNumber(0), smgr.length(stringVariable))))
        .implies(smgr.equal(stringVariable, empty));

    assertThatFormula(
            bmgr.and(
                smgr.lessOrEquals(a, stringVariable),
                smgr.lessThan(stringVariable, b),
                imgr.equal(imgr.makeNumber(1), smgr.length(stringVariable))))
        .implies(smgr.equal(stringVariable, a));

    assertThatFormula(
            bmgr.and(
                smgr.lessThan(a, stringVariable),
                smgr.lessOrEquals(stringVariable, b),
                imgr.equal(imgr.makeNumber(1), smgr.length(stringVariable))))
        .implies(smgr.equal(stringVariable, b));

    assertThatFormula(
            bmgr.and(
                smgr.lessOrEquals(abc, stringVariable),
                smgr.lessThan(stringVariable, abd),
                imgr.equal(imgr.makeNumber(3), smgr.length(stringVariable))))
        .implies(smgr.equal(stringVariable, abc));

    assertThatFormula(
            bmgr.and(
                smgr.lessThan(abc, stringVariable),
                smgr.lessThan(stringVariable, abe),
                imgr.equal(imgr.makeNumber(3), smgr.length(stringVariable))))
        .implies(smgr.equal(stringVariable, abd));

    assertThatFormula(
            bmgr.and(
                smgr.lessThan(abc, stringVariable),
                smgr.lessOrEquals(stringVariable, abd),
                imgr.equal(imgr.makeNumber(3), smgr.length(stringVariable))))
        .implies(smgr.equal(stringVariable, abd));

    assertThatFormula(
            bmgr.and(
                smgr.lessThan(abaab, stringVariable),
                smgr.lessThan(stringVariable, abcab),
                smgr.prefix(ab, stringVariable),
                smgr.suffix(ab, stringVariable),
                imgr.equal(imgr.makeNumber(5), smgr.length(stringVariable))))
        .implies(smgr.equal(stringVariable, abbab));
  }

  /** Takeaway: invalid positions always refer to the empty string! */
  @Test
  public void testCharAtWithConstString() throws SolverException, InterruptedException {
    assertEqual(smgr.charAt(empty, imgr.makeNumber(1)), empty);
    assertEqual(smgr.charAt(empty, imgr.makeNumber(0)), empty);
    assertEqual(smgr.charAt(empty, imgr.makeNumber(-1)), empty);

    assertDistinct(smgr.charAt(a, imgr.makeNumber(-1)), a);
    assertEqual(smgr.charAt(a, imgr.makeNumber(-1)), empty);
    assertEqual(smgr.charAt(a, imgr.makeNumber(0)), a);
    assertDistinct(smgr.charAt(a, imgr.makeNumber(1)), a);
    assertEqual(smgr.charAt(a, imgr.makeNumber(1)), empty);
    assertDistinct(smgr.charAt(a, imgr.makeNumber(2)), a);
    assertEqual(smgr.charAt(a, imgr.makeNumber(2)), empty);

    assertEqual(smgr.charAt(ab, imgr.makeNumber(0)), a);
    assertEqual(smgr.charAt(ab, imgr.makeNumber(1)), b);
    assertDistinct(smgr.charAt(ab, imgr.makeNumber(0)), b);
    assertDistinct(smgr.charAt(ab, imgr.makeNumber(1)), a);
  }

  @Test
  public void testCharAtHasAlwaysLengthZeroOrOne() throws SolverException, InterruptedException {
    StringFormula someString = smgr.makeVariable("someString");
    IntegerFormula position = imgr.makeVariable("position");
    IntegerFormula length = smgr.length(smgr.charAt(someString, position));

    BooleanFormula lengthZero = imgr.equal(length, imgr.makeNumber(0));
    BooleanFormula lengthOne = imgr.equal(length, imgr.makeNumber(1));

    assertThatFormula(bmgr.or(lengthZero, lengthOne)).isTautological();
  }

  @Test
  public void testStringToCodePoint() throws SolverException, InterruptedException {
    // TODO report to developers
    assume()
        .withMessage("Solver %s crashes", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    assertEqual(smgr.toCodePoint(a), imgr.makeNumber('a'));
    assertEqual(smgr.toCodePoint(b), imgr.makeNumber('b'));

    // string of length != 1 are invalid and return -1
    assertEqual(smgr.toCodePoint(ab), imgr.makeNumber(-1));
    assertEqual(smgr.toCodePoint(empty), imgr.makeNumber(-1));
  }

  @Test
  public void testToCodePointInRange() throws SolverException, InterruptedException {
    // TODO report to developers
    assume()
        .withMessage("Solver %s crashes", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    StringFormula str = smgr.makeVariable("str");
    IntegerFormula cp = smgr.toCodePoint(str);
    BooleanFormula invalidStr = imgr.equal(cp, imgr.makeNumber(-1));
    BooleanFormula cpInRange =
        bmgr.and(
            imgr.lessOrEquals(imgr.makeNumber(0), cp),
            imgr.lessOrEquals(cp, imgr.makeNumber(MAX_SINGLE_CODE_POINT_IN_UTF16)));
    assertThatFormula(bmgr.or(invalidStr, cpInRange)).isTautological();
  }

  @Test
  public void testFromCodePointInRange() throws SolverException, InterruptedException {
    // TODO report to developers
    assume()
        .withMessage("Solver %s crashes", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    IntegerFormula cp = imgr.makeVariable("cp");
    StringFormula str = smgr.fromCodePoint(cp);
    IntegerFormula len = smgr.length(str);

    // all normal code points are in range, i.e., string length is 1.
    BooleanFormula cpInRange =
        bmgr.and(
            imgr.lessOrEquals(imgr.makeNumber(0), cp),
            imgr.lessOrEquals(cp, imgr.makeNumber(MAX_SINGLE_CODE_POINT_IN_UTF16)));
    assertThatFormula(cpInRange).isEquivalentTo(imgr.equal(len, imgr.makeNumber(1)));

    // all other code points are out of range, i.e., they match the empty string with length 0.
    assertThatFormula(bmgr.not(cpInRange)).isEquivalentTo(smgr.equal(str, empty));
  }

  @Test
  public void testStringFromCodePoint() throws SolverException, InterruptedException {
    StringFormula cpA = smgr.fromCodePoint(imgr.makeNumber('a'));
    StringFormula cpB = smgr.fromCodePoint(imgr.makeNumber('b'));
    assertEqual(cpA, a);
    assertEqual(cpB, b);
    assertEqual(cpA, smgr.makeString(Character.toString(97)));
    assertEqual(cpB, smgr.makeString(Character.toString(98)));

    StringFormula cpOne = smgr.fromCodePoint(imgr.makeNumber(1));
    StringFormula cpTen = smgr.fromCodePoint(imgr.makeNumber(10));
    // some solvers allow direct Unicode, other solvers need escape sequences
    assertEqual(cpOne, smgr.makeString(Character.toString(1)));
    assertEqual(cpTen, smgr.makeString(Character.toString(10)));

    // negative numbers are invalid and return empty string
    StringFormula cpNegOne = smgr.fromCodePoint(imgr.makeNumber(-1));
    StringFormula cpNegTen = smgr.fromCodePoint(imgr.makeNumber(-10));
    StringFormula cpNeg256 = smgr.fromCodePoint(imgr.makeNumber(-100));
    assertEqual(cpNegOne, empty);
    assertEqual(cpNegTen, empty);
    assertEqual(cpNeg256, empty);
  }

  /**
   * Test escapecharacter treatment. Escape characters are treated as a single char! Example:
   * "a\u1234T" has "a" at position 0, "\u1234" at position 1 and "T" at position 2
   *
   * <p>SMTLIB2 uses an escape sequence for the numerals of the sort: {1234}.
   */
  @Test
  public void testCharAtWithSpecialCharacters() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does only support 2 byte unicode", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    StringFormula num1 = smgr.makeString("1");
    StringFormula u = smgr.makeString("u");
    StringFormula curlyOpen = smgr.makeString("{");
    StringFormula curlyClose = smgr.makeString("}");
    StringFormula u1234WOEscape = smgr.makeString("u1234");
    StringFormula au1234WOEscape = smgr.makeString("au1234");

    String workaround = "au{1234}";
    StringFormula au1234WOEscapeCurly = smgr.makeString(workaround);
    StringFormula backSlash = smgr.makeString("\\");
    StringFormula u1234 = smgr.makeString("\\u{1234}");
    StringFormula au1234b = smgr.makeString("a\\u{1234}b");

    assertEqual(smgr.length(backSlash), imgr.makeNumber(1));
    assertEqual(smgr.charAt(au1234b, imgr.makeNumber(0)), a);
    assertEqual(smgr.charAt(au1234b, imgr.makeNumber(1)), u1234);
    assertEqual(smgr.charAt(au1234b, imgr.makeNumber(2)), b);

    assertEqual(smgr.charAt(u1234WOEscape, imgr.makeNumber(0)), u);
    assertEqual(smgr.charAt(u1234WOEscape, imgr.makeNumber(1)), num1);

    assertEqual(smgr.charAt(au1234WOEscape, imgr.makeNumber(0)), a);
    assertEqual(smgr.charAt(au1234WOEscape, imgr.makeNumber(1)), u);
    assertEqual(smgr.charAt(au1234WOEscape, imgr.makeNumber(2)), num1);

    assertEqual(smgr.charAt(au1234WOEscapeCurly, imgr.makeNumber(0)), a);
    assertEqual(smgr.charAt(au1234WOEscapeCurly, imgr.makeNumber(1)), u);
    assertEqual(smgr.charAt(au1234WOEscapeCurly, imgr.makeNumber(2)), curlyOpen);
    assertEqual(smgr.charAt(au1234WOEscapeCurly, imgr.makeNumber(7)), curlyClose);

    // Check that the Unicode is not treated as separate chars
    assertThatFormula(smgr.equal(smgr.charAt(u1234, imgr.makeNumber(0)), smgr.makeString("\\")))
        .isUnsatisfiable();
    assertThatFormula(smgr.equal(smgr.charAt(u1234, imgr.makeNumber(1)), u)).isUnsatisfiable();
    assertThatFormula(smgr.equal(smgr.charAt(u1234, imgr.makeNumber(2)), num1)).isUnsatisfiable();
  }

  @SuppressWarnings("UnicodeEscape")
  @Test
  public void testUnicodeEscaping() throws SolverException, InterruptedException {
    // SMTLIB has different representations for the same symbol
    assertEqual(a, smgr.makeString("\u0061"));
    assertEqual(a, smgr.makeString("\\u0061"));
    assertEqual(a, smgr.makeString("\\u{61}"));
    assertEqual(a, smgr.makeString("\\u{00061}"));
    assertEqual(smgr.length(a), imgr.makeNumber(1));

    StringFormula u0 = smgr.makeString("\\u0000");
    assertEqual(u0, smgr.makeString("\u0000"));
    assertEqual(u0, smgr.makeString("\\u{0}"));
    assertEqual(u0, smgr.makeString("\\u{00000}"));
    assertEqual(smgr.length(u0), imgr.makeNumber(1));

    StringFormula u1 = smgr.makeString("\\u1234");
    assertEqual(u1, smgr.makeString("\u1234"));
    assertEqual(u1, smgr.makeString("\\u{1234}"));
    assertEqual(u1, smgr.makeString("\\u{01234}"));
    assertEqual(smgr.length(u1), imgr.makeNumber(1));

    if (solverToUse() == Solvers.PRINCESS) {
      for (String invalidStr :
          List.of(
              "\\u{10000}",
              Character.toString(0x10000),
              "\\u{2FFFF}",
              Character.toString(0x2FFFF))) {
        assertThrows(IllegalArgumentException.class, () -> smgr.makeString(invalidStr));
      }
    } else {
      StringFormula u2 = smgr.makeString("\\u{2FFFF}");
      assertEqual(u2, smgr.makeString(Character.toString(0x2FFFF)));
      assertEqual(smgr.length(u2), imgr.makeNumber(1));
    }
  }

  /**
   * Same as {@link #testCharAtWithSpecialCharacters} but only with 2 Byte special chars as Z3 only
   * supports those.
   */
  @Test
  public void testCharAtWithSpecialCharacters2Byte() throws SolverException, InterruptedException {
    StringFormula num7 = smgr.makeString("7");
    StringFormula u = smgr.makeString("u");
    StringFormula curlyOpen2BUnicode = smgr.makeString("\\u{7B}");
    StringFormula curlyClose2BUnicode = smgr.makeString("\\u{7D}");
    StringFormula acurlyClose2BUnicodeb = smgr.makeString("a\\u{7D}b");
    StringFormula acurlyOpen2BUnicodeWOEscapeCurly = smgr.makeString("au{7B}");
    StringFormula backSlash = smgr.makeString("\\");

    assertEqual(smgr.length(backSlash), imgr.makeNumber(1));
    assertEqual(smgr.length(curlyOpen2BUnicode), imgr.makeNumber(1));
    assertEqual(smgr.length(curlyClose2BUnicode), imgr.makeNumber(1));

    assertEqual(smgr.charAt(acurlyClose2BUnicodeb, imgr.makeNumber(0)), a);
    assertEqual(smgr.charAt(acurlyClose2BUnicodeb, imgr.makeNumber(1)), curlyClose2BUnicode);
    assertEqual(smgr.charAt(acurlyClose2BUnicodeb, imgr.makeNumber(2)), b);

    assertEqual(smgr.charAt(acurlyOpen2BUnicodeWOEscapeCurly, imgr.makeNumber(0)), a);
    assertEqual(smgr.charAt(acurlyOpen2BUnicodeWOEscapeCurly, imgr.makeNumber(1)), u);
    assertEqual(
        smgr.charAt(acurlyOpen2BUnicodeWOEscapeCurly, imgr.makeNumber(2)), curlyOpen2BUnicode);
    assertEqual(smgr.charAt(acurlyOpen2BUnicodeWOEscapeCurly, imgr.makeNumber(3)), num7);
    assertEqual(
        smgr.charAt(acurlyOpen2BUnicodeWOEscapeCurly, imgr.makeNumber(4)), smgr.makeString("B"));
    assertEqual(
        smgr.charAt(acurlyOpen2BUnicodeWOEscapeCurly, imgr.makeNumber(5)), curlyClose2BUnicode);
  }

  @Test
  public void testCharAtWithStringVariable() throws SolverException, InterruptedException {
    StringFormula aa = smgr.makeString("aa");
    StringFormula abc = smgr.makeString("abc");
    StringFormula aabc = smgr.makeString("aabc");
    StringFormula abcb = smgr.makeString("abcb");
    StringFormula stringVariable = smgr.makeVariable("stringVariable");

    assertThatFormula(smgr.equal(smgr.charAt(ab, imgr.makeNumber(0)), stringVariable))
        .implies(smgr.equal(stringVariable, a));

    assertThatFormula(smgr.equal(smgr.charAt(ab, imgr.makeNumber(1)), stringVariable))
        .implies(smgr.equal(stringVariable, b));

    assertThatFormula(
            bmgr.and(
                smgr.equal(smgr.charAt(ab, imgr.makeNumber(0)), stringVariable),
                smgr.equal(smgr.charAt(ab, imgr.makeNumber(1)), stringVariable)))
        .isUnsatisfiable();

    assertThatFormula(
            bmgr.and(
                smgr.equal(smgr.charAt(aa, imgr.makeNumber(0)), stringVariable),
                smgr.equal(smgr.charAt(aa, imgr.makeNumber(1)), stringVariable)))
        .implies(smgr.equal(stringVariable, a));

    assertThatFormula(
            bmgr.and(
                smgr.equal(smgr.charAt(stringVariable, imgr.makeNumber(0)), a),
                smgr.equal(smgr.charAt(stringVariable, imgr.makeNumber(1)), b),
                imgr.equal(imgr.makeNumber(2), smgr.length(stringVariable))))
        .implies(smgr.equal(stringVariable, ab));

    assertThatFormula(
            bmgr.and(
                smgr.equal(smgr.charAt(stringVariable, imgr.makeNumber(0)), a),
                smgr.equal(smgr.charAt(stringVariable, imgr.makeNumber(2)), b),
                imgr.equal(imgr.makeNumber(4), smgr.length(stringVariable)),
                smgr.suffix(abc, stringVariable)))
        .implies(smgr.equal(stringVariable, aabc));

    assertThatFormula(
            bmgr.and(
                smgr.equal(smgr.charAt(stringVariable, imgr.makeNumber(0)), a),
                smgr.equal(smgr.charAt(stringVariable, imgr.makeNumber(3)), b),
                imgr.equal(imgr.makeNumber(4), smgr.length(stringVariable)),
                smgr.suffix(abc, stringVariable)))
        .implies(smgr.equal(stringVariable, abcb));

    assertThatFormula(
            bmgr.and(
                smgr.equal(smgr.charAt(stringVariable, imgr.makeNumber(0)), a),
                smgr.equal(smgr.charAt(stringVariable, imgr.makeNumber(3)), b),
                imgr.equal(imgr.makeNumber(4), smgr.length(stringVariable)),
                smgr.prefix(abc, stringVariable)))
        .implies(smgr.equal(stringVariable, abcb));
  }

  @Test
  public void testConstStringContains() throws SolverException, InterruptedException {
    StringFormula aUppercase = smgr.makeString("A");
    StringFormula bUppercase = smgr.makeString("B");
    StringFormula bbbbbb = smgr.makeString("bbbbbb");
    StringFormula bbbbbbb = smgr.makeString("bbbbbbb");
    StringFormula abbbbbb = smgr.makeString("abbbbbb");
    StringFormula aaaaaaaB = smgr.makeString("aaaaaaaB");
    StringFormula abcAndSoOn = smgr.makeString("abcdefghijklmnopqrstuVwxyz");
    StringFormula curlyOpen2BUnicode = smgr.makeString("\\u{7B}");
    StringFormula curlyClose2BUnicode = smgr.makeString("\\u{7D}");
    StringFormula multipleCurlys2BUnicode = smgr.makeString("\\u{7B}\\u{7D}\\u{7B}\\u{7B}");
    StringFormula curlyClose2BUnicodeEncased = smgr.makeString("blabla\\u{7D}bla");

    assertThatFormula(smgr.contains(empty, empty)).isSatisfiable();
    assertThatFormula(smgr.contains(empty, a)).isUnsatisfiable();
    assertThatFormula(smgr.contains(a, empty)).isSatisfiable();
    assertThatFormula(smgr.contains(a, a)).isSatisfiable();
    assertThatFormula(smgr.contains(a, aUppercase)).isUnsatisfiable();
    assertThatFormula(smgr.contains(aUppercase, a)).isUnsatisfiable();
    assertThatFormula(smgr.contains(a, b)).isUnsatisfiable();
    assertThatFormula(smgr.contains(b, b)).isSatisfiable();
    assertThatFormula(smgr.contains(abbbbbb, a)).isSatisfiable();
    assertThatFormula(smgr.contains(abbbbbb, b)).isSatisfiable();
    assertThatFormula(smgr.contains(abbbbbb, bbbbbb)).isSatisfiable();
    assertThatFormula(smgr.contains(abbbbbb, bbbbbbb)).isUnsatisfiable();
    assertThatFormula(smgr.contains(abbbbbb, aUppercase)).isUnsatisfiable();
    assertThatFormula(smgr.contains(abbbbbb, aUppercase)).isUnsatisfiable();
    assertThatFormula(smgr.contains(aaaaaaaB, a)).isSatisfiable();
    assertThatFormula(smgr.contains(aaaaaaaB, b)).isUnsatisfiable();
    assertThatFormula(smgr.contains(aaaaaaaB, bUppercase)).isSatisfiable();
    assertThatFormula(smgr.contains(aaaaaaaB, curlyOpen2BUnicode)).isUnsatisfiable();
    assertThatFormula(smgr.contains(abcAndSoOn, smgr.makeString("xyz"))).isSatisfiable();
    assertThatFormula(smgr.contains(abcAndSoOn, smgr.makeString("Vwxyz"))).isSatisfiable();
    assertThatFormula(smgr.contains(abcAndSoOn, smgr.makeString("Vwxyza"))).isUnsatisfiable();
    assertThatFormula(smgr.contains(abcAndSoOn, smgr.makeString("t Vwxyz"))).isUnsatisfiable();
    assertThatFormula(smgr.contains(multipleCurlys2BUnicode, curlyOpen2BUnicode)).isSatisfiable();
    assertThatFormula(smgr.contains(multipleCurlys2BUnicode, curlyClose2BUnicode)).isSatisfiable();
    assertThatFormula(smgr.contains(curlyClose2BUnicodeEncased, curlyClose2BUnicode))
        .isSatisfiable();
  }

  @Test
  public void testStringVariableContains() throws SolverException, InterruptedException {
    requireVariableStringLiterals();

    StringFormula var1 = smgr.makeVariable("var1");
    StringFormula var2 = smgr.makeVariable("var2");

    StringFormula bUppercase = smgr.makeString("B");
    StringFormula bbbbbb = smgr.makeString("bbbbbb");
    StringFormula abbbbbb = smgr.makeString("abbbbbb");
    StringFormula curlyOpen2BUnicode = smgr.makeString("\\u{7B}");
    StringFormula curlyClose2BUnicode = smgr.makeString("\\u{7D}");

    assertThatFormula(
            bmgr.and(smgr.contains(var1, empty), imgr.equal(imgr.makeNumber(0), smgr.length(var1))))
        .implies(smgr.equal(var1, empty));

    assertThatFormula(bmgr.and(smgr.contains(var1, var2), smgr.contains(var2, var1)))
        .implies(smgr.equal(var1, var2));

    // Unicode is treated as 1 char. So \\u{7B} is treated as { and the B inside is not contained!
    assertThatFormula(
            bmgr.and(
                smgr.contains(var1, curlyOpen2BUnicode),
                smgr.contains(var1, bUppercase),
                imgr.equal(imgr.makeNumber(1), smgr.length(var1))))
        .isUnsatisfiable();
    // Same goes for the curly brackets used as escape sequence
    assertThatFormula(
            bmgr.and(
                smgr.contains(var1, curlyOpen2BUnicode),
                smgr.contains(var1, curlyClose2BUnicode),
                imgr.equal(imgr.makeNumber(1), smgr.length(var1))))
        .isUnsatisfiable();

    assertThatFormula(
            bmgr.and(
                smgr.contains(var1, bbbbbb),
                smgr.contains(var1, ab),
                imgr.equal(imgr.makeNumber(7), smgr.length(var1))))
        .implies(smgr.equal(var1, abbbbbb));
  }

  @Test
  public void testStringContainsOtherVariable() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s runs endlessly on this task", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    requireVariableStringLiterals();

    StringFormula var1 = smgr.makeVariable("var1");
    StringFormula var2 = smgr.makeVariable("var2");

    StringFormula abUppercase = smgr.makeString("AB");

    assertThatFormula(
            bmgr.and(
                smgr.contains(var1, ab),
                smgr.contains(var2, abUppercase),
                smgr.contains(var1, var2)))
        .implies(smgr.contains(var1, abUppercase));
  }

  @Test
  public void testConstStringIndexOf() throws SolverException, InterruptedException {
    StringFormula aUppercase = smgr.makeString("A");
    StringFormula bbbbbb = smgr.makeString("bbbbbb");
    StringFormula bbbbbbb = smgr.makeString("bbbbbbb");
    StringFormula abbbbbb = smgr.makeString("abbbbbb");
    StringFormula abcAndSoOn = smgr.makeString("abcdefghijklmnopqrstuVwxyz");
    StringFormula curlyOpen2BUnicode = smgr.makeString("\\u{7B}");
    StringFormula curlyClose2BUnicode = smgr.makeString("\\u{7D}");
    StringFormula multipleCurlys2BUnicode = smgr.makeString("\\u{7B}\\u{7D}\\u{7B}\\u{7B}");
    StringFormula curlys2BUnicodeWOEscape = smgr.makeString("\\u7B\\u7D");

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);
    IntegerFormula negOne = imgr.makeNumber(-1); // indexOf returns -1 if substring is not found

    assertEqual(smgr.indexOf(empty, empty, zero), zero);
    assertEqual(smgr.indexOf(a, empty, zero), zero);
    assertEqual(smgr.indexOf(a, a, zero), zero);
    assertEqual(smgr.indexOf(a, aUppercase, zero), negOne);
    assertEqual(smgr.indexOf(abbbbbb, a, zero), zero);
    assertEqual(smgr.indexOf(abbbbbb, b, zero), one);
    assertEqual(smgr.indexOf(abbbbbb, ab, zero), zero);
    assertEqual(smgr.indexOf(abbbbbb, bbbbbb, zero), one);
    assertEqual(smgr.indexOf(abbbbbb, bbbbbbb, zero), negOne);
    assertEqual(smgr.indexOf(abbbbbb, smgr.makeString("c"), zero), negOne);
    assertEqual(smgr.indexOf(abcAndSoOn, smgr.makeString("z"), zero), imgr.makeNumber(25));
    assertEqual(smgr.indexOf(abcAndSoOn, smgr.makeString("V"), zero), imgr.makeNumber(21));
    assertEqual(smgr.indexOf(abcAndSoOn, smgr.makeString("v"), zero), negOne);

    assertEqual(smgr.indexOf(multipleCurlys2BUnicode, curlyOpen2BUnicode, zero), zero);
    assertEqual(smgr.indexOf(multipleCurlys2BUnicode, curlyClose2BUnicode, zero), one);
    assertEqual(smgr.indexOf(multipleCurlys2BUnicode, curlys2BUnicodeWOEscape, zero), negOne);
    assertEqual(smgr.indexOf(multipleCurlys2BUnicode, curlys2BUnicodeWOEscape, one), negOne);
    assertEqual(smgr.indexOf(multipleCurlys2BUnicode, smgr.makeString("B"), zero), negOne);
  }

  @Test
  public void testStringVariableIndexOf() throws SolverException, InterruptedException {
    requireVariableStringLiterals();

    StringFormula var1 = smgr.makeVariable("var1");
    StringFormula var2 = smgr.makeVariable("var2");
    IntegerFormula intVar = imgr.makeVariable("intVar");

    StringFormula curlyOpen2BUnicode = smgr.makeString("\\u{7B}");

    IntegerFormula zero = imgr.makeNumber(0);

    // If the index of var2 is not -1, it is contained in var1.
    assertThatFormula(
            bmgr.and(
                bmgr.not(imgr.equal(intVar, imgr.makeNumber(-1))),
                imgr.equal(intVar, smgr.indexOf(var1, var2, zero))))
        .implies(smgr.contains(var1, var2));

    // If the index is less than 0 (only -1 possible) it is not contained.
    assertThatFormula(
            bmgr.and(
                imgr.equal(intVar, smgr.indexOf(var1, var2, zero)), imgr.lessThan(intVar, zero)))
        .implies(bmgr.not(smgr.contains(var1, var2)));

    // If the index of var2 in var is >= 0 and vice versa, both contain each other.
    assertThatFormula(
            bmgr.and(
                imgr.greaterOrEquals(smgr.indexOf(var1, var2, zero), zero),
                imgr.greaterOrEquals(smgr.indexOf(var2, var1, zero), zero)))
        .implies(bmgr.and(smgr.contains(var1, var2), smgr.contains(var2, var1)));

    // If the are indices equal and one is >= 0 and the strings are not "", both are contained in
    // each other and the chars at the position must be the same.
    assertThatFormula(
            bmgr.and(
                imgr.equal(smgr.indexOf(var1, var2, zero), smgr.indexOf(var2, var1, zero)),
                imgr.greaterOrEquals(smgr.indexOf(var1, var2, zero), zero),
                bmgr.not(smgr.equal(empty, smgr.charAt(var1, smgr.indexOf(var1, var2, zero))))))
        .implies(
            bmgr.and(
                smgr.contains(var1, var2),
                smgr.contains(var2, var1),
                smgr.equal(
                    smgr.charAt(var1, smgr.indexOf(var2, var1, zero)),
                    smgr.charAt(var1, smgr.indexOf(var1, var2, zero)))));

    // If a String contains {, but not B, the index of B must be -1. (unicode of { contains B)
    assertThatFormula(
            bmgr.and(
                smgr.contains(var1, curlyOpen2BUnicode),
                bmgr.not(smgr.contains(var1, smgr.makeString("B")))))
        .implies(
            bmgr.and(
                imgr.greaterOrEquals(smgr.indexOf(var1, curlyOpen2BUnicode, zero), zero),
                imgr.equal(imgr.makeNumber(-1), smgr.indexOf(var1, smgr.makeString("B"), zero))));
  }

  @Test
  public void testStringIndexOfWithSubStrings() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s runs endlessly on this task", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    StringFormula var1 = smgr.makeVariable("var1");

    IntegerFormula zero = imgr.makeNumber(0);

    // If the index of the string abba is 0, the index of the string bba is 1, and b is 1, and ba is
    // 2
    assertThatFormula(imgr.equal(zero, smgr.indexOf(var1, smgr.makeString("abba"), zero)))
        .implies(
            bmgr.and(
                smgr.contains(var1, smgr.makeString("abba")),
                imgr.equal(imgr.makeNumber(1), smgr.indexOf(var1, smgr.makeString("bba"), zero)),
                imgr.equal(imgr.makeNumber(1), smgr.indexOf(var1, b, zero)),
                imgr.equal(imgr.makeNumber(2), smgr.indexOf(var1, smgr.makeString("ba"), zero))));
  }

  @Test
  public void testStringPrefixImpliesPrefixIndexOf() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s runs endlessly on this task", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.Z3, Solvers.CVC4);

    requireVariableStringLiterals();

    StringFormula var1 = smgr.makeVariable("var1");
    StringFormula var2 = smgr.makeVariable("var2");

    IntegerFormula zero = imgr.makeNumber(0);

    // If a prefix (var2) is non empty, the length of the string (var1) has to be larger or equal to
    // the prefix
    // and the chars have to be the same for the lenth of the prefix, meaning the indexOf the prefix
    // must be 0 in the string.
    assertThatFormula(bmgr.and(imgr.greaterThan(smgr.length(var2), zero), smgr.prefix(var2, var1)))
        .implies(
            bmgr.and(
                smgr.contains(var1, var2),
                imgr.greaterOrEquals(smgr.length(var1), smgr.length(var2)),
                imgr.equal(zero, smgr.indexOf(var1, var2, zero))));
  }

  @Test
  public void testConstStringSubStrings() throws SolverException, InterruptedException {
    StringFormula aUppercase = smgr.makeString("A");
    StringFormula bUppercase = smgr.makeString("B");
    StringFormula bbbbbb = smgr.makeString("bbbbbb");
    StringFormula curlyOpen2BUnicode = smgr.makeString("\\u{7B}");
    StringFormula curlyClose2BUnicode = smgr.makeString("\\u{7D}");
    StringFormula multipleCurlys2BUnicode = smgr.makeString("\\u{7B}\\u{7D}\\u{7B}\\u{7B}");

    IntegerFormula zero = imgr.makeNumber(0);
    IntegerFormula one = imgr.makeNumber(1);

    // Check empty string
    assertEqual(smgr.substring(empty, zero, zero), empty);
    // Check length 0 = empty string
    assertEqual(smgr.substring(a, one, zero), empty);
    // Check that it correctly recognized uppercase
    assertDistinct(smgr.substring(a, zero, one), aUppercase);
    assertDistinct(smgr.substring(aUppercase, zero, one), a);
    assertDistinct(smgr.substring(bbbbbb, zero, one), bUppercase);
    // Check smgr length interaction
    assertEqual(smgr.substring(bbbbbb, zero, smgr.length(bbbbbb)), bbbbbb);
    // Check unicode substrings
    assertEqual(smgr.substring(multipleCurlys2BUnicode, zero, one), curlyOpen2BUnicode);
    assertEqual(smgr.substring(multipleCurlys2BUnicode, one, one), curlyClose2BUnicode);
  }

  @Test
  public void testConstStringAllPossibleSubStrings() throws SolverException, InterruptedException {
    for (String wordString : WORDS) {
      StringFormula word = smgr.makeString(wordString);

      for (int j = 0; j < wordString.length(); j++) {
        for (int k = j; k < wordString.length(); k++) {
          // Loop through all combinations of substrings
          // Note: String.substring uses begin index and end index (non-including) while SMT based
          // substring uses length!
          // Length = endIndex - beginIndex
          String wordSubString = wordString.substring(j, k);
          assertEqual(
              smgr.substring(word, imgr.makeNumber(j), imgr.makeNumber(k - j)),
              smgr.makeString(wordSubString));
        }
      }
    }
  }

  @Test
  public void testStringSubstringOutOfBounds() throws SolverException, InterruptedException {
    StringFormula bbbbbb = smgr.makeString("bbbbbb");
    StringFormula abbbbbb = smgr.makeString("abbbbbb");

    StringFormula multipleCurlys2BUnicode = smgr.makeString("\\u{7B}\\u{7D}\\u{7B}\\u{7B}");
    StringFormula multipleCurlys2BUnicodeFromIndex1 = smgr.makeString("\\u{7D}\\u{7B}\\u{7B}");

    assertEqual(smgr.substring(abbbbbb, imgr.makeNumber(0), imgr.makeNumber(10000)), abbbbbb);
    assertEqual(smgr.substring(abbbbbb, imgr.makeNumber(6), imgr.makeNumber(10000)), b);
    assertEqual(smgr.substring(abbbbbb, imgr.makeNumber(1), imgr.makeNumber(10000)), bbbbbb);
    assertEqual(
        smgr.substring(multipleCurlys2BUnicode, imgr.makeNumber(1), imgr.makeNumber(10000)),
        multipleCurlys2BUnicodeFromIndex1);
  }

  @Test
  public void testStringVariablesSubstring() throws SolverException, InterruptedException {
    // FIXME: Princess will timeout on this test
    assume().that(solverToUse()).isNotEqualTo(Solvers.PRINCESS);

    StringFormula var1 = smgr.makeVariable("var1");
    StringFormula var2 = smgr.makeVariable("var2");
    IntegerFormula intVar1 = imgr.makeVariable("intVar1");
    IntegerFormula intVar2 = imgr.makeVariable("intVar2");

    // If a Prefix of a certain length exists, the substring over that equals the prefix
    assertThatFormula(smgr.prefix(var2, var1))
        .implies(smgr.equal(var2, smgr.substring(var1, imgr.makeNumber(0), smgr.length(var2))));

    // Same with suffix
    assertThatFormula(smgr.suffix(var2, var1))
        .implies(
            smgr.equal(
                var2,
                smgr.substring(
                    var1, imgr.subtract(smgr.length(var1), smgr.length(var2)), smgr.length(var2))));

    // If a string has a char at a specified position, a substring beginning with the same index
    // must have the same char, independent of the length of the substring.
    // But its not really relevant to check out of bounds cases, hence the exclusion.
    // So we test substring length 1 (== charAt) and larger
    assertThatFormula(
            bmgr.and(
                imgr.greaterThan(intVar2, imgr.makeNumber(1)),
                smgr.equal(var2, smgr.charAt(var1, intVar1)),
                imgr.greaterThan(smgr.length(var1), intVar1)))
        .implies(
            smgr.equal(
                var2, smgr.charAt(smgr.substring(var1, intVar1, intVar2), imgr.makeNumber(0))));

    assertEqual(smgr.charAt(var1, intVar1), smgr.substring(var1, intVar1, imgr.makeNumber(1)));
  }

  @Test
  public void testConstStringReplace() throws SolverException, InterruptedException {
    for (int i = 0; i < WORDS.size(); i++) {
      for (int j = 2; j < WORDS.size(); j++) {
        String word1 = WORDS.get(j - 1);
        String word2 = WORDS.get(j);
        String word3 = WORDS.get(i);
        StringFormula word1F = smgr.makeString(word1);
        StringFormula word2F = smgr.makeString(word2);
        StringFormula word3F = smgr.makeString(word3);

        StringFormula result = smgr.makeString(word3.replaceFirst(word2, word1));
        assertEqual(smgr.replace(word3F, word2F, word1F), result);
      }
    }
  }

  // Neither CVC4 nor Z3 can solve this!
  @Ignore
  @Test
  public void testStringVariableReplacePrefix() throws SolverException, InterruptedException {
    StringFormula var1 = smgr.makeVariable("var1");
    StringFormula var2 = smgr.makeVariable("var2");
    StringFormula var3 = smgr.makeVariable("var3");
    StringFormula prefix = smgr.makeVariable("prefix");

    // If var1 has a prefix, and you replace said prefix with var3 (saved in var2), the prefix of
    // var2 is var3
    assertThatFormula(
            bmgr.and(
                smgr.equal(var2, smgr.replace(var1, prefix, var3)),
                smgr.prefix(prefix, var1),
                bmgr.not(smgr.equal(prefix, var3)),
                imgr.greaterThan(smgr.length(prefix), imgr.makeNumber(0)),
                imgr.greaterThan(smgr.length(var3), imgr.makeNumber(0))))
        .implies(bmgr.and(bmgr.not(smgr.equal(var1, var2)), smgr.prefix(var3, var2)));
    assertThatFormula(
            bmgr.and(
                smgr.equal(var2, smgr.replace(var1, prefix, var3)),
                smgr.prefix(prefix, var1),
                bmgr.not(smgr.equal(prefix, var3))))
        .implies(bmgr.and(smgr.prefix(var3, var2), bmgr.not(smgr.equal(var1, var2))));
  }

  @Test
  public void testStringVariableReplaceSubstring() throws SolverException, InterruptedException {
    requireVariableStringLiterals();

    // I couldn't find stronger constraints in the implication that don't run endlessly.....
    StringFormula original = smgr.makeVariable("original");
    StringFormula prefix = smgr.makeVariable("prefix");
    StringFormula replacement = smgr.makeVariable("replacement");
    StringFormula replaced = smgr.makeVariable("replaced");

    // Set a prefix that does not contain the suffix substring, make sure that the substring that
    // comes after the prefix is replaced
    assertThatFormula(
            bmgr.and(
                smgr.prefix(prefix, original),
                imgr.equal(
                    smgr.length(prefix),
                    smgr.indexOf(
                        original,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)),
                        imgr.makeNumber(0))),
                imgr.greaterThan(smgr.length(original), smgr.length(prefix)),
                imgr.greaterThan(smgr.length(prefix), imgr.makeNumber(0)),
                imgr.greaterThan(
                    smgr.length(
                        smgr.substring(original, smgr.length(prefix), smgr.length(original))),
                    imgr.makeNumber(0)),
                smgr.equal(
                    replaced,
                    smgr.replace(
                        original,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)),
                        replacement))))
        .implies(
            smgr.equal(
                replacement, smgr.substring(replaced, smgr.length(prefix), smgr.length(replaced))));

    // In this version it is still possible that parts of the prefix and suffix together build the
    // suffix, replacing parts of the prefix additionally to the implication above (or the
    // replacement is empty)
    assertThatFormula(
            bmgr.and(
                smgr.prefix(prefix, original),
                bmgr.not(smgr.contains(original, replacement)),
                bmgr.not(
                    smgr.contains(
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)),
                        prefix)),
                bmgr.not(
                    smgr.contains(
                        prefix,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)))),
                imgr.greaterThan(smgr.length(original), smgr.length(prefix)),
                imgr.greaterThan(smgr.length(prefix), imgr.makeNumber(0)),
                smgr.equal(
                    replaced,
                    smgr.replace(
                        original,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)),
                        replacement))))
        .implies(smgr.contains(replacement, replacement));

    // This version may have the original as a larger version of the prefix; prefix: a, original:
    // aaa
    assertThatFormula(
            bmgr.and(
                smgr.prefix(prefix, original),
                bmgr.not(smgr.contains(original, replacement)),
                bmgr.not(
                    smgr.contains(
                        prefix,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)))),
                imgr.greaterThan(smgr.length(original), smgr.length(prefix)),
                imgr.greaterThan(smgr.length(prefix), imgr.makeNumber(0)),
                smgr.equal(
                    replaced,
                    smgr.replace(
                        original,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)),
                        replacement))))
        .implies(smgr.contains(replacement, replacement));

    // This version can contain the substring in the prefix!
    assertThatFormula(
            bmgr.and(
                smgr.prefix(prefix, original),
                bmgr.not(smgr.contains(original, replacement)),
                imgr.greaterThan(smgr.length(original), smgr.length(prefix)),
                imgr.greaterThan(smgr.length(prefix), imgr.makeNumber(0)),
                smgr.equal(
                    replaced,
                    smgr.replace(
                        original,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)),
                        replacement))))
        .implies(smgr.contains(replacement, replacement));
  }

  @Test
  public void testStringVariableReplaceMiddle() throws SolverException, InterruptedException {
    // TODO: either rework that this terminates, or remove
    assume()
        .withMessage("Solver %s runs endlessly on this task.", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.CVC4, Solvers.Z3);

    requireVariableStringLiterals();

    StringFormula original = smgr.makeVariable("original");
    StringFormula replacement = smgr.makeVariable("replacement");
    StringFormula replaced = smgr.makeVariable("replaced");
    StringFormula beginning = smgr.makeVariable("beginning");
    StringFormula middle = smgr.makeVariable("middle");
    StringFormula end = smgr.makeVariable("end");

    // If beginning + middle + end (length of each > 0) get concatenated (in original), replacing
    // beginning/middle/end
    // with replacement (result = replaces; replacement > 0 and != the replaced) results in a
    // string that is equal to the concat of the 2 remaining start strings and the replaced one
    // replaced
    // This is tested with 2 different implications, 1 that only checks whether or not the
    // replacement is contained in the string and not in the original and vice verse for the
    // replaced String
    BooleanFormula formula =
        bmgr.and(
            smgr.equal(original, smgr.concat(beginning, middle, end)),
            smgr.equal(replaced, smgr.replace(original, middle, replacement)),
            bmgr.not(smgr.equal(middle, replacement)),
            bmgr.not(smgr.equal(beginning, replacement)),
            bmgr.not(smgr.equal(end, replacement)),
            bmgr.not(smgr.equal(beginning, middle)),
            imgr.greaterThan(smgr.length(middle), imgr.makeNumber(0)),
            imgr.greaterThan(smgr.length(replacement), imgr.makeNumber(0)),
            imgr.greaterThan(smgr.length(beginning), imgr.makeNumber(0)));
    assertThatFormula(formula)
        .implies(
            bmgr.and(
                bmgr.not(smgr.equal(original, replaced)), smgr.contains(replaced, replacement)));

    assume()
        .withMessage("Solver %s returns the initial formula.", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.CVC5);

    // Same as above, but with concat instead of contains
    assertThatFormula(formula)
        .implies(
            bmgr.and(
                bmgr.not(smgr.equal(original, replaced)),
                smgr.equal(replaced, smgr.concat(beginning, replacement, end))));
  }

  @Test
  public void testStringVariableReplaceFront() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s runs endlessly on this task.", solverToUse())
        .that(solverToUse())
        .isNoneOf(Solvers.Z3, Solvers.CVC5);

    requireVariableStringLiterals();

    StringFormula var1 = smgr.makeVariable("var1");
    StringFormula var2 = smgr.makeVariable("var2");
    StringFormula var3 = smgr.makeVariable("var3");
    StringFormula var4 = smgr.makeVariable("var4");
    StringFormula var5 = smgr.makeVariable("var5");

    // If var1 and 2 get concated (in var4) such that var1 is in front, replacing var1 with var3
    // (var5) results in a
    // string that is equal to var3 + var2
    // First with length constraints, second without
    assertThatFormula(
            bmgr.and(
                smgr.equal(var4, smgr.concat(var1, var2)),
                smgr.equal(var5, smgr.replace(var4, var1, var3)),
                bmgr.not(smgr.equal(var1, var3)),
                imgr.greaterThan(smgr.length(var1), imgr.makeNumber(0)),
                imgr.greaterThan(smgr.length(var3), imgr.makeNumber(0))))
        .implies(bmgr.and(bmgr.not(smgr.equal(var4, var5)), smgr.prefix(var3, var5)));

    assertThatFormula(
            bmgr.and(
                smgr.equal(var4, smgr.concat(var1, var2)),
                smgr.equal(var5, smgr.replace(var4, var1, var3)),
                bmgr.not(smgr.equal(var1, var3))))
        .implies(bmgr.and(bmgr.not(smgr.equal(var4, var5)), smgr.prefix(var3, var5)));
  }

  @Test
  public void testConstStringReplaceAll() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support replaceAll()", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    for (int i = 0; i < WORDS.size(); i++) {
      for (int j = 1; j < WORDS.size(); j++) {
        String word1 = WORDS.get(i);
        String word2 = WORDS.get(j);
        String word3 = "replacement";
        StringFormula word1F = smgr.makeString(word1);
        StringFormula word2F = smgr.makeString(word2);
        StringFormula word3F = smgr.makeString(word3);

        StringFormula result = smgr.makeString(word3.replaceAll(word2, word1));
        assertEqual(smgr.replaceAll(word3F, word2F, word1F), result);
      }
    }
  }

  /**
   * Concat a String that consists of a String that is later replaces with replaceAll. The resulting
   * String should consist of only concatinated versions of itself.
   */
  @Test
  public void testStringVariableReplaceAllConcatedString()
      throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support replaceAll()", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    requireVariableStringLiterals();

    // 2 concats is the max number CVC4 supports without running endlessly
    for (int numOfConcats = 0; numOfConcats < 3; numOfConcats++) {

      StringFormula original = smgr.makeVariable("original");
      StringFormula replacement = smgr.makeVariable("replacement");
      StringFormula replaced = smgr.makeVariable("replaced");
      StringFormula segment = smgr.makeVariable("segment");

      StringFormula[] concatSegments = new StringFormula[numOfConcats];
      StringFormula[] concatReplacements = new StringFormula[numOfConcats];

      for (int i = 0; i < numOfConcats; i++) {
        concatSegments[i] = segment;
        concatReplacements[i] = replacement;
      }

      BooleanFormula formula =
          bmgr.and(
              smgr.equal(original, smgr.concat(concatSegments)),
              smgr.equal(replaced, smgr.replaceAll(original, segment, replacement)),
              bmgr.not(smgr.equal(segment, replacement)),
              imgr.greaterThan(smgr.length(segment), imgr.makeNumber(0)),
              imgr.greaterThan(smgr.length(replacement), imgr.makeNumber(0)));
      assertThatFormula(formula).implies(smgr.equal(replaced, smgr.concat(concatReplacements)));
    }
  }

  @Test
  public void testStringVariableReplaceAllSubstring() throws SolverException, InterruptedException {
    assume()
        .withMessage("Solver %s does not support replaceAll()", solverToUse())
        .that(solverToUse())
        .isNotEqualTo(Solvers.Z3);

    requireVariableStringLiterals();

    // I couldn't find stronger constraints in the implication that don't run endlessly.....
    StringFormula original = smgr.makeVariable("original");
    StringFormula prefix = smgr.makeVariable("prefix");
    StringFormula replacement = smgr.makeVariable("replacement");
    StringFormula replaced = smgr.makeVariable("replaced");

    // Set a prefix that does not contain the suffix substring, make sure that the substring that
    // comes after the prefix is replaced
    assertThatFormula(
            bmgr.and(
                smgr.prefix(prefix, original),
                imgr.equal(
                    smgr.length(prefix),
                    smgr.indexOf(
                        original,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)),
                        imgr.makeNumber(0))),
                imgr.greaterThan(smgr.length(original), smgr.length(prefix)),
                imgr.greaterThan(smgr.length(prefix), imgr.makeNumber(0)),
                imgr.greaterThan(
                    smgr.length(
                        smgr.substring(original, smgr.length(prefix), smgr.length(original))),
                    imgr.makeNumber(0)),
                smgr.equal(
                    replaced,
                    smgr.replaceAll(
                        original,
                        smgr.substring(original, smgr.length(prefix), smgr.length(original)),
                        replacement))))
        .implies(
            smgr.equal(
                replacement, smgr.substring(replaced, smgr.length(prefix), smgr.length(replaced))));
  }

  @Test
  public void testStringConcatWUnicode() throws SolverException, InterruptedException {
    StringFormula backslash = smgr.makeString("\\");
    StringFormula u = smgr.makeString("u");
    StringFormula curlyOpen = smgr.makeString("\\u{7B}");
    StringFormula sevenB = smgr.makeString("7B");
    StringFormula curlyClose = smgr.makeString("\\u{7D}");
    StringFormula concat = smgr.concat(backslash, u, curlyOpen, sevenB, curlyClose);
    StringFormula complete = smgr.makeString("\\u{7B}");

    // Concatting parts of unicode does not result in the unicode char!
    assertDistinct(concat, complete);
  }

  @Test
  public void testStringSimpleRegex() {
    // TODO
  }

  @Test
  public void testVisitorForStringConstants() {
    BooleanFormula eq =
        bmgr.and(
            smgr.equal(smgr.makeString("x"), smgr.makeString("xx")),
            smgr.lessThan(smgr.makeString("y"), smgr.makeString("yy")));
    Map<String, Formula> freeVars = mgr.extractVariables(eq);
    assertThat(freeVars).isEmpty();
    Map<String, Formula> freeVarsAndUfs = mgr.extractVariablesAndUFs(eq);
    assertThat(freeVarsAndUfs).isEmpty();
  }

  @Test
  public void testVisitorForRegexConstants() {
    RegexFormula concat = smgr.concat(smgr.makeRegex("x"), smgr.makeRegex("xx"));
    Map<String, Formula> freeVars = mgr.extractVariables(concat);
    assertThat(freeVars).isEmpty();
    Map<String, Formula> freeVarsAndUfs = mgr.extractVariablesAndUFs(concat);
    assertThat(freeVarsAndUfs).isEmpty();
  }

  @Test
  public void testVisitorForStringSymbols() {
    BooleanFormula eq = smgr.equal(smgr.makeVariable("x"), smgr.makeString("xx"));
    Map<String, Formula> freeVars = mgr.extractVariables(eq);
    assertThat(freeVars).containsExactly("x", smgr.makeVariable("x"));
    Map<String, Formula> freeVarsAndUfs = mgr.extractVariablesAndUFs(eq);
    assertThat(freeVarsAndUfs).containsExactly("x", smgr.makeVariable("x"));
  }

  @Test
  public void testVisitorForRegexSymbols() {
    BooleanFormula in = smgr.in(smgr.makeVariable("x"), smgr.makeRegex("xx"));
    Map<String, Formula> freeVars = mgr.extractVariables(in);
    assertThat(freeVars).containsExactly("x", smgr.makeVariable("x"));
    Map<String, Formula> freeVarsAndUfs = mgr.extractVariablesAndUFs(in);
    assertThat(freeVarsAndUfs).containsExactly("x", smgr.makeVariable("x"));
  }

  @Test
  public void validCodesTest() {
    for (Map.Entry<String, String> code :
        ImmutableMap.<String, String>builder()
            .put("\\u0061", "a")
            .put("\\uabcd", "ꯍ")
            .put("\\u{a}", "\n")
            .put("\\u{ab}", "«")
            .put("\\u{abc}", "઼")
            .put("\\u{abcd}", "ꯍ")
            .put("X\\u{abcd}Y\\u0061z", "XꯍYaz")
            .buildOrThrow()
            .entrySet()) {
      assertThat(unescapeUnicodeForSmtlib(code.getKey())).isEqualTo(code.getValue());
    }
  }

  @Test
  public void invalidCodesTest() {
    for (String code : ImmutableList.of("\\uabc", "\\u000g", "\\u{}", "\\u{abcd")) {
      assertThat(unescapeUnicodeForSmtlib(code)).isEqualTo(code);
    }
  }

  @Test
  public void unsupportedCodesTest() {
    // SMTLIB does not specify support for Unicode characters over 0x2FFFF
    assertThrows(IllegalArgumentException.class, () -> unescapeUnicodeForSmtlib("\\u{abcde}"));
    assertThat(unescapeUnicodeForSmtlib("\\u{abcdg}")).isEqualTo("\\u{abcdg}");
  }
}
