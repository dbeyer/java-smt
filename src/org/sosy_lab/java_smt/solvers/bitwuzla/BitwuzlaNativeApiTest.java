// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.truth.Truth.assertThat;
import static org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaSolverContext.loadLibrary;

import com.google.common.truth.Truth;
import org.junit.After;
import org.junit.AssumptionViolatedException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.NativeLibraries;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Bitwuzla;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Map_TermTerm;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Option;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Options;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Parser;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Result;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.RoundingMode;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Int;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

public class BitwuzlaNativeApiTest {
  private TermManager termManager;
  private Bitwuzla bitwuzla;

  @BeforeClass
  public static void load() {
    try {
      loadLibrary(NativeLibraries::loadLibrary);
    } catch (UnsatisfiedLinkError e) {
      throw new AssumptionViolatedException("Bitwuzla is not available", e);
    }
  }

  @Before
  public void createEnvironment() {
    termManager = new TermManager();
    bitwuzla = new Bitwuzla(termManager, createOptions());
  }

  private Options createOptions() {
    Options options = new Options();
    options.set(Option.PRODUCE_MODELS, 2);
    return options;
  }

  @After
  public void freeEnvironment() {
    if (bitwuzla != null) {
      bitwuzla.delete();
    }
  }

  @Test
  public void signedFunctions() {
    Sort sortbv4 = termManager.mk_bv_sort(4);
    Sort sortbv8 = termManager.mk_bv_sort(8);
    // Create function sort.
    Sort[] domain = {sortbv8, sortbv4};
    Sort sortfun = termManager.mk_fun_sort(new Vector_Sort(domain), sortbv8);

    Term x = termManager.mk_const(sortbv8, "x");
    Term f = termManager.mk_const(sortfun, "f");

    Term term =
        termManager.mk_term(Kind.APPLY, f, x, termManager.mk_term(Kind.BV_EXTRACT, x, 6, 3));

    Sort resultSort = term.sort();

    assertThat(sortbv8).isEqualTo(resultSort);
  }

  @Test
  public void boolType() {
    Sort pBoolType = termManager.mk_bool_sort();
    assertThat(pBoolType.is_bool()).isTrue();
  }

  @Test
  public void repeatedTermCreationInMultipleSolversTest() {
    Term tru1 = termManager.mk_true();
    Term tru12 = termManager.mk_true();
    assertThat(tru1.is_true()).isTrue();
    assertThat(tru12.is_true()).isTrue();

    new Thread(
            () -> {
              assertThat(tru1.is_true()).isTrue();
              assertThat(tru12.is_true()).isTrue();
            })
        .start();
  }

  @Test
  public void isFalse() {
    Sort pBoolType = termManager.mk_bool_sort();
    Term var1 = termManager.mk_const(pBoolType, "var1");
    Term var2 = termManager.mk_const(pBoolType, "var2");

    Truth.assertThat(var1.is_false()).isFalse();
    Truth.assertThat(var1.is_true()).isFalse();
    Truth.assertThat(var2.is_false()).isFalse();
    Truth.assertThat(var2.is_true()).isFalse();
  }

  @Test
  public void testBvModel() {
    Sort bvSort = termManager.mk_bv_sort(32);
    Term a = termManager.mk_const(bvSort, "a");
    Term one = termManager.mk_bv_one(bvSort);
    Term two = termManager.mk_bv_value_int64(bvSort, 2);

    // 1 + 2 = a
    Term add = termManager.mk_term(Kind.BV_ADD, one, two);
    Term eq = termManager.mk_term(Kind.EQUAL, add, a);

    bitwuzla.assert_formula(eq);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    // Get model value as String
    String aString = a.toString();
    assertThat(aString).isEqualTo("a");
    String aValue = bitwuzla.get_value(a).toString();
    // #b00000000000000000000000000000011 == 3
    assertThat(aValue).isEqualTo("#b00000000000000000000000000000011");
    assertThat(one.toString()).isEqualTo("#b00000000000000000000000000000001");
    assertThat(two.toString()).isEqualTo("#b00000000000000000000000000000010");
  }

  @Test
  public void testBvArrayModelStore() {
    Sort bvSort4 = termManager.mk_bv_sort(4);
    Sort bvSort8 = termManager.mk_bv_sort(8);
    Sort sortArr = termManager.mk_array_sort(bvSort4, bvSort8);

    Term var = termManager.mk_const(bvSort8, "var");
    Term eleven = termManager.mk_bv_value_int64(bvSort8, 11);
    Term zero = termManager.mk_bv_zero(bvSort4);
    Term one = termManager.mk_bv_one(bvSort4);

    Term arr = termManager.mk_const(sortArr, "arr");

    // Array arr = {11, var} AND arr[0] == arr[1] -> var == 11
    Term arrW11At0 = termManager.mk_term(Kind.ARRAY_STORE, arr, zero, eleven);
    Term arrWVarAt1 = termManager.mk_term(Kind.ARRAY_STORE, arrW11At0, one, var);
    Term eq =
        termManager.mk_term(
            Kind.EQUAL,
            termManager.mk_term(Kind.ARRAY_SELECT, arrWVarAt1, one),
            termManager.mk_term(Kind.ARRAY_SELECT, arrWVarAt1, zero));

    bitwuzla.assert_formula(eq);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    // Get model value as String
    String varString = var.toString();
    assertThat(varString).isEqualTo("var");
    String varValue = bitwuzla.get_value(var).toString();

    assertThat(varValue).isEqualTo("#b00001011");
    assertThat(bitwuzla.get_value(eleven).toString()).isEqualTo(varValue);
    assertThat(one.toString()).isEqualTo("#b0001");
    assertThat(zero.toString()).isEqualTo("#b0000");

    assertThat(arrWVarAt1.sort().is_array()).isTrue();
    assertThat(arr.sort().is_array()).isTrue();

    // Getting the model of the array prints the SMTLIB2 representation
    Term valueArrWVarAt1 = bitwuzla.get_value(arrWVarAt1);
    // The value of an STORE expression is not really helpful, see string below
    String arrWVarAt1ValueString = valueArrWVarAt1.toString();
    assertThat(arrWVarAt1ValueString)
        .isEqualTo(
            "(store (store ((as const (Array (_ BitVec 4) (_ BitVec 8))) #b00000000) #b0000"
                + " #b00001011) #b0001 #b00001011)");

    // We can access the children of the arrays
    // Array children are structured in the following way:
    // {starting array, index, value} in "we add value at index to array"
    // Just declared (empty) arrays return an empty array
    Vector_Term children = arrWVarAt1.children();
    assertThat(children).hasSize(3);
    assertThat(children.get(0)).isEqualTo(arrW11At0);
    assertThat(children.get(1)).isEqualTo(one);
    assertThat(children.get(2)).isEqualTo(var);
    Vector_Term children2 = arrW11At0.children();
    assertThat(children).hasSize(3);
    assertThat(children2.get(0)).isEqualTo(arr);
    assertThat(children2.get(1)).isEqualTo(zero);
    assertThat(children2.get(2)).isEqualTo(eleven);
    Vector_Term children3 = arr.children();
    assertThat(children3).isEmpty();
  }

  @Test
  public void testBvArrayModelSelect() {
    Sort bvSort4 = termManager.mk_bv_sort(4);
    Sort bvSort8 = termManager.mk_bv_sort(8);
    Sort sortArr = termManager.mk_array_sort(bvSort4, bvSort8);

    Term eleven = termManager.mk_bv_value_int64(bvSort8, 11);
    Term zero = termManager.mk_bv_zero(bvSort4);
    Term one = termManager.mk_bv_one(bvSort4);

    Term arr = termManager.mk_const(sortArr, "arr");

    // Array arr[0] == (store arr[1] 11))[1]
    Term selectArrAtZero = termManager.mk_term(Kind.ARRAY_SELECT, arr, zero);
    Term arrWElevenAt1 = termManager.mk_term(Kind.ARRAY_STORE, arr, one, eleven);
    Term selectArrWElevenAtOne = termManager.mk_term(Kind.ARRAY_SELECT, arrWElevenAt1, one);
    Term eq = termManager.mk_term(Kind.EQUAL, selectArrAtZero, selectArrWElevenAtOne);

    bitwuzla.assert_formula(eq);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    String arrAtZeroString = selectArrAtZero.symbol();
    assertThat(arrAtZeroString).isNull();
    // Get model value arr[0] as String
    String arrAtZeroValueString = bitwuzla.get_value(selectArrAtZero).to_bv();
    // 00001011 == 11
    assertThat(arrAtZeroValueString).isEqualTo("00001011");

    // Arrays w 2 children are structured in the following way:
    // {starting array, index} in "we select index from array"
    // Just declared (empty) arrays return an empty children array
    Vector_Term children = selectArrAtZero.children();
    assertThat(children).hasSize(2);
    assertThat(children.get(0)).isEqualTo(arr);
    String arrSymbol = children.get(0).symbol();
    assertThat(arrSymbol).isEqualTo("arr");
    assertThat(children.get(1)).isEqualTo(zero);
  }

  @Test
  public void testUfModel() {
    Sort boolSort = termManager.mk_bool_sort();
    Term res = termManager.mk_const(boolSort, "res");
    Sort bvSort8 = termManager.mk_bv_sort(8);
    Term arg1 = termManager.mk_const(bvSort8, "arg1");
    Term arg2 = termManager.mk_bv_value_int64(bvSort8, 11);
    Sort[] domain = {bvSort8, bvSort8};
    Sort sortFun = termManager.mk_fun_sort(new Vector_Sort(domain), boolSort);

    Term foo = termManager.mk_const(sortFun, "foo");
    Term appliedFoo = termManager.mk_term(Kind.APPLY, foo, arg1, arg2);

    Term eq = termManager.mk_term(Kind.EQUAL, appliedFoo, res);
    bitwuzla.assert_formula(eq);
    Result result = bitwuzla.check_sat();
    assertThat(result).isEqualTo(Result.SAT);

    // Get model value as String
    String resString = res.toString();
    assertThat(resString).isEqualTo("res");
    String resValue = bitwuzla.get_value(res).toString();

    // Bitwuzla seems to default to false and zero
    assertThat(resValue).isEqualTo("false");
    assertThat(bitwuzla.get_value(arg1).toString()).isEqualTo("#b00000000");
    assertThat(arg2.toString()).isEqualTo("#b00001011");

    // Children of the UF are ordered the following:
    // {function, arguments...}
    // Declaration is empty array
    Vector_Term childrenAppliedFoo = appliedFoo.children();
    assertThat(childrenAppliedFoo).hasSize(3);
    assertThat(childrenAppliedFoo.get(0)).isEqualTo(foo);
    assertThat(childrenAppliedFoo.get(1)).isEqualTo(arg1);
    assertThat(childrenAppliedFoo.get(2)).isEqualTo(arg2);
    Vector_Term childrenFoo = foo.children();
    assertThat(childrenFoo).isEmpty();
  }

  @Test
  public void testBoolModel() {
    Sort boolSort = termManager.mk_bool_sort();
    Term x = termManager.mk_const(boolSort, "x");
    Term t = termManager.mk_true();
    Term f = termManager.mk_false();

    // (x AND true) OR false
    Term and = termManager.mk_term(Kind.AND, x, t);
    Term or = termManager.mk_term(Kind.OR, and, f);

    bitwuzla.assert_formula(or);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    // Get model value as String
    String xString = x.toString();
    assertThat(xString).isEqualTo("x");
    String xValue = bitwuzla.get_value(x).toString();

    assertThat(xValue).isEqualTo("true");
    assertThat(t.toString()).isEqualTo("true");
    assertThat(f.toString()).isEqualTo("false");

    // Children of AND and OR
    Vector_Term childrenOr = or.children();
    assertThat(childrenOr).hasSize(2);
    assertThat(childrenOr.get(0)).isEqualTo(and);
    assertThat(childrenOr.get(1)).isEqualTo(f);

    assertThat(or.kind()).isEqualTo(Kind.OR);

    Vector_Term childrenAnd = and.children();
    assertThat(childrenOr).hasSize(2);
    assertThat(childrenAnd.get(0)).isEqualTo(x);
    assertThat(childrenAnd.get(1)).isEqualTo(t);

    assertThat(and.kind()).isEqualTo(Kind.AND);
  }

  // -0 == 0 for FP equals is SAT
  // -0 != 0 for equals
  // -------  NAN  --------
  // nan != nan for FP equals
  // nan == nan for equals is SAT
  // ------  pos infinity and neg infinity  ------
  // pos inf != neg inf FP eq
  // pos inf != neg inf eq
  @Test
  public void testFpSpecialValueEquality() {
    Sort fpSort = termManager.mk_fp_sort(5, 11);
    Term zero = termManager.mk_fp_pos_zero(fpSort);
    assertThat(zero.is_fp_value_pos_zero()).isTrue();
    assertThat(zero.is_fp_value_neg_zero()).isFalse();
    Term negZero = termManager.mk_fp_neg_zero(fpSort);
    assertThat(negZero.is_fp_value_neg_zero()).isTrue();
    assertThat(negZero.is_fp_value_pos_zero()).isFalse();

    // -0 == 0 for FP equals is SAT
    Term negZeroFpEqZero = termManager.mk_term(Kind.FP_EQUAL, zero, negZero);
    bitwuzla.push(1);
    bitwuzla.assert_formula(negZeroFpEqZero);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);
    bitwuzla.pop(1);

    // -0 != 0 for fp equals is UNSAT
    Term notNegZeroFpEqZero = termManager.mk_term(Kind.NOT, negZeroFpEqZero);
    bitwuzla.push(1);
    bitwuzla.assert_formula(notNegZeroFpEqZero);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.UNSAT);
    bitwuzla.pop(1);

    // -0 == 0 for equals is UNSAT
    Term negZeroEqZero = termManager.mk_term(Kind.EQUAL, zero, negZero);
    bitwuzla.push(1);
    bitwuzla.assert_formula(negZeroEqZero);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.UNSAT);
    bitwuzla.pop(1);

    // -0 != 0 for equals is SAT
    Term notnegZeroEqZero = termManager.mk_term(Kind.NOT, negZeroEqZero);
    bitwuzla.push(1);
    bitwuzla.assert_formula(notnegZeroEqZero);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);
    bitwuzla.pop(1);

    // -------  NAN  --------
    Term nan = termManager.mk_fp_nan(fpSort);
    assertThat(nan.is_fp_value_nan()).isTrue();
    assertThat(negZero.is_fp_value_nan()).isFalse();
    assertThat(zero.is_fp_value_nan()).isFalse();
    assertThat(nan.is_fp_value_neg_zero()).isFalse();
    assertThat(nan.is_fp_value_pos_zero()).isFalse();

    // nan == nan for FP equals is UNSAT
    Term nanFpEqNan = termManager.mk_term(Kind.FP_EQUAL, nan, nan);
    bitwuzla.push(1);
    bitwuzla.assert_formula(nanFpEqNan);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.UNSAT);
    bitwuzla.pop(1);

    // nan != nan for fp equals is SAT
    Term notNanFpEqNan = termManager.mk_term(Kind.NOT, nanFpEqNan);
    bitwuzla.push(1);
    bitwuzla.assert_formula(notNanFpEqNan);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);
    bitwuzla.pop(1);

    // nan == nan for equals is SAT
    Term nanEqNan = termManager.mk_term(Kind.EQUAL, nan, nan);
    bitwuzla.push(1);
    bitwuzla.assert_formula(nanEqNan);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);
    bitwuzla.pop(1);

    // nan != nan for equals is UNSAT
    Term notNanEqNan = termManager.mk_term(Kind.NOT, nanEqNan);
    bitwuzla.push(1);
    bitwuzla.assert_formula(notNanEqNan);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.UNSAT);
    bitwuzla.pop(1);

    // ------  pos infinity and neg infinity  ------
    Term posInf = termManager.mk_fp_pos_inf(fpSort);
    Term negInf = termManager.mk_fp_neg_inf(fpSort);
    assertThat(posInf.is_fp_value_pos_inf()).isTrue();
    assertThat(posInf.is_fp_value_neg_inf()).isFalse();
    assertThat(negInf.is_fp_value_pos_inf()).isFalse();
    assertThat(negInf.is_fp_value_neg_inf()).isTrue();
    assertThat(nan.is_fp_value_pos_inf()).isFalse();
    assertThat(nan.is_fp_value_neg_inf()).isFalse();
    assertThat(zero.is_fp_value_pos_inf()).isFalse();
    assertThat(zero.is_fp_value_neg_inf()).isFalse();
    assertThat(negZero.is_fp_value_pos_inf()).isFalse();
    assertThat(negZero.is_fp_value_neg_inf()).isFalse();

    // pos inf == neg inf fp eq is UNSAT
    Term posInfFpEqNegInf = termManager.mk_term(Kind.FP_EQUAL, posInf, negInf);
    bitwuzla.push(1);
    bitwuzla.assert_formula(posInfFpEqNegInf);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.UNSAT);
    bitwuzla.pop(1);

    // pos inf != neg inf fp eq is SAT
    Term notPosInfFpEqNegInf = termManager.mk_term(Kind.NOT, posInfFpEqNegInf);
    bitwuzla.push(1);
    bitwuzla.assert_formula(notPosInfFpEqNegInf);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);
    bitwuzla.pop(1);

    // pos inf == neg inf eq is UNSAT
    Term posInfEqNegInf = termManager.mk_term(Kind.EQUAL, posInf, negInf);
    bitwuzla.push(1);
    bitwuzla.assert_formula(posInfEqNegInf);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.UNSAT);
    bitwuzla.pop(1);

    // pos inf != neg inf eq is SAT
    Term notPosInfEqNegInf = termManager.mk_term(Kind.NOT, posInfEqNegInf);
    bitwuzla.push(1);
    bitwuzla.assert_formula(notPosInfEqNegInf);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);
    bitwuzla.pop(1);
  }

  @Test
  public void testFpModel() {
    Sort fpSort = termManager.mk_fp_sort(5, 11);
    Term rm = termManager.mk_rm_value(RoundingMode.RNE);
    Term a = termManager.mk_const(fpSort, "a");
    Term one = termManager.mk_fp_value(fpSort, rm, "1");
    // Rational with 0 (or only 0s) as the second argument crashes Bitwuzla!
    Term two = termManager.mk_fp_value(fpSort, rm, "2", "1");

    // 1 + 2 = a
    Term add = termManager.mk_term(Kind.FP_ADD, rm, two, one);
    Term eq = termManager.mk_term(Kind.EQUAL, add, a);

    bitwuzla.assert_formula(eq);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    // Get model value as String
    String aString = a.toString();
    assertThat(aString).isEqualTo("a");
    String aValue = bitwuzla.get_value(a).toString();

    assertThat(aValue).isEqualTo("(fp #b0 #b10000 #b1000000000)");
    assertThat(one.toString()).isEqualTo("(fp #b0 #b01111 #b0000000000)");
    assertThat(two.toString()).isEqualTo("(fp #b0 #b10000 #b0000000000)");
  }

  @Test
  public void testFpToBv() {
    // A constant (BITWUZLA_KIND_CONSTANT) is both, a variable and a constant value
    // However a value is also a BITWUZLA_KIND_VALUE, while a variable is not
    Sort fpSort = termManager.mk_fp_sort(5, 11);
    Term rm = termManager.mk_rm_value(RoundingMode.RTZ);
    Term a = termManager.mk_const(fpSort, "a");
    Term one = termManager.mk_fp_value(fpSort, rm, "-1");
    Term two = termManager.mk_fp_value(fpSort, rm, "2");

    Term bvOne = termManager.mk_term(Kind.FP_TO_SBV, rm, one, 11 + 5);
    Term bvTwo = termManager.mk_term(Kind.FP_TO_SBV, rm, two, 11 + 5);
    Term add = termManager.mk_term(Kind.FP_ADD, rm, two, one);
    Term eq = termManager.mk_term(Kind.EQUAL, add, a);

    Term bvA = termManager.mk_term(Kind.FP_TO_SBV, rm, a, 11 + 5);
    Term bvAdd = termManager.mk_term(Kind.BV_ADD, bvOne, bvTwo);
    Term eqBv = termManager.mk_term(Kind.EQUAL, bvAdd, bvA);

    bitwuzla.assert_formula(eq);
    bitwuzla.assert_formula(eqBv);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    String bvAString = bitwuzla.get_value(bvA).toString();

    assertThat(bvAString).isEqualTo("#b0000000000000001");
    assertThat(bitwuzla.get_value(bvOne).toString()).isEqualTo("#b1111111111111111");
    assertThat(bitwuzla.get_value(bvTwo).toString()).isEqualTo("#b0000000000000010");
    // Now test -0.9 to 0 and 0.9 to 0
    Term nearlyMin1 = termManager.mk_fp_value(fpSort, rm, "-0.9");
    Term nearly1 = termManager.mk_fp_value(fpSort, rm, "0.9");
    Term bvnearlyMin1 = termManager.mk_term(Kind.FP_TO_SBV, rm, nearlyMin1, 11 + 5);
    Term bvnearly1 = termManager.mk_term(Kind.FP_TO_SBV, rm, nearly1, 11 + 5);
    Term b = termManager.mk_const(termManager.mk_bv_sort(11 + 5), "b");
    Term bvAdd2 = termManager.mk_term(Kind.BV_ADD, bvnearlyMin1, bvnearly1);
    Term eqBv2 = termManager.mk_term(Kind.EQUAL, bvAdd2, b);

    bitwuzla.assert_formula(eqBv2);
    res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    assertThat(bitwuzla.get_value(bvnearlyMin1).toString()).isEqualTo("#b0000000000000000");
    assertThat(bitwuzla.get_value(bvnearly1).toString()).isEqualTo("#b0000000000000000");
  }

  @Test
  public void testTypes() {
    // A constant (BITWUZLA_KIND_CONSTANT) is both, a variable and a constant value
    // However a value is also a BITWUZLA_KIND_VALUE, while a variable is not
    Sort fpSort = termManager.mk_fp_sort(5, 11);
    Term rm = termManager.mk_rm_value(RoundingMode.RNE);
    Term a = termManager.mk_const(fpSort, "a");
    Term one = termManager.mk_fp_value(fpSort, rm, "1");
    Term two = termManager.mk_fp_value(fpSort, rm, "2");

    Sort boolSort = termManager.mk_bool_sort();
    //    Result res = termManager.mk_const(boolSort, "res");
    Sort bvSort8 = termManager.mk_bv_sort(8);
    Term arg1 = termManager.mk_const(bvSort8, "arg1");
    Term arg2 = termManager.mk_bv_value_int64(bvSort8, 11);
    Sort[] domain = {bvSort8, bvSort8};
    Sort sortFun = termManager.mk_fun_sort(new Vector_Sort(domain), boolSort);

    // (applied) UFs have 1 + arity children, the UF decl (in this case foo), then the arguments
    // in order. Applied UFs are also no "fun", but can only be discerned by KIND
    // The decl has no children, but you can get domain and codomain with API calls
    Term foo = termManager.mk_const(sortFun, "foo");
    Term appliedFoo = termManager.mk_term(Kind.APPLY, foo, arg1, arg2);
    assertThat(appliedFoo.sort().is_fun()).isFalse();
    assertThat(appliedFoo.sort().is_bool()).isTrue();
    assertThat(appliedFoo.symbol()).isNull();
    assertThat(foo.symbol()).isEqualTo("foo");
    assertThat(foo.is_const()).isTrue();
    assertThat(foo.sort().is_fun()).isTrue();
    assertThat(appliedFoo.get(0)).isEqualTo(foo);
    assertThat(appliedFoo.get(1)).isEqualTo(arg1);
    assertThat(appliedFoo.get(2)).isEqualTo(arg2);
    assertThat(appliedFoo.get(0).children()).isEmpty();
    assertThat(appliedFoo.kind()).isEqualTo(Kind.APPLY);
    assertThat(foo.kind()).isEqualTo(Kind.CONSTANT);

    Term add = termManager.mk_term(Kind.FP_ADD, rm, two, one);
    Term eq = termManager.mk_term(Kind.EQUAL, add, a);
    Term neg = termManager.mk_term(Kind.NOT, eq);

    // The type of add is fp (a bv add would be bv)
    assertThat(add.sort().is_fp()).isTrue();
    // eq is bool
    assertThat(eq.sort().is_bool()).isTrue();
    // neg is also bool
    assertThat(neg.sort().is_bool()).isTrue();
    assertThat(neg.sort().is_fun()).isFalse();

    // Non-UF functions consist of a KIND and arguments.
    // You can get the KIND w bitwuzla_term_get_kind() and the arguments in the correct order w
    // bitwuzla_term_get_children()
    assertThat(appliedFoo.sort().is_fun()).isFalse();
    assertThat(add.sort().is_fun()).isFalse();
    assertThat(eq.sort().is_fun()).isFalse();
    assertThat(neg.sort().is_fun()).isFalse();

    assertThat(rm.sort().is_rm()).isTrue();

    Sort aSort = a.sort();
    assertThat(aSort.is_bv()).isFalse();
    assertThat(aSort.is_fp()).isTrue();
    assertThat(aSort.is_fun()).isFalse();
    assertThat(aSort.is_rm()).isFalse();
    assertThat(aSort.is_bool()).isFalse();
    assertThat(aSort.is_array()).isFalse();

    assertThat(a.is_const()).isTrue();
    assertThat(a.is_variable()).isFalse();
    assertThat(a.is_value()).isFalse();
    assertThat(a.kind()).isEqualTo(Kind.CONSTANT);

    assertThat(a.toString()).isEqualTo("a");

    Sort oneSort = one.sort();
    assertThat(one.kind()).isEqualTo(Kind.VALUE);
    assertThat(one.kind()).isNotEqualTo(Kind.VARIABLE);
    assertThat(one.kind()).isNotEqualTo(Kind.CONSTANT);
    assertThat(oneSort.is_bv()).isFalse();
    assertThat(oneSort.is_fp()).isTrue();
    assertThat(one.is_const()).isFalse();
    assertThat(oneSort.is_fp()).isTrue();
    assertThat(one.is_variable()).isFalse();
    assertThat(oneSort.is_fun()).isFalse();
    assertThat(oneSort.is_rm()).isFalse();
    assertThat(oneSort.is_bool()).isFalse();
    assertThat(oneSort.is_array()).isFalse();

    assertThat(one.toString()).isEqualTo("(fp #b0 #b01111 #b0000000000)");
  }

  /*
   * This serves as a testbed for indexed terms
   */
  @Test
  public void testExtend() {
    Sort bvSort8 = termManager.mk_bv_sort(8);
    Sort bvSort10 = termManager.mk_bv_sort(10);
    Term x = termManager.mk_const(bvSort8, "x");
    Term y = termManager.mk_const(bvSort10, "y");
    Term xExt = termManager.mk_term(Kind.BV_SIGN_EXTEND, x, 2);
    Term xExtEqY = termManager.mk_term(Kind.EQUAL, xExt, y);
    bitwuzla.assert_formula(xExtEqY);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    assertThat(xExt.num_children()).isEqualTo(1);
    assertThat(xExt.num_indices()).isGreaterThan(0);
    Vector_Int indices = xExt.indices();
    assertThat(indices).hasSize(1);
    assertThat(indices.get(0)).isEqualTo(2);
  }

  @Test
  public void testExists() {
    // EXISTS x, y . (z != 0) AND (x = z AND y = z) implies x = y
    Sort bvSort8 = termManager.mk_bv_sort(8);
    Term x = termManager.mk_const(bvSort8, "x");
    Term y = termManager.mk_const(bvSort8, "y");
    Term z = termManager.mk_const(bvSort8, "z");

    Term xEqZ = termManager.mk_term(Kind.EQUAL, x, z);
    Term yEqZ = termManager.mk_term(Kind.EQUAL, y, z);
    Term xEqY = termManager.mk_term(Kind.EQUAL, x, y);
    Term zNotEq0 =
        termManager.mk_term(
            Kind.NOT, termManager.mk_term(Kind.EQUAL, z, termManager.mk_bv_zero(bvSort8)));
    Term implies =
        termManager.mk_term(Kind.IMPLIES, termManager.mk_term(Kind.AND, xEqZ, yEqZ), xEqY);
    Term formula = termManager.mk_term(Kind.AND, zNotEq0, implies);

    // Substitute the free vars with bound vars
    Term xB = termManager.mk_var(bvSort8, "x");
    Term yB = termManager.mk_var(bvSort8, "y");
    // Substitution does not return a new term, but modifies the existing!
    Map_TermTerm mapping = new Map_TermTerm();
    mapping.put(x, xB);
    mapping.put(y, yB);
    termManager.substitute_term(formula, mapping);
    // Build quantifier
    Term[] argsAndBody = {xB, yB, formula};
    Term ex = termManager.mk_term(Kind.FORALL, new Vector_Term(argsAndBody), new Vector_Int());

    // Check SAT
    bitwuzla.assert_formula(ex);
    Result res = bitwuzla.check_sat();
    assertThat(res).isEqualTo(Result.SAT);

    // Get model values and compare
    String xString = x.toString();
    assertThat(xString).isEqualTo("x");
    String xValue = bitwuzla.get_value(x).toString();
    String yString = y.toString();
    assertThat(yString).isEqualTo("y");
    String yValue = bitwuzla.get_value(y).toString();
    String zString = z.toString();
    assertThat(zString).isEqualTo("z");
    String zValue = bitwuzla.get_value(z).toString();
    assertThat(xValue).isEqualTo(yValue);
    assertThat(zValue).isEqualTo(xValue);
    assertThat(zValue).doesNotContain("00000000");
  }

  private static final String SMT2DUMP =
      "(declare-fun a () Bool)\n"
          + "(declare-fun b () Bool)\n"
          + "(declare-fun d () Bool)\n"
          + "(declare-fun e () Bool)\n"
          + "(define-fun .def_9 () Bool (= a b))\n"
          + "(define-fun .def_10 () Bool (not .def_9))\n"
          + "(define-fun .def_13 () Bool (and .def_10 d))\n"
          + "(define-fun .def_14 () Bool (or e .def_13))\n"
          + "(assert .def_14)";

  private Vector_Term parse(String smt2dump) {
    Parser parser = new Parser(termManager, createOptions());
    parser.parse(smt2dump, true, false);
    return parser.bitwuzla().get_assertions();
  }

  private Term parseVariable(String pName) {
    return parse(String.format("(declare-const %s Bool)(assert %s)", pName, pName)).get(0);
  }

  private String dump(Term pTerm) {
    Bitwuzla prover = new Bitwuzla(termManager, createOptions());
    prover.assert_formula(pTerm);
    return prover.print_formula();
  }

  // Bitwuzla currently REWRITES terms when parsing
  @Ignore
  @Test
  public void parserTest2() {
    Vector_Term assertions = parse(SMT2DUMP);
    bitwuzla.push(1);
    bitwuzla.assert_formula(assertions.get(0));
    String newDump = bitwuzla.print_formula();
    newDump = newDump.replace("(set-logic ALL)", "");
    newDump = newDump.replace("(check-sat)", "");
    newDump = newDump.replace("(exit)", "");
    assertThat(newDump).isEqualTo(SMT2DUMP);
  }

  @Test
  public void parserTest() {
    Sort boolSort = termManager.mk_bool_sort();
    Term x = termManager.mk_const(boolSort, "x");
    Term y = termManager.mk_const(boolSort, "y");
    Term xOrY = termManager.mk_term(Kind.XOR, x, y);
    bitwuzla.push(1);
    bitwuzla.assert_formula(xOrY);

    // dump formulas in SMTLIB2 format
    String dump = bitwuzla.print_formula();
    bitwuzla.pop(1);

    // parse the dumped formulas
    Vector_Term assertions = parse(dump);

    // add the parsed assertion to our stack
    bitwuzla.push(1);
    assertThat(assertions).hasSize(1);
    bitwuzla.assert_formula(assertions.get(0));

    // the output of print_formula should stay the same
    String newDump = bitwuzla.print_formula();
    assertThat(newDump).isEqualTo(dump);
  }

  @SuppressWarnings("CheckReturnValue")
  @Test(expected = IllegalArgumentException.class)
  public void parserFailTest() {
    // valid
    String input = "(declare-const a Bool)(declare-const b Bool)(assert (or a b))";
    Vector_Term assertions = parse(input);
    assertThat(assertions).isNotEmpty();
    // invalid/fails
    String badInput = "(declare-const a Bool)(assert (or a b))";
    parse(badInput);
  }

  @Test
  public void noVariableCacheTest() {
    // Bitwuzla allows us to create the same variable twice
    // Here t1 and t2 are treated as different variables, even though they share a name and have
    // the same sort
    Sort sortBool = termManager.mk_bool_sort();
    Term t1 = termManager.mk_const(sortBool, "var");
    Term t2 = termManager.mk_const(sortBool, "var");

    bitwuzla.assert_formula(termManager.mk_term(Kind.NOT, termManager.mk_term(Kind.IFF, t1, t2)));
    assertThat(bitwuzla.check_sat()).isEqualTo(Result.SAT);

    boolean r1 = bitwuzla.get_value(t1).is_true();
    boolean r2 = bitwuzla.get_value(t2).is_true();
    assertThat(r1).isNotEqualTo(r2);
  }

  @Test
  public void quotedSymbolTest() {
    // When parsing formulas Bitwuzla will preserve any || quotes in the name.
    // The parser still makes sure that "var" and "|var|" can't be declared in the same file as
    // both names are identical accoridng to the SMTLIB standard
    assertThat(parseVariable("var").symbol()).isEqualTo("var");
    assertThat(parseVariable("|var|").symbol()).isEqualTo("|var|");
  }

  @Test
  @Ignore
  public void illegalSmtlibTest() {
    // Bitwuzla does not put reserved variable names in quotes while printing and will produce
    // illegal output
    Sort sortBool = termManager.mk_bool_sort();
    Term t1 = termManager.mk_const(sortBool, "exit");

    String expected =
        "(set-logic ALL)\n"
            + "(declare-const |exit| Bool)\n"
            + "(assert |exit|)\n"
            + "(check-sat)\n"
            + "(exit)\n";
    assertThat(dump(t1)).isEqualTo(expected);
  }

  @Test
  @Ignore
  public void illegalSmtlibParseTest() {
    // Even with the quotes added Bitwuzla will not parse keywords
    String input =
        "(set-logic ALL)\n"
            + "(declare-const |exit| Bool)\n"
            + "(assert |exit|)\n"
            + "(check-sat)\n"
            + "(exit)\n";
    assertThat(parse(input).get(0).symbol()).isEqualTo("|exit|");
  }

  @Test
  @Ignore
  public void illegalSmtlibNumberTest() {
    // Bitwuzla also won't quote variable names that are numbers (like "1" or "1.4") while printing
    Sort sortBool = termManager.mk_bool_sort();
    Term t1 = termManager.mk_const(sortBool, "1");

    String expected =
        "(set-logic ALL)\n"
            + "(declare-const |1| Bool)\n"
            + "(assert |1|)\n"
            + "(check-sat)\n"
            + "(exit)\n";
    assertThat(dump(t1)).isEqualTo(expected);
  }

  @Test
  @Ignore
  public void illegalSmtlibParseNumberTest() {
    // Even though it can read back input with quoted numbers as variable names
    String input =
        "(set-logic ALL)\n"
            + "(declare-const |1| Bool)\n"
            + "(assert |1|)\n"
            + "(check-sat)\n"
            + "(exit)\n";
    assertThat(parse(input).get(0).symbol()).isEqualTo("|1|");
  }
}
