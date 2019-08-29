/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_check_sat;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_declare_function;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_env;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_bv_type_size;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type_exp_width;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_fp_type_mant_width;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_integer_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_bv_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_bv_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_constant;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_equal;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_int_modular_congruence;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_pop_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_push_backtrack_point;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_repr;

import org.junit.After;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.java_smt.api.SolverException;

@Ignore("prevent this abstract class being executed as testcase by ant")
public abstract class Mathsat5AbstractNativeApiTest {

  protected long env;

  @After
  public void freeEnvironment() {
    msat_destroy_env(env);
  }

  @Test
  public void bvSize() {
    long number = msat_make_bv_number(env, "42", 32, 10);
    long type = msat_term_get_type(number);

    assertTrue(msat_is_bv_type(env, type));
    assertEquals(32, msat_get_bv_type_size(env, type));

    long funcDecl = msat_declare_function(env, "testVar", type);
    long var = msat_make_constant(env, funcDecl);
    type = msat_term_get_type(var);

    assertTrue(msat_is_bv_type(env, type));
    assertEquals(32, msat_get_bv_type_size(env, type));
  }

  @Test
  public void fpExpWidth() {
    long type = msat_get_fp_type(env, 8, 23);
    assertEquals(8, msat_get_fp_type_exp_width(env, type));
  }

  @Test
  public void fpMantWidth() {
    long type = msat_get_fp_type(env, 8, 23);
    assertEquals(23, msat_get_fp_type_mant_width(env, type));
  }

  @Test(expected = IllegalArgumentException.class)
  @SuppressWarnings("CheckReturnValue")
  public void fpExpWidthIllegal() {
    long type = msat_get_integer_type(env);
    msat_get_fp_type_exp_width(env, type);
  }

  @Test
  public void modularCongruence()
      throws InterruptedException, IllegalStateException, SolverException {
    long type = msat_get_integer_type(env);

    long v1 = msat_declare_function(env, "v1", type);
    long t1 = msat_make_constant(env, v1);
    long v2 = msat_declare_function(env, "v2", type);
    long t2 = msat_make_constant(env, v2);

    long t = msat_make_int_modular_congruence(env, "42", t1, t2);

    assertEquals("(`int_mod_congr_42` (`+_int` v1 (`*_int` -1 v2)) 0)", msat_term_repr(t));

    msat_assert_formula(env, t);

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, t1, msat_make_number(env, "3")));
    msat_assert_formula(env, msat_make_equal(env, t2, msat_make_number(env, "45")));
    assertTrue(msat_check_sat(env)); // 3 == 45 mod 42
    msat_pop_backtrack_point(env);

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, t1, msat_make_number(env, "45")));
    msat_assert_formula(env, msat_make_equal(env, t2, msat_make_number(env, "45")));
    assertTrue(msat_check_sat(env)); // 45 == 45 mod 42 according to Mathsat
    msat_pop_backtrack_point(env);

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, t1, msat_make_number(env, "87")));
    msat_assert_formula(env, msat_make_equal(env, t2, msat_make_number(env, "45")));
    assertTrue(msat_check_sat(env)); // 87 == 45 mod 42 according to Mathsat
    msat_pop_backtrack_point(env);

    msat_push_backtrack_point(env);
    msat_assert_formula(env, msat_make_equal(env, t1, msat_make_number(env, "4")));
    msat_assert_formula(env, msat_make_equal(env, t2, msat_make_number(env, "45")));
    assertFalse(msat_check_sat(env)); // 4 != 45 mod 42
    msat_pop_backtrack_point(env);
  }
}
