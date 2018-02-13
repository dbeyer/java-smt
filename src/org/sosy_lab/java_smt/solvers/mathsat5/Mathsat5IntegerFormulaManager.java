/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

import static com.google.common.base.Verify.verify;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_int_modular_congruence;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_times;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_repr;

import com.google.common.base.Splitter;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class Mathsat5IntegerFormulaManager
    extends Mathsat5NumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  Mathsat5IntegerFormulaManager(Mathsat5FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected long getNumeralType() {
    return getFormulaCreator().getIntegerType();
  }

  @Override
  protected Long makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  public Long divide(Long pNumber1, Long pNumber2) {
    if (!isNumeral(pNumber2)) {
      return super.divide(pNumber1, pNumber2);
    }
    long mathsatEnv = getFormulaCreator().getEnv();
    long t1 = pNumber1;
    long t2 = pNumber2;

    // invert t2 and multiply with it
    String n = msat_term_repr(t2);
    if (n.startsWith("(")) {
      n = n.substring(1, n.length() - 1);
    }
    List<String> frac = Splitter.on('/').splitToList(n);
    if (frac.size() == 1) {
      // cannot multiply with term 1/n because the result will have type rat instead of int
      return super.divide(pNumber1, pNumber2);
    } else {
      verify(frac.size() == 2);
      n = frac.get(1) + "/" + frac.get(0);
    }
    t2 = msat_make_number(mathsatEnv, n);
    return msat_make_times(mathsatEnv, t2, t1);
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, BigInteger pModulo) {
    return modularCongruence0(pNumber1, pNumber2, pModulo.toString());
  }

  @Override
  protected Long modularCongruence(Long pNumber1, Long pNumber2, long pModulo) {
    return modularCongruence0(pNumber1, pNumber2, Long.toString(pModulo));
  }

  protected Long modularCongruence0(Long pNumber1, Long pNumber2, String pModulo) {
    return msat_make_int_modular_congruence(
        getFormulaCreator().getEnv(), pModulo, pNumber1, pNumber2);
  }
}
