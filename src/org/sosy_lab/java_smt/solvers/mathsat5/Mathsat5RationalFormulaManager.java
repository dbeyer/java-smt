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
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_number;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_times;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_repr;

import com.google.common.base.Splitter;
import java.math.BigDecimal;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

class Mathsat5RationalFormulaManager
    extends Mathsat5NumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  Mathsat5RationalFormulaManager(Mathsat5FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected long getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  protected Long makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
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
      n = "1/" + n;
    } else {
      verify(frac.size() == 2);
      n = frac.get(1) + "/" + frac.get(0);
    }
    t2 = msat_make_number(mathsatEnv, n);
    return msat_make_times(mathsatEnv, t2, t1);
  }
}
