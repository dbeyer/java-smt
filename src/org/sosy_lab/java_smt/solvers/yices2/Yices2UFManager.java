// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR GPL-3.0-or-later

package org.sosy_lab.java_smt.solvers.yices2;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

class Yices2UFManager extends AbstractUFManager<Integer, Integer, Integer, Long> {

  protected Yices2UFManager(Yices2FormulaCreator pCreator) {
    super(pCreator);
  }
}
