// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.errorprone.annotations.Immutable;
import java.util.List;

/**
 * Function declaration, for both UFs and built-in functions (theory and boolean).
 *
 * <p>Can be instantiated using {@link FormulaManager#makeApplication}
 */
@Immutable
public interface FunctionDeclaration<E extends Formula> {

  /** @return Type of the function (LT / GT / UF / etc...). */
  FunctionDeclarationKind getKind();

  /** @return Name of the function (UF name / "LT" / etc...). */
  String getName();

  /** @return Sort of the function output. */
  FormulaType<E> getType();

  /** @return Sorts of the arguments. */
  List<FormulaType<?>> getArgumentTypes();
}
