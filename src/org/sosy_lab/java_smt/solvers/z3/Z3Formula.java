// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.errorprone.annotations.Immutable;
import com.microsoft.z3.Native;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

@Immutable
abstract class Z3Formula implements Formula {

  private final long z3expr;
  private final long z3context;
  private final int hashCache;

  private Z3Formula(long z3context, long z3expr) {
    checkArgument(z3context != 0, "Z3 context is null");
    checkArgument(z3expr != 0, "Z3 formula is null");
    this.z3expr = z3expr;
    this.z3context = z3context;

    Native.incRef(z3context, z3expr);
    this.hashCache = Native.getAstHash(z3context, z3expr);
  }

  @Override
  public final String toString() {
    return Native.astToString(z3context, z3expr);
  }

  @Override
  public final boolean equals(@Nullable Object obj) {
    if (obj == this) {
      return true;
    }
    if (!(obj instanceof Z3Formula)) {
      return false;
    }
    Z3Formula other = (Z3Formula) obj;
    return (z3context == other.z3context) && Native.isEqAst(z3context, z3expr, other.z3expr);
  }

  @Override
  public final int hashCode() {
    return hashCache;
  }

  final long getFormulaInfo() {
    return z3expr;
  }

  @SuppressWarnings("ClassTypeParameterName")
  static final class Z3ArrayFormula<TI extends Formula, TE extends Formula> extends Z3Formula
      implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    Z3ArrayFormula(
        long pZ3context, long pZ3expr, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
      super(pZ3context, pZ3expr);
      indexType = pIndexType;
      elementType = pElementType;
    }

    public FormulaType<TI> getIndexType() {
      return indexType;
    }

    public FormulaType<TE> getElementType() {
      return elementType;
    }
  }

  @Immutable
  static final class Z3BitvectorFormula extends Z3Formula implements BitvectorFormula {

    Z3BitvectorFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3FloatingPointFormula extends Z3Formula implements FloatingPointFormula {

    Z3FloatingPointFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3FloatingPointRoundingModeFormula extends Z3Formula
      implements FloatingPointRoundingModeFormula {

    Z3FloatingPointRoundingModeFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3IntegerFormula extends Z3Formula implements IntegerFormula {

    Z3IntegerFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3RationalFormula extends Z3Formula implements RationalFormula {

    Z3RationalFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }

  @Immutable
  static final class Z3BooleanFormula extends Z3Formula implements BooleanFormula {
    Z3BooleanFormula(long z3context, long z3expr) {
      super(z3context, z3expr);
    }
  }
}
