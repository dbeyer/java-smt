// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.Iterables;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class CVC5BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Term, Sort, TermManager, Term> {

  private final TermManager termManager;
  private final Term pTrue;
  private final Term pFalse;

  protected CVC5BooleanFormulaManager(CVC5FormulaCreator pCreator) {
    super(pCreator);
    termManager = pCreator.getEnv();
    pTrue = termManager.mkBoolean(true);
    pFalse = termManager.mkBoolean(false);
  }

  @Override
  @VisibleForTesting
  public Term makeVariableImpl(String pVar) {
    return formulaCreator.makeVariable(getFormulaCreator().getBoolType(), pVar);
  }

  @Override
  protected Term makeBooleanImpl(boolean pValue) {
    return pValue ? pTrue : pFalse;
  }

  @Override
  protected Term not(Term pParam1) {
    try {
      if (isTrue(pParam1)) {
        return pFalse;
      } else if (isFalse(pParam1)) {
        return pTrue;
      } else if (pParam1.getKind() == Kind.NOT) {
        return pParam1.getChild(0);
      }
    } catch (CVC5ApiException e) {
      throw new IllegalArgumentException("Failure when negating the term '" + pParam1 + "'.", e);
    }
    return termManager.mkTerm(Kind.NOT, pParam1);
  }

  @Override
  protected Term and(Term pParam1, Term pParam2) {
    if (isTrue(pParam1)) {
      return pParam2;
    } else if (isTrue(pParam2)) {
      return pParam1;
    } else if (isFalse(pParam1)) {
      return pFalse;
    } else if (isFalse(pParam2)) {
      return pFalse;
    } else if (pParam1.equals(pParam2)) {
      return pParam1;
    }
    return termManager.mkTerm(Kind.AND, pParam1, pParam2);
  }

  @Override
  protected Term andImpl(Collection<Term> pParams) {
    // CVC5 does not do any simplifications,
    // so we filter "true", short-circuit on "false", and filter out (simple) redundancies.
    final Set<Term> operands = new LinkedHashSet<>();
    for (final Term operand : pParams) {
      if (isFalse(operand)) {
        return pFalse;
      }
      if (!isTrue(operand)) {
        operands.add(operand);
      }
    }
    switch (operands.size()) {
      case 0:
        return pTrue;
      case 1:
        return Iterables.getOnlyElement(operands);
      default:
        return termManager.mkTerm(Kind.AND, operands.toArray(new Term[0]));
    }
  }

  @Override
  protected Term or(Term pParam1, Term pParam2) {
    if (isTrue(pParam1)) {
      return pTrue;
    } else if (isTrue(pParam2)) {
      return pTrue;
    } else if (isFalse(pParam1)) {
      return pParam2;
    } else if (isFalse(pParam2)) {
      return pParam1;
    } else if (pParam1.equals(pParam2)) {
      return pParam1;
    }
    return termManager.mkTerm(Kind.OR, pParam1, pParam2);
  }

  @Override
  protected Term orImpl(Collection<Term> pParams) {
    // CVC5 does not do any simplifications,
    // so we filter "true", short-circuit on "false", and filter out (simple) redundancies.
    final Set<Term> operands = new LinkedHashSet<>();
    for (final Term operand : pParams) {
      if (isTrue(operand)) {
        return pTrue;
      }
      if (!isFalse(operand)) {
        operands.add(operand);
      }
    }
    switch (operands.size()) {
      case 0:
        return pFalse;
      case 1:
        return Iterables.getOnlyElement(operands);
      default:
        return termManager.mkTerm(Kind.OR, operands.toArray(new Term[0]));
    }
  }

  @Override
  protected Term xor(Term pParam1, Term pParam2) {
    return termManager.mkTerm(Kind.XOR, pParam1, pParam2);
  }

  @Override
  protected Term equivalence(Term pBits1, Term pBits2) {
    return termManager.mkTerm(Kind.EQUAL, pBits1, pBits2);
  }

  @Override
  protected Term implication(Term bits1, Term bits2) {
    return termManager.mkTerm(Kind.IMPLIES, bits1, bits2);
  }

  @Override
  protected boolean isTrue(Term pBits) {
    return pBits.isBooleanValue() && pBits.getBooleanValue();
  }

  @Override
  protected boolean isFalse(Term pBits) {
    return pBits.isBooleanValue() && !pBits.getBooleanValue();
  }

  @Override
  protected Term ifThenElse(Term pCond, Term pF1, Term pF2) {
    if (isTrue(pCond)) {
      return pF1;
    } else if (isFalse(pCond)) {
      return pF2;
    } else if (pF1.equals(pF2)) {
      return pF1;
    } else if (isTrue(pF1) && isFalse(pF2)) {
      return pCond;
    } else if (isFalse(pF1) && isTrue(pF2)) {
      return not(pCond);
    }
    return termManager.mkTerm(Kind.ITE, pCond, pF1, pF2);
  }
}
