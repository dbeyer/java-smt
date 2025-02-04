// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator.SymbolViewVisitor;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements BooleanFormulaManager {

  private @Nullable BooleanFormula trueFormula = null;
  private @Nullable BooleanFormula falseFormula = null;

  protected AbstractBooleanFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator) {
    super(pCreator);
  }

  private BooleanFormula wrap(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateBoolean(formulaInfo);
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    return wrap(makeVariableImpl(FormulaCreator.escapeName(pVar)));
  }

  protected abstract TFormulaInfo makeVariableImpl(String pVar);

  @Override
  public BooleanFormula makeTrue() {
    if (trueFormula == null) {
      trueFormula = wrap(makeBooleanImpl(true));
    }
    return trueFormula;
  }

  @Override
  public BooleanFormula makeFalse() {
    if (falseFormula == null) {
      falseFormula = wrap(makeBooleanImpl(false));
    }
    return falseFormula;
  }

  protected abstract TFormulaInfo makeBooleanImpl(boolean value);

  @Override
  public BooleanFormula not(BooleanFormula pBits) {
    TFormulaInfo param1 = extractInfo(pBits);
    return wrap(not(param1));
  }

  protected abstract TFormulaInfo not(TFormulaInfo pParam1);

  @Override
  public BooleanFormula and(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(and(param1, param2));
  }

  protected abstract TFormulaInfo and(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula and(Collection<BooleanFormula> pBits) {
    switch (pBits.size()) {
      case 0:
        return makeTrue();
      case 1:
        return pBits.iterator().next();
      case 2:
        Iterator<BooleanFormula> it = pBits.iterator();
        return and(it.next(), it.next());
      default:
        return wrap(andImpl(Collections2.transform(pBits, this::extractInfo)));
    }
  }

  @Override
  public BooleanFormula and(BooleanFormula... pBits) {
    return and(Arrays.asList(pBits));
  }

  /**
   * Create an n-ary conjunction. The default implementation delegates to {@link #and(Object,
   * Object)} and assumes that all simplifications are done by that method. This method can be
   * overridden, in which case it should filter out irrelevant operands.
   *
   * @param pParams A collection of at least 3 operands.
   * @return A term that is equivalent to a conjunction of pParams.
   */
  protected TFormulaInfo andImpl(Collection<TFormulaInfo> pParams) {
    TFormulaInfo result = makeBooleanImpl(true);
    for (TFormulaInfo formula : ImmutableSet.copyOf(pParams)) {
      if (isFalse(formula)) {
        return formula;
      }
      result = and(result, formula);
    }
    return result;
  }

  @Override
  public final Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  public BooleanFormula or(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(or(param1, param2));
  }

  @Override
  public BooleanFormula or(BooleanFormula... pBits) {
    return or(Arrays.asList(pBits));
  }

  protected abstract TFormulaInfo or(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula xor(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(xor(param1, param2));
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> pBits) {
    switch (pBits.size()) {
      case 0:
        return makeFalse();
      case 1:
        return pBits.iterator().next();
      case 2:
        Iterator<BooleanFormula> it = pBits.iterator();
        return or(it.next(), it.next());
      default:
        return wrap(orImpl(Collections2.transform(pBits, this::extractInfo)));
    }
  }

  /**
   * Create an n-ary disjunction. The default implementation delegates to {@link #or(Object,
   * Object)} and assumes that all simplifications are done by that method. This method can be
   * overridden, in which case it should filter out irrelevant operands.
   *
   * @param pParams A collection of at least 3 operands.
   * @return A term that is equivalent to a disjunction of pParams.
   */
  protected TFormulaInfo orImpl(Collection<TFormulaInfo> pParams) {
    TFormulaInfo result = makeBooleanImpl(false);
    for (TFormulaInfo formula : ImmutableSet.copyOf(pParams)) {
      if (isTrue(formula)) {
        return formula;
      }
      result = or(result, formula);
    }
    return result;
  }

  @Override
  public final Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
  }

  protected abstract TFormulaInfo xor(TFormulaInfo pParam1, TFormulaInfo pParam2);

  /**
   * Creates a formula representing an equivalence of the two arguments.
   *
   * @param pBits1 a Formula
   * @param pBits2 a Formula
   * @return {@code f1 <-> f2}
   */
  @Override
  public final BooleanFormula equivalence(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);
    return wrap(equivalence(param1, param2));
  }

  protected abstract TFormulaInfo equivalence(TFormulaInfo bits1, TFormulaInfo bits2);

  @Override
  public final BooleanFormula implication(BooleanFormula pBits1, BooleanFormula pBits2) {
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);
    return wrap(implication(param1, param2));
  }

  protected TFormulaInfo implication(TFormulaInfo bits1, TFormulaInfo bits2) {
    return or(not(bits1), bits2);
  }

  @Override
  public final boolean isTrue(BooleanFormula pBits) {
    return isTrue(extractInfo(pBits));
  }

  protected abstract boolean isTrue(TFormulaInfo bits);

  @Override
  public final boolean isFalse(BooleanFormula pBits) {
    return isFalse(extractInfo(pBits));
  }

  protected abstract boolean isFalse(TFormulaInfo bits);

  /**
   * Creates a formula representing "IF cond THEN f1 ELSE f2".
   *
   * @param pBits a Formula
   * @param f1 a Formula
   * @param f2 a Formula
   * @return (IF cond THEN f1 ELSE f2)
   */
  @Override
  public final <T extends Formula> T ifThenElse(BooleanFormula pBits, T f1, T f2) {
    FormulaType<T> t1 = getFormulaCreator().getFormulaType(f1);
    FormulaType<T> t2 = getFormulaCreator().getFormulaType(f2);
    checkArgument(
        t1.equals(t2),
        "Cannot create if-then-else formula with branches of different types: "
            + "%s is of type %s; %s is of type %s",
        f1,
        t1,
        f2,
        t2);
    TFormulaInfo result = ifThenElse(extractInfo(pBits), extractInfo(f1), extractInfo(f2));
    return getFormulaCreator().encapsulate(t1, result);
  }

  protected abstract TFormulaInfo ifThenElse(TFormulaInfo cond, TFormulaInfo f1, TFormulaInfo f2);

  @Override
  public <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> visitor) {
    return formulaCreator.visit(
        pFormula, new SymbolViewVisitor<>(new DelegatingFormulaVisitor<>(visitor)));
  }

  @Override
  public void visitRecursively(
      BooleanFormula pF, BooleanFormulaVisitor<TraversalProcess> pFormulaVisitor) {
    formulaCreator.visitRecursively(
        new SymbolViewVisitor<>(new DelegatingFormulaVisitor<>(pFormulaVisitor)),
        pF,
        p -> p instanceof BooleanFormula);
  }

  @Override
  public BooleanFormula transformRecursively(
      BooleanFormula f, BooleanFormulaTransformationVisitor pVisitor) {
    return formulaCreator.transformRecursively(
        new SymbolViewVisitor<>(new DelegatingFormulaVisitor<>(pVisitor)),
        f,
        p -> p instanceof BooleanFormula);
  }

  private class DelegatingFormulaVisitor<R> implements FormulaVisitor<R> {
    private final BooleanFormulaVisitor<R> delegate;

    DelegatingFormulaVisitor(BooleanFormulaVisitor<R> pDelegate) {
      delegate = pDelegate;
    }

    @Override
    public R visitFreeVariable(Formula f, String name) {

      // Only boolean formulas can appear here.
      assert f instanceof BooleanFormula;
      BooleanFormula casted = (BooleanFormula) f;
      return delegate.visitAtom(
          casted,
          FunctionDeclarationImpl.of(
              name,
              FunctionDeclarationKind.VAR,
              ImmutableList.of(),
              FormulaType.BooleanType,
              formulaCreator.getBooleanVarDeclaration(casted)));
    }

    @Override
    public R visitBoundVariable(Formula f, int deBruijnIdx) {

      // Only boolean formulas can appear here.
      assert f instanceof BooleanFormula;
      return delegate.visitBoundVar((BooleanFormula) f, deBruijnIdx);
    }

    @Override
    public R visitConstant(Formula f, Object value) {
      checkState(value instanceof Boolean);
      return delegate.visitConstant((boolean) value);
    }

    private List<BooleanFormula> getBoolArgs(List<Formula> args) {
      checkState(Iterables.all(args, arg -> arg instanceof BooleanFormula));
      @SuppressWarnings("unchecked")
      List<BooleanFormula> out = (List<BooleanFormula>) (List<?>) args;
      return out;
    }

    @Override
    public R visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      switch (functionDeclaration.getKind()) {
        case AND:
          R out = delegate.visitAnd(getBoolArgs(args));
          return out;
        case NOT:
          checkState(args.size() == 1);
          Formula arg = args.get(0);

          checkArgument(arg instanceof BooleanFormula);
          return delegate.visitNot((BooleanFormula) arg);
        case OR:
          R out2 = delegate.visitOr(getBoolArgs(args));
          return out2;
        case IFF:
          checkState(args.size() == 2);
          Formula a = args.get(0);
          Formula b = args.get(1);
          checkState(a instanceof BooleanFormula && b instanceof BooleanFormula);
          R out3 = delegate.visitEquivalence((BooleanFormula) a, (BooleanFormula) b);
          return out3;
        case EQ:
          if (args.size() == 2
              && args.get(0) instanceof BooleanFormula
              && args.get(1) instanceof BooleanFormula) {
            return delegate.visitEquivalence(
                (BooleanFormula) args.get(0), (BooleanFormula) args.get(1));
          } else {
            return delegate.visitAtom(
                (BooleanFormula) f, toBooleanDeclaration(functionDeclaration));
          }
        case ITE:
          checkArgument(args.size() == 3);
          Formula ifC = args.get(0);
          Formula then = args.get(1);
          Formula elseC = args.get(2);
          checkState(
              ifC instanceof BooleanFormula
                  && then instanceof BooleanFormula
                  && elseC instanceof BooleanFormula);
          return delegate.visitIfThenElse(
              (BooleanFormula) ifC, (BooleanFormula) then, (BooleanFormula) elseC);
        case XOR:
          checkArgument(args.size() == 2);
          Formula a1 = args.get(0);
          Formula a2 = args.get(1);
          checkState(a1 instanceof BooleanFormula && a2 instanceof BooleanFormula);
          return delegate.visitXor((BooleanFormula) a1, (BooleanFormula) a2);
        case IMPLIES:
          checkArgument(args.size() == 2);
          Formula b1 = args.get(0);
          Formula b2 = args.get(1);
          checkArgument(b1 instanceof BooleanFormula && b2 instanceof BooleanFormula);
          return delegate.visitImplication((BooleanFormula) b1, (BooleanFormula) b2);
        default:
          return delegate.visitAtom((BooleanFormula) f, toBooleanDeclaration(functionDeclaration));
      }
    }

    @Override
    public R visitQuantifier(
        BooleanFormula f,
        Quantifier quantifier,
        List<Formula> boundVariables,
        BooleanFormula body) {
      return delegate.visitQuantifier(quantifier, f, boundVariables, body);
    }

    @SuppressWarnings("unchecked")
    private FunctionDeclaration<BooleanFormula> toBooleanDeclaration(FunctionDeclaration<?> decl) {
      return (FunctionDeclaration<BooleanFormula>) decl;
    }
  }

  @Override
  public Set<BooleanFormula> toConjunctionArgs(BooleanFormula f, boolean flatten) {
    if (flatten) {
      return asFuncRecursive(f, conjunctionFinder);
    }
    return formulaCreator.visit(f, conjunctionFinder);
  }

  @Override
  public Set<BooleanFormula> toDisjunctionArgs(BooleanFormula f, boolean flatten) {
    if (flatten) {
      return asFuncRecursive(f, disjunctionFinder);
    }
    return formulaCreator.visit(f, disjunctionFinder);
  }

  /** Optimized non-recursive flattening implementation. */
  private Set<BooleanFormula> asFuncRecursive(
      BooleanFormula f, FormulaVisitor<Set<BooleanFormula>> visitor) {
    ImmutableSet.Builder<BooleanFormula> output = ImmutableSet.builder();
    Deque<BooleanFormula> toProcess = new ArrayDeque<>();
    Map<BooleanFormula, Set<BooleanFormula>> cache = new HashMap<>();
    toProcess.add(f);

    while (!toProcess.isEmpty()) {
      BooleanFormula s = toProcess.pop();
      Set<BooleanFormula> out = cache.computeIfAbsent(s, ss -> formulaCreator.visit(ss, visitor));
      if (out.size() == 1 && s.equals(out.iterator().next())) {
        output.add(s);
      }
      for (BooleanFormula arg : out) {
        if (cache.get(arg) == null) { // Wasn't processed yet.
          toProcess.add(arg);
        }
      }
    }

    return output.build();
  }

  private final FormulaVisitor<Set<BooleanFormula>> conjunctionFinder =
      new DefaultFormulaVisitor<>() {
        @Override
        protected Set<BooleanFormula> visitDefault(Formula f) {
          assert f instanceof BooleanFormula;
          BooleanFormula bf = (BooleanFormula) f;
          if (isTrue(bf)) {
            return ImmutableSet.of();
          }
          return ImmutableSet.of((BooleanFormula) f);
        }

        @SuppressWarnings("unchecked")
        @Override
        public Set<BooleanFormula> visitFunction(
            Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
          if (functionDeclaration.getKind() == FunctionDeclarationKind.AND) {
            return ImmutableSet.copyOf((List<BooleanFormula>) (List<?>) args);
          }
          return visitDefault(f);
        }
      };

  /**
   * Optimized, but ugly, implementation of argument extraction. Avoids extra visitor instantiation.
   */
  private final FormulaVisitor<Set<BooleanFormula>> disjunctionFinder =
      new DefaultFormulaVisitor<>() {
        @Override
        protected Set<BooleanFormula> visitDefault(Formula f) {
          assert f instanceof BooleanFormula;
          BooleanFormula bf = (BooleanFormula) f;
          if (isFalse(bf)) {
            return ImmutableSet.of();
          }
          return ImmutableSet.of((BooleanFormula) f);
        }

        @SuppressWarnings("unchecked")
        @Override
        public Set<BooleanFormula> visitFunction(
            Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
          if (functionDeclaration.getKind() == FunctionDeclarationKind.OR) {
            return ImmutableSet.copyOf((List<BooleanFormula>) (List<?>) args);
          }
          return visitDefault(f);
        }
      };
}
