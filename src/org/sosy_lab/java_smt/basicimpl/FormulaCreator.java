// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.CharMatcher;
import com.google.common.collect.ImmutableBiMap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Predicate;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.RegexFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.ArrayFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.BitvectorFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.BooleanFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.EnumerationFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.FloatingPointFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.FloatingPointRoundingModeFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.IntegerFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.RationalFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.RegexFormulaImpl;
import org.sosy_lab.java_smt.basicimpl.AbstractFormula.StringFormulaImpl;

/**
 * This is a helper class with several methods that are commonly used throughout the basicimpl
 * package and may have solver-specific implementations. Each solver package is expected to provide
 * an instance of this class, with the appropriate methods overwritten. Depending on the solver,
 * some or all non-final methods in this class may need to be overwritten.
 *
 * @param <TFormulaInfo> the solver specific type for formulas.
 * @param <TType> the solver specific type for formula types.
 * @param <TEnv> the solver specific type for the environment/context.
 */
@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
public abstract class FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> {

  private final TType boolType;
  private final @Nullable TType integerType;
  private final @Nullable TType rationalType;
  private final @Nullable TType stringType;
  private final @Nullable TType regexType;
  protected final TEnv environment;

  /**
   * Avoid using escape characters of SMT-LIB2 as part of names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  @VisibleForTesting
  public static final ImmutableList<String> RESERVED =
      ImmutableList.of(
          // Keywords
          "_",
          "!",
          "as",
          "let",
          "exists",
          "forall",
          "match",
          "par",

          // Commands
          "assert",
          "check-sat",
          "check-sat-assuming",
          "declare-const",
          "declare-datatype",
          "declare-datatypes",
          "declare-fun",
          "declare-sort",
          "define-fun",
          "define-fun-rec",
          "define-funs-rec",
          "define-sort",
          "echo",
          "exit",
          "get-assertions",
          "get-assignment",
          "get-info",
          "get-model",
          "get-option",
          "get-proof",
          "get-unsat-assumptions",
          "get-unsat-core",
          "get-value",
          "pop",
          "push",
          "reset",
          "reset-assertions",
          "set-info",
          "set-logic",
          "set-option",

          // Predefined symbols
          // Arrays
          "select",
          "store",
          "const",

          // Bitvectors
          "concat",
          "extract",
          "zero_extend",
          "sign_extend",
          "rotate_left",
          "rotate_right",
          "bv2int",
          "int2bv",
          "bvadd",
          "bvsub",
          "bvneg",
          "bvmul",
          "bvudiv",
          "bvsdiv",
          "bvurem",
          "bvsrem",
          "bvsmod",
          "bvshl",
          "bvlshr",
          "bvashr",
          "bvor",
          "bvand",
          "bvnot",
          "bvxor",
          "bvule",
          "bvult",
          "bvuge",
          "bvugt",
          "bvsle",
          "bvslt",
          "bvsge",
          "bvsgt",

          // Core
          "true",
          "false",
          "not",
          "=>",
          "and",
          "or",
          "xor",
          "=",
          "distinct",
          "ite",

          // Floats
          "roundNearestTiesToEven RoundingMode",
          "roundNearestTiesToAway",
          "roundTowardPositive",
          "roundTowardNegative",
          "roundTowardZero",
          "RNE",
          "RNA",
          "RTP",
          "RTN",
          "RTZ",
          "fp",
          "+oo",
          "-oo",
          "+zero",
          "-zero",
          "NaN",
          "to_fp",
          "to_fp_unsigned",
          // + any symbol starting with "fp."

          // Integers and Reals
          "-",
          "~",
          "+",
          "*",
          "div",
          "mod",
          "/",
          "abs",
          "<=",
          "<",
          ">=",
          ">",
          "divisible",
          "to_real",
          "to_int",
          "is_int"

          // Strings
          // + any symbol starting with "str."
          // + any symbol starting with "re."
          );

  /**
   * Avoid using escape characters of SMT-LIB2 as part of names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  @VisibleForTesting
  public static final CharMatcher DISALLOWED_CHARACTERS = CharMatcher.anyOf("|\\,");

  /**
   * Mapping of disallowed char to their escaped counterparts.
   *
   * <p>Keep this map in sync with {@link #DISALLOWED_CHARACTERS}. Counterparts can be any unique
   * string. For optimization, we could even use plain chars.
   */
  @VisibleForTesting
  public static final ImmutableBiMap<Character, String> DISALLOWED_CHARACTER_REPLACEMENT =
      ImmutableBiMap.of('|', "pipe", '\\', "backslash", ',', "comma");

  @VisibleForTesting
  public static final char ESCAPE = '$'; // just some allowed symbol, can be any char

  protected FormulaCreator(
      TEnv env,
      TType boolType,
      @Nullable TType pIntegerType,
      @Nullable TType pRationalType,
      @Nullable TType stringType,
      @Nullable TType regexType) {
    this.environment = env;
    this.boolType = boolType;
    this.integerType = pIntegerType;
    this.rationalType = pRationalType;
    this.stringType = stringType;
    this.regexType = regexType;
  }

  public final TEnv getEnv() {
    return environment;
  }

  public final TType getBoolType() {
    return boolType;
  }

  public final TType getIntegerType() {
    if (integerType == null) {
      throw new UnsupportedOperationException("Integer theory is not supported by this solver.");
    }
    return integerType;
  }

  public final TType getRationalType() {
    if (rationalType == null) {
      throw new UnsupportedOperationException("Rational theory is not supported by this solver.");
    }
    return rationalType;
  }

  public abstract TType getBitvectorType(int bitwidth);

  public abstract TType getFloatingPointType(FloatingPointType type);

  public abstract TType getArrayType(TType indexType, TType elementType);

  public final TType getStringType() {
    if (stringType == null) {
      throw new UnsupportedOperationException("String theory is not supported by this solver.");
    }
    return stringType;
  }

  public final TType getRegexType() {
    if (regexType == null) {
      throw new UnsupportedOperationException("String theory is not supported by this solver.");
    }
    return regexType;
  }

  public abstract TFormulaInfo makeVariable(TType type, String varName);

  public BooleanFormula encapsulateBoolean(TFormulaInfo pTerm) {
    checkArgument(
        getFormulaType(pTerm).isBooleanType(),
        "Boolean formula has unexpected type: %s",
        getFormulaType(pTerm));
    return new BooleanFormulaImpl<>(pTerm);
  }

  protected BitvectorFormula encapsulateBitvector(TFormulaInfo pTerm) {
    checkArgument(
        getFormulaType(pTerm).isBitvectorType(),
        "Bitvector formula has unexpected type: %s",
        getFormulaType(pTerm));
    return new BitvectorFormulaImpl<>(pTerm);
  }

  protected FloatingPointFormula encapsulateFloatingPoint(TFormulaInfo pTerm) {
    checkArgument(
        getFormulaType(pTerm).isFloatingPointType(),
        "Floatingpoint formula has unexpected type: %s",
        getFormulaType(pTerm));
    return new FloatingPointFormulaImpl<>(pTerm);
  }

  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      TFormulaInfo pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    checkArgument(
        getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType)),
        "Array formula has unexpected type: %s",
        getFormulaType(pTerm));
    return new ArrayFormulaImpl<>(pTerm, pIndexType, pElementType);
  }

  protected StringFormula encapsulateString(TFormulaInfo pTerm) {
    checkArgument(
        getFormulaType(pTerm).isStringType(),
        "String formula has unexpected type: %s",
        getFormulaType(pTerm));
    return new StringFormulaImpl<>(pTerm);
  }

  protected RegexFormula encapsulateRegex(TFormulaInfo pTerm) {
    checkArgument(
        getFormulaType(pTerm).isRegexType(),
        "Regex formula has unexpected type: %s",
        getFormulaType(pTerm));
    return new RegexFormulaImpl<>(pTerm);
  }

  protected EnumerationFormula encapsulateEnumeration(TFormulaInfo pTerm) {
    checkArgument(
        getFormulaType(pTerm).isEnumerationType(),
        "Enumeration formula has unexpected type: %s",
        getFormulaType(pTerm));
    return new EnumerationFormulaImpl<>(pTerm);
  }

  public Formula encapsulateWithTypeOf(TFormulaInfo pTerm) {
    return encapsulate(getFormulaType(pTerm), pTerm);
  }

  @SuppressWarnings("unchecked")
  public <T extends Formula> T encapsulate(FormulaType<T> pType, TFormulaInfo pTerm) {
    checkArgument(
        pType.equals(getFormulaType(pTerm)),
        "Trying to encapsulate formula %s of type %s as %s",
        pTerm,
        getFormulaType(pTerm),
        pType);
    if (pType.isBooleanType()) {
      return (T) new BooleanFormulaImpl<>(pTerm);
    } else if (pType.isIntegerType()) {
      return (T) new IntegerFormulaImpl<>(pTerm);
    } else if (pType.isRationalType()) {
      return (T) new RationalFormulaImpl<>(pTerm);
    } else if (pType.isStringType()) {
      return (T) new StringFormulaImpl<>(pTerm);
    } else if (pType.isRegexType()) {
      return (T) new RegexFormulaImpl<>(pTerm);
    } else if (pType.isBitvectorType()) {
      return (T) new BitvectorFormulaImpl<>(pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) new FloatingPointFormulaImpl<>(pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T) new FloatingPointRoundingModeFormulaImpl<>(pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrayType = (ArrayFormulaType<?, ?>) pType;
      return (T) encapsulateArray(pTerm, arrayType.getIndexType(), arrayType.getElementType());
    } else if (pType.isEnumerationType()) {
      return (T) new EnumerationFormulaImpl<>(pTerm);
    }
    throw new IllegalArgumentException(
        "Cannot create formulas of type " + pType + " in the Solver!");
  }

  @SuppressWarnings("unchecked")
  protected TFormulaInfo extractInfo(Formula pT) {
    if (pT instanceof AbstractFormula) {
      return ((AbstractFormula<TFormulaInfo>) pT).getFormulaInfo();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  @SuppressWarnings("unchecked")
  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {
    return ((ArrayFormulaImpl<TI, TE, TFormulaInfo>) pArray).getElementType();
  }

  @SuppressWarnings("unchecked")
  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {
    return ((ArrayFormulaImpl<TI, TE, TFormulaInfo>) pArray).getIndexType();
  }

  /** Returns the type of the given Formula. */
  @SuppressWarnings("unchecked")
  protected <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    checkNotNull(formula);
    FormulaType<?> t;
    if (formula instanceof BooleanFormula) {
      t = FormulaType.BooleanType;
    } else if (formula instanceof IntegerFormula) {
      t = FormulaType.IntegerType;
    } else if (formula instanceof RationalFormula) {
      t = FormulaType.RationalType;
    } else if (formula instanceof StringFormula) {
      t = FormulaType.StringType;
    } else if (formula instanceof RegexFormula) {
      t = FormulaType.RegexType;
    } else if (formula instanceof FloatingPointRoundingModeFormula) {
      t = FormulaType.FloatingPointRoundingModeType;
    } else if (formula instanceof ArrayFormula) {
      throw new UnsupportedOperationException(
          "SMT solvers with support for arrays need to overwrite FormulaCreator.getFormulaType()");
    } else if (formula instanceof BitvectorFormula) {
      throw new UnsupportedOperationException(
          "SMT solvers with support for bitvectors "
              + "need to overwrite FormulaCreator.getFormulaType()");
    } else if (formula instanceof EnumerationFormula) {
      throw new UnsupportedOperationException(
          "SMT solvers with support for enumerations need to overwrite FormulaCreator"
              + ".getFormulaType()");
    } else {
      throw new IllegalArgumentException("Formula with unexpected type " + formula.getClass());
    }
    return (FormulaType<T>) t;
  }

  public abstract FormulaType<?> getFormulaType(TFormulaInfo formula);

  static class SymbolViewVisitor<R> implements FormulaVisitor<R> {
    private final FormulaVisitor<R> delegate;

    SymbolViewVisitor(FormulaVisitor<R> pDelegate) {
      delegate = pDelegate;
    }

    @Override
    public R visitFreeVariable(Formula f, String name) {
      return delegate.visitFreeVariable(f, unescapeName(name));
    }

    @Override
    public R visitBoundVariable(Formula f, int deBruijnIdx) {
      return delegate.visitBoundVariable(f, deBruijnIdx);
    }

    @Override
    public R visitConstant(Formula f, Object value) {
      return delegate.visitConstant(f, value);
    }

    @Override
    public R visitQuantifier(
        BooleanFormula f,
        Quantifier quantifier,
        List<Formula> boundVariables,
        BooleanFormula body) {
      return delegate.visitQuantifier(f, quantifier, boundVariables, body);
    }

    @Override
    public R visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      return delegate.visitFunction(
          f,
          args,
          FunctionDeclarationImpl.of(
              unescapeName(functionDeclaration.getName()),
              functionDeclaration.getKind(),
              functionDeclaration.getArgumentTypes(),
              functionDeclaration.getType(),
              ((FunctionDeclarationImpl<?, ?>) functionDeclaration).getSolverDeclaration()));
    }
  }

  /**
   * @see org.sosy_lab.java_smt.api.FormulaManager#visit
   */
  @CanIgnoreReturnValue
  public <R> R visit(Formula input, FormulaVisitor<R> visitor) {
    return visit(visitor, input, extractInfo(input));
  }

  /**
   * @see org.sosy_lab.java_smt.api.FormulaManager#visit
   */
  public abstract <R> R visit(FormulaVisitor<R> visitor, Formula formula, TFormulaInfo f);

  protected List<TFormulaInfo> extractInfo(List<? extends Formula> input) {
    return Lists.transform(input, this::extractInfo);
  }

  /**
   * @see org.sosy_lab.java_smt.api.FormulaManager#visitRecursively
   */
  public void visitRecursively(FormulaVisitor<TraversalProcess> pFormulaVisitor, Formula pF) {
    visitRecursively(pFormulaVisitor, pF, t -> true);
  }

  /**
   * @see org.sosy_lab.java_smt.api.FormulaManager#visitRecursively
   */
  public void visitRecursively(
      FormulaVisitor<TraversalProcess> pFormulaVisitor,
      Formula pF,
      Predicate<Formula> shouldProcess) {
    RecursiveFormulaVisitorImpl recVisitor = new RecursiveFormulaVisitorImpl(pFormulaVisitor);
    recVisitor.addToQueue(pF);
    while (!recVisitor.isQueueEmpty()) {
      Formula tt = recVisitor.pop();
      if (shouldProcess.test(tt)) {
        TraversalProcess process = visit(tt, recVisitor);
        if (process == TraversalProcess.ABORT) {
          return;
        }
      }
    }
  }

  public <T extends Formula> T transformRecursively(
      FormulaVisitor<? extends Formula> pFormulaVisitor, T pF) {
    return transformRecursively(pFormulaVisitor, pF, t -> true);
  }

  public <T extends Formula> T transformRecursively(
      FormulaVisitor<? extends Formula> pFormulaVisitor, T pF, Predicate<Object> shouldProcess) {

    final Deque<Formula> toProcess = new ArrayDeque<>();
    Map<Formula, Formula> pCache = new HashMap<>();
    FormulaTransformationVisitorImpl recVisitor =
        new FormulaTransformationVisitorImpl(pFormulaVisitor, toProcess, pCache);
    toProcess.push(pF);

    // Process the work queue
    while (!toProcess.isEmpty()) {
      Formula tt = toProcess.peek();

      if (pCache.containsKey(tt)) {
        toProcess.pop();
        continue;
      }

      if (shouldProcess.test(tt)) {
        visit(tt, recVisitor);
      } else {
        pCache.put(tt, tt);
      }
    }
    @SuppressWarnings("unchecked")
    T out = (T) pCache.get(pF);
    return out;
  }

  /**
   * Wrapper for {@link #extractVariablesAndUFs(Formula, boolean, BiConsumer)} which unwraps both
   * input and output.
   */
  public Map<String, TFormulaInfo> extractVariablesAndUFs(
      final TFormulaInfo pFormula, final boolean extractUFs) {
    Map<String, TFormulaInfo> found = new LinkedHashMap<>();
    extractVariablesAndUFs(
        encapsulateWithTypeOf(pFormula), extractUFs, (name, f) -> found.put(name, extractInfo(f)));
    return found;
  }

  /**
   * Wrapper for {@link #extractVariablesAndUFs(Formula, boolean, BiConsumer)} which unwraps both
   * input and output.
   */
  public void extractVariablesAndUFs(
      final TFormulaInfo pFormula,
      final boolean extractUFs,
      final BiConsumer<String, TFormulaInfo> pConsumer) {
    extractVariablesAndUFs(
        encapsulateWithTypeOf(pFormula),
        extractUFs,
        (name, f) -> pConsumer.accept(name, extractInfo(f)));
  }

  /** Extract all free variables from the formula, optionally including UFs. */
  public void extractVariablesAndUFs(
      final Formula pFormula,
      final boolean extractUF,
      final BiConsumer<String, Formula> pConsumer) {
    visitRecursively(
        new VariableAndUFExtractor(extractUF, pConsumer, ImmutableSet.of(), new LinkedHashSet<>()),
        pFormula);
  }

  private class VariableAndUFExtractor extends DefaultFormulaVisitor<TraversalProcess> {

    private final boolean extractUF;
    private final BiConsumer<String, Formula> consumer;
    private final Set<Formula> boundVariablesInContext;

    /**
     * let's collect all visited symbols here, to avoid redundant visitation of symbols in nested
     * quantified formulas.
     */
    private final Set<Formula> alreadyVisited;

    VariableAndUFExtractor(
        boolean pExtractUF,
        BiConsumer<String, Formula> pConsumer,
        Set<Formula> pBoundVariablesInContext,
        Set<Formula> pAlreadyVisited) {
      extractUF = pExtractUF;
      consumer = pConsumer;
      boundVariablesInContext = pBoundVariablesInContext;
      alreadyVisited = pAlreadyVisited;
    }

    @Override
    protected TraversalProcess visitDefault(Formula f) {
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {

      if (!boundVariablesInContext.contains(f) // TODO can UFs be bounded?
          && functionDeclaration.getKind() == FunctionDeclarationKind.UF
          && extractUF) {
        if (alreadyVisited.add(f)) {
          consumer.accept(functionDeclaration.getName(), f);
        }
      }
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitFreeVariable(Formula f, String name) {

      // If we are inside a quantified formula, bound variables appear to be free,
      // but they are actually bound by the surrounding context.
      if (!boundVariablesInContext.contains(f)) {
        if (alreadyVisited.add(f)) {
          consumer.accept(name, f);
        }
      }
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitQuantifier(
        BooleanFormula f, Quantifier q, List<Formula> boundVariables, BooleanFormula body) {

      // We begin a new nested scope, thus we need a 'really' recursive call and
      // use another visitor-instance which knows the corresponding bound variables.
      visitRecursively(
          new VariableAndUFExtractor(
              extractUF,
              consumer,
              Sets.union(boundVariablesInContext, ImmutableSet.copyOf(boundVariables)),
              alreadyVisited),
          body);

      // Afterwards, we skip the already finished body-formula.
      return TraversalProcess.SKIP;
    }
  }

  @SuppressWarnings("unchecked")
  public final <T extends Formula> T callFunction(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {
    checkArgument(
        args.size() >= declaration.getArgumentTypes().size(),
        "function application '%s' requires %s arguments, but received %s arguments",
        declaration,
        declaration.getArgumentTypes().size(),
        args.size());

    for (int i = 0; i < args.size(); i++) {
      // For chainable functions like EQ, DISTINCT, ADD, LESS, LESS_EQUAL, ..., with a variable
      // number of arguments, we repeat the last argument-type several times.
      int index = Math.min(i, declaration.getArgumentTypes().size() - 1);
      checkArgument(
          isCompatible(getFormulaType(args.get(i)), declaration.getArgumentTypes().get(index)),
          "function application '%s' requires argument types %s, but received argument types %s",
          declaration,
          declaration.getArgumentTypes(),
          Lists.transform(args, this::getFormulaType));
    }

    return encapsulate(
        declaration.getType(),
        callFunctionImpl(
            ((FunctionDeclarationImpl<T, TFuncDecl>) declaration).getSolverDeclaration(),
            extractInfo(args)));
  }

  /**
   * This function checks whether the used type of the function argument is compatible with the
   * declared type in the function declaration.
   *
   * <p>Identical types are always compatible, a subtype like INT to supertype RATIONAL is also
   * compatible. A solver-specific wrapper can override this method if it does an explicit
   * transformation between (some) types, e.g., from BV to BOOLEAN or from BOOLEAN to INT.
   */
  protected boolean isCompatible(FormulaType<?> usedType, FormulaType<?> declaredType) {
    // INT is a subtype of RATIONAL
    if (usedType.isIntegerType() && declaredType.isRationalType()) {
      return true;
    }

    return usedType.equals(declaredType);
  }

  public abstract TFormulaInfo callFunctionImpl(TFuncDecl declaration, List<TFormulaInfo> args);

  public abstract TFuncDecl declareUFImpl(String pName, TType pReturnType, List<TType> pArgTypes);

  public TFuncDecl getBooleanVarDeclaration(BooleanFormula var) {
    return getBooleanVarDeclarationImpl(extractInfo(var));
  }

  protected abstract TFuncDecl getBooleanVarDeclarationImpl(TFormulaInfo pTFormulaInfo);

  /**
   * Convert the formula into a Java object as far as possible, i.e., try to match a primitive or
   * simple type like Boolean, BigInteger, Rational, or String.
   *
   * <p>If the formula is not a simple constant expression, we simply return <code>null</code>.
   *
   * @param pF the formula to be converted.
   */
  public Object convertValue(TFormulaInfo pF) {
    throw new UnsupportedOperationException(
        "This SMT solver needs a second term to determine a correct type. "
            + "Please use the other method 'convertValue(formula, formula)'.");
  }

  /**
   * Convert the formula into a Java object as far as possible, i.e., try to match a primitive or
   * simple type.
   *
   * @param pAdditionalF an additional formula where the type can be received from.
   * @param pF the formula to be converted.
   */
  // only some solvers require the additional (first) parameter, other solvers ignore it.
  public Object convertValue(
      @SuppressWarnings("unused") TFormulaInfo pAdditionalF, TFormulaInfo pF) {
    return convertValue(pF);
  }

  /** Variable names (symbols) can be wrapped with "|". This function removes those chars. */
  @VisibleForTesting
  public static String dequote(String s) {
    int l = s.length();
    if (l >= 2 && s.charAt(0) == '|' && s.charAt(l - 1) == '|') {
      return s.substring(1, l - 1);
    }
    return s;
  }

  private static boolean isReservedName(String pVar) {
    return pVar.isEmpty()
        || pVar.matches("^-?[0-9].*")
        || pVar.startsWith("'")
        || pVar.startsWith("fp.")
        || pVar.startsWith("re.")
        || pVar.startsWith("str.")
        || RESERVED.contains(pVar);
  }

  @VisibleForTesting
  public static boolean isValidName(String pVar) {
    return !isReservedName(pVar) && !DISALLOWED_CHARACTERS.matchesAnyOf(pVar);
  }

  /* This escaping works for simple escape sequences only, i.e., keywords are unique enough. */
  @VisibleForTesting
  public static String escapeName(String pVar) {
    // as long as keywords stay simple, this simple escaping is sufficient
    String prefix = "";
    if (isReservedName(pVar)) {
      prefix += ESCAPE;
    }
    if (pVar.indexOf(ESCAPE) != -1) {
      pVar = pVar.replace("" + ESCAPE, "" + ESCAPE + ESCAPE);
    }
    if (DISALLOWED_CHARACTERS.matchesAnyOf(pVar)) {
      for (Map.Entry<Character, String> e : DISALLOWED_CHARACTER_REPLACEMENT.entrySet()) {
        pVar = pVar.replace(e.getKey().toString(), ESCAPE + e.getValue());
      }
    }
    return prefix + pVar;
  }

  static String unescapeName(String pVar) {
    int idx = pVar.indexOf(ESCAPE);
    if (idx != -1) {
      // unescape BASIC_OPERATORS and SMTLIB2_KEYWORDS
      if (idx == 0) {
        String tmp = pVar.substring(1);
        if (!isValidName(tmp)) {
          pVar = tmp;
        }
      }

      // unescape DISALLOWED_CHARACTERS
      StringBuilder str = new StringBuilder();
      for (int i = 0; i < pVar.length(); i++) {
        if (pVar.charAt(i) == ESCAPE) {
          if (pVar.charAt(i + 1) == ESCAPE) {
            str.append(ESCAPE);
            i++;
          } else {
            String rest = pVar.substring(i + 1);
            for (Map.Entry<Character, String> e : DISALLOWED_CHARACTER_REPLACEMENT.entrySet()) {
              if (rest.startsWith(e.getValue())) {
                str.append(e.getKey());
                i += e.getValue().length();
                break;
              }
            }
          }
        } else {
          str.append(pVar.charAt(i));
        }
      }
      return str.toString();
    }
    return pVar; // unchanged
  }
}
