// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SLFormulaManager;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.StringFormulaManager;
import org.sosy_lab.java_smt.api.Tactic;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator.SymbolViewVisitor;
import org.sosy_lab.java_smt.basicimpl.tactics.NNFVisitor;
import org.sosy_lab.java_smt.utils.SolverUtils;

/**
 * Simplifies building a solver from the specific theories.
 *
 * @param <TFormulaInfo> The solver specific type.
 */
@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements FormulaManager {

  private final @Nullable AbstractArrayFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      arrayManager;

  private final AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> booleanManager;

  private final @Nullable IntegerFormulaManager integerManager;

  private final @Nullable RationalFormulaManager rationalManager;

  private final @Nullable AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      bitvectorManager;

  private final @Nullable AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      floatingPointManager;

  private final AbstractUFManager<TFormulaInfo, ?, TType, TEnv> functionManager;

  private final @Nullable AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      quantifiedManager;

  private final @Nullable AbstractSLFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> slManager;

  private final @Nullable AbstractStringFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      strManager;

  private final @Nullable AbstractEnumerationFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      enumManager;

  private final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> formulaCreator;

  /** Builds a solver from the given theory implementations. */
  @SuppressWarnings("checkstyle:parameternumber")
  protected AbstractFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pFormulaCreator,
      AbstractUFManager<TFormulaInfo, ?, TType, TEnv> functionManager,
      AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> booleanManager,
      @Nullable IntegerFormulaManager pIntegerManager,
      @Nullable RationalFormulaManager pRationalManager,
      @Nullable AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
          bitvectorManager,
      @Nullable AbstractFloatingPointFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
          floatingPointManager,
      @Nullable AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
          quantifiedManager,
      @Nullable AbstractArrayFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> arrayManager,
      @Nullable AbstractSLFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> slManager,
      @Nullable AbstractStringFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl> strManager,
      @Nullable AbstractEnumerationFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
          enumManager) {

    this.arrayManager = arrayManager;
    this.quantifiedManager = quantifiedManager;
    this.functionManager = checkNotNull(functionManager, "function manager needed");
    this.booleanManager = checkNotNull(booleanManager, "boolean manager needed");
    this.integerManager = pIntegerManager;
    this.rationalManager = pRationalManager;
    this.bitvectorManager = bitvectorManager;
    this.floatingPointManager = floatingPointManager;
    this.slManager = slManager;
    this.strManager = strManager;
    this.enumManager = enumManager;
    this.formulaCreator = pFormulaCreator;

    checkArgument(
        booleanManager.getFormulaCreator() == formulaCreator
            && functionManager.getFormulaCreator() == formulaCreator
            && !(bitvectorManager != null && bitvectorManager.getFormulaCreator() != formulaCreator)
            && !(floatingPointManager != null
                && floatingPointManager.getFormulaCreator() != formulaCreator)
            && !(quantifiedManager != null
                && quantifiedManager.getFormulaCreator() != formulaCreator),
        "The creator instances must match across the managers!");
  }

  public final FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> getFormulaCreator() {
    return formulaCreator;
  }

  @Override
  public IntegerFormulaManager getIntegerFormulaManager() {
    if (integerManager == null) {
      throw new UnsupportedOperationException("Solver does not support integer theory");
    }
    return integerManager;
  }

  @Override
  public RationalFormulaManager getRationalFormulaManager() {
    if (rationalManager == null) {
      throw new UnsupportedOperationException("Solver does not support rationals theory");
    }
    return rationalManager;
  }

  @Override
  public AbstractBooleanFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      getBooleanFormulaManager() {
    return booleanManager;
  }

  @Override
  public AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      getBitvectorFormulaManager() {
    if (bitvectorManager == null) {
      throw new UnsupportedOperationException("Solver does not support bitvector theory");
    }
    return bitvectorManager;
  }

  @Override
  public FloatingPointFormulaManager getFloatingPointFormulaManager() {
    if (floatingPointManager == null) {
      throw new UnsupportedOperationException("Solver does not support floating point theory");
    }
    return floatingPointManager;
  }

  @Override
  public AbstractUFManager<TFormulaInfo, ?, TType, TEnv> getUFManager() {
    return functionManager;
  }

  @Override
  public SLFormulaManager getSLFormulaManager() {
    if (slManager == null) {
      throw new UnsupportedOperationException("Solver does not support separation logic theory");
    }
    return slManager;
  }

  @Override
  public AbstractQuantifiedFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
      getQuantifiedFormulaManager() {
    if (quantifiedManager == null) {
      throw new UnsupportedOperationException("Solver does not support quantification");
    }
    return quantifiedManager;
  }

  @Override
  public ArrayFormulaManager getArrayFormulaManager() {
    if (arrayManager == null) {
      throw new UnsupportedOperationException("Solver does not support arrays");
    }
    return arrayManager;
  }

  @Override
  public StringFormulaManager getStringFormulaManager() {
    if (strManager == null) {
      throw new UnsupportedOperationException("Solver does not support string theory");
    }
    return strManager;
  }

  @Override
  public EnumerationFormulaManager getEnumerationFormulaManager() {
    if (enumManager == null) {
      throw new UnsupportedOperationException("Solver does not support enumeration theory");
    }
    return enumManager;
  }

  protected abstract TFormulaInfo parseImpl(String formulaStr) throws IllegalArgumentException;

  /**
   * Takes a SMT-LIB2 script and cleans it up.
   *
   * <p>We remove all comments and put each command on its own line. Declarations and asserts are
   * kept and everything else is removed. For <code>(set-logic ..)</code> we make sure that it's at
   * the top of the file before removing it, and for <code>(exit)</code> we make sure that it can
   * only occur as the last command.
   */
  private String sanitize(String formulaStr) {
    List<String> tokens = Tokenizer.tokenize(formulaStr);

    StringBuilder builder = new StringBuilder();
    int pos = 0; // index of the current token

    for (String token : tokens) {
      if (Tokenizer.isSetLogicToken(token)) {
        // Skip the (set-logic ...) command at the beginning of the input
        Preconditions.checkArgument(pos == 0);

      } else if (Tokenizer.isExitToken(token)) {
        // Skip the (exit) command at the end of the input
        Preconditions.checkArgument(pos == tokens.size() - 1);

      } else if (Tokenizer.isDeclarationToken(token)
          || Tokenizer.isDefinitionToken(token)
          || Tokenizer.isAssertToken(token)) {
        // Keep only declaration, definitions and assertion
        builder.append(token).append('\n');

      } else if (Tokenizer.isForbiddenToken(token)) {
        // Throw an exception if the script contains commands like (pop) or (reset) that change the
        // state of the assertion stack.
        // We could keep track of the state of the stack and only consider the formulas that remain
        // on the stack at the end of the script. However, this does not seem worth it at the
        // moment. If needed, this feature can still be added later.
        String message;
        if (Tokenizer.isPushToken(token)) {
          message = "(push ...)";
        } else if (Tokenizer.isPopToken(token)) {
          message = "(pop ...)";
        } else if (Tokenizer.isResetAssertionsToken(token)) {
          message = "(reset-assertions)";
        } else if (Tokenizer.isResetToken(token)) {
          message = "(reset)";
        } else {
          // Should be unreachable
          throw new UnsupportedOperationException();
        }
        throw new IllegalArgumentException(
            String.format("SMTLIB command '%s' is not supported when parsing formulas.", message));

      } else {
        // Remove everything else
      }
      pos++;
    }
    return builder.toString();
  }

  @Override
  public BooleanFormula parse(String formulaStr) throws IllegalArgumentException {
    BooleanFormula r = formulaCreator.encapsulateBoolean(parseImpl(sanitize(formulaStr)));
    formulaCreator.extractVariablesAndUFs(
        r,
        true,
        (pS, pFormula) -> checkArgument(FormulaCreator.isValidName(FormulaCreator.dequote(pS))));
    return r;
  }

  protected abstract String dumpFormulaImpl(TFormulaInfo t) throws IOException;

  @Override
  public Appender dumpFormula(BooleanFormula t) {
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        String raw = dumpFormulaImpl(formulaCreator.extractInfo(t));
        out.append(sanitize(raw));
      }
    };
  }

  @Override
  public final <T extends Formula> FormulaType<T> getFormulaType(T formula) {
    return formulaCreator.getFormulaType(checkNotNull(formula));
  }

  // Utility methods that are handy for subclasses

  public final TEnv getEnvironment() {
    return getFormulaCreator().getEnv();
  }

  public final TFormulaInfo extractInfo(Formula f) {
    return formulaCreator.extractInfo(f);
  }

  @Override
  public BooleanFormula applyTactic(BooleanFormula f, Tactic tactic)
      throws InterruptedException, SolverException {
    switch (tactic) {
      case ACKERMANNIZATION:
        return applyUFEImpl(f);
      case NNF:
        return applyNNFImpl(f);
      case TSEITIN_CNF:
        return applyCNFImpl(f);
      case QE_LIGHT:
        return applyQELightImpl(f);
      default:
        throw new UnsupportedOperationException("Unexpected enum value");
    }
  }

  /** Eliminate UFs from the given input formula. */
  protected BooleanFormula applyUFEImpl(BooleanFormula pF) {
    return SolverUtils.ufElimination(this).eliminateUfs(pF);
  }

  /**
   * Eliminate quantifiers from the given input formula.
   *
   * <p>This is the light version that does not need to eliminate all quantifiers.
   *
   * @throws InterruptedException Can be thrown by the native code.
   * @throws SolverException Can be thrown by the native code.
   */
  protected BooleanFormula applyQELightImpl(BooleanFormula pF)
      throws InterruptedException, SolverException {

    // Returning the untouched formula is valid according to QE_LIGHT contract.
    // TODO: substitution-based implementation.
    return pF;
  }

  /**
   * Apply conjunctive normal form (CNF) transformation to the given input formula.
   *
   * @param pF Input to apply the CNF transformation to.
   * @throws InterruptedException Can be thrown by the native code.
   * @throws SolverException Can be thrown by the native code.
   */
  protected BooleanFormula applyCNFImpl(BooleanFormula pF)
      throws InterruptedException, SolverException {

    // TODO: generic implementation.
    throw new UnsupportedOperationException(
        "Currently there is no generic implementation for CNF conversion");
  }

  /**
   * Apply negation normal form (NNF) transformation to the given input formula.
   *
   * @throws InterruptedException Can be thrown by the native code.
   * @throws SolverException Can be thrown by the native code.
   */
  protected BooleanFormula applyNNFImpl(BooleanFormula input)
      throws InterruptedException, SolverException {
    return getBooleanFormulaManager().transformRecursively(input, new NNFVisitor(this));
  }

  @Override
  public <T extends Formula> T simplify(T f) throws InterruptedException {
    return formulaCreator.encapsulate(formulaCreator.getFormulaType(f), simplify(extractInfo(f)));
  }

  /**
   * Apply a simplification procedure for the given formula.
   *
   * <p>This does not need to change something, but it might simplify the formula.
   *
   * @throws InterruptedException Can be thrown by the native code.
   */
  protected TFormulaInfo simplify(TFormulaInfo f) throws InterruptedException {
    return f;
  }

  @Override
  public <R> R visit(Formula input, FormulaVisitor<R> visitor) {
    return formulaCreator.visit(input, new SymbolViewVisitor<>(visitor));
  }

  @Override
  public void visitRecursively(Formula pF, FormulaVisitor<TraversalProcess> pFormulaVisitor) {
    formulaCreator.visitRecursively(new SymbolViewVisitor<>(pFormulaVisitor), pF);
  }

  @Override
  public <T extends Formula> T transformRecursively(
      T f, FormulaTransformationVisitor pFormulaVisitor) {
    return formulaCreator.transformRecursively(new SymbolViewVisitor<>(pFormulaVisitor), f);
  }

  /**
   * Extract names of all free variables in a formula.
   *
   * @param f The input formula
   */
  @Override
  public ImmutableMap<String, Formula> extractVariables(Formula f) {
    ImmutableMap.Builder<String, Formula> found = ImmutableMap.builder();
    formulaCreator.extractVariablesAndUFs(
        f, false, (pS, pFormula) -> found.put(FormulaCreator.unescapeName(pS), pFormula));
    return found.buildOrThrow(); // visitation should not visit any symbol twice
  }

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f The input formula
   */
  @Override
  public ImmutableMap<String, Formula> extractVariablesAndUFs(Formula f) {
    ImmutableMap.Builder<String, Formula> found = ImmutableMap.builder();
    formulaCreator.extractVariablesAndUFs(
        f, true, (pS, pFormula) -> found.put(FormulaCreator.unescapeName(pS), pFormula));
    // We can find duplicate keys with different values, like UFs with distinct parameters.
    // In such a case, we use only one appearance (the last one).
    return found.buildKeepingLast();
  }

  @Override
  public BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherManager) {
    if (this == otherManager) {
      return formula; // shortcut
    }
    return parse(otherManager.dumpFormula(formula).toString());
  }

  @Override
  public <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name) {
    Formula t;
    if (formulaType.isBooleanType()) {
      t = booleanManager.makeVariable(name);
    } else if (formulaType.isIntegerType()) {
      assert integerManager != null;
      t = integerManager.makeVariable(name);
    } else if (formulaType.isRationalType()) {
      assert rationalManager != null;
      t = rationalManager.makeVariable(name);
    } else if (formulaType.isStringType()) {
      assert strManager != null;
      t = strManager.makeVariable(name);
    } else if (formulaType.isBitvectorType()) {
      assert bitvectorManager != null;
      t = bitvectorManager.makeVariable((BitvectorType) formulaType, name);
    } else if (formulaType.isFloatingPointType()) {
      assert floatingPointManager != null;
      t = floatingPointManager.makeVariable(name, (FloatingPointType) formulaType);
    } else if (formulaType.isArrayType()) {
      assert arrayManager != null;
      t = arrayManager.makeArray(name, (ArrayFormulaType<?, ?>) formulaType);
    } else {
      throw new IllegalArgumentException("Unknown formula type");
    }

    @SuppressWarnings("unchecked")
    T out = (T) t;
    return out;
  }

  @Override
  @SuppressWarnings("unchecked")
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args) {

    if (declaration.getKind() == FunctionDeclarationKind.CONST) {
      ArrayFormulaType<?, ?> arrayType = (ArrayFormulaType<?, ?>) declaration.getType();
      Formula defaultElement = Iterables.getOnlyElement(args);
      return (T)
          arrayManager.makeArray(
              arrayType.getIndexType(),
              getFormulaType(defaultElement),
              Iterables.getOnlyElement(args));
    }

    return formulaCreator.callFunction(declaration, args);
  }

  @Override
  public <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, Formula... args) {
    return makeApplication(declaration, Arrays.asList(args));
  }

  @Override
  public <T extends Formula> T substitute(
      final T pF, final Map<? extends Formula, ? extends Formula> pFromToMapping) {
    return transformRecursively(
        pF,
        new FormulaTransformationVisitor(this) {
          @Override
          public Formula visitFreeVariable(Formula f, String name) {
            return replace(f);
          }

          @Override
          public Formula visitFunction(
              Formula f, List<Formula> newArgs, FunctionDeclaration<?> functionDeclaration) {
            Formula out = pFromToMapping.get(f);
            if (out == null) {
              return makeApplication(functionDeclaration, newArgs);
            } else {
              return out;
            }
          }

          private Formula replace(Formula f) {
            Formula out = pFromToMapping.get(f);
            if (out == null) {
              return f;
            } else {
              return out;
            }
          }
        });
  }

  /**
   * Check whether the given String can be used as symbol/name for variables or undefined functions.
   * We disallow some keywords from SMTLib2 and other basic operators to be used as symbols.
   */
  @Override
  public final boolean isValidName(String pVar) {
    return FormulaCreator.isValidName(pVar);
  }

  /* This escaping works for simple escape sequences only, i.e., keywords are unique enough. */
  @Override
  public final String escape(String pVar) {
    return FormulaCreator.escapeName(pVar);
  }

  /* This unescaping works for simple escape sequences only, i.e., keywords are unique enough. */
  @Override
  public final String unescape(String pVar) {
    return FormulaCreator.unescapeName(pVar);
  }
}
