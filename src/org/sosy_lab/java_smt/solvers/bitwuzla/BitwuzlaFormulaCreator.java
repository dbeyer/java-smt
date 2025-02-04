// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.common.collect.Collections3.transformedImmutableSetCopy;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Table;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaArrayFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaBitvectorFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaBooleanFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaFloatingPointFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.BitwuzlaFormula.BitwuzlaFloatingPointRoundingModeFormula;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Map_TermTerm;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Int;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

public class BitwuzlaFormulaCreator extends FormulaCreator<Term, Sort, Void, BitwuzlaDeclaration> {
  private final TermManager termManager;

  /**
   * Variable cache, contains terms for all declared symbols
   *
   * <p>Bitwuzla allows the variables to be declared multiple times. Each of these instances will be
   * considered a separate variable, even if the names and types are the same. We fix this by
   * keeping track of all declared variables in this cache. If a variable is already defined we
   * return it from the cache, otherwise a new Term for the variable is created and added to the
   * cache.
   *
   * <p>It is important to keep this cache synchronized with the variable declarations for the
   * parser. This is handled in {@link BitwuzlaFormulaManager#parse(String)}.
   */
  private final Table<String, Sort, Term> formulaCache = HashBasedTable.create();

  /**
   * Remove SMTLIB quotes from a symbol name.
   *
   * <p>If the symbol is not quoted, just return it as is .
   */
  static String removeQuotes(String pSymbol) {
    if (pSymbol.startsWith("|") && pSymbol.endsWith("|")) {
      return pSymbol.substring(1, pSymbol.length() - 1);
    }
    return pSymbol;
  }

  /**
   * This mapping stores symbols and their constraints, such as from fp-to-bv casts with their
   * defining equation.
   *
   * <p>Bitwuzla does not support casts from floating-point to bitvector natively. The reason given
   * is that the value is undefined for NaN and that the SMT-LIB standard also does not include such
   * an operation. We try to work around this limitation by introducing a fresh variable <code>
   * __CAST_FROM_BV_XXX</code>for the result and then adding the constraint <code>
   * fp.to_fp(__CAST_FROM_BV_XXX) = &lt;float-term&gt;</code> as a side-condition. This is also what
   * is recommended by the SMT-LIB2 standard. The map <code>variableCasts</code> is used to store
   * these side-conditions so that they can later be added as assertions. The keys of the map are
   * the newly introduced variable symbols and the values are the defining equations as mentioned
   * above.
   */
  private final Map<String, Term> constraintsForVariables = new HashMap<>();

  protected BitwuzlaFormulaCreator(TermManager pTermManager) {
    super(null, pTermManager.mk_bool_sort(), null, null, null, null);
    termManager = pTermManager;
  }

  TermManager getTermManager() {
    return termManager;
  }

  @Override
  public Sort getBitvectorType(int bitwidth) {
    return termManager.mk_bv_sort(bitwidth);
  }

  @Override
  public BitvectorFormula encapsulateBitvector(Term pTerm) {
    assert getFormulaType(pTerm).isBitvectorType()
        : "Unexpected formula type for BV formula: " + getFormulaType(pTerm);
    return new BitwuzlaBitvectorFormula(pTerm);
  }

  // Assuming that JavaSMT FloatingPointType follows IEEE 754, if it is in the decimal
  // system instead use bitwuzla_mk_fp_value_from_real somehow or convert myself
  @Override
  public Sort getFloatingPointType(FloatingPointType type) {
    return termManager.mk_fp_sort(type.getExponentSize(), type.getMantissaSize() + 1);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> FormulaType<TE> getArrayFormulaElementType(
      ArrayFormula<TI, TE> pArray) {
    return ((BitwuzlaArrayFormula<TI, TE>) pArray).getElementType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> FormulaType<TI> getArrayFormulaIndexType(
      ArrayFormula<TI, TE> pArray) {
    return ((BitwuzlaArrayFormula<TI, TE>) pArray).getIndexType();
  }

  @Override
  public Sort getArrayType(Sort indexType, Sort elementType) {
    return termManager.mk_array_sort(indexType, elementType);
  }

  @Override
  protected FloatingPointFormula encapsulateFloatingPoint(Term pTerm) {
    assert getFormulaType(pTerm).isFloatingPointType()
        : String.format("%s is no FP, but %s (%s)", pTerm, pTerm.sort(), getFormulaType(pTerm));
    return new BitwuzlaFloatingPointFormula(pTerm);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      Term pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).isArrayType()
        : "Unexpected formula type for array formula: " + getFormulaType(pTerm);
    return new BitwuzlaArrayFormula<>(pTerm, pIndexType, pElementType);
  }

  @Override
  public Term makeVariable(Sort pSort, String varName) {
    Term maybeFormula = formulaCache.get(varName, pSort);
    if (maybeFormula != null) {
      return maybeFormula;
    }

    Term newVar = termManager.mk_const(pSort, varName);
    formulaCache.put(varName, pSort, newVar);
    return newVar;
  }

  public Term makeBoundVariable(Term var) {
    String name = var.symbol();
    Sort sort = var.sort();
    // TODO: do we need a bound cache?
    // Term maybeVar = boundFormulaCache.get(name, sort);
    // if (maybeVar != null) {
    // return maybeVar;
    // }

    Term newVar = termManager.mk_var(sort, name);
    // boundFormulaCache.put(name, sort, newVar);
    return newVar;
  }

  public FormulaType<?> bitwuzlaSortToType(Sort pSort) {
    // UFs play by different rules. For them, we need to extract the domain
    if (pSort.is_fp()) {
      int exponent = pSort.fp_exp_size();
      int mantissa = pSort.fp_sig_size() - 1;
      return FormulaType.getFloatingPointType(exponent, mantissa);
    } else if (pSort.is_bv()) {
      return FormulaType.getBitvectorTypeWithSize(pSort.bv_size());
    } else if (pSort.is_array()) {
      FormulaType<?> domainSort = bitwuzlaSortToType(pSort.array_index());
      FormulaType<?> rangeSort = bitwuzlaSortToType(pSort.array_element());
      return FormulaType.getArrayType(domainSort, rangeSort);
    } else if (pSort.is_bool()) {
      return FormulaType.BooleanType;
    } else if (pSort.is_rm()) {
      return FormulaType.FloatingPointRoundingModeType;
    }

    throw new UnsupportedOperationException(
        "Could not find the JavaSMT type for sort" + pSort + ".");
  }

  private FunctionDeclarationKind getDeclarationKind(Term term) {
    Kind kind = term.kind();

    if (kind.equals(Kind.AND)) {
      return FunctionDeclarationKind.AND;
    } else if (kind.equals(Kind.DISTINCT)) {
      return FunctionDeclarationKind.DISTINCT;
    } else if (kind.equals(Kind.EQUAL)) {
      return FunctionDeclarationKind.EQ;
    } else if (kind.equals(Kind.IFF)) {
      return FunctionDeclarationKind.IFF;
    } else if (kind.equals(Kind.IMPLIES)) {
      return FunctionDeclarationKind.IMPLIES;
    } else if (kind.equals(Kind.NOT)) {
      return FunctionDeclarationKind.NOT;
    } else if (kind.equals(Kind.OR)) {
      return FunctionDeclarationKind.OR;
    } else if (kind.equals(Kind.XOR)) {
      return FunctionDeclarationKind.XOR;
    } else if (kind.equals(Kind.ITE)) {
      return FunctionDeclarationKind.ITE;
    } else if (kind.equals(Kind.APPLY)) {
      return FunctionDeclarationKind.UF;
    } else if (kind.equals(Kind.ARRAY_SELECT)) {
      return FunctionDeclarationKind.SELECT;
    } else if (kind.equals(Kind.ARRAY_STORE)) {
      return FunctionDeclarationKind.STORE;
    } else if (kind.equals(Kind.CONST_ARRAY)) {
      return FunctionDeclarationKind.CONST;
    } else if (kind.equals(Kind.BV_ADD)) {
      return FunctionDeclarationKind.BV_ADD;
    } else if (kind.equals(Kind.BV_AND)) {
      return FunctionDeclarationKind.BV_AND;
    } else if (kind.equals(Kind.BV_ASHR)) {
      return FunctionDeclarationKind.BV_ASHR;
    } else if (kind.equals(Kind.BV_CONCAT)) {
      return FunctionDeclarationKind.BV_CONCAT;
    } else if (kind.equals(Kind.BV_MUL)) {
      return FunctionDeclarationKind.BV_MUL;
    } else if (kind.equals(Kind.BV_NEG)) {
      return FunctionDeclarationKind.BV_NEG;
    } else if (kind.equals(Kind.BV_NOT)) {
      return FunctionDeclarationKind.BV_NOT;
    } else if (kind.equals(Kind.BV_OR)) {
      return FunctionDeclarationKind.BV_OR;
    } else if (kind.equals(Kind.BV_SDIV)) {
      return FunctionDeclarationKind.BV_SDIV;
    } else if (kind.equals(Kind.BV_SGE)) {
      return FunctionDeclarationKind.BV_SGE;
    } else if (kind.equals(Kind.BV_SGT)) {
      return FunctionDeclarationKind.BV_SGT;
    } else if (kind.equals(Kind.BV_SHL)) {
      return FunctionDeclarationKind.BV_SHL;
    } else if (kind.equals(Kind.BV_SHR)) {
      return FunctionDeclarationKind.BV_LSHR;
    } else if (kind.equals(Kind.BV_SLE)) {
      return FunctionDeclarationKind.BV_SLE;
    } else if (kind.equals(Kind.BV_SLT)) {
      return FunctionDeclarationKind.BV_SLT;
    } else if (kind.equals(Kind.BV_SMOD)) {
      return FunctionDeclarationKind.BV_SMOD;
    } else if (kind.equals(Kind.BV_SREM)) {
      return FunctionDeclarationKind.BV_SREM;
    } else if (kind.equals(Kind.BV_SUB)) {
      return FunctionDeclarationKind.BV_SUB;
    } else if (kind.equals(Kind.BV_UDIV)) {
      return FunctionDeclarationKind.BV_UDIV;
    } else if (kind.equals(Kind.BV_UGE)) {
      return FunctionDeclarationKind.BV_UGE;
    } else if (kind.equals(Kind.BV_UGT)) {
      return FunctionDeclarationKind.BV_UGT;
    } else if (kind.equals(Kind.BV_ULE)) {
      return FunctionDeclarationKind.BV_ULE;
    } else if (kind.equals(Kind.BV_ULT)) {
      return FunctionDeclarationKind.BV_ULT;
    } else if (kind.equals(Kind.BV_UREM)) {
      return FunctionDeclarationKind.BV_UREM;
    } else if (kind.equals(Kind.BV_EXTRACT)) {
      return FunctionDeclarationKind.BV_EXTRACT;
    } else if (kind.equals(Kind.BV_SIGN_EXTEND)) {
      return FunctionDeclarationKind.BV_SIGN_EXTENSION;
    } else if (kind.equals(Kind.BV_ZERO_EXTEND)) {
      return FunctionDeclarationKind.BV_ZERO_EXTENSION;
    } else if (kind.equals(Kind.FP_ABS)) {
      return FunctionDeclarationKind.FP_ABS;
    } else if (kind.equals(Kind.FP_ADD)) {
      return FunctionDeclarationKind.FP_ADD;
    } else if (kind.equals(Kind.FP_DIV)) {
      return FunctionDeclarationKind.FP_DIV;
    } else if (kind.equals(Kind.FP_EQUAL)) {
      return FunctionDeclarationKind.FP_EQ;
    } else if (kind.equals(Kind.FP_GEQ)) {
      return FunctionDeclarationKind.FP_GE;
    } else if (kind.equals(Kind.FP_GT)) {
      return FunctionDeclarationKind.FP_GT;
    } else if (kind.equals(Kind.FP_IS_INF)) {
      return FunctionDeclarationKind.FP_IS_INF;
    } else if (kind.equals(Kind.FP_IS_NAN)) {
      return FunctionDeclarationKind.FP_IS_NAN;
    } else if (kind.equals(Kind.FP_IS_NEG)) {
      return FunctionDeclarationKind.FP_IS_NEGATIVE;
    } else if (kind.equals(Kind.FP_IS_NORMAL)) {
      return FunctionDeclarationKind.FP_IS_NORMAL;
    } else if (kind.equals(Kind.FP_IS_SUBNORMAL)) {
      return FunctionDeclarationKind.FP_IS_SUBNORMAL;
    } else if (kind.equals(Kind.FP_IS_ZERO)) {
      return FunctionDeclarationKind.FP_IS_ZERO;
    } else if (kind.equals(Kind.FP_LEQ)) {
      return FunctionDeclarationKind.FP_LE;
    } else if (kind.equals(Kind.FP_LT)) {
      return FunctionDeclarationKind.FP_LT;
    } else if (kind.equals(Kind.FP_MAX)) {
      return FunctionDeclarationKind.FP_MAX;
    } else if (kind.equals(Kind.FP_MIN)) {
      return FunctionDeclarationKind.FP_MIN;
    } else if (kind.equals(Kind.FP_MUL)) {
      return FunctionDeclarationKind.FP_MUL;
    } else if (kind.equals(Kind.FP_REM)) {
      return FunctionDeclarationKind.FP_REM;
    } else if (kind.equals(Kind.FP_NEG)) {
      return FunctionDeclarationKind.FP_NEG;
    } else if (kind.equals(Kind.FP_RTI)) {
      return FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL;
    } else if (kind.equals(Kind.FP_SQRT)) {
      return FunctionDeclarationKind.FP_SQRT;
    } else if (kind.equals(Kind.FP_SUB)) {
      return FunctionDeclarationKind.FP_SUB;
    } else if (kind.equals(Kind.FP_TO_FP_FROM_BV)) {
      return FunctionDeclarationKind.BV_UCASTTO_FP;
    } else if (kind.equals(Kind.FP_TO_FP_FROM_FP)) {
      return FunctionDeclarationKind.FP_CASTTO_FP;
    } else if (kind.equals(Kind.FP_TO_FP_FROM_SBV)) {
      return FunctionDeclarationKind.BV_SCASTTO_FP;
    } else if (kind.equals(Kind.FP_TO_FP_FROM_UBV)) {
      return FunctionDeclarationKind.BV_UCASTTO_FP;
    } else if (kind.equals(Kind.FP_TO_SBV)) {
      return FunctionDeclarationKind.FP_CASTTO_SBV;
    } else if (kind.equals(Kind.FP_TO_UBV)) {
      return FunctionDeclarationKind.FP_CASTTO_UBV;
    } else if (kind.equals(Kind.BV_XOR)) {
      return FunctionDeclarationKind.BV_XOR;
    } else if (kind.equals(Kind.BV_ROL)) {
      return FunctionDeclarationKind.BV_ROTATE_LEFT;
    } else if (kind.equals(Kind.BV_ROR)) {
      return FunctionDeclarationKind.BV_ROTATE_RIGHT;
    } else if (kind.equals(Kind.BV_ROLI)) {
      return FunctionDeclarationKind.BV_ROTATE_LEFT_BY_INT;
    } else if (kind.equals(Kind.BV_RORI)) {
      return FunctionDeclarationKind.BV_ROTATE_RIGHT_BY_INT;
    }
    return FunctionDeclarationKind.OTHER;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, Term pTerm) {
    assert pType.equals(getFormulaType(pTerm))
        : String.format(
            "Trying to encapsulate formula of type %s as %s", getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new BitwuzlaBooleanFormula(pTerm);
    } else if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T) new BitwuzlaArrayFormula<>(pTerm, arrFt.getIndexType(), arrFt.getElementType());
    } else if (pType.isBitvectorType()) {
      return (T) new BitwuzlaBitvectorFormula(pTerm);
    } else if (pType.isFloatingPointType()) {
      return (T) new BitwuzlaFloatingPointFormula(pTerm);
    } else if (pType.isFloatingPointRoundingModeType()) {
      return (T) new BitwuzlaFloatingPointRoundingModeFormula(pTerm);
    }
    throw new IllegalArgumentException("Cannot create formulas of type " + pType + " in Bitwuzla");
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    Sort sort = extractInfo(pFormula).sort();
    if (pFormula instanceof BitvectorFormula) {
      checkArgument(sort.is_bv(), "BitvectorFormula with type missmatch: %s", pFormula);
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize(sort.bv_size());
    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    } else if (pFormula instanceof FloatingPointFormula) {
      if (!sort.is_fp()) {
        throw new IllegalArgumentException(
            "FloatingPointFormula with actual type " + sort + ": " + pFormula);
      }
      int exp = sort.fp_exp_size();
      int man = sort.fp_sig_size() - 1;
      return (FormulaType<T>) FormulaType.getFloatingPointType(exp, man);
    } else if (sort.is_rm()) {
      return (FormulaType<T>) FormulaType.FloatingPointRoundingModeType;
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(Term formula) {
    Sort pType = formula.sort();
    return bitwuzlaSortToType(pType);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, Term f)
      throws UnsupportedOperationException {
    Kind kind = f.kind();
    if (f.is_value()) {
      return visitor.visitConstant(formula, convertValue(f));
    } else if (f.is_const()) {
      String name = f.symbol();
      return visitor.visitFreeVariable(formula, name);

    } else if (f.is_variable()) {
      String name = removeQuotes(f.symbol());
      Sort sort = f.sort();
      Term originalVar = formulaCache.get(name, sort);
      return visitor.visitBoundVariable(encapsulate(getFormulaType(originalVar), originalVar), 0);

    } else if (kind.equals(Kind.EXISTS) || kind.equals(Kind.FORALL)) {
      Vector_Term children = f.children();
      // QUANTIFIER: replace bound variable with free variable for visitation
      int size = children.size();
      assert size == 2;
      Term body = children.get(size - 1);
      List<Formula> freeEncVars = new ArrayList<>();
      // The first length - 2 elements are bound vars, and the last element is the body
      Term[] boundVars = new Term[size - 1];
      Term[] freeVars = new Term[size - 1];
      for (int i = 0; i < size - 1; i++) {
        Term boundVar = children.get(i);
        boundVars[i] = boundVar;
        String name = removeQuotes(boundVar.symbol());
        assert name != null;
        Sort sort = boundVar.sort();
        Term freeVar;
        if (formulaCache.contains(name, sort)) {
          freeVar = formulaCache.get(name, sort);
        } else {
          // no free var existing (e.g. from parsing), create a new one
          freeVar = makeVariable(sort, name);
        }
        freeVars[i] = freeVar;
        freeEncVars.add(encapsulate(getFormulaType(freeVar), freeVar));
      }

      Map_TermTerm map = new Map_TermTerm();
      for (int i = 0; i < boundVars.length; i++) {
        map.put(boundVars[i], freeVars[i]);
      }
      body = termManager.substitute_term(body, map);

      Quantifier quant = kind.equals(Kind.EXISTS) ? Quantifier.EXISTS : Quantifier.FORALL;
      return visitor.visitQuantifier(
          (BooleanFormula) formula, quant, freeEncVars, encapsulateBoolean(body));

    } else {
      Vector_Term args = f.children();
      ImmutableList.Builder<Formula> arguments = ImmutableList.builder();
      ImmutableList.Builder<FormulaType<?>> argumentTypes = ImmutableList.builder();

      String name = f.symbol();

      BitwuzlaDeclaration decl = null;
      for (int i = 0; i < args.size(); i++) {
        Term argument = args.get(i);
        if (kind == Kind.APPLY && i == 0) {
          // UFs carry the decl in the first child and the decl has the name
          decl = BitwuzlaDeclaration.create(argument);
          name = argument.symbol();
          continue;
        }
        FormulaType<?> type = getFormulaType(argument);
        arguments.add(encapsulate(type, argument));
        argumentTypes.add(type);
      }

      if (name == null) {
        name = f.kind().toString();
      }
      if (decl == null) {
        decl = BitwuzlaDeclaration.create(f.kind());
      }
      if (f.num_indices() > 0) {
        // We need to retain the original formula as the declaration for indexed formulas,
        // otherwise we loose the index info, but we also need to know if its a kind or term
        decl = BitwuzlaDeclaration.create(f);
      }

      return visitor.visitFunction(
          formula,
          arguments.build(),
          FunctionDeclarationImpl.of(
              name, getDeclarationKind(f), argumentTypes.build(), getFormulaType(f), decl));
    }
  }

  @Override
  public Term callFunctionImpl(BitwuzlaDeclaration declaration, List<Term> args) {
    // For UFs the declaration needs to be a const wrapping of the function sort
    // For all other functions it needs to be the kind
    // BUT, we can never use a bitwuzla_term_is... function on a KIND
    if (!declaration.isKind() && declaration.getTerm().num_indices() > 0) {
      // The term might be indexed, then we need index creation
      Term term = declaration.getTerm();
      Kind properKind = term.kind();
      return termManager.mk_term(properKind, new Vector_Term(args), term.indices());
    }

    if (!declaration.isKind() && declaration.getTerm().sort().is_fun()) {
      Vector_Term functionAndArgs = new Vector_Term();
      functionAndArgs.add(declaration.getTerm());
      functionAndArgs.addAll(args);
      return termManager.mk_term(Kind.APPLY, functionAndArgs, new Vector_Int());
    }

    assert declaration.isKind();

    return termManager.mk_term(declaration.getKind(), new Vector_Term(args), new Vector_Int());
  }

  @Override
  public BitwuzlaDeclaration declareUFImpl(String name, Sort pReturnType, List<Sort> pArgTypes) {
    if (pArgTypes.isEmpty()) {
      // Bitwuzla does not support UFs with no args, so we make a variable
      // TODO: implement
      throw new UnsupportedOperationException("Bitwuzla does not support 0 arity UFs.");
    }
    Sort functionSort = termManager.mk_fun_sort(new Vector_Sort(pArgTypes), pReturnType);

    Term maybeFormula = formulaCache.get(name, functionSort);
    if (maybeFormula != null) {
      return BitwuzlaDeclaration.create(maybeFormula);
    }

    Term uf = termManager.mk_const(functionSort, name);
    formulaCache.put(name, functionSort, uf);
    return BitwuzlaDeclaration.create(uf);
  }

  @Override
  protected BitwuzlaDeclaration getBooleanVarDeclarationImpl(Term pTerm) {
    Kind kind = pTerm.kind();

    // CONSTANTS are "variables" and Kind.VARIABLES are bound variables in for example quantifiers
    assert kind == Kind.APPLY || kind == Kind.CONSTANT : kind.toString();
    if (kind == Kind.APPLY) {
      // Returns pointer to Uninterpreted Function used in Apply
      return BitwuzlaDeclaration.create(pTerm.get(0));
    } else {
      return BitwuzlaDeclaration.create(pTerm);
    }
  }

  @Override
  public Term extractInfo(Formula pT) {
    return BitwuzlaFormulaManager.getBitwuzlaTerm(pT);
  }

  @Override
  public BooleanFormula encapsulateBoolean(Term pTerm) {
    assert getFormulaType(pTerm).isBooleanType();
    return new BitwuzlaBooleanFormula(pTerm);
  }

  Table<String, Sort, Term> getCache() {
    return formulaCache;
  }

  @Override
  public Object convertValue(Term term) {
    Preconditions.checkArgument(term.is_value(), "Term \"%s\" is not a value.", term);
    Sort sort = term.sort();
    if (sort.is_bool()) {
      return term.to_bool();
    }
    if (sort.is_rm()) {
      return term.to_rm();
    }
    if (sort.is_bv()) {
      return new BigInteger(term.to_bv(), 2);
    }
    if (sort.is_fp()) {
      int sizeExponent = sort.fp_exp_size();
      int sizeMantissa = sort.fp_sig_size() - 1;
      return FloatingPointNumber.of(term.to_bv(), sizeExponent, sizeMantissa);
    }
    throw new AssertionError("Unknown value type.");
  }

  /** Add a constraint that is pushed onto the prover stack whenever the variable is used. */
  public void addConstraintForVariable(String variable, Term constraint) {
    constraintsForVariables.put(variable, constraint);
  }

  /**
   * Returns a set of additional constraints (side-conditions) that are needed to use some variables
   * from the given term, such as utility variables from casts.
   *
   * <p>Bitwuzla does not support fp-to-bv conversion natively. We have to use side-conditions as a
   * workaround. When a term containing fp-to-bv casts is added to the assertion stack these
   * side-conditions need to be collected by calling this method and then also adding them to the
   * assertion stack.
   */
  public Collection<Term> getConstraintsForTerm(Term pTerm) {
    final Set<String> usedConstraintVariables = new LinkedHashSet<>();
    final Deque<String> waitlist = new ArrayDeque<>(extractVariablesAndUFs(pTerm, false).keySet());
    while (!waitlist.isEmpty()) {
      String current = waitlist.pop();
      if (constraintsForVariables.containsKey(current)) { // ignore variables without constraints
        if (usedConstraintVariables.add(current)) {
          // if we found a new variable with constraint, get transitive variables from constraint
          Term constraint = constraintsForVariables.get(current);
          waitlist.addAll(extractVariablesAndUFs(constraint, false).keySet());
        }
      }
    }

    return transformedImmutableSetCopy(usedConstraintVariables, constraintsForVariables::get);
  }
}
