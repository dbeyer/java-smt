// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier.EXISTS;
import static org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier.FORALL;
import static org.sosy_lab.java_smt.solvers.princess.PrincessEnvironment.toSeq;
import static scala.collection.JavaConverters.asJava;
import static scala.collection.JavaConverters.asJavaCollection;

import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IBoolLit;
import ap.parser.IConstant;
import ap.parser.IEpsilon;
import ap.parser.IEquation;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFormulaITE;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;
import ap.parser.INot;
import ap.parser.IPlus;
import ap.parser.IQuantified;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.parser.ITimes;
import ap.parser.IVariable;
import ap.terfor.conjunctions.Quantifier;
import ap.terfor.preds.Predicate;
import ap.theories.arrays.ExtArray;
import ap.theories.bitvectors.ModuloArithmetic;
import ap.theories.nia.GroebnerMultiplication$;
import ap.theories.rationals.Rationals;
import ap.types.Sort;
import ap.types.Sort$;
import com.google.common.base.Preconditions;
import com.google.common.collect.HashBasedTable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Table;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.FunctionDeclarationImpl;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessBitvectorToBitvectorDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessBitvectorToBooleanDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessByExampleDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessEquationDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessIFunctionDeclaration;
import org.sosy_lab.java_smt.solvers.princess.PrincessFunctionDeclaration.PrincessMultiplyDeclaration;
import scala.Enumeration;

class PrincessFormulaCreator
    extends FormulaCreator<IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  // Hash-maps from interpreted functions and predicates to their corresponding
  // Java-SMT kind
  private static final Map<IFunction, FunctionDeclarationKind> theoryFunctionKind = new HashMap<>();
  private static final Map<Predicate, FunctionDeclarationKind> theoryPredKind = new HashMap<>();
  private static final Set<String> CONSTANT_UFS = ImmutableSet.of("str_cons", "str_empty");

  static {
    theoryFunctionKind.put(ModuloArithmetic.bv_concat(), FunctionDeclarationKind.BV_CONCAT);
    theoryFunctionKind.put(ModuloArithmetic.bv_extract(), FunctionDeclarationKind.BV_EXTRACT);
    theoryFunctionKind.put(ModuloArithmetic.bv_not(), FunctionDeclarationKind.BV_NOT);
    theoryFunctionKind.put(ModuloArithmetic.bv_neg(), FunctionDeclarationKind.BV_NEG);
    theoryFunctionKind.put(ModuloArithmetic.bv_and(), FunctionDeclarationKind.BV_AND);
    theoryFunctionKind.put(ModuloArithmetic.bv_or(), FunctionDeclarationKind.BV_OR);
    theoryFunctionKind.put(ModuloArithmetic.bv_add(), FunctionDeclarationKind.BV_ADD);
    theoryFunctionKind.put(ModuloArithmetic.bv_sub(), FunctionDeclarationKind.BV_SUB);
    theoryFunctionKind.put(ModuloArithmetic.bv_mul(), FunctionDeclarationKind.BV_MUL);
    theoryFunctionKind.put(ModuloArithmetic.bv_udiv(), FunctionDeclarationKind.BV_UDIV);
    theoryFunctionKind.put(ModuloArithmetic.bv_sdiv(), FunctionDeclarationKind.BV_SDIV);
    theoryFunctionKind.put(ModuloArithmetic.bv_urem(), FunctionDeclarationKind.BV_UREM);
    theoryFunctionKind.put(ModuloArithmetic.bv_srem(), FunctionDeclarationKind.BV_SREM);
    theoryFunctionKind.put(ModuloArithmetic.bv_smod(), FunctionDeclarationKind.BV_SMOD);
    theoryFunctionKind.put(ModuloArithmetic.bv_shl(), FunctionDeclarationKind.BV_SHL);
    theoryFunctionKind.put(ModuloArithmetic.bv_lshr(), FunctionDeclarationKind.BV_LSHR);
    theoryFunctionKind.put(ModuloArithmetic.bv_ashr(), FunctionDeclarationKind.BV_ASHR);
    theoryFunctionKind.put(ModuloArithmetic.bv_xor(), FunctionDeclarationKind.BV_XOR);
    // modmod.bv_xnor()?
    // modmod.bv_comp()?

    // casts to integer, sign/zero-extension?

    theoryPredKind.put(ModuloArithmetic.bv_ult(), FunctionDeclarationKind.BV_ULT);
    theoryPredKind.put(ModuloArithmetic.bv_ule(), FunctionDeclarationKind.BV_ULE);
    theoryPredKind.put(ModuloArithmetic.bv_slt(), FunctionDeclarationKind.BV_SLT);
    theoryPredKind.put(ModuloArithmetic.bv_sle(), FunctionDeclarationKind.BV_SLE);

    theoryFunctionKind.put(GroebnerMultiplication$.MODULE$.mul(), FunctionDeclarationKind.MUL);

    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_$plus$plus(), FunctionDeclarationKind.STR_CONCAT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_len(), FunctionDeclarationKind.STR_LENGTH);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_indexof(), FunctionDeclarationKind.STR_INDEX_OF);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_at(), FunctionDeclarationKind.STR_CHAR_AT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_substr(), FunctionDeclarationKind.STR_SUBSTRING);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_replace(), FunctionDeclarationKind.STR_REPLACE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_replaceall(), FunctionDeclarationKind.STR_REPLACE_ALL);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_to_re(), FunctionDeclarationKind.STR_TO_RE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_to_int(), FunctionDeclarationKind.STR_TO_INT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_to_code(), FunctionDeclarationKind.STR_TO_CODE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.str_from_code(), FunctionDeclarationKind.STR_FROM_CODE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_range(), FunctionDeclarationKind.RE_RANGE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_$plus$plus(), FunctionDeclarationKind.RE_CONCAT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_union(), FunctionDeclarationKind.RE_UNION);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_inter(), FunctionDeclarationKind.RE_INTERSECT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_$times(), FunctionDeclarationKind.RE_STAR);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_$plus(), FunctionDeclarationKind.RE_PLUS);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_diff(), FunctionDeclarationKind.RE_DIFFERENCE);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_opt(), FunctionDeclarationKind.RE_OPTIONAL);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.re_comp(), FunctionDeclarationKind.RE_COMPLEMENT);
    theoryFunctionKind.put(
        PrincessEnvironment.stringTheory.int_to_str(), FunctionDeclarationKind.INT_TO_STR);

    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_prefixof(), FunctionDeclarationKind.STR_PREFIX);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_suffixof(), FunctionDeclarationKind.STR_SUFFIX);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_contains(), FunctionDeclarationKind.STR_CONTAINS);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_$less$eq(), FunctionDeclarationKind.STR_LE);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_$less(), FunctionDeclarationKind.STR_LT);
    theoryPredKind.put(
        PrincessEnvironment.stringTheory.str_in_re(), FunctionDeclarationKind.STR_IN_RE);
  }

  /**
   * This mapping is a cache from index sort and element sort to the full array sort.
   *
   * <p>This mapping guarantees uniqueness of array types in JavaSMT, i.e. without this cache, we
   * can not compare arrays, because all of them have distinct sorts, and SELECT/STORE operations
   * are also incomparable and result in trivially satisfiable SMT queries (with no visible hint on
   * the reason, except distinct sort objects).
   */
  private final Table<Sort, Sort, Sort> arraySortCache = HashBasedTable.create();

  PrincessFormulaCreator(PrincessEnvironment pEnv) {
    super(
        pEnv,
        PrincessEnvironment.BOOL_SORT,
        PrincessEnvironment.INTEGER_SORT,
        PrincessEnvironment.FRACTION_SORT,
        PrincessEnvironment.STRING_SORT,
        PrincessEnvironment.REGEX_SORT);
  }

  @Override
  public Object convertValue(IExpression value) {
    if (value instanceof IBoolLit) {
      return ((IBoolLit) value).value();
    } else if (value instanceof IIntLit) {
      return ((IIntLit) value).value().bigIntValue();
    }
    if (value instanceof IFunApp) {
      IFunApp fun = (IFunApp) value;
      switch (fun.fun().name()) {
        case "true":
          Preconditions.checkArgument(fun.fun().arity() == 0);
          return true;
        case "false":
          Preconditions.checkArgument(fun.fun().arity() == 0);
          return false;
        case "mod_cast":
          // we found a bitvector BV(lower, upper, ctxt), lets extract the last parameter
          return ((IIntLit) fun.apply(2)).value().bigIntValue();
        case "Rat_fromRing":
          Preconditions.checkArgument(fun.fun().arity() == 1);
          ITerm term = fun.apply(0);
          if (term instanceof IIntLit) {
            return ((IIntLit) term).value().bigIntValue();
          }
          break;
        case "Rat_frac":
          Preconditions.checkArgument(fun.fun().arity() == 2);
          ITerm term1 = fun.apply(0);
          ITerm term2 = fun.apply(1);
          if (term1 instanceof IIntLit && term2 instanceof IIntLit) {
            Rational ratValue =
                Rational.of(
                    ((IIntLit) term1).value().bigIntValue(),
                    ((IIntLit) term2).value().bigIntValue());
            return ratValue.isIntegral() ? ratValue.getNum() : ratValue;
          }
          break;
        case "str_empty":
        case "str_cons":
          return strToString(fun);
        default:
      }
    }

    throw new IllegalArgumentException(
        "unhandled model value " + value + " of type " + value.getClass());
  }

  /**
   * convert a recursive string term like "str_cons(97, str_cons(98, str_cons(99, str_empty)))" to a
   * real string "abc" for the user.
   */
  private Object strToString(IFunApp fun) {
    final StringBuilder str = new StringBuilder();
    while ("str_cons".equals(fun.fun().name())) {
      checkArgument(fun.fun().arity() == 2);
      ITerm arg = fun.apply(0);
      IIntLit chr;
      if (arg instanceof IIntLit) {
        chr = ((IIntLit) arg);
      } else if (arg instanceof IFunApp
          && ModuloArithmetic.mod_cast().equals(((IFunApp) arg).fun())) {
        chr = ((IIntLit) ((IFunApp) arg).apply(2));
      } else {
        throw new AssertionError("unexpected string value: " + fun);
      }
      str.append(Character.toString(chr.value().bigIntValue().intValue()));
      fun = (IFunApp) fun.apply(1);
    }
    checkArgument("str_empty".equals(fun.fun().name()));
    checkArgument(fun.fun().arity() == 0);
    return str.toString();
  }

  @Override
  public FormulaType<?> getFormulaType(IExpression pFormula) {
    return PrincessEnvironment.getFormulaType(pFormula);
  }

  @Override
  public IExpression makeVariable(Sort type, String varName) {
    return getEnv().makeVariable(type, varName);
  }

  @Override
  public Sort getBitvectorType(int pBitwidth) {
    return ModuloArithmetic.UnsignedBVSort$.MODULE$.apply(pBitwidth);
  }

  @Override
  public Sort getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("FloatingPoint theory is not supported by Princess");
  }

  @Override
  public Sort getArrayType(Sort pIndexType, Sort pElementType) {
    Sort result = arraySortCache.get(pIndexType, pElementType);
    if (result == null) {
      result = new ExtArray(toSeq(ImmutableList.of(pIndexType)), pElementType).sort();
      arraySortCache.put(pIndexType, pElementType, result);
    }
    return result;
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(final T pFormula) {
    if (pFormula instanceof BitvectorFormula) {
      ITerm input = (ITerm) extractInfo(pFormula);
      Sort sort = Sort$.MODULE$.sortOf(input);
      scala.Option<Object> bitWidth = PrincessEnvironment.getBitWidth(sort);
      checkArgument(
          bitWidth.isDefined(), "BitvectorFormula with actual type %s: %s", sort, pFormula);
      return (FormulaType<T>) FormulaType.getBitvectorTypeWithSize((Integer) bitWidth.get());

    } else if (pFormula instanceof ArrayFormula<?, ?>) {
      final FormulaType<?> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<?, ?>) pFormula);
      final FormulaType<?> arrayElementType =
          getArrayFormulaElementType((ArrayFormula<?, ?>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }

    return super.getFormulaType(pFormula);
  }

  private String getName(IExpression input) {
    if (input instanceof IAtom) {
      return ((IAtom) input).pred().name();
    } else if (input instanceof IConstant) {
      return ((IConstant) input).c().name();
    } else if (input instanceof IBinFormula) {
      return ((IBinFormula) input).j().toString();
    } else if (input instanceof IFormulaITE || input instanceof ITermITE) {
      // in princess ite representation is the complete formula which we do not want here
      return "ite";
    } else if (input instanceof IIntFormula) {
      return ((IIntFormula) input).rel().toString();
    } else if (input instanceof INot) {
      // in princess not representation is the complete formula which we do not want here
      return "not";
    } else if (input instanceof IFunApp) {
      return ((IFunApp) input).fun().name();
    } else if (input instanceof IPlus) {
      // in princess plus representation is the complete formula which we do not want here
      return "+";
    } else if (input instanceof ITimes) {
      // in princess times representation is the complete formula which we do not want here
      return "*";
    } else if (input instanceof IEpsilon) {
      // in princess epsilon representation is the complete formula which we do not want here
      return "eps";
    } else if (input instanceof IEquation) {
      return "=";
    } else {
      throw new AssertionError("Unhandled type " + input.getClass());
    }
  }

  /** Returns true if the expression is a constant number. */
  private static boolean isConstant(IFunApp pExpr) {
    for (IExpression sub : asJava(pExpr.args())) {
      if (!(sub instanceof IIntLit)) {
        return false;
      }
    }
    return true;
  }

  /** Returns true if the expression is an integer literal. */
  private static boolean isRatInt(IFunApp pExpr) {
    return isConstant(pExpr) && pExpr.fun().equals(Rationals.fromRing());
  }

  /** Returns true if the expression is a faction literal. */
  private static boolean isRatFrac(IFunApp pExpr) {
    return isConstant(pExpr) && pExpr.fun().equals(Rationals.frac());
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, final Formula f, final IExpression input) {
    if (input instanceof IIntLit) {
      IdealInt value = ((IIntLit) input).value();
      return visitor.visitConstant(f, value.bigIntValue());

    } else if (input instanceof IBoolLit) {
      IBoolLit literal = (IBoolLit) input;
      return visitor.visitConstant(f, literal.value());

    } else if (input instanceof IFunApp
        && (isRatInt((IFunApp) input) || isRatFrac((IFunApp) input))) {
      return visitor.visitConstant(f, convertValue(input));

    } else if (input instanceof IQuantified) {
      // this is a quantifier

      BooleanFormula body = encapsulateBoolean(((IQuantified) input).subformula());
      return visitor.visitQuantifier(
          (BooleanFormula) f,
          ((IQuantified) input).quan().equals(Quantifier.apply(true)) ? FORALL : EXISTS,

          // Princess does not hold any metadata about bound variables,
          // so we can't get meaningful list here.
          // HOWEVER, passing this list to QuantifiedFormulaManager#mkQuantifier
          // works as expected.
          new ArrayList<>(),
          body);

    } else if (input instanceof IVariable) {
      // variable bound by a quantifier
      return visitor.visitBoundVariable(f, ((IVariable) input).index());

    } else if (((input instanceof IAtom) && asJavaCollection(((IAtom) input).args()).isEmpty())
        || input instanceof IConstant) {
      // nullary atoms and constant are variables
      return visitor.visitFreeVariable(f, input.toString());

    } else if (input instanceof ITimes) {
      // Princess encodes multiplication as "linear coefficient and factor" with arity 1.
      assert input.length() == 1;

      ITimes multiplication = (ITimes) input;
      IIntLit coeff = new IIntLit(multiplication.coeff());
      FormulaType<IntegerFormula> coeffType = FormulaType.IntegerType;
      IExpression factor = multiplication.subterm();
      FormulaType<?> factorType = getFormulaType(factor);

      return visitor.visitFunction(
          f,
          ImmutableList.of(encapsulate(coeffType, coeff), encapsulate(factorType, factor)),
          FunctionDeclarationImpl.of(
              getName(input),
              getDeclarationKind(input),
              ImmutableList.of(coeffType, factorType),
              getFormulaType(f),
              PrincessMultiplyDeclaration.INSTANCE));
    }

    // then we have to check the declaration kind
    final FunctionDeclarationKind kind = getDeclarationKind(input);

    if (kind == FunctionDeclarationKind.EQ) {
      scala.Option<scala.Tuple2<ITerm, ITerm>> maybeArgs =
          IExpression.Eq$.MODULE$.unapply((IFormula) input);

      assert maybeArgs.isDefined();

      final ITerm left = maybeArgs.get()._1;
      final ITerm right = maybeArgs.get()._2;

      ImmutableList.Builder<Formula> args = ImmutableList.builder();
      ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();

      FormulaType<?> argumentTypeLeft = getFormulaType(left);
      args.add(encapsulate(argumentTypeLeft, left));
      argTypes.add(argumentTypeLeft);
      FormulaType<?> argumentTypeRight = getFormulaType(right);
      args.add(encapsulate(argumentTypeRight, right));
      argTypes.add(argumentTypeRight);

      return visitor.visitFunction(
          f,
          args.build(),
          FunctionDeclarationImpl.of(
              getName(input),
              FunctionDeclarationKind.EQ,
              argTypes.build(),
              getFormulaType(f),
              PrincessEquationDeclaration.INSTANCE));
    }

    if (kind == FunctionDeclarationKind.UF && input instanceof IIntFormula) {
      assert ((IIntFormula) input).rel().equals(IIntRelation.EqZero());
      // this is really a Boolean formula, visit the lhs of the equation
      return visit(visitor, f, ((IIntFormula) input).t());
    }

    if (kind == FunctionDeclarationKind.OTHER && input instanceof IFunApp) {
      if (ModuloArithmetic.mod_cast().equals(((IFunApp) input).fun())
          && ((IFunApp) input).apply(2) instanceof IIntLit) {
        // mod_cast(0, 256, 7) -> BV=7 with bitsize=8
        return visitor.visitConstant(f, convertValue(input));
      }
    }

    if (kind == FunctionDeclarationKind.UF && input instanceof IFunApp) {
      if (CONSTANT_UFS.contains(((IFunApp) input).fun().name())) {
        return visitor.visitConstant(f, convertValue(input));
      }
    }

    ImmutableList.Builder<Formula> args = ImmutableList.builder();
    ImmutableList.Builder<FormulaType<?>> argTypes = ImmutableList.builder();
    int arity = input.length();
    int arityStart = 0;

    PrincessFunctionDeclaration solverDeclaration;
    if (isBitvectorOperationWithAdditionalArgument(kind)) {
      // the first argument is the bitsize, and it is not relevant for the user.
      // we do not want type/sort information as arguments.
      arityStart = 1;
      if (input instanceof IAtom) {
        solverDeclaration = new PrincessBitvectorToBooleanDeclaration(((IAtom) input).pred());
      } else if (input instanceof IFunApp) {
        solverDeclaration = new PrincessBitvectorToBitvectorDeclaration(((IFunApp) input).fun());
      } else {
        throw new AssertionError(
            String.format("unexpected bitvector operation '%s' for formula '%s'", kind, input));
      }
    } else if (input instanceof IFunApp) {
      if (kind == FunctionDeclarationKind.UF) {
        solverDeclaration = new PrincessIFunctionDeclaration(((IFunApp) input).fun());
      } else if (kind == FunctionDeclarationKind.MUL) {
        solverDeclaration = PrincessMultiplyDeclaration.INSTANCE;
      } else {
        solverDeclaration = new PrincessByExampleDeclaration(input);
      }
    } else {
      solverDeclaration = new PrincessByExampleDeclaration(input);
    }

    for (int i = arityStart; i < arity; i++) {
      IExpression arg = input.apply(i);
      FormulaType<?> argumentType = getFormulaType(arg);
      args.add(encapsulate(argumentType, arg));
      argTypes.add(argumentType);
    }

    return visitor.visitFunction(
        f,
        args.build(),
        FunctionDeclarationImpl.of(
            getName(input), kind, argTypes.build(), getFormulaType(f), solverDeclaration));
  }

  private boolean isBitvectorOperationWithAdditionalArgument(FunctionDeclarationKind kind) {
    switch (kind) {
      case BV_NOT:
      case BV_NEG:
      case BV_OR:
      case BV_AND:
      case BV_XOR:
      case BV_SUB:
      case BV_ADD:
      case BV_SDIV:
      case BV_UDIV:
      case BV_SREM:
      case BV_UREM:
      case BV_SMOD:
      case BV_MUL:
      case BV_ULT:
      case BV_SLT:
      case BV_ULE:
      case BV_SLE:
      case BV_UGT:
      case BV_SGT:
      case BV_UGE:
      case BV_SGE:
      case BV_EQ:
        return true;
      default:
        return false;
    }
  }

  private FunctionDeclarationKind getDeclarationKind(IExpression input) {
    assert !(((input instanceof IAtom) && asJavaCollection(((IAtom) input).args()).isEmpty())
            || input instanceof IConstant)
        : "Variables should be handled somewhere else";

    if (input instanceof IFormulaITE || input instanceof ITermITE) {
      return FunctionDeclarationKind.ITE;
    } else if (input instanceof IFunApp) {
      final IFunction fun = ((IFunApp) input).fun();
      final FunctionDeclarationKind theoryKind = theoryFunctionKind.get(fun);
      if (theoryKind != null) {
        return theoryKind;
      } else if (ExtArray.Select$.MODULE$.unapply(fun).isDefined()) {
        return FunctionDeclarationKind.SELECT;
      } else if (ExtArray.Store$.MODULE$.unapply(fun).isDefined()) {
        return FunctionDeclarationKind.STORE;
      } else if (ExtArray.Const$.MODULE$.unapply(fun).isDefined()) {
        return FunctionDeclarationKind.CONST;
      } else if (fun == ModuloArithmetic.mod_cast()) {
        return FunctionDeclarationKind.OTHER;
      } else if (fun == ModuloArithmetic.int_cast()) {
        return FunctionDeclarationKind.OTHER;
      } else if (fun == Rationals.addition()) {
        return FunctionDeclarationKind.ADD;
      } else if (fun == Rationals.multiplication()) {
        return FunctionDeclarationKind.MUL;
      } else if (fun == Rationals.division()) {
        return FunctionDeclarationKind.DIV;
      } else {
        return FunctionDeclarationKind.UF;
      }
    } else if (input instanceof IAtom) {
      final Predicate pred = ((IAtom) input).pred();
      final FunctionDeclarationKind theoryKind = theoryPredKind.get(pred);
      if (theoryKind != null) {
        return theoryKind;
      } else {
        return FunctionDeclarationKind.UF;
      }
    } else if (isBinaryFunction(input, IBinJunctor.And())) {
      return FunctionDeclarationKind.AND;
    } else if (isBinaryFunction(input, IBinJunctor.Or())) {
      return FunctionDeclarationKind.OR;
    } else if (input instanceof INot) {
      return FunctionDeclarationKind.NOT;
    } else if (isBinaryFunction(input, IBinJunctor.Eqv())) {
      return FunctionDeclarationKind.IFF;
    } else if (input instanceof ITimes) {
      return FunctionDeclarationKind.MUL;
    } else if (input instanceof IPlus) {
      // SUB does not exist in princess a - b is a + (-b) there
      return FunctionDeclarationKind.ADD;
    } else if (input instanceof IEquation) {
      return FunctionDeclarationKind.EQ;
    } else if (input instanceof IIntFormula) {
      IIntFormula f = (IIntFormula) input;
      if (f.rel().equals(IIntRelation.EqZero())) {
        final Sort sort = Sort$.MODULE$.sortOf(((IIntFormula) input).t());
        if (sort == PrincessEnvironment.BOOL_SORT) {
          // this is really a Boolean formula, it has to be UF
          return FunctionDeclarationKind.UF;
        } else if (sort == PrincessEnvironment.INTEGER_SORT) {
          return FunctionDeclarationKind.EQ_ZERO;
        } else {
          return FunctionDeclarationKind.EQ;
        }
      } else if (f.rel().equals(IIntRelation.GeqZero())) {
        return FunctionDeclarationKind.GTE_ZERO;
      } else {
        throw new AssertionError("Unhandled value for integer relation");
      }

    } else {
      // we cannot handle XOR, IMPLIES, DISTINCT, DIV, MODULO, LT, LTE GT in princess
      // they are either handled implicitly by the above-mentioned parts or not at all
      return FunctionDeclarationKind.OTHER;
    }
  }

  private static boolean isBinaryFunction(IExpression t, Enumeration.Value val) {
    return (t instanceof IBinFormula) && val.equals(((IBinFormula) t).j()); // j is the operator
  }

  @Override
  public PrincessFunctionDeclaration declareUFImpl(
      String pName, Sort pReturnType, List<Sort> args) {
    return new PrincessIFunctionDeclaration(environment.declareFun(pName, pReturnType, args));
  }

  @Override
  public IExpression callFunctionImpl(
      PrincessFunctionDeclaration declaration, List<IExpression> args) {
    return declaration.makeApp(environment, args);
  }

  @Override
  protected PrincessFunctionDeclaration getBooleanVarDeclarationImpl(IExpression pIExpression) {
    return new PrincessByExampleDeclaration(pIExpression);
  }
}
