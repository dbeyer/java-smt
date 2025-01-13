// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static scala.collection.JavaConverters.asJava;

import ap.api.PartialModel;
import ap.api.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.ITerm;
import ap.terfor.preds.Predicate;
import ap.theories.arrays.ExtArray;
import ap.theories.arrays.ExtArray.ArraySort;
import ap.theories.arrays.ExtArray.Select$;
import ap.theories.arrays.ExtArray.Store$;
import ap.types.Sort;
import ap.types.Sort$;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Multimap;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import scala.Option;

class PrincessModel extends AbstractModel<IExpression, Sort, PrincessEnvironment> {
  private final PartialModel model;
  private final SimpleAPI api;

  PrincessModel(
      PrincessAbstractProver<?> pProver,
      PartialModel partialModel,
      FormulaCreator<IExpression, Sort, PrincessEnvironment, ?> creator,
      SimpleAPI pApi) {
    super(pProver, creator);
    this.model = partialModel;
    this.api = pApi;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    scala.collection.Map<IExpression, IExpression> interpretation = model.interpretation();

    // get abbreviations, we do not want to export them.
    Set<Predicate> abbrevs = new LinkedHashSet<>();
    for (var entry : asJava(api.ap$api$SimpleAPI$$apiStack().abbrevPredicates()).entrySet()) {
      abbrevs.add(entry.getKey()); // collect the abbreviation.
      abbrevs.add(entry.getValue()._2()); // the definition is also handled as abbreviation here.
    }

    // first get the addresses of arrays
    Multimap<IFunApp, ITerm> arrays = getArrays(interpretation);

    // then iterate over the model and generate the assignments
    ImmutableSet.Builder<ValueAssignment> assignments = ImmutableSet.builder();
    for (Map.Entry<IExpression, IExpression> entry : asJava(interpretation).entrySet()) {
      if (!entry.getKey().toString().equals("Rat_denom") && !isAbbrev(abbrevs, entry.getKey())) {
        assignments.addAll(getAssignments(entry.getKey(), entry.getValue(), arrays));
      }
    }
    return assignments.build().asList();
  }

  private boolean isAbbrev(Set<Predicate> abbrevs, IExpression var) {
    return var instanceof IAtom && abbrevs.contains(((IAtom) var).pred());
  }

  /**
   * Collect array-models, we need them to replace identifiers later.
   *
   * <p>Princess models arrays as filled, based on a zero-filled array. The model for an
   * array-access (via 'select') uses the filled array instead of the name and is handled later (see
   * #getAssignment). The model gives more information, like the (partially) filled array and all
   * array accesses based on (here comes the weird part:) some intermediate array evaluation.
   *
   * <p>Example: "arr[5]=123" with a following "result_arr[6]=123" (writing into an array in SMT
   * returns a new copy of it!) is modeled as
   *
   * <pre>
   * {
   *     x -> 123,
   *     arr -> store(const(0), 5, 123),
   *     store(store(const(0), 5, 123), 6, 123) -> store(store(const(0), 5, 123), 6, 123),
   *     select(store(const(0), 5, 123), 5) -> 123
   * }
   * </pre>
   *
   * <p>The returned mapping contains the mapping of the complete array value ("store(const(0), 5,
   * 123)") to the identifier ("arr").
   */
  private Multimap<IFunApp, ITerm> getArrays(
      scala.collection.Map<IExpression, IExpression> interpretation) {
    Multimap<IFunApp, ITerm> arrays = ArrayListMultimap.create();
    for (Map.Entry<IExpression, IExpression> entry : asJava(interpretation).entrySet()) {
      if (entry.getKey() instanceof IConstant) {
        ITerm maybeArray = (IConstant) entry.getKey();
        IExpression value = entry.getValue();
        if (creator.getEnv().hasArrayType(maybeArray)
            && value instanceof IFunApp
            && Store$.MODULE$.unapply(((IFunApp) value).fun()).isDefined()) {
          // It is value -> variables, hence if 2+ vars have the same value we need a list
          arrays.put((IFunApp) value, maybeArray);
        }
      }
    }
    return arrays;
  }

  private ImmutableList<ValueAssignment> getAssignments(
      IExpression key, IExpression value, Multimap<IFunApp, ITerm> pArrays) {

    // first check array-access, for explanation see #getArrays.
    // those cases can return multiple assignments per model entry.
    if (key instanceof IConstant) {
      if (creator.getEnv().hasArrayType(key)) {
        return ImmutableList.of();
      }
    } else if (key instanceof IFunApp) {
      IFunApp cKey = (IFunApp) key;
      if ("valueAlmostEverywhere".equals(cKey.fun().name())
          && creator.getEnv().hasArrayType(Iterables.getOnlyElement(asJava(cKey.args())))) {
        return ImmutableList.of();
      }
      Sort sort = Sort$.MODULE$.sortOf(cKey);
      if (Select$.MODULE$.unapply(cKey.fun()).isDefined()) {
        return getAssignmentsFromArraySelect(value, cKey, pArrays);
      } else if (sort instanceof ArraySort) {
        ExtArray arrayTheory = ((ArraySort) sort).theory();
        if (arrayTheory.store() == cKey.fun()) {
          return getAssignmentsFromArrayStore((IFunApp) value, cKey, pArrays);
        } else if (arrayTheory.store2() == cKey.fun()) {
          return getAssignmentsFromArrayStore((IFunApp) value, cKey, pArrays);
        }
      }
    }

    // then handle assignments for non-array cases.
    // we expect exactly one assignment per model entry.

    String name;
    IFormula fAssignment;
    List<Object> argumentInterpretations = ImmutableList.of();

    if (key instanceof IAtom) {
      name = key.toString();
      fAssignment = new IBinFormula(IBinJunctor.Eqv(), (IAtom) key, (IFormula) value);

    } else if (key instanceof IConstant) {
      name = key.toString();
      fAssignment = ((IConstant) key).$eq$eq$eq((ITerm) value);

    } else if (key instanceof IFunApp) {
      // normal variable or UF
      IFunApp cKey = (IFunApp) key;
      argumentInterpretations = new ArrayList<>();
      for (ITerm arg : asJava(cKey.args())) {
        argumentInterpretations.add(creator.convertValue(arg));
      }
      name = cKey.fun().name();
      fAssignment = ((ITerm) key).$eq$eq$eq((ITerm) value);

    } else {
      throw new AssertionError(
          String.format("unknown type of key: %s -> %s (%s)", key, value, key.getClass()));
    }

    return ImmutableList.of(
        new ValueAssignment(
            creator.encapsulateWithTypeOf(key),
            creator.encapsulateWithTypeOf(value),
            creator.encapsulateBoolean(fAssignment),
            name,
            creator.convertValue(value),
            argumentInterpretations));
  }

  /** array-access, for explanation see #getArrayAddresses. */
  private ImmutableList<ValueAssignment> getAssignmentsFromArraySelect(
      IExpression fValue, IFunApp cKey, Multimap<IFunApp, ITerm> pArrays) {
    IFunApp arrayId = (IFunApp) cKey.args().apply(Integer.valueOf(0));
    ITerm arrayIndex = cKey.args().apply(Integer.valueOf(1));
    ImmutableList.Builder<ValueAssignment> arrayAssignments = ImmutableList.builder();
    for (ITerm arrayF : pArrays.get(arrayId)) {
      ITerm select = creator.getEnv().makeSelect(arrayF, arrayIndex);
      arrayAssignments.add(
          new ValueAssignment(
              creator.encapsulateWithTypeOf(select),
              creator.encapsulateWithTypeOf(fValue),
              creator.encapsulateBoolean(select.$eq$eq$eq((ITerm) fValue)),
              arrayF.toString(),
              creator.convertValue(fValue),
              ImmutableList.of(creator.convertValue(arrayIndex))));
    }
    return arrayAssignments.build();
  }

  /** array-access, for explanation see #getArrayAddresses. */
  private ImmutableList<ValueAssignment> getAssignmentsFromArrayStore(
      IFunApp value, IFunApp cKey, Multimap<IFunApp, ITerm> pArrays) {
    ITerm arrayIndex = cKey.args().apply(Integer.valueOf(1));
    ITerm arrayContent = cKey.args().apply(Integer.valueOf(2));
    ImmutableList.Builder<ValueAssignment> arrayAssignments = ImmutableList.builder();
    for (ITerm arrayF : pArrays.get(value)) {
      ITerm select = creator.getEnv().makeSelect(arrayF, arrayIndex);
      arrayAssignments.add(
          new ValueAssignment(
              creator.encapsulateWithTypeOf(select),
              creator.encapsulateWithTypeOf(arrayContent),
              creator.encapsulateBoolean(select.$eq$eq$eq(arrayContent)),
              arrayF.toString(),
              creator.convertValue(arrayContent),
              ImmutableList.of(creator.convertValue(arrayIndex))));
    }
    return arrayAssignments.build();
  }

  @Override
  public String toString() {
    return model.toString();
  }

  @Override
  protected @Nullable IExpression evalImpl(IExpression formula) {
    IExpression evaluation = evaluate(formula);
    if (evaluation == null) {
      // fallback: try to simplify the query and evaluate again.
      evaluation = evaluate(creator.getEnv().simplify(formula));
    }
    return evaluation;
  }

  @Nullable
  private IExpression evaluate(IExpression formula) {
    if (formula instanceof ITerm) {
      Option<ITerm> out = model.evalToTerm((ITerm) formula);
      return out.isEmpty() ? null : out.get();
    } else if (formula instanceof IFormula) {
      Option<IExpression> out = model.evalExpression(formula);
      return out.isEmpty() ? null : out.get();
    } else {
      throw new AssertionError("unexpected formula: " + formula);
    }
  }
}
